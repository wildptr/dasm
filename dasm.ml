open Batteries
open Format
open Inst

type prefix =
  | Prefix_26 (* ES *)
  | Prefix_2e (* CS or branch not taken *)
  | Prefix_36 (* SS *)
  | Prefix_3e (* DS or branch taken *)
  | Prefix_64 (* FS *)
  | Prefix_65 (* GS *)
  | Prefix_66
  | Prefix_67
  | Prefix_f0
  | Prefix_f2
  | Prefix_f3

(* prefixes can be packed into 7 bits *)
let prefix_mask = function
  | Prefix_26
  | Prefix_2e
  | Prefix_36
  | Prefix_3e
  | Prefix_64
  | Prefix_65 -> 0x1c
  | Prefix_66 -> 0x20
  | Prefix_67 -> 0x40
  | Prefix_f0
  | Prefix_f2
  | Prefix_f3 -> 3

let prefix_value = function
  | Prefix_26 -> 1 lsl 2
  | Prefix_2e -> 2 lsl 2
  | Prefix_36 -> 3 lsl 2
  | Prefix_3e -> 4 lsl 2
  | Prefix_64 -> 5 lsl 2
  | Prefix_65 -> 6 lsl 2
  | Prefix_66 -> 0x20
  | Prefix_67 -> 0x40
  | Prefix_f0 -> 1
  | Prefix_f2 -> 2
  | Prefix_f3 -> 3

exception Not_implemented
exception Invalid_instruction
exception Invalid_operand

type regset =
  | Reg8bitLegacy
  | Reg8bitUniform
  | Reg16bit
  | Reg32bit
  | Reg64bit

let seg_reg_table = [|R_ES;R_CS;R_SS;R_DS;R_FS;R_GS|]

let int_to_reg regset i =
  let table8 =
    [|R_AL;R_CL;R_DL;R_BL;R_AH;R_CH;R_DH;R_BH|]
  in
  let table16 =
    [|R_AX;R_CX;R_DX;R_BX;R_SP;R_BP;R_SI;R_DI|]
  in
  let table32 =
    [|R_EAX;R_ECX;R_EDX;R_EBX;R_ESP;R_EBP;R_ESI;R_EDI|]
  in
  match regset with
  | Reg8bitLegacy -> table8.(i)
  | Reg16bit -> table16.(i)
  | Reg32bit -> table32.(i)
  | _ -> raise Not_implemented

type cpu_mode =
  | Mode16bit
  | Mode32bit
  | Mode64bit

type config = {
  mode : cpu_mode;
  pc_opt : nativeint option;
}

let read_sib s : int * ((int * int) option) =
  let sib = int_of_char (s ()) in
  let sib_s = sib lsr 6 in
  let sib_i = sib lsr 3 land 7 in
  let sib_b = sib land 7 in
  let index =
    if sib_i = 4
    then None
    else Some (sib_i, 1 lsl sib_s)
  in
  let base = sib_b in
  (base, index)

let read_imm n s =
  let rec f n' acc =
    if n' = n
    then
      let shamt = n*8-1 in
      let mask = Nativeint.shift_left 1n shamt in
      if Nativeint.logand acc mask = 0n then
        acc
      else
        Nativeint.(acc - (shift_left mask 1)) (* sign-extend immediate *)
    else
      let b = int_of_char (s ()) in
      let shamt = n'*8 in
      f (n'+1) Nativeint.(logor acc (shift_left (of_int b) shamt))
  in
  f 0 0n

(* the int in return value is opcode extension field i.e. ModRM[5:3] *)
let read_regmem16 s seg_opt : int * regmem =
  let decode_base_index = function
    | 0 -> R_BX, Some (R_SI, 1)
    | 1 -> R_BX, Some (R_DI, 1)
    | 2 -> R_BP, Some (R_SI, 1)
    | 3 -> R_BP, Some (R_DI, 1)
    | 4 -> R_SI, None
    | 5 -> R_DI, None
    | 6 -> R_BP, None
    | 7 -> R_BX, None
    | _ -> assert false
  in
  let decode_seg r =
    match seg_opt with
    | Some seg -> seg
    | None ->
      begin match r with
        | 2 | 3 | 6 -> R_SS
        | _ -> R_DS
      end
  in

  let modrm = int_of_char (s ()) in
  let r = modrm land 7 in
  let rm =
    let m = modrm lsr 6 in (* mode field (ModRM[7:6]) *)
    begin match m with
      | 0 -> (* no displacement with the exn. of r=6 *)
        if r = 6 then
          let disp = read_imm 2 s in
          Mem { base = None; index = None; disp;
                seg = seg_opt |> Option.default R_DS }
        else
          let base, index = decode_base_index r in
          let seg = decode_seg r in
          Mem { base = Some base; index; disp = 0n; seg }
      | 1 | 2 ->
        let base, index = decode_base_index r in
        let disp = read_imm m s in
        let seg = decode_seg r in
        Mem { base = Some base; index; disp; seg }
      | 3 -> Reg r
      | _ -> assert false
    end
  in
  (modrm lsr 3 land 7, rm)

let read_regmem32 s seg_opt : int * regmem =
  let regset = Reg32bit in
  (* helper function *)
  let convert_index = function
    | Some (r, s) -> Some (int_to_reg Reg32bit r, s)
    | None -> None
  in

  let decode_seg b =
    match seg_opt with
    | Some seg -> seg
    | None ->
      begin match b with
        | 4 | 5 -> R_SS
        | _ -> R_DS
      end
  in

  let modrm = int_of_char (s ()) in
  let r = modrm land 7 in
  let rm =
    let m = modrm lsr 6 in (* mode field (ModRM[7:6]) *)
    begin match m with
      | 0 ->
        begin match r with
          | 4 -> (* SIB follows *)
            let sib_b, sib_si = read_sib s in
            let index = convert_index sib_si in
            if sib_b = 5
            then
              let disp = read_imm 4 s in
              let seg = seg_opt |> Option.default R_DS in
              Mem { base = None; index; disp; seg }
            else
              let base = Some (int_to_reg regset sib_b) in
              let seg = decode_seg sib_b in
              Mem { base; index; disp = 0n; seg }
          | 5 ->
            let disp = read_imm 4 s in
            let seg = seg_opt |> Option.default R_DS in
            Mem { base = None; index = None; disp; seg }
          | _ ->
            let base = Some (int_to_reg regset r) in
            let seg = decode_seg r in
            Mem { base; index = None; disp = 0n; seg }
        end
      | 1 | 2 ->
        let disp_size = if m = 1 then 1 else 4 in
        if r = 4
        then
          let sib_b, sib_si = read_sib s in
          let index = convert_index sib_si in
          let disp = read_imm disp_size s in
          let base = Some (int_to_reg regset sib_b) in
          let seg = decode_seg sib_b in
          Mem { base; index; disp; seg }
        else
          let disp = read_imm disp_size s in
          let base = Some (int_to_reg regset r) in
          let seg = decode_seg r in
          Mem { base; index = None; disp; seg }
      | 3 ->
        Reg r
      | _ -> assert false
    end
  in
  (modrm lsr 3 land 7, rm)

(*
 * 0 = none
 * 1 = I8
 * 2 = Iw (w = word size)
 * 3 = I16
 * 4 = I16I8
 * 5 = I16Iw
 * 6 = Ia (a = address size)
 *)
let inst_format_table =
  "\x10\x10\x10\x10\x01\x02\x00\x00\x10\x10\x10\x10\x01\x02\x00\x00\
   \x10\x10\x10\x10\x01\x02\x00\x00\x10\x10\x10\x10\x01\x02\x00\x00\
   \x10\x10\x10\x10\x01\x02\x00\x00\x10\x10\x10\x10\x01\x02\x00\x00\
   \x10\x10\x10\x10\x01\x02\x00\x00\x10\x10\x10\x10\x01\x02\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x10\x10\x00\x00\x00\x00\x02\x12\x01\x11\x00\x00\x00\x00\
   \x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\x01\
   \x11\x12\x11\x11\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x05\x00\x00\x00\x00\x00\
   \x06\x06\x06\x06\x00\x00\x00\x00\x01\x02\x00\x00\x00\x00\x00\x00\
   \x01\x01\x01\x01\x01\x01\x01\x01\x02\x02\x02\x02\x02\x02\x02\x02\
   \x11\x11\x03\x00\x10\x10\x11\x12\x04\x00\x03\x00\x00\x01\x00\x00\
   \x10\x10\x10\x10\x01\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x01\x01\x01\x01\x01\x01\x01\x01\x02\x02\x05\x01\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x10\x10\x00\x00\x00\x00\x00\x00\x10\x10"

let inst_format_table_0f =
  "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x10\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\x02\
   \x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\x10\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\
   \x00\x00\x00\x00\x00\x00\x10\x10\x00\x00\x00\x00\x00\x00\x10\x10\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

type operand_format =
  | R
  | R0
  | RO
  | RM
  | M
  | I
  | I2
  | O
  | FPU_R
  | XMM_R
  | XMM_RM
  | X of operand
  | Rs of int
  | RMs of int
  | Ms of int

let prefix_of_char = function
  | '\x26' -> Some Prefix_26
  | '\x2e' -> Some Prefix_2e
  | '\x36' -> Some Prefix_36
  | '\x3e' -> Some Prefix_3e
  | '\x64' -> Some Prefix_64
  | '\x65' -> Some Prefix_65
  | '\x66' -> Some Prefix_66
  | '\x67' -> Some Prefix_67
  | '\xf0' -> Some Prefix_f0
  | '\xf2' -> Some Prefix_f2
  | '\xf3' -> Some Prefix_f3
  | _ -> None

type opcode_class =
  | Opcode_1byte
  | Opcode_2byte (* 0f xx *)
  | Opcode_fpu

(* prefixes are packed into an int *)
let read_prefix_and_opcode s : int * opcode_class * int =
  let prefix = ref 0 in
  let rec loop () =
    let c = s () in
    match prefix_of_char c with
    | Some p ->
      (* validity of prefix sequence is not checked here *)
      prefix := !prefix lor prefix_value p;
      loop ()
    | None ->
      let opcode1 = int_of_char c in
      begin match opcode1 with
        | 0x0f -> Opcode_2byte, int_of_char (s ())
        | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
          Opcode_fpu, opcode1 land 7
        | _ -> Opcode_1byte, opcode1
      end
  in
  let oc, b = loop () in
  !prefix, oc, b

let extend_opcode opcode r = opcode lsl 3 lor r

type 'a entry =
  | E_inv
  | E_uni of 'a
  | E_grp of 'a array

type optable_entry =
  { op : operation entry; var : int; fmt : operand_format list entry }

let opgroup_80 =
  E_grp [| I_ADD;  I_OR;   I_ADC;  I_SBB;  I_AND;  I_SUB;  I_XOR;  I_CMP   |]

let opgroup_8f =
  E_grp [| I_POP;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD   |]

let opgroup_c0 =
  E_grp [| I_ROL;  I_ROR;  I_RCL;  I_RCR;  I_SHL;  I_SHR;  I_SHL;  I_SAR   |]

let opgroup_c6 =
  E_grp [| I_MOV;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD   |]

let opgroup_f6 =
  E_grp [| I_TEST; I_BAD;  I_NOT;  I_NEG;  I_MUL;  I_IMUL; I_DIV;  I_IDIV  |]

let opgroup_fe =
  E_grp [| I_INC;  I_DEC;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD;  I_BAD   |]

let opgroup_ff =
  E_grp [| I_INC;  I_DEC;  I_CALL; I_CALLF;I_JMP;  I_JMPF; I_PUSH; I_BAD   |]

let fmtgroup_8c =
  E_grp [|
    [X (O_reg R_ES)];
    [X (O_reg R_CS)];
    [X (O_reg R_SS)];
    [X (O_reg R_DS)];
    [X (O_reg R_FS)];
    [X (O_reg R_GS)];
    [];
    [];
  |]

let fmtgroup_f6 =
  E_grp [| [RM];   [];     [RM;I]; [RM;I]; [RM;I]; [RM;I]; [RM;I]; [RM;I]  |]

let fmtgroup_fe =
  E_grp [| [RM];   [RM];   [RM];   [M];    [RM];   [M];    [RM];   []      |]

let optable_basic = [|
  (* 00 *) { op = E_uni I_ADD;      var= 0;  fmt = E_uni [RM;R] };
  (* 01 *) { op = E_uni I_ADD;      var=15;  fmt = E_uni [RM;R] };
  (* 02 *) { op = E_uni I_ADD;      var= 0;  fmt = E_uni [R;RM] };
  (* 03 *) { op = E_uni I_ADD;      var=15;  fmt = E_uni [R;RM] };
  (* 04 *) { op = E_uni I_ADD;      var= 0;  fmt = E_uni [R0;I] };
  (* 05 *) { op = E_uni I_ADD;      var=15;  fmt = E_uni [R0;I] };
  (* 06 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [X (O_reg R_ES)] };
  (* 07 *) { op = E_uni I_POP;      var=15;  fmt = E_uni [X (O_reg R_ES)] };
  (* 08 *) { op = E_uni I_OR;       var= 0;  fmt = E_uni [RM;R] };
  (* 09 *) { op = E_uni I_OR;       var=15;  fmt = E_uni [RM;R] };
  (* 0a *) { op = E_uni I_OR;       var= 0;  fmt = E_uni [R;RM] };
  (* 0b *) { op = E_uni I_OR;       var=15;  fmt = E_uni [R;RM] };
  (* 0c *) { op = E_uni I_OR;       var= 0;  fmt = E_uni [R0;I] };
  (* 0d *) { op = E_uni I_OR;       var=15;  fmt = E_uni [R0;I] };
  (* 0e *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [X (O_reg R_CS)] };
  (* 0f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 10 *) { op = E_uni I_ADC;      var= 0;  fmt = E_uni [RM;R] };
  (* 11 *) { op = E_uni I_ADC;      var=15;  fmt = E_uni [RM;R] };
  (* 12 *) { op = E_uni I_ADC;      var= 0;  fmt = E_uni [R;RM] };
  (* 13 *) { op = E_uni I_ADC;      var=15;  fmt = E_uni [R;RM] };
  (* 14 *) { op = E_uni I_ADC;      var= 0;  fmt = E_uni [R0;I] };
  (* 15 *) { op = E_uni I_ADC;      var=15;  fmt = E_uni [R0;I] };
  (* 16 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [X (O_reg R_SS)] };
  (* 17 *) { op = E_uni I_POP;      var=15;  fmt = E_uni [X (O_reg R_SS)] };
  (* 18 *) { op = E_uni I_SBB;      var= 0;  fmt = E_uni [RM;R] };
  (* 19 *) { op = E_uni I_SBB;      var=15;  fmt = E_uni [RM;R] };
  (* 1a *) { op = E_uni I_SBB;      var= 0;  fmt = E_uni [R;RM] };
  (* 1b *) { op = E_uni I_SBB;      var=15;  fmt = E_uni [R;RM] };
  (* 1c *) { op = E_uni I_SBB;      var= 0;  fmt = E_uni [R0;I] };
  (* 1d *) { op = E_uni I_SBB;      var=15;  fmt = E_uni [R0;I] };
  (* 1e *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [X (O_reg R_DS)] };
  (* 1f *) { op = E_uni I_POP;      var=15;  fmt = E_uni [X (O_reg R_DS)] };
  (* 20 *) { op = E_uni I_AND;      var= 0;  fmt = E_uni [RM;R] };
  (* 21 *) { op = E_uni I_AND;      var=15;  fmt = E_uni [RM;R] };
  (* 22 *) { op = E_uni I_AND;      var= 0;  fmt = E_uni [R;RM] };
  (* 23 *) { op = E_uni I_AND;      var=15;  fmt = E_uni [R;RM] };
  (* 24 *) { op = E_uni I_AND;      var= 0;  fmt = E_uni [R0;I] };
  (* 25 *) { op = E_uni I_AND;      var=15;  fmt = E_uni [R0;I] };
  (* 26 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 27 *) { op = E_uni I_DAA;      var=15;  fmt = E_uni [] };
  (* 28 *) { op = E_uni I_SUB;      var= 0;  fmt = E_uni [RM;R] };
  (* 29 *) { op = E_uni I_SUB;      var=15;  fmt = E_uni [RM;R] };
  (* 2a *) { op = E_uni I_SUB;      var= 0;  fmt = E_uni [R;RM] };
  (* 2b *) { op = E_uni I_SUB;      var=15;  fmt = E_uni [R;RM] };
  (* 2c *) { op = E_uni I_SUB;      var= 0;  fmt = E_uni [R0;I] };
  (* 2d *) { op = E_uni I_SUB;      var=15;  fmt = E_uni [R0;I] };
  (* 2e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 2f *) { op = E_uni I_DAS;      var=15;  fmt = E_uni [] };
  (* 30 *) { op = E_uni I_XOR;      var= 0;  fmt = E_uni [RM;R] };
  (* 31 *) { op = E_uni I_XOR;      var=15;  fmt = E_uni [RM;R] };
  (* 32 *) { op = E_uni I_XOR;      var= 0;  fmt = E_uni [R;RM] };
  (* 33 *) { op = E_uni I_XOR;      var=15;  fmt = E_uni [R;RM] };
  (* 34 *) { op = E_uni I_XOR;      var= 0;  fmt = E_uni [R0;I] };
  (* 35 *) { op = E_uni I_XOR;      var=15;  fmt = E_uni [R0;I] };
  (* 36 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 37 *) { op = E_uni I_AAA;      var=15;  fmt = E_uni [] };
  (* 38 *) { op = E_uni I_CMP;      var= 0;  fmt = E_uni [RM;R] };
  (* 39 *) { op = E_uni I_CMP;      var=15;  fmt = E_uni [RM;R] };
  (* 3a *) { op = E_uni I_CMP;      var= 0;  fmt = E_uni [R;RM] };
  (* 3b *) { op = E_uni I_CMP;      var=15;  fmt = E_uni [R;RM] };
  (* 3c *) { op = E_uni I_CMP;      var= 0;  fmt = E_uni [R0;I] };
  (* 3d *) { op = E_uni I_CMP;      var=15;  fmt = E_uni [R0;I] };
  (* 3e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 3f *) { op = E_uni I_AAS;      var=15;  fmt = E_uni [] };
  (* 40 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 41 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 42 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 43 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 44 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 45 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 46 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 47 *) { op = E_uni I_INC;      var=15;  fmt = E_uni [RO] };
  (* 48 *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 49 *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 4a *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 4b *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 4c *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 4d *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 4e *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 4f *) { op = E_uni I_DEC;      var=15;  fmt = E_uni [RO] };
  (* 50 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 51 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 52 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 53 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 54 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 55 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 56 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 57 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [RO] };
  (* 58 *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 59 *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 5a *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 5b *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 5c *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 5d *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 5e *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 5f *) { op = E_uni I_POP;      var=15;  fmt = E_uni [RO] };
  (* 60 *) { op = E_uni I_PUSHA;    var=15;  fmt = E_uni [] };
  (* 61 *) { op = E_uni I_POPA;     var=15;  fmt = E_uni [] };
  (* 62 *) { op = E_uni I_BOUND;    var=15;  fmt = E_uni [R;M] };
  (* 63 *) { op = E_uni I_ARPL;     var=15;  fmt = E_uni [RM;R] };
  (* 64 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 65 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 66 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 67 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 68 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [I] };
  (* 69 *) { op = E_uni I_IMUL;     var=15;  fmt = E_uni [R;RM;I] };
  (* 6a *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [I] };
  (* 6b *) { op = E_uni I_IMUL;     var=15;  fmt = E_uni [R;RM;I] };
  (* 6c *) { op = E_uni I_INS;      var= 0;  fmt = E_uni [] };
  (* 6d *) { op = E_uni I_INS;      var=15;  fmt = E_uni [] };
  (* 6e *) { op = E_uni I_OUTS;     var= 0;  fmt = E_uni [] };
  (* 6f *) { op = E_uni I_OUTS;     var=15;  fmt = E_uni [] };
  (* 70 *) { op = E_uni I_CJMP;     var=0x00;fmt = E_uni [O] };
  (* 71 *) { op = E_uni I_CJMP;     var=0x10;fmt = E_uni [O] };
  (* 72 *) { op = E_uni I_CJMP;     var=0x20;fmt = E_uni [O] };
  (* 73 *) { op = E_uni I_CJMP;     var=0x30;fmt = E_uni [O] };
  (* 74 *) { op = E_uni I_CJMP;     var=0x40;fmt = E_uni [O] };
  (* 75 *) { op = E_uni I_CJMP;     var=0x50;fmt = E_uni [O] };
  (* 76 *) { op = E_uni I_CJMP;     var=0x60;fmt = E_uni [O] };
  (* 77 *) { op = E_uni I_CJMP;     var=0x70;fmt = E_uni [O] };
  (* 78 *) { op = E_uni I_CJMP;     var=0x80;fmt = E_uni [O] };
  (* 79 *) { op = E_uni I_CJMP;     var=0x90;fmt = E_uni [O] };
  (* 7a *) { op = E_uni I_CJMP;     var=0xa0;fmt = E_uni [O] };
  (* 7b *) { op = E_uni I_CJMP;     var=0xb0;fmt = E_uni [O] };
  (* 7c *) { op = E_uni I_CJMP;     var=0xc0;fmt = E_uni [O] };
  (* 7d *) { op = E_uni I_CJMP;     var=0xd0;fmt = E_uni [O] };
  (* 7e *) { op = E_uni I_CJMP;     var=0xe0;fmt = E_uni [O] };
  (* 7f *) { op = E_uni I_CJMP;     var=0xf0;fmt = E_uni [O] };
  (* 80 *) { op =       opgroup_80; var= 0;  fmt = E_uni [RM;I] };
  (* 81 *) { op =       opgroup_80; var=15;  fmt = E_uni [RM;I] };
  (* 82 *) { op =       opgroup_80; var= 0;  fmt = E_uni [RM;I] };
  (* 83 *) { op =       opgroup_80; var=15;  fmt = E_uni [RM;I] };
  (* 84 *) { op = E_uni I_TEST;     var= 0;  fmt = E_uni [RM;I] };
  (* 85 *) { op = E_uni I_TEST;     var=15;  fmt = E_uni [RM;I] };
  (* 86 *) { op = E_uni I_XCHG;     var= 0;  fmt = E_uni [RM;I] };
  (* 87 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [RM;I] };
  (* 88 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RM;R] };
  (* 89 *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RM;R] };
  (* 8a *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [R;RM] };
  (* 8b *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [R;RM] };
  (* 8c *) { op = E_uni I_MOV;      var=15;  fmt =       fmtgroup_8c };
  (* 8d *) { op = E_uni I_LEA;      var=15;  fmt = E_uni [R;M] };
  (* 8e *) { op = E_uni I_MOV;      var=15;  fmt =       fmtgroup_8c };
  (* 8f *) { op =       opgroup_8f; var=15;  fmt = E_uni [RM] };
  (* 90 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 91 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 92 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 93 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 94 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 95 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 96 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 97 *) { op = E_uni I_XCHG;     var=15;  fmt = E_uni [R0;RO] };
  (* 98 *) { op = E_uni I_CBW;      var= 0;  fmt = E_uni [] };
  (* 99 *) { op = E_uni I_CWD;      var=15;  fmt = E_uni [] };
  (* 9a *) { op = E_uni I_CALLF;    var=15;  fmt = E_uni [I;I2] };
  (* 9b *) { op = E_uni I_WAIT;     var=15;  fmt = E_uni [] };
  (* 9c *) { op = E_uni I_PUSHF;    var=15;  fmt = E_uni [] };
  (* 9d *) { op = E_uni I_POPF;     var=15;  fmt = E_uni [] };
  (* 9e *) { op = E_uni I_SAHF;     var= 0;  fmt = E_uni [] };
  (* 9f *) { op = E_uni I_LAHF;     var= 0;  fmt = E_uni [] };
  (* a0 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [R0;RM] };
  (* a1 *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [R0;RM] };
  (* a2 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RM;R0] };
  (* a3 *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RM;R0] };
  (* a4 *) { op = E_uni I_MOVS;     var= 0;  fmt = E_uni [] };
  (* a5 *) { op = E_uni I_MOVS;     var=15;  fmt = E_uni [] };
  (* a6 *) { op = E_uni I_CMPS;     var= 0;  fmt = E_uni [] };
  (* a7 *) { op = E_uni I_CMPS;     var=15;  fmt = E_uni [] };
  (* a8 *) { op = E_uni I_TEST;     var= 0;  fmt = E_uni [R0;I] };
  (* a9 *) { op = E_uni I_TEST;     var=15;  fmt = E_uni [R0;I] };
  (* aa *) { op = E_uni I_STOS;     var= 0;  fmt = E_uni [] };
  (* ab *) { op = E_uni I_STOS;     var=15;  fmt = E_uni [] };
  (* ac *) { op = E_uni I_LODS;     var= 0;  fmt = E_uni [] };
  (* ad *) { op = E_uni I_LODS;     var=15;  fmt = E_uni [] };
  (* ae *) { op = E_uni I_SCAS;     var= 0;  fmt = E_uni [] };
  (* af *) { op = E_uni I_SCAS;     var=15;  fmt = E_uni [] };
  (* b0 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b1 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b2 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b3 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b4 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b5 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b6 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b7 *) { op = E_uni I_MOV;      var= 0;  fmt = E_uni [RO;I] };
  (* b8 *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* b9 *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* ba *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* bb *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* bc *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* bd *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* be *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* bf *) { op = E_uni I_MOV;      var=15;  fmt = E_uni [RO;I] };
  (* c0 *) { op =       opgroup_c0; var= 0;  fmt = E_uni [RM;I] };
  (* c1 *) { op =       opgroup_c0; var=15;  fmt = E_uni [RM;I] };
  (* c2 *) { op = E_uni I_RETN;     var=15;  fmt = E_uni [I] };
  (* c3 *) { op = E_uni I_RET;      var=15;  fmt = E_uni [] };
  (* c4 *) { op = E_uni I_LES;      var=15;  fmt = E_uni [R;M] };
  (* c5 *) { op = E_uni I_LDS;      var=15;  fmt = E_uni [R;M] };
  (* c6 *) { op =       opgroup_c6; var= 0;  fmt = E_uni [RM;I] };
  (* c7 *) { op =       opgroup_c6; var=15;  fmt = E_uni [RM;I] };
  (* c8 *) { op = E_uni I_ENTER;    var= 0;  fmt = E_uni [] };
  (* c9 *) { op = E_uni I_LEAVE;    var=15;  fmt = E_uni [] };
  (* ca *) { op = E_uni I_RETNF;    var=15;  fmt = E_uni [I] };
  (* cb *) { op = E_uni I_RETF;     var=15;  fmt = E_uni [] };
  (* cc *) { op = E_uni I_INT3;     var= 0;  fmt = E_uni [] };
  (* cd *) { op = E_uni I_INT;      var= 0;  fmt = E_uni [I] };
  (* ce *) { op = E_uni I_INTO;     var= 0;  fmt = E_uni [] };
  (* cf *) { op = E_uni I_IRET;     var=15;  fmt = E_uni [] };
  (* d0 *) { op =       opgroup_c0; var= 0;  fmt = E_uni [RM; X (O_imm (1n, 1))] };
  (* d1 *) { op =       opgroup_c0; var=15;  fmt = E_uni [RM; X (O_imm (1n, 1))] };
  (* d2 *) { op =       opgroup_c0; var= 0;  fmt = E_uni [RM; X (O_reg R_CL)] };
  (* d3 *) { op =       opgroup_c0; var=15;  fmt = E_uni [RM; X (O_reg R_CL)] };
  (* d4 *) { op = E_uni I_AAM;      var= 0;  fmt = E_uni [I] };
  (* d5 *) { op = E_uni I_AAD;      var= 0;  fmt = E_uni [I] };
  (* d6 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d7 *) { op = E_uni I_XLAT;     var=15;  fmt = E_uni [] };
  (* d8 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d9 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* da *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* db *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* dc *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* dd *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* de *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* df *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e0 *) { op = E_uni I_LOOPNZ;   var= 0;  fmt = E_uni [O] };
  (* e1 *) { op = E_uni I_LOOPZ;    var= 0;  fmt = E_uni [O] };
  (* e2 *) { op = E_uni I_LOOP;     var= 0;  fmt = E_uni [O] };
  (* e3 *) { op = E_uni I_JCXZ;     var=15;  fmt = E_uni [O] };
  (* e4 *) { op = E_uni I_IN;       var= 0;  fmt = E_uni [R0;I] };
  (* e5 *) { op = E_uni I_IN;       var=15;  fmt = E_uni [R0;I] };
  (* e6 *) { op = E_uni I_OUT;      var= 0;  fmt = E_uni [R0;I] };
  (* e7 *) { op = E_uni I_OUT;      var=15;  fmt = E_uni [R0;I] };
  (* e8 *) { op = E_uni I_CALL;     var=15;  fmt = E_uni [O] };
  (* e9 *) { op = E_uni I_JMP;      var=15;  fmt = E_uni [O] };
  (* ea *) { op = E_uni I_JMPF;     var= 0;  fmt = E_uni [I;I2] };
  (* eb *) { op = E_uni I_JMP;      var=15;  fmt = E_uni [O] };
  (* ec *) { op = E_uni I_IN;       var= 0;  fmt = E_uni [X (O_reg R_DX)] };
  (* ed *) { op = E_uni I_IN;       var=15;  fmt = E_uni [X (O_reg R_DX)] };
  (* ee *) { op = E_uni I_OUT;      var= 0;  fmt = E_uni [X (O_reg R_DX)] };
  (* ef *) { op = E_uni I_OUT;      var=15;  fmt = E_uni [X (O_reg R_DX)] };
  (* f0 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f1 *) { op = E_uni I_INT1;     var= 0;  fmt = E_uni [] };
  (* f2 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f3 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f4 *) { op = E_uni I_HLT;      var= 0;  fmt = E_uni [] };
  (* f5 *) { op = E_uni I_CMC;      var= 0;  fmt = E_uni [] };
  (* f6 *) { op =       opgroup_f6; var= 0;  fmt =       fmtgroup_f6 };
  (* f7 *) { op =       opgroup_f6; var=15;  fmt =       fmtgroup_f6 };
  (* f8 *) { op = E_uni I_CLC;      var= 0;  fmt = E_uni [] };
  (* f9 *) { op = E_uni I_STC;      var= 0;  fmt = E_uni [] };
  (* fa *) { op = E_uni I_CLI;      var= 0;  fmt = E_uni [] };
  (* fb *) { op = E_uni I_STI;      var= 0;  fmt = E_uni [] };
  (* fc *) { op = E_uni I_CLD;      var= 0;  fmt = E_uni [] };
  (* fd *) { op = E_uni I_STD;      var= 0;  fmt = E_uni [] };
  (* fe *) { op =       opgroup_fe; var= 0;  fmt =       fmtgroup_fe };
  (* ff *) { op =       opgroup_ff; var=15;  fmt =       fmtgroup_fe };
|]

let optable_0f = [|
  (* 00 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 01 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 02 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 03 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 04 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 05 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 06 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 07 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 08 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 09 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 0a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 0b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 0c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 0d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 0e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 0f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 10 *) { op = E_uni I_MOVUPS;   var= 0;  fmt = E_uni [XMM_R; XMM_RM] };
  (* 11 *) { op = E_uni I_MOVUPS;   var= 0;  fmt = E_uni [XMM_RM; XMM_R] };
  (* 12 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 13 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 14 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 15 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 16 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 17 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 18 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 19 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 1a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 1b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 1c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 1d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 1e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 1f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 20 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 21 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 22 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 23 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 24 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 25 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 26 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 27 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 28 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 29 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 2a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 2b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 2c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 2d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 2e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 2f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 30 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 31 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 32 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 33 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 34 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 35 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 36 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 37 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 38 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 39 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 3a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 3b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 3c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 3d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 3e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 3f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 40 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 41 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 42 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 43 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 44 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 45 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 46 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 47 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 48 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 49 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 4a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 4b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 4c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 4d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 4e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 4f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 50 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 51 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 52 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 53 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 54 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 55 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 56 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 57 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 58 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 59 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 5a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 5b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 5c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 5d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 5e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 5f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 60 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 61 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 62 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 63 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 64 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 65 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 66 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 67 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 68 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 69 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 6a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 6b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 6c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 6d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 6e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 6f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 70 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 71 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 72 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 73 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 74 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 75 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 76 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 77 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 78 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 79 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 7a *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 7b *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 7c *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 7d *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 7e *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 7f *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* 80 *) { op = E_uni I_CJMP;     var=0x00;fmt = E_uni [O] };
  (* 81 *) { op = E_uni I_CJMP;     var=0x10;fmt = E_uni [O] };
  (* 82 *) { op = E_uni I_CJMP;     var=0x20;fmt = E_uni [O] };
  (* 83 *) { op = E_uni I_CJMP;     var=0x30;fmt = E_uni [O] };
  (* 84 *) { op = E_uni I_CJMP;     var=0x40;fmt = E_uni [O] };
  (* 85 *) { op = E_uni I_CJMP;     var=0x50;fmt = E_uni [O] };
  (* 86 *) { op = E_uni I_CJMP;     var=0x60;fmt = E_uni [O] };
  (* 87 *) { op = E_uni I_CJMP;     var=0x70;fmt = E_uni [O] };
  (* 88 *) { op = E_uni I_CJMP;     var=0x80;fmt = E_uni [O] };
  (* 89 *) { op = E_uni I_CJMP;     var=0x90;fmt = E_uni [O] };
  (* 8a *) { op = E_uni I_CJMP;     var=0xa0;fmt = E_uni [O] };
  (* 8b *) { op = E_uni I_CJMP;     var=0xb0;fmt = E_uni [O] };
  (* 8c *) { op = E_uni I_CJMP;     var=0xc0;fmt = E_uni [O] };
  (* 8d *) { op = E_uni I_CJMP;     var=0xd0;fmt = E_uni [O] };
  (* 8e *) { op = E_uni I_CJMP;     var=0xe0;fmt = E_uni [O] };
  (* 8f *) { op = E_uni I_CJMP;     var=0xf0;fmt = E_uni [O] };
  (* 90 *) { op = E_uni I_SET;      var=0x00;fmt = E_uni [RM] };
  (* 91 *) { op = E_uni I_SET;      var=0x10;fmt = E_uni [RM] };
  (* 92 *) { op = E_uni I_SET;      var=0x20;fmt = E_uni [RM] };
  (* 93 *) { op = E_uni I_SET;      var=0x30;fmt = E_uni [RM] };
  (* 94 *) { op = E_uni I_SET;      var=0x40;fmt = E_uni [RM] };
  (* 95 *) { op = E_uni I_SET;      var=0x50;fmt = E_uni [RM] };
  (* 96 *) { op = E_uni I_SET;      var=0x60;fmt = E_uni [RM] };
  (* 97 *) { op = E_uni I_SET;      var=0x70;fmt = E_uni [RM] };
  (* 98 *) { op = E_uni I_SET;      var=0x80;fmt = E_uni [RM] };
  (* 99 *) { op = E_uni I_SET;      var=0x90;fmt = E_uni [RM] };
  (* 9a *) { op = E_uni I_SET;      var=0xa0;fmt = E_uni [RM] };
  (* 9b *) { op = E_uni I_SET;      var=0xb0;fmt = E_uni [RM] };
  (* 9c *) { op = E_uni I_SET;      var=0xc0;fmt = E_uni [RM] };
  (* 9d *) { op = E_uni I_SET;      var=0xd0;fmt = E_uni [RM] };
  (* 9e *) { op = E_uni I_SET;      var=0xe0;fmt = E_uni [RM] };
  (* 9f *) { op = E_uni I_SET;      var=0xf0;fmt = E_uni [RM] };
  (* a0 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [X (O_reg R_FS)] };
  (* a1 *) { op = E_uni I_POP;      var=15;  fmt = E_uni [X (O_reg R_FS)] };
  (* a2 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* a3 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* a4 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* a5 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* a6 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* a7 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* a8 *) { op = E_uni I_PUSH;     var=15;  fmt = E_uni [X (O_reg R_GS)] };
  (* a9 *) { op = E_uni I_POP;      var=15;  fmt = E_uni [X (O_reg R_GS)] };
  (* aa *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ab *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ac *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ad *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ae *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* af *) { op = E_uni I_IMUL;     var=15;  fmt = E_uni [R;RM] };
  (* b0 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* b1 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* b2 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* b3 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* b4 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* b5 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* b6 *) { op = E_uni I_MOVZX;    var=15;  fmt = E_uni [R; RMs 1] };
  (* b7 *) { op = E_uni I_MOVZX;    var=15;  fmt = E_uni [R; RMs 2] };
  (* b8 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* b9 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ba *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* bb *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* bc *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* bd *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* be *) { op = E_uni I_MOVSX;    var=15;  fmt = E_uni [R; RMs 1] };
  (* bf *) { op = E_uni I_MOVSX;    var=15;  fmt = E_uni [R; RMs 2] };
  (* c0 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c1 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c2 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c3 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c4 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c5 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c6 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c7 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c8 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* c9 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ca *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* cb *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* cc *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* cd *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ce *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* cf *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d0 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d1 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d2 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d3 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d4 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d5 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d6 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d7 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d8 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* d9 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* da *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* db *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* dc *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* dd *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* de *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* df *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e0 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e1 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e2 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e3 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e4 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e5 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e6 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e7 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e8 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* e9 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ea *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* eb *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ec *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ed *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ee *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ef *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f0 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f1 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f2 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f3 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f4 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f5 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f6 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f7 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f8 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* f9 *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* fa *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* fb *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* fc *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* fd *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* fe *) { op = E_inv;            var= 0;  fmt = E_inv };
  (* ff *) { op = E_inv;            var= 0;  fmt = E_inv };
|]

let fpu_optable = [|
  (* d8 0 *) I_FADD,    [Ms 4],  E_uni I_FADD;
  (* d8 1 *) I_FMUL,    [Ms 4],  E_uni I_FMUL;
  (* d8 2 *) I_FCOM,    [Ms 4],  E_uni I_FCOM;
  (* d8 3 *) I_FCOMP,   [Ms 4],  E_uni I_FCOMP;
  (* d8 4 *) I_FSUB,    [Ms 4],  E_uni I_FSUB;
  (* d8 5 *) I_FSUBR,   [Ms 4],  E_uni I_FSUBR;
  (* d8 6 *) I_FDIV,    [Ms 4],  E_uni I_FDIV;
  (* d8 7 *) I_FDIVR,   [Ms 4],  E_uni I_FDIVR;
  (* d9 0 *) I_FLD,     [Ms 4],  E_uni I_FLD;
  (* d9 1 *) I_BAD,     [],     E_uni I_FXCH;
  (* d9 2 *) I_FST,     [Ms 4],  E_grp [|I_FNOP;    I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD    |];
  (* d9 3 *) I_FSTP,    [Ms 4],  E_inv;
  (* d9 4 *) I_FLDENV,  [Ms 0],  E_grp [|I_FCHS;    I_FABS;    I_BAD;     I_BAD;     I_FTST;    I_FXAM;    I_BAD;     I_BAD    |];
  (* d9 5 *) I_FLDCW,   [Ms 0],  E_grp [|I_FLD1;    I_FLDL2T;  I_FLDL2E;  I_FLDPI;   I_FLDLG2;  I_FLDLN2;  I_FLDZ;    I_BAD    |];
  (* d9 6 *) I_FNSTENV, [Ms 0],  E_grp [|I_F2XM1;   I_FYL2X;   I_FPTAN;   I_FPATAN;  I_FXTRACT; I_FPREM1;  I_FDECSTP; I_FINCSTP|];
  (* d9 7 *) I_FNSTCW,  [Ms 0],  E_grp [|I_FPREM;   I_FYL2XP1; I_FSQRT;   I_FSINCOS; I_FRNDINT; I_FSCALE;  I_FSIN;    I_FCOS   |];
  (* da 0 *) I_FIADD,   [Ms 4],  E_uni I_FCMOVB;
  (* da 1 *) I_FIMUL,   [Ms 4],  E_uni I_FCMOVE;
  (* da 2 *) I_FICOM,   [Ms 4],  E_uni I_FCMOVBE;
  (* da 2 *) I_FICOMP,  [Ms 4],  E_uni I_FCMOVU;
  (* da 4 *) I_FISUB,   [Ms 4],  E_inv;
  (* da 5 *) I_FISUBR,  [Ms 4],  E_grp [|I_BAD;     I_FUCOMPP; I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD    |];
  (* da 6 *) I_FIDIV,   [Ms 4],  E_inv;
  (* da 7 *) I_FIDIVR,  [Ms 4],  E_inv;
  (* db 0 *) I_FILD,    [Ms 4],  E_uni I_FCMOVNB;
  (* db 1 *) I_FISTTP,  [Ms 4],  E_uni I_FCMOVNE;
  (* db 2 *) I_FIST,    [Ms 4],  E_uni I_FCMOVNBE;
  (* db 3 *) I_FISTP,   [Ms 4],  E_uni I_FCMOVNU;
  (* db 4 *) I_BAD,     [],     E_grp [|I_BAD;     I_BAD;     I_FNCLEX;  I_FNINIT;  I_BAD;     I_BAD;     I_BAD;     I_BAD    |];
  (* db 5 *) I_FLD,     [Ms 10], E_uni I_FUCOMI;
  (* db 6 *) I_BAD,     [],     E_uni I_FCOMI;
  (* db 7 *) I_FSTP,    [Ms 10], E_inv;
  (* dc 0 *) I_FADD,    [Ms 8],  E_uni I_FADD_TO;
  (* dc 1 *) I_FMUL,    [Ms 8],  E_uni I_FMUL_TO;
  (* dc 2 *) I_FCOM,    [Ms 8],  E_inv;
  (* dc 3 *) I_FCOMP,   [Ms 8],  E_inv;
  (* dc 4 *) I_FSUB,    [Ms 8],  E_uni I_FSUBR_TO;
  (* dc 5 *) I_FSUBR,   [Ms 8],  E_uni I_FSUB_TO;
  (* dc 6 *) I_FDIV,    [Ms 8],  E_uni I_FDIVR_TO;
  (* dc 7 *) I_FDIVR,   [Ms 8],  E_uni I_FDIV_TO;
  (* dd 0 *) I_FLD,     [Ms 8],  E_uni I_FFREE;
  (* dd 1 *) I_FISTTP,  [Ms 8],  E_inv;
  (* dd 2 *) I_FST,     [Ms 8],  E_uni I_FST;
  (* dd 3 *) I_FSTP,    [Ms 8],  E_uni I_FSTP;
  (* dd 4 *) I_FRSTOR,  [Ms 0],  E_uni I_FUCOM;
  (* dd 5 *) I_BAD,     [],     E_uni I_FUCOMP;
  (* dd 6 *) I_FNSAVE,  [Ms 0],  E_inv;
  (* dd 7 *) I_FNSTSW,  [Ms 0],  E_inv;
  (* de 0 *) I_FIADD,   [Ms 2],  E_uni I_FADDP;
  (* de 1 *) I_FIMUL,   [Ms 2],  E_uni I_FMULP;
  (* de 2 *) I_FICOM,   [Ms 2],  E_inv;
  (* de 3 *) I_FICOMP,  [Ms 2],  E_grp [|I_BAD;     I_FCOMPP;  I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD    |];
  (* de 4 *) I_FISUB,   [Ms 2],  E_uni I_FSUBRP;
  (* de 5 *) I_FISUBR,  [Ms 2],  E_uni I_FSUBP;
  (* de 6 *) I_FIDIV,   [Ms 2],  E_uni I_FDIVRP;
  (* de 7 *) I_FIDIVR,  [Ms 2],  E_uni I_FDIVP;
  (* df 0 *) I_FILD,    [Ms 2],  E_inv;
  (* df 1 *) I_FISTTP,  [Ms 2],  E_inv;
  (* df 2 *) I_FIST,    [Ms 2],  E_inv;
  (* df 3 *) I_FISTP,   [Ms 2],  E_inv;
  (* df 4 *) I_FBLD,    [Ms 0],  E_grp [|I_FNSTSW;  I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD;     I_BAD    |];
  (* df 5 *) I_FILD,    [Ms 8],  E_uni I_FUCOMIP;
  (* df 6 *) I_FBSTP,   [Ms 0],  E_uni I_FCOMIP;
  (* df 7 *) I_FISTP,   [Ms 8],  E_inv;
|]

let operand_size_prefix (mode : cpu_mode) (prefix : int) : string option =
  if prefix land (prefix_mask Prefix_66) <> 0
  then
    match mode with
    | Mode16bit -> Some "o32"
    | Mode32bit
    | Mode64bit -> Some "o16"
  else None

let with_operand_size_prefix (mode : cpu_mode) (prefix : int) (m : string) : string =
  match operand_size_prefix mode prefix with
  | Some o -> o^" "^m
  | None -> m

(* in bytes *)
let log_word_size mode prefix =
  let has_66 = prefix land (prefix_mask Prefix_66) <> 0 in
  match mode, has_66 with
  | Mode16bit, false
  | Mode32bit, true
  | Mode64bit, true -> 1
  | Mode16bit, true
  | Mode32bit, false
  | Mode64bit, false -> 2

let format_of_inst optable mode prefix b x =
  let ent = optable.(b) in
  let op =
    match ent.op with
    | E_inv -> raise Invalid_instruction
    | E_uni op -> op
    | E_grp grp -> grp.(x)
  in
  let lw = log_word_size mode prefix in
  let var =
    if ent.var land 15 = 15 then lw else ent.var
  in
  let fmt =
    match ent.fmt with
    | E_inv -> raise Invalid_instruction
    | E_uni fmt -> fmt
    | E_grp grp -> grp.(x)
  in
  op, var, fmt

let gpr_set_of_size = function
  | 1 -> Reg8bitLegacy
  | 2 -> Reg16bit
  | 4 -> Reg32bit
  | 8 -> Reg64bit
  | _ -> assert false

let convert_reg size r =
  let regset = gpr_set_of_size size in
  O_reg (int_to_reg regset r)

let get_fpu_reg r =
  match r with
  | 0 -> R_ST0
  | 1 -> R_ST1
  | 2 -> R_ST2
  | 3 -> R_ST3
  | 4 -> R_ST4
  | 5 -> R_ST5
  | 6 -> R_ST6
  | 7 -> R_ST7
  | _ -> assert false

let get_xmm_reg r =
  match r with
  | 0 -> R_XMM0
  | 1 -> R_XMM1
  | 2 -> R_XMM2
  | 3 -> R_XMM3
  | 4 -> R_XMM4
  | 5 -> R_XMM5
  | 6 -> R_XMM6
  | 7 -> R_XMM7
  | _ -> assert false

let disassemble config str pos =
  let buf = Buffer.create 8 in
  let p = ref pos in
  let s () =
    let c = str.[!p] in
    Buffer.add_char buf c;
    p := !p+1;
    c
  in
  let prefix, oc, b = read_prefix_and_opcode s in
  let fmt =
    match oc with
    | Opcode_1byte -> int_of_char inst_format_table.[b]
    | Opcode_2byte -> int_of_char inst_format_table_0f.[b]
    | Opcode_fpu -> 0x10
  in
  let has_66 = prefix land (prefix_mask Prefix_66) <> 0 in
  let has_67 = prefix land (prefix_mask Prefix_67) <> 0 in

  (* for reading immediates *)
  let data_size =
    match config.mode with
    | Mode16bit -> if has_66 then 4 else 2
    | Mode32bit -> if has_66 then 2 else 4
    | _ -> failwith "not implemented"
  in
  let addr_size =
    match config.mode with
    | Mode16bit -> if has_67 then 4 else 2
    | Mode32bit -> if has_67 then 2 else 4
    | _ -> failwith "not implemented"
  in

  let seg_opt =
    match prefix land 0x1c with
    | 0x04 -> Some R_ES
    | 0x08 -> Some R_CS
    | 0x0c -> Some R_SS
    | 0x10 -> Some R_DS
    | 0x14 -> Some R_FS
    | 0x18 -> Some R_GS
    | _ -> None
  in
  let x, rm =
    if fmt land 0x10 <> 0
    then (* has regmem operand *)
      let read_regmem =
        match config.mode with
        | Mode16bit -> if has_67 then read_regmem32 else read_regmem16
        | Mode32bit -> if has_67 then read_regmem16 else read_regmem32
        | _ -> failwith "not implemented"
      in
      read_regmem s seg_opt
    else if fmt = 6
    then
      let disp = read_imm addr_size s in
      let seg = seg_opt |> Option.default R_DS in
      0, Mem { base = None; index = None; disp; seg }
    else
      0, Reg 0
  in
  (* handle special cases *)
  let fmt' =
    if oc = Opcode_1byte && b lor 1 = 0xf7 && x = 0 then
      0x11 + (b land 1)
    else
      fmt
  in
  let imm1, imm2 =
    match fmt' land 7 with
    | 0 -> 0n, 0n
    | 1 -> read_imm 1 s, 0n
    | 2 -> read_imm data_size s, 0n
    | 3 -> read_imm 2 s, 0n
    | 4 ->
      let imm1 = read_imm 2 s in
      let imm2 = read_imm 1 s in
      imm1, imm2
    | 5 ->
      let imm1 = read_imm 2 s in
      let imm2 = read_imm data_size s in
      imm1, imm2
    | 6 -> 0n, 0n
    | _ -> assert false
  in
  let op, var, argfmt =
    match oc with
    | Opcode_1byte ->
      format_of_inst optable_basic config.mode prefix b x
    | Opcode_2byte ->
      format_of_inst optable_0f config.mode prefix b x
    | Opcode_fpu ->
      let index1 = b lsl 3 lor x in
      let op, argfmt, op_r = fpu_optable.(index1) in
      begin match rm with
        | Reg r ->
          begin match op_r with
            | E_inv -> raise Invalid_instruction
            | E_uni op -> op, 0, [FPU_R]
            | E_grp a ->
              let op = a.(r) in
              match op with
              | I_BAD -> raise Invalid_instruction
              | _ -> op, 0, []
          end
        | Mem _ ->
          op, 0, argfmt
      end
  in
  let bytes = Buffer.contents buf in
  let size = 1 lsl (var land 3) in
  let convert_operand = function
    | R -> convert_reg size x
    | Rs size -> convert_reg size x
    | R0 -> convert_reg size 0
    | RO -> convert_reg size (b land 7)
    | RM ->
      begin match rm with
        | Reg r -> convert_reg size r
        | Mem m -> O_mem (m, size)
      end
    | RMs size ->
      begin match rm with
        | Reg r -> convert_reg size r
        | Mem m -> O_mem (m, size)
      end
    | M ->
      begin match rm with
        | Reg _ -> raise Invalid_operand
        | Mem m -> O_mem (m, size)
      end
    | Ms size ->
      begin match rm with
        | Reg _ -> raise Invalid_operand
        | Mem m -> O_mem (m, size)
      end
    | I -> O_imm (imm1, size)
    | I2 -> O_imm (imm2, size)
    | O ->
      let offset = Nativeint.(imm1 + of_int (String.length bytes)) in
      begin match config.pc_opt with
        | Some pc -> O_imm (Nativeint.(pc + offset), 4(* FIXME *))
        | None -> O_offset offset
      end
    | FPU_R ->
      begin match rm with
        | Reg r -> O_reg (get_fpu_reg r)
        | Mem _ -> assert false
      end
    | XMM_R -> O_reg (get_xmm_reg x)
    | XMM_RM ->
      begin match rm with
        | Reg r -> O_reg (get_xmm_reg r)
        | Mem m -> O_mem (m, 16)
      end
    | X o -> o
  in
  let operands = List.map convert_operand argfmt in
  Inst.make bytes op var operands
