open Format
open Inst

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

let read_sib buf s : int * ((int * int) option) =
  let c = s () in
  Buffer.add_char buf c;
  let sib = int_of_char c in
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

let read_imm n buf s =
  let rec f n' acc =
    if n' = n
    then
      if acc land (1 lsl (n*8-1)) = 0
      then acc
      else acc - (1 lsl (n*8)) (* sign-extend immediate *)
    else
      let c = s () in
      Buffer.add_char buf c;
      let b = int_of_char c in
      f (n'+1) (acc lor (b lsl (n'*8)))
  in
  f 0 0

(* the int in return value is opcode extension field i.e. ModRM[5:3] *)
let read_regmem32 buf s : int * regmem =
  let regset = Reg32bit in
  (* helper function *)
  let convert_index = function
    | Some (r, s) -> Some (int_to_reg regset r, s)
    | None -> None
  in

  let c = s () in
  Buffer.add_char buf c;
  let modrm = int_of_char c in
  let r = modrm land 7 in
  let g =
    let m = modrm lsr 6 in (* mode field (ModRM[7:6]) *)
    begin match m with
      | 0 ->
        begin match r with
          | 4 -> (* SIB follows *)
            let base, index = read_sib buf s in
            if base = 5
            then
              let disp = read_imm 4 buf s in
              Mem { base = None; index = convert_index index; disp }
            else
              Mem { base = Some (int_to_reg regset base); index = convert_index index; disp = 0 }
          | 5 ->
            let disp = read_imm 4 buf s in
            Mem { base = None; index = None; disp }
          | _ ->
            Mem { base = Some (int_to_reg regset r); index = None; disp = 0 }
        end
      | 1 | 2 ->
        let disp_size = if m = 1 then 1 else 4 in
        if r = 4
        then
          let base, index = read_sib buf s in
          let disp = read_imm disp_size buf s in
          Mem { base = Some (int_to_reg regset base); index = convert_index index; disp }
        else
          let disp = read_imm disp_size buf s in
          Mem { base = Some (int_to_reg regset r); index = None; disp }
      | 3 ->
        Reg r
      | _ -> assert false
    end
  in
  (modrm lsr 3 land 7, g)

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
   \x10\x10\x10\x10\x01\x01\x00\x00\x10\x10\x10\x10\x10\x10\x10\x10\
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
  | R of int
  | R0 of int
  | R_opcode of int (* GPR[opcode&7] *)
  | RM of int
  | M of int
  | I of int
  | I2 of int
  | Offset
  | Far_ptr
  | FPU_R
  | XMM_R
  | XMM_RM
  | Lit of operand

let fpu_mnem_table1 =
  [|
    (* d8 *)
    Some (I_fadd , [M 4]);
    Some (I_fmul , [M 4]);
    Some (I_fcom , [M 4]);
    Some (I_fcomp, [M 4]);
    Some (I_fsub , [M 4]);
    Some (I_fsubr, [M 4]);
    Some (I_fdiv , [M 4]);
    Some (I_fdivr, [M 4]);
    (* d9 *)
    Some (I_fld, [M 4]);
    None;
    Some (I_fst    , [M 4]);
    Some (I_fstp   , [M 4]);
    Some (I_fldenv , [M 0]);
    Some (I_fldcw  , [M 0]);
    Some (I_fnstenv, [M 0]);
    Some (I_fnstcw , [M 0]);
    (* da *)
    Some (I_fiadd , [M 4]);
    Some (I_fimul , [M 4]);
    Some (I_ficom , [M 4]);
    Some (I_ficomp, [M 4]);
    Some (I_fisub , [M 4]);
    Some (I_fisubr, [M 4]);
    Some (I_fidiv , [M 4]);
    Some (I_fidivr, [M 4]);
    (* db *)
    Some (I_fild  , [M 4]);
    Some (I_fisttp, [M 4]);
    Some (I_fist  , [M 4]);
    Some (I_fistp , [M 4]);
    None;
    Some (I_fld   , [M 10]);
    None;
    Some (I_fstp  , [M 10]);
    (* dc *)
    Some (I_fadd , [M 8]);
    Some (I_fmul , [M 8]);
    Some (I_fcom , [M 8]);
    Some (I_fcomp, [M 8]);
    Some (I_fsub , [M 8]);
    Some (I_fsubr, [M 8]);
    Some (I_fdiv , [M 8]);
    Some (I_fdivr, [M 8]);
    (* dd *)
    Some (I_fld   , [M 8]);
    Some (I_fisttp, [M 8]);
    Some (I_fst   , [M 8]);
    Some (I_fstp  , [M 8]);
    Some (I_frstor, [M 0]);
    None;
    Some (I_fnsave, [M 0]);
    Some (I_fnstsw, [M 0]);
    (* de *)
    Some (I_fiadd , [M 2]);
    Some (I_fimul , [M 2]);
    Some (I_ficom , [M 2]);
    Some (I_ficomp, [M 2]);
    Some (I_fisub , [M 2]);
    Some (I_fisubr, [M 2]);
    Some (I_fidiv , [M 2]);
    Some (I_fidivr, [M 2]);
    (* df *)
    Some (I_fild  , [M 2]);
    Some (I_fisttp, [M 2]);
    Some (I_fist  , [M 2]);
    Some (I_fistp , [M 2]);
    Some (I_fbld  , [M 0]);
    Some (I_fild  , [M 8]);
    Some (I_fbstp , [M 0]);
    Some (I_fistp , [M 8]);
  |]

type fpu_inst_format =
  | FPU_A of operation
  | FPU_B of operation array

let fpu_mnem_table2 : fpu_inst_format array =
  [|
    (* d8 *)
    FPU_A I_fadd  ;
    FPU_A I_fmul  ;
    FPU_A I_fcom  ;
    FPU_A I_fcomp ;
    FPU_A I_fsub  ;
    FPU_A I_fsubr ;
    FPU_A I_fdiv  ;
    FPU_A I_fdivr ;
    (* d9 *)
    FPU_A I_fld ;
    FPU_A I_fxch;
    FPU_B [|I_fnop   ; I_       ; I_       ; I_       ; I_       ; I_       ; I_       ; I_       |];
    FPU_A I_;
    FPU_B [|I_fchs   ; I_fabs   ; I_       ; I_       ; I_ftst   ; I_fxam   ; I_       ; I_       |];
    FPU_B [|I_fld1   ; I_fldl2t ; I_fldl2e ; I_fldpi  ; I_fldlg2 ; I_fldln2 ; I_fldz   ; I_       |];
    FPU_B [|I_f2xm1  ; I_fyl2x  ; I_fptan  ; I_fpatan ; I_fxtract; I_fprem1 ; I_fdecstp; I_fincstp|];
    FPU_B [|I_fprem  ; I_fyl2xp1; I_fsqrt  ; I_fsincos; I_frndint; I_fscale ; I_fsin   ; I_fcos   |];
    (* da *)
    FPU_A I_fcmovb ;
    FPU_A I_fcmove ;
    FPU_A I_fcmovbe;
    FPU_A I_fcmovu ;
    FPU_A I_;
    FPU_B [|I_       ; I_fucompp; I_       ; I_       ; I_       ; I_       ; I_       ; I_       |];
    FPU_A I_;
    FPU_A I_;
    (* db *)
    FPU_A I_fcmovnb;
    FPU_A I_fcmovne;
    FPU_A I_fcmovnbe;
    FPU_A I_fcmovnu;
    FPU_B [|I_       ; I_       ; I_fnclex ; I_fninit ; I_       ; I_       ; I_       ; I_       |];
    FPU_A I_fucomi ;
    FPU_A I_fcomi  ;
    FPU_A I_;
    (* dc *)
    FPU_A I_fadd_to;
    FPU_A I_fmul_to;
    FPU_A I_;
    FPU_A I_;
    FPU_A I_fsubr_to;
    FPU_A I_fsub_to;
    FPU_A I_fdivr_to;
    FPU_A I_fdiv_to;
    (* dd *)
    FPU_A I_ffree;
    FPU_A I_;
    FPU_A I_fst;
    FPU_A I_fstp;
    FPU_A I_fucom;
    FPU_A I_fucomp;
    FPU_A I_;
    FPU_A I_;
    (* de *)
    FPU_A I_faddp;
    FPU_A I_fmulp;
    FPU_A I_;
    FPU_B [|I_       ; I_fcompp ; I_       ; I_       ; I_       ; I_       ; I_       ; I_       |];
    FPU_A I_fsubrp;
    FPU_A I_fsubp;
    FPU_A I_fdivrp;
    FPU_A I_fdivp;
    (* df *)
    FPU_A I_;
    FPU_A I_;
    FPU_A I_;
    FPU_A I_;
    FPU_B [|I_fnstsw (*ax*) ; I_       ; I_       ; I_       ; I_       ; I_       ; I_       ; I_       |];
    FPU_A I_fucomip;
    FPU_A I_fcomip;
    FPU_A I_;
  |]

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

(* prefixes are packed into an int *)
let read_prefix_and_opcode buf s : int * int (* prefix, opcode *) =
  let prefix = ref 0 in
  let rec loop () =
    let c = s () in
    Buffer.add_char buf c;
    match prefix_of_char c with
    | Some p ->
      (* validity of prefix sequence is not checked here *)
      prefix := !prefix lor prefix_value p;
      loop ()
    | None ->
      let opcode1 = int_of_char c in
      let opcode =
        match opcode1 with
        | 0x0f ->
          let c' = s () in
          Buffer.add_char buf c';
          let opcode2 = int_of_char c' in
          opcode1 lsl 8 lor opcode2
        | _ -> opcode1
      in
      opcode
  in
  let opcode = loop () in
  !prefix, opcode

let extend_opcode opcode r = opcode lsl 3 lor r

type operand_pack =
  (* here 'I' stands for immediate operand and 'M' for r/m operand *)
  | Op_N
  | Op_I   of int
  | Op_II  of int * int
  | Op_M   of regmem
  | Op_MI  of regmem * int
  | Op_MII of regmem * int * int

let optable_add = [| I_add; I_or ; I_adc; I_sbb; I_and; I_sub; I_xor; I_cmp |]
let optable_rol = [| I_rol; I_ror; I_rcl; I_rcr; I_shl; I_shr; I_shl; I_sar |]

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

let word_size mode prefix =
  let has_prefix_66 = prefix land (prefix_mask Prefix_66) <> 0 in
  match mode, has_prefix_66 with
  | Mode16bit, false
  | Mode32bit, true
  | Mode64bit, true -> 2
  | Mode16bit, true
  | Mode32bit, false
  | Mode64bit, false -> 4

(* r is ModRM[5:3] *)
(* returns None if (opcode, r) does not denote a valid instruction *)
let format_of_inst_single_byte mode prefix opcode r =
  let w = word_size mode prefix in
  let lw =
    match w with
    | 1 -> 0
    | 2 -> 1
    | 4 -> 2
    | 8 -> 3
    | _ -> assert false
  in
  let s = if opcode land 1 = 0 then 0 else lw in
  match opcode with
  | 0x00 | 0x01 | 0x02 | 0x03 | 0x04 | 0x05
  | 0x08 | 0x09 | 0x0a | 0x0b | 0x0c | 0x0d
  | 0x10 | 0x11 | 0x12 | 0x13 | 0x14 | 0x15
  | 0x18 | 0x19 | 0x1a | 0x1b | 0x1c | 0x1d
  | 0x20 | 0x21 | 0x22 | 0x23 | 0x24 | 0x25
  | 0x28 | 0x29 | 0x2a | 0x2b | 0x2c | 0x2d
  | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35
  | 0x38 | 0x39 | 0x3a | 0x3b | 0x3c | 0x3d ->
    let fmt =
      match opcode land 7 with
      | 0 -> [RM 1; R 1]
      | 1 -> [RM w; R w]
      | 2 -> [R 1; RM 1]
      | 3 -> [R w; RM w]
      | 4 -> [R0 1; I 1]
      | 5 -> [R0 w; I w]
      | _ -> assert false
    in
    optable_add.(opcode lsr 3), s, fmt
  | 0x06 | 0x07 | 0x0e | 0x16 | 0x17 | 0x1e | 0x1f ->
    let op = if opcode land 1 = 0 then I_push else I_pop in
    op, lw, [Lit (O_reg seg_reg_table.(opcode lsr 3))]
  | 0x0f -> assert false (* escape *)
  | 0x26 -> assert false (* prefix *)
  | 0x27 -> I_daa, 0, []
  | 0x2e -> assert false (* prefix *)
  | 0x2f -> I_das, 0, []
  | 0x36 -> assert false (* prefix *)
  | 0x37 -> I_aaa, 0, []
  | 0x3e -> assert false (* prefix *)
  | 0x3f -> I_aas, 0, []
  | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x47
  | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f ->
    let op = if opcode land 8 = 0 then I_inc else I_dec in
    op, lw, [R_opcode w]
  | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57
  | 0x58 | 0x59 | 0x5a | 0x5b | 0x5c | 0x5d | 0x5e | 0x5f ->
    let op = if opcode land 8 = 0 then I_push else I_pop in
    op, lw, [R_opcode w]
  | 0x60 -> I_pusha, lw, []
  | 0x61 -> I_popa, lw, []
  | 0x62 -> I_bound, lw, [R w; M 0]
  | 0x63 -> I_arpl, 0, [RM 2; R 2]
  | 0x64 | 0x65 | 0x66 | 0x67 -> assert false (* prefix *)
  | 0x68 | 0x6a -> I_push, lw, [I w]
  | 0x69 -> I_imul, lw, [R w; RM w; I w]
  | 0x6b -> I_imul, lw, [R w; RM w; I 1]
  | 0x6c -> I_ins, 0, []
  | 0x6d -> I_ins, lw, []
  | 0x6e -> I_outs, 0, []
  | 0x6f -> I_outs, lw, []
  | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77
  | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f ->
    I_cjmp, (opcode land 15) lsl 2, [Offset]
  | 0x80 | 0x81 | 0x83 ->
    let op = optable_add.(r) in
    let s, fmt =
      if opcode land 1 = 0
      then 0, [RM 1; I 1]
      else lw, [RM w; I w]
    in
    op, s, fmt
  | 0x82 -> raise Invalid_instruction (* canonical opcode is 0x80 *)
  | 0x84 -> I_test,  0, [RM 1; R 1]
  | 0x85 -> I_test, lw, [RM w; R w]
  | 0x86 -> I_xchg,  0, [RM 1; R 1]
  | 0x87 -> I_xchg, lw, [RM w; R w]
  | 0x88 | 0x89 | 0x8a | 0x8b ->
    let fmt =
      match opcode land 3 with
      | 0 -> [RM 1; R 1]
      | 1 -> [RM w; R w]
      | 2 -> [R 1; RM 1]
      | 3 -> [R w; RM w]
      | _ -> assert false
    in
    I_mov, s, fmt
  | 0x8c ->
    if r >= 6 then raise Invalid_instruction;
    let sr = seg_reg_table.(r) in
    I_movfromseg, lw, [RM w; Lit (O_reg sr)]
  | 0x8d -> I_lea, lw, [R w; M 0]
  | 0x8e ->
    if r >= 6 then raise Invalid_instruction;
    let sr = seg_reg_table.(r) in
    I_movtoseg, lw, [Lit (O_reg sr); RM w]
  | 0x8f ->
    if r = 0
    then I_pop, lw, [M w]
    else raise Invalid_instruction
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 ->
    I_xchg, lw, [R0 w; R_opcode w]
  | 0x98 -> I_cbw, 0, []
  | 0x99 -> I_cwd, lw, []
  | 0x9a -> I_callfar, lw, [Far_ptr]
  | 0x9b -> I_wait, 0, []
  | 0x9c -> I_pushf, lw, []
  | 0x9d -> I_popf, lw, []
  | 0x9e -> I_sahf, 0, []
  | 0x9f -> I_lahf, 0, []
  | 0xa0 | 0xa1 | 0xa2 | 0xa3 ->
    let fmt =
      match opcode with
      | 0xa0 -> [R0 1; M 1]
      | 0xa1 -> [R0 w; M w]
      | 0xa2 -> [M 1; R0 1]
      | 0xa3 -> [M w; R0 w]
      | _ -> assert false
    in
    I_mov, s, fmt
  | 0xa4 | 0xa5 -> I_movs, s, []
  | 0xa6 | 0xa7 -> I_cmps, s, []
  | 0xa8 -> I_test, 0, [R0 1; I 1]
  | 0xa9 -> I_test, lw, [R0 w; I w]
  | 0xaa | 0xab -> I_stos, s, []
  | 0xac | 0xad -> I_lods, s, []
  | 0xae | 0xaf -> I_scas, s, []
  | 0xb0 | 0xb1 | 0xb2 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7
  | 0xb8 | 0xb9 | 0xba | 0xbb | 0xbc | 0xbd | 0xbe | 0xbf ->
    let s' = if opcode land 8 = 0 then  0 else lw in
    I_mov, s', [R_opcode (1 lsl s'); I (1 lsl s')]
  | 0xc0 | 0xc1 ->
    let op = optable_rol.(r) in
    op, s, [RM (1 lsl s); I (1 lsl s)]
  | 0xc2 -> I_retn, lw, [I (1 lsl lw)]
  | 0xc3 -> I_ret, lw, []
  | 0xc4 | 0xc5 ->
    let op = if opcode land 1 = 0 then I_les else I_lds in
    op, lw, [R w; M w]
  | 0xc6 | 0xc7 ->
    if r = 0
    then I_mov, s, [RM (1 lsl s); I (1 lsl s)]
    else raise Invalid_instruction
  | 0xc8 -> I_enter, lw, [I (1 lsl lw); I2 (1 lsl lw)]
  | 0xc9 -> I_leave, 0, []
  | 0xca -> I_retnfar, lw, [I (1 lsl lw)]
  | 0xcb -> I_retfar, lw, []
  | 0xcc -> I_int3, 0, []
  | 0xcd -> I_int, 0, [I 1]
  | 0xce -> I_into, 0, []
  | 0xcf -> I_iret, lw, []
  | 0xd0 | 0xd1 | 0xd2 | 0xd3 ->
    let op = optable_rol.(r) in
    let shift_amount =
      match opcode land 2 with
      | 0 -> O_imm (1, 1)
      | 2 -> O_reg R_CL
      | _ -> assert false
    in
    op, s, [RM (1 lsl s); Lit shift_amount]
  | 0xd4 -> I_aam, 0, [I 1]
  | 0xd5 -> I_aad, 0, [I 1]
  | 0xd6 -> raise Invalid_instruction
  | 0xd7 -> I_xlat, 0, []
  | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
    (match fpu_mnem_table1.((opcode land 7) lsl 3 lor r) with
       Some (op, fmt) -> op, 0, fmt | None -> raise Invalid_instruction)
  | 0xe0 | 0xe1 | 0xe2 | 0xe3 ->
    let op = [|I_loopnz;I_loopz;I_loop;I_jcxz|].(opcode land 3) in
    op, lw, [Offset]
  | 0xe4 | 0xe5 | 0xe6 | 0xe7 ->
    let op = if opcode land 2 = 0 then I_in else I_out in
    op, s, [R0 (1 lsl s); I (1 lsl s)]
  | 0xe8 -> I_call, lw, [Offset]
  | 0xe9 | 0xeb -> I_jmp, 0, [Offset]
  | 0xea -> I_jmpfar, 0, [Far_ptr]
  | 0xec | 0xed | 0xee | 0xef ->
    let op = if opcode land 2 = 0 then I_in else I_out in
    op, s, [R0 (1 lsl s); Lit (O_reg R_DX)]
  | 0xf0 -> assert false (* prefix *)
  | 0xf1 -> I_int1, 0, []
  | 0xf2 | 0xf3 -> assert false (* prefix *)
  | 0xf4 -> I_hlt, 0, []
  | 0xf5 -> I_cmc, 0, []
  | 0xf6 | 0xf7 ->
    let op =
      match r with
      | 0 -> I_test
      | 1 -> raise Invalid_instruction
      | 2 -> I_not
      | 3 -> I_neg
      | 4 -> I_mul
      | 5 -> I_imul
      | 6 -> I_div
      | 7 -> I_idiv
      | _ -> assert false
    in
    let fmt =
      let dst = RM (1 lsl s) in
      if r = 0 then [dst; I (1 lsl s)] else [dst]
    in
    op, s, fmt
  | 0xf8 -> I_clc, 0, []
  | 0xf9 -> I_stc, 0, []
  | 0xfa -> I_cli, 0, []
  | 0xfb -> I_sti, 0, []
  | 0xfc -> I_cld, 0, []
  | 0xfd -> I_std, 0, []
  | 0xfe ->
    let op =
      match r with
      | 0 -> I_inc
      | 1 -> I_dec
      | _ -> raise Invalid_instruction
    in
    op, 0, [RM 1]
  | 0xff ->
    let op =
      match r with
      | 0 -> I_inc
      | 1 -> I_dec
      | 2 -> I_call
      | 3 -> I_callfar
      | 4 -> I_jmp
      | 5 -> I_jmpfar
      | 6 -> I_push
      | _ -> raise Invalid_instruction
    in
    let fmt =
      match r with
      (* call/jmp far *)
      | 3 | 5 -> [M 0]
      | _ -> [RM w]
    in
    op, lw, fmt
  | _ -> assert false

let format_of_inst_0f mode prefix opcode _r =
  let w = word_size mode prefix in
  let lw =
    match w with
    | 1 -> 0
    | 2 -> 1
    | 4 -> 2
    | 8 -> 3
    | _ -> assert false
  in
  match opcode with
  | 0x10 | 0x11 ->
    let fmt = if opcode land 1 = 0 then [XMM_R; XMM_RM] else [XMM_RM; XMM_R] in
    I_movups, 0, fmt
  | 0x80 | 0x81 | 0x82 | 0x83 | 0x84 | 0x85 | 0x86 | 0x87
  | 0x88 | 0x89 | 0x8a | 0x8b | 0x8c | 0x8d | 0x8e | 0x8f ->
    I_cjmp, (opcode land 15) lsl 2, [Offset]
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97
  | 0x98 | 0x99 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f ->
    I_set, (opcode land 15) lsl 2, [RM 1]
  | 0xa0 -> I_push, lw, [Lit (O_reg R_FS)]
  | 0xa1 -> I_pop , lw, [Lit (O_reg R_FS)]
  | 0xa8 -> I_push, lw, [Lit (O_reg R_GS)]
  | 0xa9 -> I_pop , lw, [Lit (O_reg R_GS)]
  | 0xaf -> I_imul, lw, [R w; RM w]
  | 0xb6 | 0xb7 | 0xbe | 0xbf ->
    (* variant[3:2] denotes size of src operand *)
    let op = if opcode land 8 = 0 then I_movzx else I_movsx in
    if opcode land 1 = 0
    then op, lw, [R w; RM 1]
    else
      begin match prefix land (prefix_mask Prefix_66) <> 0, mode with
        | true , Mode16bit
        | false, Mode32bit
        | false, Mode64bit ->
          op, 0b110, [R 4; RM 2]
        | _ -> raise Invalid_instruction
      end
  | _ ->
    let err = Printf.sprintf "unknown opcode: 0f %02x" opcode in
    failwith err

let format_of_inst_fpu opcode1 _mode _prefix opcode2 _r =
  (* topmost 2 bits of opcode2 are both 1; r = 0 *)
  let index1 = (opcode1 land 7) lsl 3 lor (opcode2 lsr 3 land 7) in
  match fpu_mnem_table2.(index1) with
  | FPU_A op ->
    if op = I_ then raise Invalid_instruction else op, 0, [FPU_R]
  | FPU_B a ->
    let index2 = opcode2 land 7 in
    let op = a.(index2) in
    match op with
    | I_ -> raise Invalid_instruction
    | I_fnstsw -> I_fnstsw, 0, [Lit (O_reg R_AX)]
    | _ -> op, 0, []

let format_of_inst mode prefix opcode r =
  let opcode1 = opcode lsr 8 in
  let opcode2 = opcode land 0xff in
  let f =
    match opcode1 with
    | 0 -> format_of_inst_single_byte
    | 0x0f -> format_of_inst_0f
    | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
      format_of_inst_fpu opcode1
    | _ -> assert false
  in
  f mode prefix opcode2 r

let gpr_set_of_size = function
  | 1 -> Reg8bitLegacy
  | 2 -> Reg16bit
  | 4 -> Reg32bit
  | 8 -> Reg64bit
  | _ -> assert false

let convert_reg size r =
  let regset = gpr_set_of_size size in
  O_reg (int_to_reg regset r)

let convert_inst mode ext_opcode prefix bytes operand_pack =
  let opcode = ext_opcode lsr 3 in
  let r = ext_opcode land 7 in
  let g, imm1, imm2 =
    match operand_pack with
    | Op_N -> Reg 0, 0, 0
    | Op_I i -> Reg 0, i, 0
    | Op_II (i1, i2) -> Reg 0, i1, i2
    | Op_M g -> g, 0, 0
    | Op_MI (g, i) -> g, i, 0
    | Op_MII (g, i1, i2) -> g, i1, i2
  in
  let op, var, fmt = format_of_inst mode prefix opcode r in
  let convert_operand = function
    | R size -> convert_reg size r
    | R0 size -> convert_reg size 0
    | R_opcode size -> convert_reg size (opcode land 7)
    | RM size ->
      begin match g with
        | Reg r -> convert_reg size r
        | Mem m -> O_mem (m, size)
      end
    | M size ->
      begin match g with
        | Reg r -> raise Invalid_operand
        | Mem m -> O_mem (m, size)
      end
    | I size -> O_imm (imm1, size)
    | I2 size -> O_imm (imm2, size)
    | Offset -> O_offset (imm1 + String.length bytes)
    | Far_ptr -> O_farptr (imm1, imm2)
    | FPU_R ->
      begin match g with
        | Reg r -> O_reg (R_fpu r)
        | Mem _ -> assert false
      end
    | XMM_R -> O_reg (R_xmm r)
    | XMM_RM ->
      begin match g with
        | Reg r -> O_reg (R_xmm r)
        | Mem m -> O_mem (m, 16)
      end
    | Lit o -> o
  in
  let operands = List.map convert_operand fmt in
  Inst.make ext_opcode prefix bytes op var operands

let disassemble mode s : Inst.t =
  let buf = Buffer.create 8 in
  let prefix, opcode = read_prefix_and_opcode buf s in
  let inst_format =
    let opcode1 = opcode lsr 8 in
    let opcode2 = opcode land 0xff in
    match opcode1 with
    | 0 -> int_of_char inst_format_table.[opcode2]
    | 0x0f -> int_of_char inst_format_table_0f.[opcode2]
    | _ ->
      Printf.fprintf stderr "fatal: invalid opcode1: %x\n" opcode1;
      assert false
  in
  let alt_data = prefix land (prefix_mask Prefix_66) <> 0 in
  let alt_addr = prefix land (prefix_mask Prefix_67) <> 0 in
  let data_size = if alt_data then 2 else 4 in
  let addr_size = if alt_addr then 2 else 4 in
  let ext_opcode, operand_pack =
    if inst_format land 0x10 <> 0
    then (* has regmem operand *)
      let r, g = read_regmem32 buf s in
      let ext_opcode = extend_opcode opcode r in
      begin match opcode with
      | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
        let index = ((opcode land 7) lsl 3 lor r) in
        begin match g with
          | Reg r' ->
            let opcode2 = (3 lsl 3 lor r) lsl 3 lor r' in
            let opcode' = opcode lsl 8 lor opcode2 in
            let ext_opcode' = extend_opcode opcode' 0 in
            let operand_pack =
              match fpu_mnem_table2.(index) with
              | FPU_A _ -> Op_M g
              | FPU_B _ -> Op_N
            in
            ext_opcode', operand_pack
          | Mem _ ->
            ext_opcode, Op_M g
        end
      | 0xf6 | 0xf7 ->
        let operand_pack =
          if r = 0
          then
            let imm_size = if opcode land 1 = 0 then 1 else data_size in
            Op_MI (g, read_imm imm_size buf s)
          else Op_M g
        in
        ext_opcode, operand_pack
      | _ ->
        let operand_pack =
          match inst_format land 7 with
          | 0 -> Op_M g
          | 1 -> Op_MI (g, read_imm 1 buf s)
          | 2 -> Op_MI (g, read_imm data_size buf s)
          | 3 -> Op_MI (g, read_imm 2 buf s)
          | 4 ->
            let imm1 = read_imm 2 buf s in
            let imm2 = read_imm 1 buf s in
            Op_MII (g, imm1, imm2)
          | 5 ->
            let imm1 = read_imm 2 buf s in
            let imm2 = read_imm data_size buf s in
            Op_MII (g, imm1, imm2)
          | _ -> assert false
        in
        ext_opcode, operand_pack
      end
    else (* no regmem operand *)
      let ext_opcode = extend_opcode opcode 0 in
      let operand_pack =
        match inst_format land 7 with
        | 0 -> Op_N
        | 1 -> Op_I (read_imm 1 buf s)
        | 2 -> Op_I (read_imm data_size buf s)
        | 3 -> Op_I (read_imm 2 buf s)
        | 4 ->
          let imm1 = read_imm 2 buf s in
          let imm2 = read_imm 1 buf s in
          Op_II (imm1, imm2)
        | 5 ->
          let imm1 = read_imm 2 buf s in
          let imm2 = read_imm data_size buf s in
          Op_II (imm1, imm2)
        | 6 ->
          let g =
            Mem { base = None; index = None; disp = read_imm addr_size buf s }
          in
          Op_M g
        | _ -> assert false
      in
      ext_opcode, operand_pack
  in
  convert_inst mode ext_opcode prefix (Buffer.contents buf) operand_pack
