open Format
open Inst

exception Not_implemented
exception Invalid_instruction

type regset =
  | Reg8bitLegacy
  | Reg8bitUniform
  | Reg16bit
  | Reg32bit
  | Reg64bit

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

let gpr_set_of_addr_reg mode alt_addr_size =
  match mode, alt_addr_size with
  | Mode16bit, false -> Reg16bit
  | Mode16bit,  true -> Reg32bit
  | Mode32bit, false -> Reg32bit
  | Mode32bit,  true -> Reg16bit
  | Mode64bit, false -> Reg64bit
  | Mode64bit,  true -> Reg32bit

let format_size = function
  | 1 -> "byte"
  | 2 -> "word"
  | 4 -> "dword"
  | 8 -> "qword"
  | 10 -> "tword"
  | 16 -> "oword"
  | _ -> assert false

let read_sib buf s : int * ((int * int) option) =
  let c = Stream.next s in
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
      let c = Stream.next s in
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

  let c = Stream.next s in
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
  | M
  | M_size of int
  | I
  | I2
  | I_size of int
  | Offset
  | Far_ptr
  | FPU_R
  | XMM_R
  | XMM_RM
  | Lit of string

let fpu_mnem_table1 =
  [|
    (* d8 *)
    Some ("fadd" , [M_size 4]);
    Some ("fmul" , [M_size 4]);
    Some ("fcom" , [M_size 4]);
    Some ("fcomp", [M_size 4]);
    Some ("fsub" , [M_size 4]);
    Some ("fsubr", [M_size 4]);
    Some ("fdiv" , [M_size 4]);
    Some ("fdivr", [M_size 4]);
    (* d9 *)
    Some ("fld", [M_size 4]);
    None;
    Some ("fst"    , [M_size 4]);
    Some ("fstp"   , [M_size 4]);
    Some ("fldenv" , [M]);
    Some ("fldcw"  , [M]);
    Some ("fnstenv", [M]);
    Some ("fnstcw" , [M]);
    (* da *)
    Some ("fiadd" , [M_size 4]);
    Some ("fimul" , [M_size 4]);
    Some ("ficom" , [M_size 4]);
    Some ("ficomp", [M_size 4]);
    Some ("fisub" , [M_size 4]);
    Some ("fisubr", [M_size 4]);
    Some ("fidiv" , [M_size 4]);
    Some ("fidivr", [M_size 4]);
    (* db *)
    Some ("fild"  , [M_size 4]);
    Some ("fisttp", [M_size 4]);
    Some ("fist"  , [M_size 4]);
    Some ("fistp" , [M_size 4]);
    None;
    Some ("fld"   , [M_size 10]);
    None;
    Some ("fstp"  , [M_size 10]);
    (* dc *)
    Some ("fadd" , [M_size 8]);
    Some ("fmul" , [M_size 8]);
    Some ("fcom" , [M_size 8]);
    Some ("fcomp", [M_size 8]);
    Some ("fsub" , [M_size 8]);
    Some ("fsubr", [M_size 8]);
    Some ("fdiv" , [M_size 8]);
    Some ("fdivr", [M_size 8]);
    (* dd *)
    Some ("fld"   , [M_size 8]);
    Some ("fisttp", [M_size 8]);
    Some ("fst"   , [M_size 8]);
    Some ("fstp"  , [M_size 8]);
    Some ("frstor", [M]);
    None;
    Some ("fnsave", [M]);
    Some ("fnstsw", [M]);
    (* de *)
    Some ("fiadd" , [M_size 2]);
    Some ("fimul" , [M_size 2]);
    Some ("ficom" , [M_size 2]);
    Some ("ficomp", [M_size 2]);
    Some ("fisub" , [M_size 2]);
    Some ("fisubr", [M_size 2]);
    Some ("fidiv" , [M_size 2]);
    Some ("fidivr", [M_size 2]);
    (* df *)
    Some ("fild"  , [M_size 2]);
    Some ("fisttp", [M_size 2]);
    Some ("fist"  , [M_size 2]);
    Some ("fistp" , [M_size 2]);
    Some ("fbld"  , [M]);
    Some ("fild"  , [M_size 8]);
    Some ("fbstp" , [M]);
    Some ("fistp" , [M_size 8]);
  |]

type fpu_inst_format =
  | FPU_A of string
  | FPU_B of string array

let fpu_mnem_table2 : fpu_inst_format array =
  [|
    (* d8 *)
    FPU_A "fadd"  ;
    FPU_A "fmul"  ;
    FPU_A "fcom"  ;
    FPU_A "fcomp" ;
    FPU_A "fsub"  ;
    FPU_A "fsubr" ;
    FPU_A "fdiv"  ;
    FPU_A "fdivr" ;
    (* d9 *)
    FPU_A "fld" ;
    FPU_A "fxch";
    FPU_B [|"fnop"   ; ""       ; ""       ; ""       ; ""       ; ""       ; ""       ; ""       |];
    FPU_A "";
    FPU_B [|"fchs"   ; "fabs"   ; ""       ; ""       ; "ftst"   ; "fxam"   ; ""       ; ""       |];
    FPU_B [|"fld1"   ; "fldl2t" ; "fldl2e" ; "fldpi"  ; "fldlg2" ; "fldln2" ; "fldz"   ; ""       |];
    FPU_B [|"f2xm1"  ; "fyl2x"  ; "fptan"  ; "fpatan" ; "fxtract"; "fprem1" ; "fdecstp"; "fincstp"|];
    FPU_B [|"fprem"  ; "fyl2xp1"; "fsqrt"  ; "fsincos"; "frndint"; "fscale" ; "fsin"   ; "fcos"   |];
    (* da *)
    FPU_A "fcmovb" ;
    FPU_A "fcmove" ;
    FPU_A "fcmovbe";
    FPU_A "fcmovu" ;
    FPU_A "";
    FPU_B [|""       ; "fucompp"; ""       ; ""       ; ""       ; ""       ; ""       ; ""       |];
    FPU_A "";
    FPU_A "";
    (* db *)
    FPU_A "fcmovnb";
    FPU_A "fcmovne";
    FPU_A "fcmovnbe";
    FPU_A "fcmovnu";
    FPU_B [|""       ; ""       ; "fnclex" ; "fninit" ; ""       ; ""       ; ""       ; ""       |];
    FPU_A "fucomi" ;
    FPU_A "fcomi"  ;
    FPU_A "";
    (* dc *)
    FPU_A "fadd to"  ;
    FPU_A "fmul to"  ;
    FPU_A "";
    FPU_A "";
    FPU_A "fsubr to"  ;
    FPU_A "fsub to" ;
    FPU_A "fdivr to"  ;
    FPU_A "fdiv to" ;
    (* dd *)
    FPU_A "ffree";
    FPU_A "";
    FPU_A "fst";
    FPU_A "fstp";
    FPU_A "fucom";
    FPU_A "fucomp";
    FPU_A "";
    FPU_A "";
    (* de *)
    FPU_A "faddp";
    FPU_A "fmulp";
    FPU_A "";
    FPU_B [|""       ; "fcompp" ; ""       ; ""       ; ""       ; ""       ; ""       ; ""       |];
    FPU_A "fsubrp";
    FPU_A "fsubp";
    FPU_A "fdivrp";
    FPU_A "fdivp";
    (* df *)
    FPU_A "";
    FPU_A "";
    FPU_A "";
    FPU_A "";
    FPU_B [|"fnstsw ax" ; ""       ; ""       ; ""       ; ""       ; ""       ; ""       ; ""       |];
    FPU_A "fucomip";
    FPU_A "fcomip";
    FPU_A "";
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
    let c = Stream.next s in
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
          let c' = Stream.next s in
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
  let ext_opcode, operand =
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
            let operand =
              match fpu_mnem_table2.(index) with
              | FPU_A _ -> Op_M g
              | FPU_B _ -> Op_N
            in
            ext_opcode', operand
          | Mem _ ->
            ext_opcode, Op_M g
        end
      | 0xf6 | 0xf7 ->
        let operand =
          if r = 0
          then
            let imm_size = if opcode land 1 = 0 then 1 else data_size in
            Op_MI (g, read_imm imm_size buf s)
          else Op_M g
        in
        ext_opcode, operand
      | _ ->
        let operand =
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
        ext_opcode, operand
      end
    else (* no regmem operand *)
      let ext_opcode = extend_opcode opcode 0 in
      let operand =
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
      ext_opcode, operand
  in
  Inst.make ext_opcode prefix (Buffer.contents buf) operand

let mnemonics_add = [|"add";"or" ;"adc";"sbb";"and";"sub";"xor";"cmp"|]
let mnemonics_rol = [|"rol";"ror";"rcl";"rcr";"shl";"shr";""   ;"sar"|]

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

let cond_code =
  [|"o";"no";"b";"ae";"z";"nz";"be";"a";
    "s";"ns";"p";"np";"l";"ge";"le";"g"|]

let seg_reg_name =
  [|"es";"cs";"ss";"ds";"fs";"gs";"segr6";"segr7"|]

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
let format_of_inst_0 mode prefix opcode r =
  let w = word_size mode prefix in
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
      | 4 -> [R0 1; I]
      | 5 -> [R0 w; I]
      | _ -> assert false
    in
    (mnemonics_add.(opcode lsr 3), fmt)
  | 0x06 | 0x07 | 0x0e | 0x16 | 0x17 | 0x1e | 0x1f ->
    let m = if opcode land 1 = 0 then "push" else "pop" in
    (with_operand_size_prefix mode prefix m,
     [|"es";"cs";"ss";"ds"|].(opcode lsr 3) |> (fun s -> [Lit s]))
  | 0x0f -> assert false (* escape *)
  | 0x26 -> assert false (* prefix *)
  | 0x27 -> ("daa", [])
  | 0x2e -> assert false (* prefix *)
  | 0x2f -> ("das", [])
  | 0x36 -> assert false (* prefix *)
  | 0x37 -> ("aaa", [])
  | 0x3e -> assert false (* prefix *)
  | 0x3f -> ("aas", [])
  | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x47
  | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f
  | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57
  | 0x58 | 0x59 | 0x5a | 0x5b | 0x5c | 0x5d | 0x5e | 0x5f ->
    ([|"inc";"dec";"push";"pop"|].(opcode lsr 3 land 3), [R_opcode w])
  | 0x60 | 0x61 ->
    let m = if opcode land 1 = 0 then "pusha" else "popa" in
    (with_operand_size_prefix mode prefix m, [])
  | 0x62 -> ("bound", [R w; M])
  | 0x63 -> ("arpl", [RM 2; R 2])
  | 0x64 | 0x65 | 0x66 | 0x67 -> assert false (* prefix *)
  | 0x68 | 0x6a ->
    ("push", [I_size w])
  | 0x69 -> ("imul", [R w; RM w; I_size w])
  | 0x6b -> ("imul", [R w; RM w; I_size 1])
  | 0x6c -> ("insb", [])
  | 0x6d ->
    let m =
      match w with
      | 2 -> "insw"
      | 4 -> "insd"
      | _ -> assert false
    in
    (m, [])
  | 0x6e -> ("outsb", [])
  | 0x6f ->
    let m =
      match w with
      | 2 -> "outsw"
      | 4 -> "outsd"
      | _ -> assert false
    in
    (m, [])
  | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77
  | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f ->
    ("j"^cond_code.(opcode land 15), [Offset])
  | 0x80 | 0x81 | 0x83 ->
    (mnemonics_add.(r), if opcode land 1 = 0 then [RM 1; I] else [RM w; I])
  | 0x82 -> raise Invalid_instruction (* canonical opcode is 0x80 *)
  | 0x84 | 0x85 | 0x86 | 0x87 ->
    let m = if opcode land 2 = 0 then "test" else "xchg" in
    let s = if opcode land 1 = 0 then [RM 1; R 1] else [RM w; R w] in
    (m, s)
  | 0x88 | 0x89 | 0x8a | 0x8b ->
    let s =
      match opcode land 3 with
      | 0 -> [RM 1; R 1]
      | 1 -> [RM w; R w]
      | 2 -> [R 1; RM 1]
      | 3 -> [R w; RM w]
      | _ -> assert false
    in
    ("mov", s)
  | 0x8c ->
    let s = seg_reg_name.(r) in
    ("mov", [RM w; Lit s])
  | 0x8d ->
    ("lea", [RM w; M])
  | 0x8e ->
    let s = seg_reg_name.(r) in
    (with_operand_size_prefix mode prefix "mov", [Lit s; RM w])
  | 0x8f ->
    if r = 0
    then ("pop", [M_size w])
    else raise Invalid_instruction
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 ->
    ("xchg", [R0 w; R_opcode w])
  | 0x98 -> ("cbw", [])
  | 0x99 ->
    let m =
      match w with
      | 2 -> "cwd"
      | 4 -> "cdq"
      | _ -> assert false
    in
    (m, [])
  | 0x9a -> ("call", [Far_ptr])
  | 0x9b -> ("wait", [])
  | 0x9c -> ("pushf", [])
  | 0x9d -> ("popf", [])
  | 0x9e -> ("sahf", [])
  | 0x9f -> ("lahf", [])
  | 0xa0 | 0xa1 | 0xa2 | 0xa3 ->
    let s =
      match opcode with
      | 0xa0 -> [R0 1; M]
      | 0xa1 -> [R0 w; M]
      | 0xa2 -> [M; R0 1]
      | 0xa3 -> [M; R0 w]
      | _ -> assert false
    in
    ("mov", s)
  | 0xa4 -> ("movsb", [])
  | 0xa5 ->
    let m =
      match w with
      | 2 -> "movsw"
      | 4 -> "movsd"
      | _ -> assert false
    in
    (m, [])
  | 0xa6 -> ("cmpsb", [])
  | 0xa7 ->
    let m =
      match w with
      | 2 -> "cmpsw"
      | 4 -> "cmpsd"
      | _ -> assert false
    in
    (m, [])
  | 0xa8 | 0xa9 ->
    ("test", if opcode land 1 = 0 then [R0 1; I] else [R0 w; I])
  | 0xaa -> ("stosb", [])
  | 0xab ->
    let m =
      match w with
      | 2 -> "stosw"
      | 4 -> "stosd"
      | _ -> assert false
    in
    (m, [])
  | 0xac -> ("lodsb", [])
  | 0xad ->
    let m =
      match w with
      | 2 -> "lodsw"
      | 4 -> "lodsd"
      | _ -> assert false
    in
    (m, [])
  | 0xae -> ("scasb", [])
  | 0xaf ->
    let m =
      match w with
      | 2 -> "scasw"
      | 4 -> "scasd"
      | _ -> assert false
    in
    (m, [])
  | 0xb0 | 0xb1 | 0xb2 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7
  | 0xb8 | 0xb9 | 0xba | 0xbb | 0xbc | 0xbd | 0xbe | 0xbf ->
    ("mov", if opcode land 8 = 0 then [R_opcode 1; I] else [R_opcode w; I])
  | 0xc0 | 0xc1 ->
    let m = mnemonics_rol.(r) in
    if m = ""
    then raise Invalid_instruction
    else (m, if opcode land 1 = 0 then [RM 1; I] else [RM w; I])
  | 0xc2 -> ("ret", [I])
  | 0xc3 -> ("ret", [])
  | 0xc4 | 0xc5 ->
    ((if opcode land 1 = 0 then "les" else "lds"), [R w; M])
  | 0xc6 | 0xc7 ->
    if r = 0
    then
      let s = if opcode land 1 = 0 then [RM 1; I] else [RM w; I] in
      ("mov", s)
    else raise Invalid_instruction
  | 0xc8 -> ("enter", [I; I2])
  | 0xc9 -> ("leave", [])
  | 0xca -> ("retf", [I])
  | 0xcb -> ("retf", [])
  | 0xcc -> ("int3", [])
  | 0xcd -> ("int", [I])
  | 0xce -> ("into", [])
  | 0xcf -> ("iret", [])
  | 0xd0 | 0xd1 | 0xd2 | 0xd3 ->
    let m = mnemonics_rol.(r) in
    if m = ""
    then raise Invalid_instruction
    else
      let s =
        match opcode land 3 with
        | 0 -> [RM 1; Lit "1"]
        | 1 -> [RM w; Lit "1"]
        | 2 -> [RM 1; Lit "cl"]
        | 3 -> [RM w; Lit "cl"]
        | _ -> assert false
      in
      (m, s)
  | 0xd4 | 0xd5 ->
    let m = if opcode land 1 = 0 then "aam" else "aad" in
    (m, [I])
  | 0xd6 -> raise Invalid_instruction
  | 0xd7 -> ("xlat", [])
  | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
    (match fpu_mnem_table1.((opcode land 7) lsl 3 lor r) with
       Some t -> t | None -> raise Invalid_instruction)
  | 0xe0 | 0xe1 | 0xe2 | 0xe3 ->
    ([|"loopnz";"loopz";"loop";"jcxz"|].(opcode land 3), [Offset])
  | 0xe4 | 0xe5 | 0xe6 | 0xe7 ->
    let m = if opcode land 2 = 0 then "in" else "out" in
    let s = if opcode land 1 = 0 then [R0 1; I] else [R0 w; I] in
    (m, s)
  | 0xe8 | 0xe9 | 0xeb ->
    let m = if opcode land 1 = 0 then "call" else "jmp" in
    (m, [Offset])
  | 0xea -> ("jmp", [Far_ptr])
  | 0xec | 0xed | 0xee | 0xef ->
    let m = if opcode land 2 = 0 then "in" else "out" in
    let s = if opcode land 1 = 0 then [R0 1; Lit "dx"] else [R0 w; Lit "dx"] in
    (m, s)
  | 0xf0 -> assert false (* prefix *)
  | 0xf1 -> ("int1", [])
  | 0xf2 | 0xf3 -> assert false (* prefix *)
  | 0xf4 -> ("hlt", [])
  | 0xf5 -> ("cmc", [])
  | 0xf6 | 0xf7 ->
    if r = 1 then raise Invalid_instruction
    else
      let m =
        match r with
        | 0 -> "test"
        | 2 -> "not"
        | 3 -> "neg"
        | 4 -> "mul"
        | 5 -> "imul"
        | 6 -> "div"
        | 7 -> "idiv"
        | _ -> assert false
      in
      let s =
        if opcode land 1 = 0
        then (if r = 0 then [RM 1; I] else [RM 1])
        else (if r = 0 then [RM w; I] else [RM w])
      in
      (m, s)
  | 0xf8 -> ("clc", [])
  | 0xf9 -> ("stc", [])
  | 0xfa -> ("cli", [])
  | 0xfb -> ("sti", [])
  | 0xfc -> ("cld", [])
  | 0xfd -> ("std", [])
  | 0xfe ->
    if r >= 2 then raise Invalid_instruction
    else
      let m =
        match r with
        | 0 -> "inc"
        | 1 -> "dec"
        | _ -> assert false
      in
      (m, [RM 1])
  | 0xff ->
    let m = [|"inc";"dec";"call";"callf";"jmp";"jmpf";"push";""|].(r) in
    if m = "" then raise Invalid_instruction;
    let s =
      match r with
      (* call/jmp far *)
      | 3 | 5 -> [M]
      | _ -> [RM w]
    in
    (m, s)
  | _ -> assert false

let format_of_inst_0f mode prefix opcode _r =
  let w = word_size mode prefix in
  match opcode with
  | 0x10 | 0x11 ->
    let s = if opcode land 1 = 0 then [XMM_R; XMM_RM] else [XMM_RM; XMM_R] in
    ("movups", s)
  | 0x80 | 0x81 | 0x82 | 0x83 | 0x84 | 0x85 | 0x86 | 0x87
  | 0x88 | 0x89 | 0x8a | 0x8b | 0x8c | 0x8d | 0x8e | 0x8f ->
    ("j"^cond_code.(opcode land 15), [Offset])
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97
  | 0x98 | 0x99 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f ->
    ("set"^cond_code.(opcode land 15), [RM 1])
  | 0xa0 | 0xa1 | 0xa8 | 0xa9 ->
    let m = if opcode land 1 = 0 then "push" else "pop" in
    let s = [|"fs";"gs"|].(opcode lsr 3 land 1) in
    (with_operand_size_prefix mode prefix m, [Lit s])
  | 0xaf -> ("imul", [R w; RM w])
  | 0xb6 | 0xb7 | 0xbe | 0xbf ->
    let m = if opcode lsr 3 land 1 = 0 then "movzx" else "movsx" in
    if opcode land 1 = 0
    then (m, [R w; RM 1])
    else
      begin match prefix land (prefix_mask Prefix_66) <> 0, mode with
        | true , Mode16bit
        | false, Mode32bit
        | false, Mode64bit ->
          (m, [R 4; RM 2])
        | _ -> raise Invalid_instruction
      end
  | _ ->
    let err = Printf.sprintf "unknown opcode: 0f %02x" opcode in
    failwith err

let format_of_inst_fpu opcode1 _mode _prefix opcode2 _r =
  (* topmost 2 bits of opcode2 are both 1; r = 0 *)
  let index1 = (opcode1 land 7) lsl 3 lor (opcode2 lsr 3 land 7) in
  match fpu_mnem_table2.(index1) with
  | FPU_A m ->
    if m = "" then raise Invalid_instruction else (m, [FPU_R])
  | FPU_B a ->
    let index2 = opcode2 land 7 in
    let m = a.(index2) in
    if m = "" then raise Invalid_instruction else (m, [])

let format_of_inst mode prefix opcode r =
  let opcode1 = opcode lsr 8 in
  let opcode2 = opcode land 0xff in
  let f =
    match opcode1 with
    | 0 -> format_of_inst_0
    | 0x0f -> format_of_inst_0f
    | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
      format_of_inst_fpu opcode1
    | _ -> assert false
  in
  f mode prefix opcode2 r

let pp_r size f r =
  let regset =
    match size with
    | 1 -> Reg8bitLegacy
    | 2 -> Reg16bit
    | 4 -> Reg32bit
    | 8 -> Reg64bit
    | _ -> assert false
  in
  pp_print_string f (string_of_reg (int_to_reg regset r))

let pp_mem_sized size f m =
  fprintf f "%s " (format_size size);
  pp_mem f m

let pp_inst mode f inst =
  let ext_opcode = ext_opcode_of inst in
  let opcode = ext_opcode lsr 3 in
  let r = ext_opcode land 7 in
  let prefix = prefix_of inst in
  let operand = operand_of inst in
  let g, imm1, imm2 =
    match operand with
    | Op_N -> Reg 0, 0, 0
    | Op_I i -> Reg 0, i, 0
    | Op_II (i1, i2) -> Reg 0, i1, i2
    | Op_M g -> g, 0, 0
    | Op_MI (g, i) -> g, i, 0
    | Op_MII (g, i1, i2) -> g, i1, i2
  in
  let mne, fmt = format_of_inst mode prefix opcode r in
  let pp_operand = function
    | R size -> pp_r size f r
    | R0 size -> pp_r size f 0
    | R_opcode size -> pp_r size f (opcode land 7)
    | RM size ->
      begin match g with
        | Reg r -> pp_r size f r
        | Mem m -> pp_mem_sized size f m
      end
    | M ->
      begin match g with
        | Reg r ->
          (* a reg operand found where a mem operand is expected *)
          fprintf f "R%d" r
        | Mem m -> pp_mem f m
      end
    | M_size size ->
      begin match g with
        | Reg r ->
          (* a reg operand found where a mem operand is expected *)
          fprintf f "R%d" r
        | Mem m -> pp_mem_sized size f m
      end
    | I -> pp_print_int f imm1
    | I2 -> pp_print_int f imm2
    | I_size size -> fprintf f "%s %d" (format_size size) imm1
    | Offset ->
      let disp = imm1 + length_of inst in
      if disp = 0 then pp_print_string f "$" else fprintf f "$%+d" disp
    | Far_ptr ->
      fprintf f "0x%x:0x%x" imm1 imm2
    | FPU_R ->
      begin match g with
        | Reg r -> fprintf f "st%d" r
        | Mem _ -> assert false
      end
    | XMM_R -> fprintf f "xmm%d" r
    | XMM_RM ->
      begin match g with
        | Reg r -> fprintf f "xmm%d" r
        | Mem m -> pp_mem_sized size f m
      end
    | Lit s -> pp_print_string f s
  in
  pp_print_string f mne;
  match fmt with
  | [] -> ()
  | fmt_hd::fmt_tl ->
    pp_print_string f " ";
    pp_operand fmt_hd;
    List.iter (fun fmt -> pp_print_string f ","; pp_operand fmt) fmt_tl

let main () =
  (* Elaborate.load_spec (); *)
  let mode = Mode32bit in
  let in_path = Sys.argv.(1) in
  let in_chan = open_in in_path in
  let s = Stream.of_channel in_chan in
  let rec loop () =
    let inst = disassemble mode s in
    fprintf std_formatter "%a@." (pp_inst mode) inst;
    (* let e = Elaborate.elaborate_inst inst in
       printf "{%a}@." Semant.pp_expr e; *)
    loop ()
  in
  print_string "[bits 32]\n";
  try loop () with _ -> close_in in_chan

let () = main ()
