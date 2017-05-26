open Printf

type processor_mode =
  | Mode16bit
  | Mode32bit
  | Mode64bit

let encode_processor_mode = function
  | Mode16bit -> 0
  | Mode32bit -> 1
  | Mode64bit -> 2

let decode_processor_mode = function
  | 0 -> Mode16bit
  | 1 -> Mode32bit
  | 2 -> Mode64bit
  | _ -> assert false

type gpr_set =
  | Reg8bitLegacy
  | Reg8bitUniform
  | Reg16bit
  | Reg32bit
  | Reg64bit

let gpr_name (set : gpr_set) (index : int) : string =
  match set with
  | Reg8bitLegacy ->
      (* assert (index >= 0 && index < 8); *)
      [|"al";"cl";"dl";"bl";"ah";"ch";"dh";"bh"|].(index)
  | Reg8bitUniform ->
      (* assert (index >= 0 && index < 16); *)
      [| "al"; "cl"; "dl" ;  "bl"; "spl"; "bpl"; "sil"; "dil";
        "r8l";"r9l";"r10l";"r11l";"r12l";"r13l";"r14l";"r15l"|].(index)
  | Reg16bit ->
      (* assert (index >= 0 && index < 16); *)
      [| "ax"; "cx"; "dx" ;  "bx";  "sp";  "bp";  "si";  "di";
        "r8w";"r9w";"r10w";"r11w";"r12w";"r13w";"r14w";"r15w"|].(index)
  | Reg32bit ->
      (* assert (index >= 0 && index < 16); *)
      [|"eax";"ecx";"edx" ; "ebx"; "esp"; "ebp"; "esi"; "edi";
        "r8d";"r9d";"r10d";"r11d";"r12d";"r13d";"r14d";"r15d"|].(index)
  | Reg64bit ->
      (* assert (index >= 0 && index < 16); *)
      [|"rax";"rcx";"rdx";"rbx";"rsp";"rbp";"rsi";"rdi";
         "r8"; "r9";"r10";"r11";"r12";"r13";"r14";"r15"|].(index)

let gpr_set_of_reg_operand (mode : processor_mode) (data_size : int) : gpr_set =
  match data_size, mode with
  | 1, Mode16bit
  | 1, Mode32bit -> Reg8bitLegacy
  | 1, Mode64bit -> Reg8bitUniform
  | 2, _ -> Reg16bit
  | 4, _ -> Reg32bit
  | 8, _ -> Reg64bit
  | _ -> assert false

type mem_operand = {
  base : int (* reg *) option;
  index : (int * int) (* reg, scale *) option;
  disp : int;
}

let gpr_set_of_addr_reg (mode : processor_mode) (alt_addr_size : bool) =
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
  | _ -> assert false

let format_mem_operand (addr_reg_set : gpr_set) (size_opt : int option) (m : mem_operand) : string =
  let string_of_index index =
    let index_reg_s = gpr_name addr_reg_set (fst index) in
    let scale = snd index in
    if scale > 1
    then sprintf "%s*%d" index_reg_s scale
    else index_reg_s
  in
  let m_s =
    match m.base, m.index with
    | Some base, Some index ->
        let base_s = gpr_name addr_reg_set base in
        let index_s = string_of_index index in
        let disp_s = if m.disp = 0 then "" else sprintf "%+d" m.disp in
        sprintf "[%s+%s%s]" base_s index_s disp_s
    | Some base, None ->
        let base_s = gpr_name addr_reg_set base in
        let disp_s = if m.disp = 0 then "" else sprintf "%+d" m.disp in
        sprintf "[%s%s]" base_s disp_s
    | None, Some index ->
        let index_s = string_of_index index in
        let disp_s = if m.disp = 0 then "" else sprintf "%+d" m.disp in
        sprintf "[%s%s]" index_s disp_s
    | None, None ->
        sprintf "[%d]" m.disp
  in
  match size_opt with
  | Some size -> sprintf "%s %s" (format_size size) m_s
  | None -> m_s

type g_operand =
  | G_reg of int
  | G_mem of mem_operand

let read_sib (s : char Stream.t) : int * ((int * int) option) =
  let sib = int_of_char (Stream.next s) in
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

let read_imm (n : int) (s : char Stream.t) =
  let rec f n' acc =
    if n' = n
    then
      if acc land (1 lsl (n*8-1)) = 0
      then acc
      else acc - (1 lsl (n*8)) (* sign-extend immediate *)
    else
      let b = int_of_char (Stream.next s) in
      f (n'+1) (acc lor (b lsl (n'*8)))
  in
  f 0 0

let read_g_operand (s : char Stream.t) : int * g_operand =
  let modrm = int_of_char (Stream.next s) in
  let r = modrm land 7 in
  let g =
    let m = modrm lsr 6 in (* mode field (modrm[7:6]) *)
    begin match m with
    | 0 ->
        begin match r with
        | 4 -> (* SIB follows *)
            let (base, index) = read_sib s in
            if base = 5
            then
              let disp = read_imm 4 s in
              G_mem { base = None; index; disp }
            else
              G_mem { base = Some base; index; disp = 0 }
        | 5 ->
            let disp = read_imm 4 s in
            G_mem { base = None; index = None; disp }
        | _ ->
            G_mem { base = Some r; index = None; disp = 0 }
        end
    | 1 | 2 ->
        let disp_size = if m = 1 then 1 else 4 in
        if r = 4
        then
          let (base, index) = read_sib s in
          let disp = read_imm disp_size s in
          G_mem { base = Some base; index; disp }
        else
          let disp = read_imm disp_size s in
          G_mem { base = Some r; index = None; disp }
    | 3 ->
        G_reg r
    | _ -> assert false
    end
  in
  (modrm lsr 3 land 7, g)

(*
 * 0 = none
 * 1 = I8
 * 2 = Iw
 * 3 = I16
 * 4 = I16I8
 * 5 = I16Iw
 * 6 = Ia abs
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
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
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

let fpu_mnem_table1 : (string * string) option array =
  [|
    (* d8 *)
    Some ("fadd" , "m4");
    Some ("fmul" , "m4");
    Some ("fcom" , "m4");
    Some ("fcomp", "m4");
    Some ("fsub" , "m4");
    Some ("fsubr", "m4");
    Some ("fdiv" , "m4");
    Some ("fdivr", "m4");
    (* d9 *)
    Some ("fld", "m4");
    None;
    Some ("fst"    , "m4");
    Some ("fstp"   , "m4");
    Some ("fldenv" , "m" );
    Some ("fldcw"  , "m" );
    Some ("fnstenv", "m" );
    Some ("fnstcw" , "m" );
    (* da *)
    Some ("fiadd" , "m4");
    Some ("fimul" , "m4");
    Some ("ficom" , "m4");
    Some ("ficomp", "m4");
    Some ("fisub" , "m4");
    Some ("fisubr", "m4");
    Some ("fidiv" , "m4");
    Some ("fidivr", "m4");
    (* db *)
    Some ("fild"  , "m4");
    Some ("fisttp", "m4");
    Some ("fist"  , "m4");
    Some ("fistp" , "m4");
    None;
    Some ("fld"   , "m10");
    None;
    Some ("fstp"  , "m10");
    (* dc *)
    Some ("fadd" , "m8");
    Some ("fmul" , "m8");
    Some ("fcom" , "m8");
    Some ("fcomp", "m8");
    Some ("fsub" , "m8");
    Some ("fsubr", "m8");
    Some ("fdiv" , "m8");
    Some ("fdivr", "m8");
    (* dd *)
    Some ("fld"   , "m8");
    Some ("fisttp", "m8");
    Some ("fst"   , "m8");
    Some ("fstp"  , "m8");
    Some ("frstor", "m" );
    None;
    Some ("fnsave", "m" );
    Some ("fnstsw", "m" );
    (* de *)
    Some ("fiadd" , "m2");
    Some ("fimul" , "m2");
    Some ("ficom" , "m2");
    Some ("ficomp", "m2");
    Some ("fisub" , "m2");
    Some ("fisubr", "m2");
    Some ("fidiv" , "m2");
    Some ("fidivr", "m2");
    (* df *)
    Some ("fild"  , "m2");
    Some ("fisttp", "m2");
    Some ("fist"  , "m2");
    Some ("fistp" , "m2");
    Some ("fbld"  , "m" );
    Some ("fild"  , "m8");
    Some ("fbstp" , "m" );
    Some ("fistp" , "m8");
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

type inst =
  | Inst_N   of int
  | Inst_I   of int * int
  | Inst_II  of int * int * int
  | Inst_M   of int * g_operand
  | Inst_MI  of int * g_operand * int
  | Inst_MII of int * g_operand * int * int

type prefix =
  | Prefix_26
  | Prefix_2e
  | Prefix_36
  | Prefix_3e
  | Prefix_64
  | Prefix_65
  | Prefix_66
  | Prefix_67
  | Prefix_f0
  | Prefix_f2
  | Prefix_f3

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
  | Prefix_66 -> 1 lsl 5
  | Prefix_67 -> 1 lsl 6
  | Prefix_f0 -> 1
  | Prefix_f2 -> 2
  | Prefix_f3 -> 3

exception MutuallyExclusivePrefixes
exception NotImplemented

(* prefixes are packed into an int *)
let read_prefix_and_opcode (s : char Stream.t) : int * int =
  let rec f acc =
    let c = Stream.next s in
    match prefix_of_char c with
    | Some prefix ->
        if acc land prefix_mask prefix = 0
        then f (acc lor prefix_value prefix)
        else raise MutuallyExclusivePrefixes
    | None ->
        let opcode1 = int_of_char c in
        let opcode =
          match opcode1 with
          | 0x0f ->
              let opcode2 = int_of_char (Stream.next s) in
              opcode1 lsl 8 lor opcode2
          | _ -> opcode1
        in
        acc, opcode
  in
  f 0

let encode_opcode opcode r prefix mode =
  let mode_enc = encode_processor_mode mode in
  ((opcode lsl 3 lor r) lsl 7 lor prefix) lsl 2 lor mode_enc

let decode_opcode opf =
  (opf lsr 12,
   opf lsr 9 land 7,
   opf lsr 2 land 0x7f,
   decode_processor_mode (opf land 3))

let disassemble (mode : processor_mode) (s : char Stream.t) : inst =
  let prefix, opcode = read_prefix_and_opcode s in
  let inst_format =
    let opcode1 = opcode lsr 8 in
    let opcode2 = opcode land 0xff in
    match opcode1 with
    | 0 -> int_of_char inst_format_table.[opcode2]
    | 0x0f -> int_of_char inst_format_table_0f.[opcode2]
    | _ ->
        fprintf stderr "fatal: invalid opcode1: %x\n" opcode1;
        assert false
  in
  let alt_data = prefix land (prefix_mask Prefix_66) <> 0 in
  let alt_addr = prefix land (prefix_mask Prefix_67) <> 0 in 
  let word_size = if alt_data then 2 else 4 in
  let addr_size = if alt_addr then 2 else 4 in
  if inst_format land 0x10 <> 0 (* has g-operand *)
  then
    let r, g = read_g_operand s in
    let opf = encode_opcode opcode r prefix mode in
    match opcode with
    | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
        let index = ((opcode land 7) lsl 3 lor r) in
        begin match g with
        | G_reg r' ->
            let opcode2 = (3 lsl 3 lor r) lsl 3 lor r' in
            let opf' = encode_opcode (opcode lsl 8 lor opcode2) 0 prefix mode in
            begin match fpu_mnem_table2.(index) with
            | FPU_A _ -> Inst_M (opf', g)
            | FPU_B _ -> Inst_N opf'
            end
        | G_mem _ ->
            Inst_M (opf, g)
        end
    | 0xf6 | 0xf7 ->
        if r = 0
        then
          let imm_size = if opcode land 1 = 0 then 1 else word_size in
          Inst_MI (opf, g, read_imm imm_size s)
        else Inst_M  (opf, g)
    | _ ->
        begin match inst_format land 7 with
        | 0 -> Inst_M   (opf, g)
        | 1 -> Inst_MI  (opf, g, read_imm 1 s)
        | 2 -> Inst_MI  (opf, g, read_imm word_size s)
        | 3 -> Inst_MI  (opf, g, read_imm 2 s)
        | 4 ->
            let imm1 = read_imm 2 s in
            let imm2 = read_imm 1 s in
            Inst_MII (opf, g, imm1, imm2)
        | 5 ->
            let imm1 = read_imm 2 s in
            let imm2 = read_imm word_size s in
            Inst_MII (opf, g, imm1, imm2)
        | _ -> assert false
        end
  else
    let opf = encode_opcode opcode 0 prefix mode in
    match inst_format land 7 with
    | 0 -> Inst_N  (opf)
    | 1 -> Inst_I  (opf, read_imm 1 s)
    | 2 -> Inst_I  (opf, read_imm word_size s)
    | 3 -> Inst_I  (opf, read_imm 2 s)
    | 4 ->
        let imm1 = read_imm 2 s in
        let imm2 = read_imm 1 s in
        Inst_II (opf, imm1, imm2)
    | 5 ->
        let imm1 = read_imm 2 s in
        let imm2 = read_imm word_size s in
        Inst_II (opf, imm1, imm2)
    | 6 ->
        let g =
          G_mem { base = None; index = None; disp = read_imm addr_size s }
        in
        Inst_M (opf, g)
    | _ -> assert false

let mnemonics_add = [|"add";"or" ;"adc";"sbb";"and";"sub";"xor";"cmp"|]
let mnemonics_rol = [|"rol";"ror";"rcl";"rcr";"shl";"shr";""   ;"sar"|]

let operand_size_prefix (mode : processor_mode) (prefix : int) : string option =
  if prefix land (prefix_mask Prefix_66) <> 0
  then
    match mode with
    | Mode16bit -> Some "o32"
    | Mode32bit
    | Mode64bit -> Some "o16"
  else None

let with_operand_size_prefix (mode : processor_mode) (prefix : int) (m : string) : string =
  match operand_size_prefix mode prefix with
  | Some o -> sprintf "%s %s" o m
  | None -> m

let cond_code =
  [|"o";"no";"b";"ae";"z";"nz";"be";"a";
    "s";"ns";"p";"np";"l";"ge";"le";"g"|]

let seg_reg_name =
  [|"es";"cs";"ss";"ds";"fs";"gs"|]

(* r is ModRM[5:3] *)
(* returns None if (opcode, r) does not denote a valid instruction *)
let format_of_inst_0 (mode : processor_mode) (prefix : int) (opcode : int) (r : int) : (string * string) option =
  (* let () = printf "; format_of_inst: opcode=%02x r=%d\n" opcode r in *)
  match opcode with
  | 0x00 | 0x01 | 0x02 | 0x03 | 0x04 | 0x05
  | 0x08 | 0x09 | 0x0a | 0x0b | 0x0c | 0x0d
  | 0x10 | 0x11 | 0x12 | 0x13 | 0x14 | 0x15
  | 0x18 | 0x19 | 0x1a | 0x1b | 0x1c | 0x1d
  | 0x20 | 0x21 | 0x22 | 0x23 | 0x24 | 0x25
  | 0x28 | 0x29 | 0x2a | 0x2b | 0x2c | 0x2d
  | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35
  | 0x38 | 0x39 | 0x3a | 0x3b | 0x3c | 0x3d ->
      let formats = [|"g1,r1";"gw,rw";"r1,g1";"rw,gw";"a1,i";"aw,i"|] in
      Some (mnemonics_add.(opcode lsr 3), formats.(opcode land 7))
  | 0x06 | 0x07 | 0x0e | 0x16 | 0x17 | 0x1e | 0x1f ->
      let m = if opcode land 1 = 0 then "push" else "pop" in
      Some (with_operand_size_prefix mode prefix m, [|"'es";"'cs";"'ss";"'ds"|].(opcode lsr 3))
  | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x47
  | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f
  | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57
  | 0x58 | 0x59 | 0x5a | 0x5b | 0x5c | 0x5d | 0x5e | 0x5f ->
      Some ([|"inc";"dec";"push";"pop"|].(opcode lsr 3 land 3), "qw")
  | 0x62 ->
      Some ("bound", "rw,m")
  | 0x68 | 0x6a ->
      let spec =
        if prefix land (prefix_mask Prefix_66) <> 0
        then
          match mode with
          | Mode16bit -> "i4"
          | Mode32bit
          | Mode64bit -> "i2"
        else "i"
      in
      Some ("push", spec)
  | 0x69 | 0x6b ->
      Some ("imul", "rw,gw,i")
  | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77
  | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f ->
      Some ("j"^cond_code.(opcode land 15), "o")
  | 0x80 | 0x81 | 0x82 | 0x83 ->
      Some (mnemonics_add.(r), if opcode land 1 = 0 then "G1,i" else "Gw,i")
  | 0x84 | 0x85 | 0x86 | 0x87 ->
      let m = if opcode land 2 = 0 then "test" else "xchg" in
      let s = if opcode land 1 = 0 then "g1,r1" else "gw,rw" in
      Some (m, s)
  | 0x88 | 0x89 | 0x8a | 0x8b ->
      Some ("mov", [|"g1,r1";"gw,rw";"r1,g1";"rw,gw"|].(opcode land 3))
  | 0x8c ->
      if r < 6
      then
        let s = seg_reg_name.(r) in
        Some ("mov", sprintf "gw,'%s" s)
      else None
  | 0x8d ->
      Some ("lea", "rw,m")
  | 0x8e ->
      if r < 6 && r <> 1
      then
        let s = seg_reg_name.(r) in
        Some (with_operand_size_prefix mode prefix "mov", sprintf "'%s,gw" s)
      else None
  | 0x8f ->
      if r = 0
      then Some ("pop", "Gw")
      else None
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 ->
      Some ("xchg", "aw,qw")
  | 0xa0 | 0xa1 | 0xa2 | 0xa3 ->
      let spec =
        match opcode with
        | 0xa0 -> "a1,m"
        | 0xa1 -> "aw,m"
        | 0xa2 -> "m,a1"
        | 0xa3 -> "m,aw"
        | _ -> assert false
      in
      Some ("mov", spec)
  | 0xa8 | 0xa9 ->
      Some ("test", if opcode land 1 = 0 then "a1,i" else "aw,i")
  | 0xb0 | 0xb1 | 0xb2 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7
  | 0xb8 | 0xb9 | 0xba | 0xbb | 0xbc | 0xbd | 0xbe | 0xbf ->
      Some ("mov", if opcode land 8 = 0 then "q1,i" else "qw,i")
  | 0xc0 | 0xc1 ->
      Some (mnemonics_rol.(r), if opcode land 1 = 0 then "G1,i" else "Gw,i")
  | 0xc2 ->
      Some ("ret", "i")
  | 0xc4 | 0xc5 ->
      Some ((if opcode land 1 = 0 then "les" else "lds"), "rw,m")
  | 0xc6 | 0xc7 ->
      if r = 0
      then
        let s = if opcode land 1 = 0 then "G1,i" else "Gw,i" in
        Some ("mov", s)
      else None
  | 0xca ->
      Some ("retf", "i")
  | 0xcd ->
      Some ("int", "i")
  | 0xd0 | 0xd1 | 0xd2 | 0xd3 ->
      let m = mnemonics_rol.(r) in
      let s = [|"g1,'1";"gw,'1";"g1,'cl";"gw,'cl"|].(opcode land 3) in
      Some (m, s)
  | 0xd4 | 0xd5 ->
      let m = if opcode land 1 = 0 then "aam" else "aad" in
      Some (m, "i")
  | 0xd6 -> None
  | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
      fpu_mnem_table1.((opcode land 7) lsl 3 lor r)
  | 0xe0 | 0xe1 | 0xe2 | 0xe3 ->
      Some ([|"loopnz";"loopz";"loop";"jcxz"|].(opcode land 3), "o")
  | 0xe4 | 0xe5 | 0xe6 | 0xe7 ->
      let m = if opcode land 2 = 0 then "in" else "out" in
      let s = if opcode land 1 = 0 then "a1,i" else "aw,i" in
      Some (m, s)
  | 0xe8 | 0xe9 | 0xeb ->
      let m = if opcode land 1 = 0 then "call" else "jmp" in
      Some (m, "o")
  | 0xec | 0xed | 0xee | 0xef ->
      let m = if opcode land 2 = 0 then "in" else "out" in
      let s = if opcode land 1 = 0 then "a1,'dx" else "aw,'dx" in
      Some (m, s)
  | 0xf6 | 0xf7 ->
      if r = 1 then None
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
          then (if r = 0 then "G1,i" else "G1")
          else (if r = 0 then "Gw,i" else "Gw")
        in
        Some (m, s)
  | 0xfe ->
      if r >= 2 then None
      else
        let m =
          match r with
          | 0 -> "inc"
          | 1 -> "dec"
          | _ -> assert false
        in
        Some (m, "g1")
  | 0xff ->
      let m = [|"inc";"dec";"call";"callf";"jmp";"jmpf";"push";""|].(r) in
      let s =
        match r with
        (* call/jmp far *)
        | 3 | 5 -> "m"
        | _ -> "Gw"
      in
      Some (m, s)
  | _ ->
      fprintf stderr "fatal: format_of_inst: opcode=%02x r=%d\n" opcode r;
      assert false

let format_of_inst_0f (mode : processor_mode) (prefix : int) (opcode : int) (r : int) : (string * string) option =
  match opcode with
  | 0x80 | 0x81 | 0x82 | 0x83 | 0x84 | 0x85 | 0x86 | 0x87
  | 0x88 | 0x89 | 0x8a | 0x8b | 0x8c | 0x8d | 0x8e | 0x8f ->
      Some ("j"^cond_code.(opcode land 15), "o")
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97
  | 0x98 | 0x99 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f ->
      Some ("set"^cond_code.(opcode land 15), "g1")
  | 0xa0 | 0xa1 | 0xa8 | 0xa9 ->
      let m = if opcode land 1 = 0 then "push" else "pop" in
      let s = [|"'fs";"'gs"|].(opcode lsr 3 land 1) in
      Some (with_operand_size_prefix mode prefix m, s)
  | 0xb6 | 0xb7 | 0xbe | 0xbf ->
      let m = if opcode lsr 3 land 1 = 0 then "movzx" else "movsx" in
      if opcode land 1 = 0
      then Some (m, "rw,g1")
      else
        begin match prefix land (prefix_mask Prefix_66) <> 0, mode with
        | true , Mode16bit
        | false, Mode32bit
        | false, Mode64bit ->
            Some (m, "r4,g2")
        | _ -> None
        end
  | 0xaf -> Some ("imul", "rw,gw")
  | _ ->
      let err = sprintf "unknown opcode: 0f %02x" opcode in
      failwith err

let format_of_inst_fpu (opcode1 : int) (mode : processor_mode) (prefix : int) (opcode2 : int) (r : int) : (string * string) option =
  (* topmost 2 bits of opcode2 are both 1; r = 0 *)
  let index1 = (opcode1 land 7) lsl 3 lor (opcode2 lsr 3 land 7) in
  match fpu_mnem_table2.(index1) with
  | FPU_A m ->
      if m = "" then None else Some (m, "f")
  | FPU_B a ->
      let index2 = opcode2 land 7 in
      let m = a.(index2) in
      if m = "" then None else Some (m, "")

let format_of_inst (mode : processor_mode) (prefix : int) (opcode : int) (r : int) : (string * string) option =
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

let format_inst opf g i =
  let opcode, r, prefix, mode = decode_opcode opf in
  let alt_data = prefix land (prefix_mask Prefix_66) <> 0 in
  let alt_addr = prefix land (prefix_mask Prefix_67) <> 0 in
  let word_size =
    match mode, alt_data with
    | Mode16bit, false
    | Mode32bit,  true
    | Mode64bit,  true -> Reg16bit
    | Mode16bit,  true
    | Mode32bit, false
    | Mode64bit, false -> Reg32bit
  in
  match opcode with
  | 0x27 -> "daa"
  | 0x2f -> "das"
  | 0x3f -> "aas"
  | 0x60 ->
      begin match word_size with
      | Reg16bit -> "pusha"
      | Reg32bit -> "pushad"
      | _ -> failwith "TODO"
      end
  | 0x61 ->
      begin match word_size with
      | Reg16bit -> "popa"
      | Reg32bit -> "popad"
      | _ -> failwith "TODO"
      end
  | 0x6c -> "insb"
  | 0x6d ->
      begin match word_size with
      | Reg16bit -> "insw"
      | Reg32bit -> "insd"
      | _ -> failwith "TODO"
      end
  | 0x6e -> "outsb"
  | 0x6f ->
      begin match word_size with
      | Reg16bit -> "outsw"
      | Reg32bit -> "outsd"
      | _ -> failwith "TODO"
      end
  | 0x98 -> "cbw"
  | 0x99 ->
      begin match word_size with
      | Reg16bit -> "cwd"
      | Reg32bit -> "cdq"
      | _ -> failwith "TODO"
      end
  | 0x9b -> "wait"
  | 0x9c -> "pushf"
  | 0x9d -> "popf"
  | 0x9e -> "sahf"
  | 0x9f -> "lahf"
  | 0xa4 -> "movsb"
  | 0xa5 ->
      begin match word_size with
      | Reg16bit -> "movsw"
      | Reg32bit -> "movsd"
      | _ -> failwith "TODO"
      end
  | 0xa6 -> "cmpsb"
  | 0xa7 ->
      begin match word_size with
      | Reg16bit -> "cmpsw"
      | Reg32bit -> "cmpsd"
      | _ -> failwith "TODO"
      end
  | 0xaa -> "stosb"
  | 0xab ->
      begin match word_size with
      | Reg16bit -> "stosw"
      | Reg32bit -> "stosd"
      | _ -> failwith "TODO"
      end
  | 0xac -> "lodsb"
  | 0xad ->
      begin match word_size with
      | Reg16bit -> "lodsw"
      | Reg32bit -> "lodsd"
      | _ -> failwith "TODO"
      end
  | 0xae -> "scasb"
  | 0xaf ->
      begin match word_size with
      | Reg16bit -> "scasw"
      | Reg32bit -> "scasd"
      | _ -> failwith "TODO"
      end
  | 0xc3 -> "ret"
  | 0xc9 -> "leave"
  | 0xcb -> "retf"
  | 0xcc -> "int3"
  | 0xce -> "into"
  | 0xcf -> "iret"
  | 0xd7 -> "xlat"
  | 0xf1 -> "int1"
  | 0xf4 -> "hlt"
  | 0xf5 -> "cmc"
  | 0xf8 -> "clc"
  | 0xf9 -> "stc"
  | 0xfa -> "cli"
  | 0xfb -> "sti"
  | 0xfc -> "cld"
  | 0xfd -> "std"
  | _ ->
      let format_opt = format_of_inst mode prefix opcode r in
      begin match format_opt with
      | None -> "<invalid instruction>"
      | Some (mne, fmt) ->
        let format_operand spec =
          let data_size = function
            | '1' -> 1
            | '2' -> 2
            | '4' -> 4
            | 'w' ->
                begin match mode, alt_data with
                | Mode16bit, false -> 2
                | Mode16bit, true  -> 4
                | Mode32bit, false -> 4
                | Mode32bit, true  -> 2
                | Mode64bit, false -> 4
                | Mode64bit, true  -> 2
                end
            | _ ->
                fprintf stderr "invalid spec: %s\n" spec;
                assert false
          in
          let format_r (r : int) : string =
            let gpr_set = gpr_set_of_reg_operand mode (data_size spec.[1]) in
            gpr_name gpr_set r
          in
          let format_g (mem_is_sized : bool) (g : g_operand) : string =
            match g with
            | G_reg r -> format_r r
            | G_mem m ->
                let size = data_size spec.[1] in
                let addr_reg_set = gpr_set_of_addr_reg mode alt_addr in
                format_mem_operand addr_reg_set (Some size) m
          in
          let extract_size spec =
            let len = String.length spec in
            if len > 1
            then Some (int_of_string (String.sub spec 1 (len-1)))
            else None
          in
          match spec.[0] with
          | 'a' -> format_r 0
          | 'f' ->
              begin match g with
              | G_reg r -> sprintf "st%d" r
              | G_mem _ -> assert false
              end
          | 'g' -> format_g false g
          | 'G' -> format_g  true g
          | 'i' ->
              let size_opt = extract_size spec in
              begin match size_opt with
              | Some size -> sprintf "%s %d" (format_size size) i
              | None -> string_of_int i
              end
          | 'm' ->
              begin match g with
              | G_reg r -> "R" ^ (string_of_int r) (* TODO proper error handling *)
              | G_mem m ->
                  let size_opt =
                    let len = String.length spec in
                    if len > 1
                    then Some (int_of_string (String.sub spec 1 (len-1)))
                    else None
                  in
                  format_mem_operand (gpr_set_of_addr_reg mode alt_addr) size_opt m
              end
          | 'o' -> if i = 0 then "$" else sprintf "$%+d" i
          | 'q' -> format_r (opcode land 7)
          | 'r' -> format_r r
          | '\'' -> String.sub spec 1 (String.length spec - 1)
          | _ -> assert false
        in
        if fmt = "" then mne
        else
          sprintf "%s %s" mne
            begin
              String.split_on_char ',' fmt |>
              List.map format_operand |>
              String.concat ","
            end
      end

let string_of_inst : inst -> string =
  function
  | Inst_N opf ->
      format_inst opf (G_reg 0) 0
  | Inst_I (opf, imm) ->
      format_inst opf (G_reg 0) imm
  | Inst_II (opf, imm1, imm2) ->
      "<TODO>"
  | Inst_M (opf, g) ->
      format_inst opf g 0
  | Inst_MI (opf, g, imm) ->
      format_inst opf g imm
  | Inst_MII (opf, g, imm1, imm2) ->
      "<TODO>"

let () =
  let in_path = Sys.argv.(1) in
  let in_chan = open_in in_path in
  let in_stream = Stream.of_channel in_chan in
  let rec loop () =
    let inst = disassemble Mode32bit in_stream in
    printf "%s\n" (string_of_inst inst);
    loop ()
  in
  print_string "[bits 32]\n";
  try
    loop ()
  with Stream.Failure -> ()
