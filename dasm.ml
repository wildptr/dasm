type processor_mode =
  | Mode16bit
  | Mode32bit
  | Mode64bit

let encode_processor_mode = function
  | Mode16bit -> 0
  | Mode32bit -> 1
  | Mode64bit -> 2

type gpr_set =
  | Reg8bitLegacy
  | Reg8bitUniform
  | Reg16bit
  | Reg32bit
  | Reg64bit

let gpr_name (set : gpr_set) (index : int) : string =
  match set with
  | Reg8bitLegacy ->
      let () = assert (index >= 0 && index < 8) in
      [|"al";"cl";"dl";"bl";"ah";"ch";"dh";"bh"|].(index)
  | Reg8bitUniform ->
      let () = assert (index >= 0 && index < 16) in
      [| "al"; "cl"; "dl" ;  "bl"; "spl"; "bpl"; "sil"; "dil";
        "r8l";"r9l";"r10l";"r11l";"r12l";"r13l";"r14l";"r15l"|].(index)
  | Reg16bit ->
      let () = assert (index >= 0 && index < 16) in
      [| "ax"; "cx"; "dx" ;  "bx";  "sp";  "bp";  "si";  "di";
        "r8w";"r9w";"r10w";"r11w";"r12w";"r13w";"r14w";"r15w"|].(index)
  | Reg32bit ->
      let () = assert (index >= 0 && index < 16) in
      [|"eax";"ecx";"edx" ; "ebx"; "esp"; "ebp"; "esi"; "edi";
        "r8d";"r9d";"r10d";"r11d";"r12d";"r13d";"r14d";"r15d"|].(index)
  | Reg64bit ->
      let () = assert (index >= 0 && index < 16) in
      [|"rax";"rcx";"rdx";"rbx";"rsp";"rbp";"rsi";"rdi";
         "r8"; "r9";"r10";"r11";"r12";"r13";"r14";"r15"|].(index)

let format_reg_operand mode alt_data_size w r =
  let gpr_set =
    begin match mode, alt_data_size, w with
    | Mode16bit,     _, false -> Reg8bitLegacy
    | Mode16bit, false,  true -> Reg16bit
    | Mode16bit,  true,  true -> Reg32bit
    | Mode32bit,     _, false -> Reg8bitLegacy
    | Mode32bit, false,  true -> Reg32bit
    | Mode32bit,  true,  true -> Reg16bit
    | Mode64bit,     _, false -> Reg8bitUniform
    | Mode64bit, false,  true -> Reg32bit
    | Mode64bit,  true,  true -> Reg16bit
    end
  in
  gpr_name gpr_set r

type mem_operand = {
  base : int (* reg *) option;
  index : (int * int) (* reg, scale *) option;
  disp : int;
}

let format_mem_operand (mode : processor_mode) (alt_addr_size : bool) (m : mem_operand) : string =
  let gpr_set =
    begin match mode, alt_addr_size with
    | Mode16bit, false -> Reg16bit
    | Mode16bit,  true -> Reg32bit
    | Mode32bit, false -> Reg32bit
    | Mode32bit,  true -> Reg16bit
    | Mode64bit, false -> Reg64bit
    | Mode64bit,  true -> Reg32bit
    end
  in
  let string_of_index index =
    let index_reg_s = gpr_name gpr_set (fst index) in
    let scale = snd index in
    if scale > 1
    then Printf.sprintf "%s*%d" index_reg_s scale
    else index_reg_s
  in
  match m.base, m.index with
  | Some base, Some index ->
      let base_s = gpr_name gpr_set base in
      let index_s = string_of_index index in
      let disp_s = if m.disp = 0 then "" else Printf.sprintf "%+d" m.disp in
      Printf.sprintf "[%s+%s%s]" base_s index_s disp_s
  | Some base, None ->
      let base_s = gpr_name gpr_set base in
      let disp_s = if m.disp = 0 then "" else Printf.sprintf "%+d" m.disp in
      Printf.sprintf "[%s%s]" base_s disp_s
  | None, Some index ->
      let index_s = string_of_index index in
      let disp_s = if m.disp = 0 then "" else Printf.sprintf "%+d" m.disp in
      Printf.sprintf "[%s%s]" index_s disp_s
  | None, None ->
      Printf.sprintf "[%d]" m.disp

type g_operand =
  | G_reg of int
  | G_mem of mem_operand

let format_g_operand mode alt_data_size alt_addr_size w = function
  | G_reg r -> format_reg_operand mode alt_data_size w r
  | G_mem m -> format_mem_operand mode alt_addr_size m

let read_sib (s : char Stream.t) : int * ((int * int) option) =
  let sib = int_of_char (Stream.next s) in
  let sib_s = sib lsr 6 in
  let sib_i = sib lsr 3 land 3 in
  let sib_b = sib land 3 in
  let index =
    if sib_b = 4
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
 * 6 = Ia
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
   \x10\x10\x10\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\
   \x01\x01\x01\x01\x01\x01\x01\x01\x02\x02\x05\x01\x00\x00\x00\x00\
   \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x10"

type inst =
  | Inst_N   of int
  | Inst_I   of int * int
  | Inst_II  of int * int * int
  | Inst_M   of int * g_operand
  | Inst_MI  of int * g_operand * int
  | Inst_MII of int * g_operand * int * int

let disassemble (mode : processor_mode) (s : char Stream.t) : inst =
  let opcode = int_of_char (Stream.next s) in
  let inst_format =
    int_of_char begin
      match opcode with
      | 0x0f ->
          failwith "not implemented"
      | 0xf6 | 0xf7 ->
          failwith "not implemented"
      | _ ->
          inst_format_table.[opcode]
    end
  in
  let compute_opcodef r =
    let mode_enc = encode_processor_mode mode in
    (opcode lsl 3 lor r) lsl 5 lor mode_enc in
  if inst_format land 0x10 <> 0 (* has g-operand *)
  then
    let r, g = read_g_operand s in
    let opcodef = compute_opcodef r in
    match inst_format land 7 with
    | 0 -> Inst_M   (opcodef, g)
    | 1 -> Inst_MI  (opcodef, g, read_imm 1 s)
    | 2 -> Inst_MI  (opcodef, g, read_imm 4 s)
    | 3 -> Inst_MI  (opcodef, g, read_imm 2 s)
    | 4 ->
        let imm1 = read_imm 2 s in
        let imm2 = read_imm 1 s in
        Inst_MII (opcodef, g, imm1, imm2)
    | 5 ->
        let imm1 = read_imm 2 s in
        let imm2 = read_imm 4 s in
        Inst_MII (opcodef, g, imm1, imm2)
    | _ -> assert false
    (*Printf.sprintf "%02x\t%d, %s" opcode r (string_of_g_operand g)*)
  else
    let opcodef = compute_opcodef 0 in
    match inst_format land 7 with
    | 0 -> Inst_N  (opcodef)
    | 1 -> Inst_I  (opcodef, read_imm 1 s)
    | 2 -> Inst_I  (opcodef, read_imm 4 s)
    | 3 -> Inst_I  (opcodef, read_imm 2 s)
    | 4 -> Inst_II (opcodef, read_imm 2 s, read_imm 1 s)
    | 5 -> Inst_II (opcodef, read_imm 2 s, read_imm 4 s)
    | _ -> assert false

let mnemonics_add = [|"add";"or" ;"adc";"sbb";"and";"sub";"xor";"cmp"|]
let mnemonics_rol = [|"rol";"ror";"rcl";"rcr";"shl";"shr";""   ;"sar"|]

(* r is ModRM[5:3] *)
(* returns ("", _) if (opcode, r) does not denote a valid instruction *)
let format_of_inst (opcode : int) (r : int) : string * string =
  (* let () = Printf.printf "; format_of_inst: opcode=%02x r=%d\n" opcode r in *)
  match opcode with
  | 0x00 | 0x01 | 0x02 | 0x03 | 0x04 | 0x05
  | 0x08 | 0x09 | 0x0a | 0x0b | 0x0c | 0x0d
  | 0x10 | 0x11 | 0x12 | 0x13 | 0x14 | 0x15
  | 0x18 | 0x19 | 0x1a | 0x1b | 0x1c | 0x1d
  | 0x20 | 0x21 | 0x22 | 0x23 | 0x24 | 0x25
  | 0x28 | 0x29 | 0x2a | 0x2b | 0x2c | 0x2d
  | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35
  | 0x38 | 0x39 | 0x3a | 0x3b | 0x3c | 0x3d ->
      let formats = [|"gb,rb";"gw,rw";"rb,gb";"rw,gw";"ab,i";"aw,i"|] in
      (mnemonics_add.(opcode lsr 3), formats.(opcode land 7))
  | 0x06 | 0x07 | 0x0e | 0x16 | 0x17 | 0x1e | 0x1f ->
      (if opcode land 1 = 0 then "push" else "pop"),
       [|"'es";"'cs";"'ss";"'ds"|].(opcode lsr 3)
  | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x47
  | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f
  | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57
  | 0x58 | 0x59 | 0x5a | 0x5b | 0x5c | 0x5d | 0x5e | 0x5f ->
      ([|"inc";"dec";"push";"pop"|].(opcode lsr 3 land 3), "qw")
  | 0x62 ->
      ("bound", "rw,m")
  | 0x68 | 0x6a ->
      ("push", "i")
  | 0x69 | 0x6b ->
      ("imul", "rw,gw,i")
  | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77
  | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f ->
      let mnemonics =
        [|"jo";"jno";"jb";"jae";"jz";"jnz";"jbe";"ja";
          "js";"jns";"jp";"jnp";"jl";"jge";"jle";"jg"|]
      in
      (mnemonics.(opcode land 15), "o")
  | 0x80 | 0x81 | 0x82 | 0x83 ->
      (mnemonics_add.(r), if opcode land 1 = 0 then "gb,i" else "gw,i")
  | 0x84 | 0x85 | 0x86 | 0x87 ->
      (if opcode land 2 = 0 then "test" else "xchg"),
      (if opcode land 1 = 0 then "gb,rb" else "gw,rw")
  | 0x88 | 0x89 | 0x8a | 0x8b ->
      ("mov", [|"gb,rb";"gw,rw";"rb,gb";"rw,gw"|].(opcode land 3))
  | 0x8d ->
      ("lea", "rw,m")
  | 0x8f ->
      (if r = 0 then "pop" else ""), "gw"
  | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 ->
      ("xchg", "aw,qw")
  | 0xa8 | 0xa9 ->
      ("test", if opcode land 1 = 0 then "ab,i" else "aw,i")
  | 0xb0 | 0xb1 | 0xb2 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7
  | 0xb8 | 0xb9 | 0xba | 0xbb | 0xbc | 0xbd | 0xbe | 0xbf ->
      ("mov", if opcode land 8 = 0 then "qb,i" else "qw,i")
  | 0xc0 | 0xc1 ->
      (mnemonics_rol.(r), if opcode land 1 = 0 then "gb,i" else "gw,i")
  | 0xc2 ->
      ("ret", "i")
  | 0xc4 | 0xc5 ->
      (if opcode land 1 = 0 then "les" else "lds"), "rw,m"
  | 0xc6 | 0xc7 ->
      (if r = 0 then "mov" else ""),
      (if opcode land 1 = 0 then "gb,i" else "gw,i")
  | 0xca ->
      ("retf", "i")
  | 0xcd ->
      ("int", "i")
  | 0xd0 | 0xd1 | 0xd2 | 0xd3 ->
      (mnemonics_rol.(r),
       [|"gb,'1";"gw,'1";"gb,'cl";"gw,'cl"|].(opcode land 3))
  | 0xe0 | 0xe1 | 0xe2 | 0xe3 ->
      ([|"loopnz";"loopz";"loop";"jcxz"|].(opcode land 3), "o")
  | 0xe4 | 0xe5 | 0xe6 | 0xe7 ->
      (if opcode land 2 = 0 then "in" else "out"),
      (if opcode land 1 = 0 then "ab,i" else "aw,i")
  | 0xe8 | 0xe9 | 0xeb ->
      (if opcode land 1 = 0 then "call" else "jmp"), "o"
  | 0xfe ->
      let m = match r with
      | 0 -> "inc"
      | 1 -> "dec"
      | _ -> ""
      in
      (m, "g8")
  | 0xff ->
      ([|"inc";"dec";"call";"callf";"jmp";"jmpf";"push";""|].(r),
       match r with (* call/jmp far *) 3 | 5 -> "m" | _ -> "gw")
  | _ ->
      let () = Printf.printf "format_of_inst: opcode=%02x r=%d\n" opcode r in
      assert false

let format_inst opcodef g i =
  let mode = match opcodef land 3 with
  | 0 -> Mode16bit
  | 1 -> Mode32bit
  | 2 -> Mode64bit
  | _ -> assert false
  in
  let alt_data = opcodef land 4 = 1 in
  let alt_addr = opcodef land 8 = 1 in
  let opcode = opcodef lsr 8 in
  let long_mode = false (* FIXME *) in
  match opcode with
  | 0x27 -> "daa"
  | 0x2f -> "das"
  | 0x3f -> "aas"
  | 0x60 -> "pusha"
  | 0x61 -> "popa"
  | 0x6c -> "insb"
  | 0x6d -> if long_mode then "insd" else "insw"
  | 0x6e -> "outsb"
  | 0x6f -> if long_mode then "outsd" else "outsw"
  | 0x98 -> "cbw"
  | 0x99 -> if long_mode then "cdq" else "cwd"
  | 0x9b -> "wait"
  | 0x9c -> "pushf"
  | 0x9d -> "popf"
  | 0x9e -> "sahf"
  | 0x9f -> "lahf"
  | 0xa4 -> "movsb"
  | 0xa5 -> if long_mode then "movsd" else "movsw"
  | 0xa6 -> "cmpsb"
  | 0xa7 -> if long_mode then "cmpsd" else "cmpsw"
  | 0xaa -> "stosb"
  | 0xab -> if long_mode then "stosd" else "stosw"
  | 0xac -> "lodsb"
  | 0xad -> if long_mode then "lodsd" else "lodsw"
  | 0xae -> "scasb"
  | 0xaf -> if long_mode then "scasd" else "scasw"
  | 0xc3 -> "ret"
  | 0xc9 -> "leave"
  | 0xcb -> "retf"
  | 0xcc -> "int3"
  | 0xce -> "into"
  | 0xcf -> "iret"
  | 0xd4 -> "aam"
  | 0xd5 -> "aad"
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
      let r = opcodef lsr 5 land 7 in
      let mne, fmt = format_of_inst opcode r in
      if mne = "" (* invalid instruction *)
      then ""
      else
        let format_operand spec =
          let format_g (g : g_operand) : string =
            begin match spec.[1] with
            | 'b' -> format_g_operand mode alt_data alt_addr false g
            | 'w' -> format_g_operand mode alt_data alt_addr true g
            | _ -> assert false
            end
          in
          match spec.[0] with
          | 'a' -> format_g (G_reg 0)
          | 'g' -> format_g g
          | 'i' -> string_of_int i
          | 'm' ->
              begin match g with
              | G_reg r -> "R" ^ (string_of_int r) (* TODO proper error handling *)
              | G_mem m -> format_mem_operand mode alt_addr m
              end
          | 'o' -> if i = 0 then "$" else Printf.sprintf "$%+d" i
          | 'q' -> format_g (G_reg (opcode land 7))
          | 'r' -> format_g (G_reg r)
          | '\'' -> String.sub spec 1 (String.length spec - 1)
          | _ -> let () = Printf.printf "spec=%s\n" spec in assert false
        in
        Printf.sprintf "%s %s" mne
          begin
            String.split_on_char ',' fmt |>
            List.map format_operand |>
            String.concat ","
          end

let string_of_inst : inst -> string =
  function
  | Inst_N opcodef ->
      format_inst opcodef (G_reg 0) 0
  | Inst_I (opcodef, imm) ->
      format_inst opcodef (G_reg 0) imm
  | Inst_II (opcodef, imm1, imm2) ->
      "<TODO>"
  | Inst_M (opcodef, g) ->
      format_inst opcodef g 0
  | Inst_MI (opcodef, g, imm) ->
      format_inst opcodef g imm
  | Inst_MII (opcodef, g, imm1, imm2) ->
      "<TODO>"

let () =
  let in_path = if true then "code" else Sys.argv.(1) in
  let in_chan = open_in in_path in
  let in_stream = Stream.of_channel in_chan in
  let rec loop () =
    let inst = disassemble Mode32bit in_stream in
    let () = Printf.printf "%s\n" (string_of_inst inst) in
    loop ()
  in
  loop ()
