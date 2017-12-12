open Format

type reg =
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH
  | R_AX | R_CX | R_DX | R_BX | R_SI | R_DI | R_SP | R_BP
  | R_EAX | R_ECX | R_EDX | R_EBX | R_ESI | R_EDI | R_ESP | R_EBP

let string_of_reg = function
  | R_AL -> "al"
  | R_CL -> "cl"
  | R_DL -> "dl"
  | R_BL -> "bl"
  | R_AH -> "ah"
  | R_CH -> "ch"
  | R_DH -> "dh"
  | R_BH -> "bh"
  | R_AX -> "ax"
  | R_CX -> "cx"
  | R_DX -> "dx"
  | R_BX -> "bx"
  | R_SI -> "si"
  | R_DI -> "di"
  | R_SP -> "sp"
  | R_BP -> "bp"
  | R_EAX -> "eax"
  | R_ECX -> "ecx"
  | R_EDX -> "edx"
  | R_EBX -> "ebx"
  | R_ESI -> "esi"
  | R_EDI -> "edi"
  | R_ESP -> "esp"
  | R_EBP -> "ebp"

(* used for ... *)
let index_of_reg = function
  | R_AL -> 0
  | R_CL -> 1
  | R_DL -> 2
  | R_BL -> 3
  | R_AH -> 4
  | R_CH -> 5
  | R_DH -> 6
  | R_BH -> 7
  | R_AX -> 0
  | R_CX -> 1
  | R_DX -> 2
  | R_BX -> 3
  | R_SI -> 4
  | R_DI -> 5
  | R_SP -> 6
  | R_BP -> 7
  | R_EAX -> 0
  | R_ECX -> 1
  | R_EDX -> 2
  | R_EBX -> 3
  | R_ESI -> 4
  | R_EDI -> 5
  | R_ESP -> 6
  | R_EBP -> 7

(* TODO: add segment field *)
type mem = {
  base : reg option;
  index : (reg * int (* scale *)) option;
  disp : int;
}

let pp_mem f m =
  let open Format in
  let pp_index f (reg, scale) =
    pp_print_string f (string_of_reg reg);
    if scale > 1 then fprintf f "*%d" scale
  in
  match m.base, m.index with
  | Some base, Some index ->
    fprintf f "[%s+%a" (string_of_reg base) pp_index index;
    if m.disp <> 0 then fprintf f "%+d" m.disp;
    fprintf f "]"
  | Some base, None ->
    fprintf f "[%s" (string_of_reg base);
    if m.disp <> 0 then fprintf f "%+d" m.disp;
    fprintf f "]"
  | None, Some index ->
    fprintf f "[%a" pp_index index;
    if m.disp <> 0 then fprintf f "%+d" m.disp;
    fprintf f "]"
  | None, None ->
    fprintf f "[%d]" m.disp

type regmem =
  | Reg of int
  | Mem of mem

type operand =
  (* here 'I' stands for immediate operand and 'M' for r/m operand *)
  | Op_N
  | Op_I   of int
  | Op_II  of int * int
  | Op_M   of regmem
  | Op_MI  of regmem * int
  | Op_MII of regmem * int * int

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

type t = {
  ext_opcode : int; (* opcode << 3 | opcode_extension *)
  prefix : int;
  bytes : string;
  operand : operand;
}

let make ext_opcode prefix bytes operand =
  { ext_opcode; prefix; bytes; operand }

let ext_opcode_of inst = inst.ext_opcode

let prefix_of inst = inst.prefix

let bytes_of inst = inst.bytes

let length_of inst = String.length inst.bytes

let operand_of inst = inst.operand

let hax_prefix inst prefix =
  inst.prefix land (prefix_mask prefix) = prefix_value prefix
