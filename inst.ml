(* TODO: add segment field *)
type mem_operand = {
  base : int (* reg *) option;
  index : (int * int) (* reg, scale *) option;
  disp : int;
}

type g_operand =
  | G_reg of int
  | G_mem of mem_operand

type inst_operand =
  | Op_N
  | Op_I   of int
  | Op_II  of int * int
  | Op_M   of g_operand
  | Op_MI  of g_operand * int
  | Op_MII of g_operand * int * int

type inst = int * int * inst_operand (* extended_opcode, length, operand *)

let extopcode_of_inst (inst : inst) : int =
  let opf, _, _ = inst in opf

let length_of_inst inst =
  let _, len, _ = inst in len

let operand_of_inst inst =
  let _, _, operand = inst in operand

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

let decode_extopcode opf =
  (opf lsr 12,
   opf lsr 9 land 7,
   opf lsr 2 land 0x7f,
   decode_processor_mode (opf land 3))

type gpr_set =
  | Reg8bitLegacy
  | Reg8bitUniform
  | Reg16bit
  | Reg32bit
  | Reg64bit

let gpr_set_of_reg_operand (mode : processor_mode) (data_size : int) : gpr_set =
  match data_size, mode with
  | 1, Mode16bit
  | 1, Mode32bit -> Reg8bitLegacy
  | 1, Mode64bit -> Reg8bitUniform
  | 2, _ -> Reg16bit
  | 4, _ -> Reg32bit
  | 8, _ -> Reg64bit
  | _ -> assert false

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
