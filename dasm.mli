type cpu_mode =
  | Mode16bit
  | Mode32bit
  | Mode64bit

type config = {
  mode : cpu_mode;
  pc_opt : int option;
}

val disassemble : config -> string -> int -> Inst.inst
