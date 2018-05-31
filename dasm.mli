type config = {
  mode : cpu_mode;
  pc_opt : int option;
}

val disassemble : config -> string -> int -> Inst.inst
