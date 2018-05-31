type proc = {
  mutable cfg : Inst.inst Cfg.cfg;
  mutable inst_snode : Inst.inst Cfg.ctlstruct;
  mutable stmt_snode : Semant.stmt Cfg.ctlstruct;
}

type db = {
  code : string;
  inst_table : (int, Inst.inst) Hashtbl.t;
  jump_info : (int, Semant.jump) Hashtbl.t;
  proc_table : (int, proc) Hashtbl.t;
}

let create code =
  let inst_table = Hashtbl.create 0 in
  let jump_info = Hashtbl.create 0 in
  let proc_table = Hashtbl.create 0 in
  { code; inst_table; jump_info; proc_table }
