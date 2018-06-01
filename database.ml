type proc = {
  mutable cfg : Inst.inst Cfg.cfg;
  mutable inst_snode : Inst.inst Cfg.ctlstruct;
  mutable stmt_snode : Semant.stmt Cfg.ctlstruct;
}

type jump =
  | J_unknown
  | J_resolved
  | J_call
  | J_ret

type db = {
  code : string;
  inst_table : (nativeint, Inst.inst) Hashtbl.t;
  jump_info : (nativeint, jump) Hashtbl.t;
  proc_table : (nativeint, proc) Hashtbl.t;
}

let create code =
  let inst_table = Hashtbl.create 0 in
  let jump_info = Hashtbl.create 0 in
  let proc_table = Hashtbl.create 0 in
  { code; inst_table; jump_info; proc_table }
