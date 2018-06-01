open Batteries

type proc = {
  mutable cfg : Inst.inst Cfg.cfg;
  mutable inst_cs : Inst.inst Cfg.ctlstruct;
  mutable stmt_cs : Semant.stmt Cfg.ctlstruct;
  mutable span : nativeint Itree.t;
  mutable il : Semant.stmt list;
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

let translate_va db va =
  Nativeint.(to_int (va - 0x400000n)) (*TODO *)

let get_proc db va =
  Hashtbl.find db.proc_table va

let has_proc db va =
  Hashtbl.mem db.proc_table va
