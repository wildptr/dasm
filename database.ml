open Batteries

type proc = {
  mutable inst_cfg : Inst.inst Cfg.cfg;
  mutable inst_cs  : Inst.inst Cfg.ctlstruct;
  mutable stmt_cfg : Semant.Plain.stmt Cfg.cfg;
  mutable stmt_cs  : Semant.Plain.stmt Cfg.ctlstruct;
  mutable span : nativeint Itree.t;
  mutable il : Semant.Plain.stmt list;
  temp_tab : int array;
}

type jump =
  | J_unknown
  | J_resolved
  | J_call
  | J_ret

type db = {
  mutable image : Pe.pe option;
  inst_table : (nativeint, Inst.inst) Hashtbl.t;
  jump_info : (nativeint, jump) Hashtbl.t;
  proc_table : (nativeint, proc) Hashtbl.t;
}

let create () =
  let inst_table = Hashtbl.create 0 in
  let jump_info = Hashtbl.create 0 in
  let proc_table = Hashtbl.create 0 in
  { image = None ; inst_table; jump_info; proc_table }

let translate_va db va =
  Nativeint.(to_int (va - 0x400000n)) (*TODO *)

let get_proc db va =
  Hashtbl.find db.proc_table va

let set_proc db va proc =
  Hashtbl.add db.proc_table va proc

let has_proc db va =
  Hashtbl.mem db.proc_table va

let load_image db path =
  let pe = Pe.load path in
  db.image <- Some pe

let get_code db =
  (Option.get db.image).Pe.code

let get_jump_info db va =
  Hashtbl.find db.jump_info va

let get_inst db va =
  Hashtbl.find db.inst_table va
