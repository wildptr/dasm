open Batteries

type proc = {
  mutable inst_cfg : Inst.inst CFG.cfg;
  mutable is_complete : bool;
  mutable is_leaf : bool;
  mutable has_loop : bool;
  mutable defs : Semant.global list;
  mutable uses : Semant.global list;
}

type db = {
  image : PE.pe;
  jump_info : (nativeint, Semant.jump) Hashtbl.t;
  proc_table : (nativeint, proc) Hashtbl.t;
}

let translate_va db va =
  Nativeint.(to_int (va - db.image.image_base))

let get_proc db va =
  Hashtbl.find db.proc_table va

let has_proc db va =
  Hashtbl.mem db.proc_table va

let create_proc db va inst_cfg =
  if has_proc db va then failwith "create_proc: already exists";
  let proc = {
    inst_cfg;
(*     stmt_cfg = Elaborate.elaborate_cfg db inst_cfg; *)
    is_leaf = false;
    is_complete = false;
    has_loop = false;
    defs = Semant.all_globals;
    uses = Semant.all_globals;
  } in
  Hashtbl.add db.proc_table va proc;
  proc

let load_image path =
  let image = PE.load path in
  let jump_info = Hashtbl.create 0 in
  let proc_table = Hashtbl.create 0 in
  { image; jump_info; proc_table }

let get_code db =
  db.image.code

let get_jump_info db va =
  Hashtbl.find db.jump_info va

let get_proc_entry_list db =
  Hashtbl.keys db.proc_table |> List.of_enum |> List.sort Nativeint.compare
