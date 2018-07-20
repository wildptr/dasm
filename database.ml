open Batteries

(* type proc = {
  mutable inst_cfg : Inst.inst Cfg.cfg;
  mutable stmt_cfg : Semant.Plain.stmt Cfg.cfg;
  mutable span : nativeint Itree.t;
  mutable il : Pseudocode.Plain.pstmt list;
  temp_tab : int array;
} *)

type jump =
  | J_unknown
  | J_resolved
  | J_call
  | J_ret

type db = {
  image : Pe.pe;
  jump_info : (nativeint, jump) Hashtbl.t;
  cfg_table : (nativeint, Inst.inst Cfg.cfg) Hashtbl.t;
}

let translate_va db va =
  Nativeint.(to_int (va - 0x400000n)) (*TODO *)

let get_cfg db va =
  Hashtbl.find db.cfg_table va

let set_cfg db va cfg =
  Hashtbl.add db.cfg_table va cfg

let has_cfg db va =
  Hashtbl.mem db.cfg_table va

let load_image path =
  let image = Pe.load path in
  let jump_info = Hashtbl.create 0 in
  let cfg_table = Hashtbl.create 0 in
  { image; jump_info; cfg_table }

let get_code db =
  db.image.code

let get_jump_info db va =
  Hashtbl.find db.jump_info va

let get_proc_entry_list db =
  Hashtbl.keys db.cfg_table |> List.of_enum |> List.sort Nativeint.compare
