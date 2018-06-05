open Batteries
open Semant

type env = {
  local_tab : (string, int) Hashtbl.t;
  temp_tab : (int, int) Hashtbl.t;
  mutable stmts_rev : Plain.stmt list;
  rename_table : (string, Plain.expr_proper) Hashtbl.t;
  mutable next_nondet_id : int;
  db : Database.db;
}

let emit env stmt =
  env.stmts_rev <- stmt :: env.stmts_rev

let create db =
  {
    local_tab = Hashtbl.create 0;
    temp_tab = Hashtbl.create 0;
    stmts_rev = [];
    rename_table = Hashtbl.create 0;
    next_nondet_id = 0;
    db;
  }

let temp_count env =
  Hashtbl.length env.temp_tab

let new_temp env width =
  let n = temp_count env in
  let var = Var.Temp n in
  Hashtbl.add env.temp_tab n width;
  var

let get_stmts env =
  List.rev env.stmts_rev

let width_of_temp tid env =
  Hashtbl.find env.temp_tab tid
