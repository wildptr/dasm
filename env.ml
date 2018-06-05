open Batteries
open Semant

type env = {
  local_tab : (string, int) Hashtbl.t;
  mutable temp_size_tab : int array;
  mutable temp_avail_tab : bool array;
  mutable temp_tab_cap : int;
  mutable n_temp : int;
  mutable stmts_rev : Plain.stmt list;
  rename_table : (string, Plain.expr_proper) Hashtbl.t;
  mutable next_nondet_id : int;
  db : Database.db;
}

let emit env stmt =
  env.stmts_rev <- stmt :: env.stmts_rev

let init_temp_tab_size = 16

let create db =
  {
    local_tab = Hashtbl.create 0;
    temp_size_tab  = Array.make init_temp_tab_size 0;
    temp_avail_tab = Array.make init_temp_tab_size false;
    temp_tab_cap = init_temp_tab_size;
    n_temp = 0;
    stmts_rev = [];
    rename_table = Hashtbl.create 0;
    next_nondet_id = 0;
    db;
  }

let temp_count env = env.n_temp

exception Found of int

let acquire_temp env width =
  let n = temp_count env in
  try
    for i=0 to n-1 do
      if env.temp_size_tab.(i) = width && env.temp_avail_tab.(i) then begin
        env.temp_avail_tab.(i) <- false;
        raise (Found i)
      end
    done;
    let cap = env.temp_tab_cap in
    if env.n_temp = cap then begin
      let new_size = cap * 2 in
      let new_size_tab = Array.make new_size 0 in
      let new_avail_tab = Array.make new_size false in
      for i=0 to cap-1 do
        new_size_tab.(i) <- env.temp_size_tab.(i);
        new_avail_tab.(i) <- env.temp_avail_tab.(i)
      done;
      env.temp_size_tab <- new_size_tab;
      env.temp_avail_tab <- new_avail_tab
    end;
    let i = env.n_temp in
    env.n_temp <- env.n_temp + 1;
    env.temp_size_tab.(i) <- width;
    env.temp_avail_tab.(i) <- false;
    Var.Temp i
  with Found i -> Var.Temp i

let release_temp env temp =
  match temp with
  | Var.Temp i -> env.temp_avail_tab.(i) <- true
  | _ -> failwith "release_temp: not a temporary"

let get_stmts env =
  List.rev env.stmts_rev

let width_of_temp tid env =
  env.temp_size_tab.(tid)
