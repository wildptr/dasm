open Batteries
open Semant
open Template
open Spec_ast

type value =
  | Var of templ_var * typ
  | Proc of proc
  | Templ of proc_templ
  | IConst of int
  | BVConst of Bitvec.t
  | Prim of string

type symtab = value Map.String.t

type env = {
  mutable temp_type_tab : typ array;
  mutable temp_avail_tab : bool array;
  mutable temp_tab_cap : int;
  mutable n_temp : int;
  mutable stmts_rev : stmt list;
  rename_table : (string, expr) Hashtbl.t;
  mutable symtab : symtab;
  var_tab : (string, typ) Hashtbl.t;
}

let emit env stmt =
  env.stmts_rev <- stmt :: env.stmts_rev

let init_temp_tab_size = 16

let create symtab =
  {
    temp_type_tab  = Array.make init_temp_tab_size T_bool;
    temp_avail_tab = Array.make init_temp_tab_size false;
    temp_tab_cap = init_temp_tab_size;
    n_temp = 0;
    stmts_rev = [];
    rename_table = Hashtbl.create 0;
    symtab;
    var_tab = Hashtbl.create 0;
  }

let temp_count env = env.n_temp

exception Found of int

let acquire_temp env typ =
  let n = temp_count env in
  try
    for i=0 to n-1 do
      if env.temp_type_tab.(i) = typ && env.temp_avail_tab.(i) then begin
        env.temp_avail_tab.(i) <- false;
        raise (Found i)
      end
    done;
    let cap = env.temp_tab_cap in
    if env.n_temp = cap then begin
      let new_size = cap * 2 in
      let new_type_tab = Array.make new_size T_bool in
      let new_avail_tab = Array.make new_size false in
      for i=0 to cap-1 do
        new_type_tab.(i) <- env.temp_type_tab.(i);
        new_avail_tab.(i) <- env.temp_avail_tab.(i)
      done;
      env.temp_type_tab <- new_type_tab;
      env.temp_avail_tab <- new_avail_tab
    end;
    let i = env.n_temp in
    env.n_temp <- env.n_temp + 1;
    env.temp_type_tab.(i) <- typ;
    env.temp_avail_tab.(i) <- false;
    TV_Local i
  with Found i -> TV_Local i

let release_temp env temp =
  match temp with
  | TV_Local i -> env.temp_avail_tab.(i) <- true
  | _ -> failwith "release_temp: not a temporary"

let get_stmts env =
  List.rev env.stmts_rev

let type_of_temp tid env =
  env.temp_type_tab.(tid)
