open Batteries
open Semant

type env = {
  local_tab : (string, int) Hashtbl.t;
  temp_tab : (int, int) Hashtbl.t;
  mutable stmts_rev : stmt list;
  rename_table : (string, expr) Hashtbl.t;
  mutable next_nondet_id : int;
  db : Database.db;
}

let rec size_of_expr env = function
  | E_lit b -> Bitvec.length b
  | E_var var ->
    begin match var with
      | V_global name ->
        let name' =
          match String.index_opt name '_' with
          | Some i -> String.sub name 0 i
          | None -> name
        in
        Inst.(lookup_reg name' |> size_of_reg)
      | V_local name ->
        Hashtbl.find env.local_tab name
      | V_temp i ->
        Hashtbl.find env.temp_tab i
      | V_pc -> 32 (* TODO *)
    end
  | E_part (e, lo, hi) -> hi-lo
  | E_prim1 (p, e) ->
    begin match p with
      | P1_not | P1_neg -> size_of_expr env e
      | P1_foldand
      | P1_foldxor
      | P1_foldor -> 1
    end
  | E_prim2 (p, e1, e2) ->
    begin match p with
      | P2_sub
      | P2_shiftleft
      | P2_logshiftright
      | P2_arishiftright -> size_of_expr env e1
      | P2_eq
      | P2_less
      | P2_below -> 1
    end
  | E_prim3 (p, e1, e2, e3) ->
    begin match p with
      | P3_carry -> 1
    end
  | E_primn (p, es) ->
    begin match p with
      | Pn_concat -> es |> List.map (size_of_expr env) |> List.sum
      | Pn_add
      | Pn_and
      | Pn_xor
      | Pn_or -> List.hd es |> size_of_expr env
    end
  | E_load (size, _, _) -> size * 8
  | E_nondet (n, _) -> n
  | E_extend (_, e, n) -> n

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

let new_temp env width =
  let n = Hashtbl.length env.temp_tab in
  let var = V_temp n in
  Hashtbl.add env.temp_tab n width;
  var

let get_stmts env =
  List.rev env.stmts_rev
