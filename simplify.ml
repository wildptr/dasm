open Batteries
open Semant
open Normal

module T = Transform(Var)(Var)

let simplify tab = function
  | E_lit _ | E_const _ | E_var _ | E_nondet _ as e -> e
  | e ->
    let z3e =
      try e |> Z3_intf.to_z3expr tab with err ->
        Format.printf "%a@." pp_expr e;
        raise err
    in
    let z3e' = Z3.Expr.simplify z3e None in
    let e' = Z3_intf.of_z3expr z3e' in
(*
      Format.printf "%a\n=> %s\n=> %s\n=> %a@."
        pp_expr e (Z3.Expr.to_string z3e) (Z3.Expr.to_string z3e') pp_expr e';
*)
    e'

let simplify_cfg (cfg : stmt CFG.cfg) =
  let n = Array.length cfg.node in
  let changed = ref false in
  for i=0 to n-1 do
    cfg.node.(i).stmts <-
      cfg.node.(i).stmts |> List.map begin fun stmt ->
        let stmt' = T.map_stmt (fun v -> v) (simplify cfg.temp_tab) stmt in
        if stmt' <> stmt then changed := true;
        stmt'
      end
  done;
  !changed
