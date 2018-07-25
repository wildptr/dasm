open Batteries
open Semant

module Make(V : VarType) = struct

  module Sem = Make(V)
  open Sem

  let simplify tab e =
    let z3 = Z3.mk_context [] in
    let z3e =
      try e |> to_z3expr z3 tab with (Z3.Error _ as err) ->
        Format.printf "%a@." pp_expr e;
        raise err
    in
    let z3e' = Z3.Expr.simplify z3e None in
    let e' = from_z3expr z3e' in
    Format.printf "%a\n=> %s\n=> %s\n=> %a@."
      pp_expr e (Z3.Expr.to_string z3e) (Z3.Expr.to_string z3e') pp_expr e';
    e'

  let simplify_cfg cfg =
    let n = Array.length cfg.Cfg.node in
    let changed = ref false in
    for i=0 to n-1 do
      cfg.Cfg.node.(i).Cfg.stmts <-
        cfg.Cfg.node.(i).Cfg.stmts |> List.map begin fun stmt ->
          let stmt' = map_stmt (simplify cfg.temp_tab) stmt in
          if stmt' <> stmt then changed := true;
          stmt'
        end
    done;
    !changed

end

module Plain = Make(Var)
module SSA = Make(SSAVar)
