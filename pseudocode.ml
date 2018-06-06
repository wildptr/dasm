open Batteries
open Cfg
open Control_flow
open Semant

module Make(V : VarType) = struct

  module S = Make(V)
  open S

  let make_cond (condp, _ as cond) t =
    if t then cond else
      match condp with
      | E_prim1 (P1_not, e) -> e
      | _ -> not_expr cond

  let rec convert = function
    | Virtual -> []
    | BB (b, _) -> b.stmts
    | Seq (v1, v2) ->
      let stmts1 = convert v1 in
      let stmts2 = convert v2 in
      stmts1 @ stmts2
    | If (cond, t, body, _) ->
      let cond_stmts, cond_expr = convert_cond cond in
      let if_stmt =
        S_if (make_cond cond_expr t, convert body)
      in
      cond_stmts @ [if_stmt]
    | If_else (cond, t, body_t, body_f) ->
      let cond_stmts, cond_expr = convert_cond cond in
      let if_else_stmt =
        S_if_else (make_cond cond_expr t, convert body_t, convert body_f)
      in
      cond_stmts @ [if_else_stmt]
    | Do_while (cond, t) ->
      let cond_stmts, cond_expr = convert_cond cond in
      [S_do_while (cond_stmts, make_cond cond_expr t)]
    | Generic (_, node, _) ->
      node |> Array.to_list |> List.map convert |> List.concat
    | _ -> failwith "not implemented"

  and convert_cond = function
    | BB (b, _) ->
      let stmts_rev = List.rev b.stmts in
      begin match List.hd stmts_rev with
      | S_jump (Some cond, e) -> List.rev (List.tl stmts_rev), cond
      | _ -> assert false
      end
    | Seq (v1, v2) ->
      let stmts1 = convert v1 in
      let stmts2, cond = convert_cond v2 in
      stmts1 @ stmts2, cond
    | _ -> assert false

(*
  let remove_unused_labels stmts =
    let module S = Set.Nativeint in
    let used_labels =
      let temp = ref S.empty in
      let rec mark = function
        | S_jump (_, (E_lit bv, _)) ->
          let dst = Bitvec.to_nativeint bv in
          temp := S.add dst !temp
        | S_if (_, body) -> body |> List.iter mark
        | S_if_else (_, body1, body2) ->
          body1 |> List.iter mark;
          body2 |> List.iter mark
        | S_do_while (body, _) -> body |> List.iter mark
        | _ -> ()
      in
      stmts |> List.iter mark;
      !temp
    in
    let rec sweep = function
      | S_label va as s -> if S.mem va used_labels then Some s else None
      | S_if (cond, body) ->
        Some (S_if (cond, body |> List.filter_map sweep))
      | S_if_else (cond, body1, body2) ->
        let body1' = body1 |> List.filter_map sweep in
        let body2' = body2 |> List.filter_map sweep in
        Some (S_if_else (cond, body1', body2'))
      | S_do_while (body, cond) ->
        Some (S_do_while (body |> List.filter_map sweep, cond))
      | s -> Some s
    in
    stmts |> List.filter_map sweep
*)

end

module Plain = Make(Var)
module SSA = Make(SSAVar)
