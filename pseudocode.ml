open Batteries
open Cfg
open Control_flow
open Semant

let make_cond cond t =
  if t then cond else
    match cond with
    | E_prim1 (P1_not, e) -> e
    | _ -> E_prim1 (P1_not, cond)

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
    | S_jump (Some cond, e, _, _) -> List.rev (List.tl stmts_rev), cond
    | _ -> assert false
    end
  | Seq (v1, v2) ->
    let stmts1 = convert v1 in
    let stmts2, cond = convert_cond v2 in
    stmts1 @ stmts2, cond
  | _ -> assert false
