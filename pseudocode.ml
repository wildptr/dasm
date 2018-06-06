open Batteries
open Cfg
open Control_flow
open Semant
open Format

module Make(V : VarType) = struct

  module S = Make(V)
  open S

  type lvalue =
    | L_var of var
    | L_mem of expr * expr * int

  type pstmt =
    | P_set of lvalue * expr
    | P_goto of expr
    | P_if of expr * pstmt list
    | P_if_else of expr * pstmt list * pstmt list
    | P_do_while of pstmt list * expr
    | P_label of nativeint
    | P_comment of string

  let rec convert_stmt = function
    | S_set (var, e) ->
      P_set (L_var var, e)
    | S_store (size, seg, off, data) ->
      let lv = L_mem (seg, off, size) in
      P_set (lv, data)
    | S_jump (cond_opt, dst) ->
      begin match cond_opt with
        | Some cond ->
          P_if (cond, [P_goto dst])
        | None ->
          P_goto dst
      end
    | S_if (cond, body) ->
      P_if (cond, convert_stmt_list body)
    | S_if_else (cond, body1, body2) ->
      P_if_else (cond, convert_stmt_list body1, convert_stmt_list body2)
    | S_do_while (body, cond) ->
      P_do_while (convert_stmt_list body, cond)
    | _ -> invalid_arg "convert_stmt"

  and convert_stmt_list stmts = stmts |> List.map convert_stmt

  let make_cond (condp, _ as cond) t =
    if t then cond else
      match condp with
      | E_prim1 (P1_not, e) -> e
      | _ -> not_expr cond

  let rec convert = function
    | Virtual -> []
    | BB (b, _) ->
      let stmts =
        if b.conclusion = Jump then
          b.stmts |> List.rev |> List.tl |> List.rev
        else
          b.stmts
      in
      convert_bb b stmts
    | Seq (v1, v2) ->
      let stmts1 = convert v1 in
      let stmts2 = convert v2 in
      stmts1 @ stmts2
    | If (cond, t, body, _) ->
      let cond_stmts, cond_expr = convert_cond cond in
      let if_stmt =
        P_if (make_cond cond_expr t, convert body)
      in
      cond_stmts @ [if_stmt]
    | If_else (cond, t, body_t, body_f) ->
      let cond_stmts, cond_expr = convert_cond cond in
      let if_else_stmt =
        P_if_else (make_cond cond_expr t, convert body_t, convert body_f)
      in
      cond_stmts @ [if_else_stmt]
    | Do_while (cond, t) ->
      let cond_stmts, cond_expr = convert_cond cond in
      [P_do_while (cond_stmts, make_cond cond_expr t)]
    | Generic (_, node, edges) ->
      let n = Array.length node in
      let need_label = Array.make n false in
      edges |> List.iter begin fun (src, dst, _) ->
        if src+1 <> dst && node.(dst) <> Virtual then need_label.(dst) <- true
      end;
      node |> Array.to_list |> List.map convert |>
      List.mapi begin fun i stmts ->
        if need_label.(i) then
          P_label (start_of_ctlstruct node.(i)) :: stmts
        else
          stmts
      end |> List.concat
    | _ -> failwith "not implemented"

  and convert_cond = function
    | BB (b, _) ->
      assert (b.conclusion = Branch);
      let stmts_rev = List.rev b.stmts in
      begin match List.hd stmts_rev with
      | S_jump (Some cond, e) ->
        convert_bb b (stmts_rev |> List.tl |> List.rev), cond
      | _ -> assert false
      end
    | Seq (v1, v2) ->
      let stmts1 = convert v1 in
      let stmts2, cond = convert_cond v2 in
      stmts1 @ stmts2, cond
    | _ -> assert false

  and convert_bb bb stmts =
    (*let comment = P_comment (sprintf "%nx" bb.start) in
    comment ::*) (stmts |> convert_stmt_list)

  let pp_lvalue f = function
    | L_var var -> V.pp f var
    | L_mem (seg, off, size) -> pp_expr f (E_load (size, seg, off), size*8)

  let pp_label_expr f (ep, _ as e) =
    match ep with
    | E_lit bv -> fprintf f "%nx" (Bitvec.to_nativeint bv)
    | _ -> pp_expr f e

  let rec pp_pstmt' indent f = function
    | P_set (lv, e) ->
      fprintf f "%s%a = %a;\n" indent pp_lvalue lv pp_expr e
    | P_goto e ->
      fprintf f "%sgoto %a;\n" indent pp_label_expr e
    | P_if (cond, body) ->
      fprintf f "%sif (%a) {\n" indent pp_expr cond;
      body |> List.iter (pp_pstmt' (indent^"\t") f);
      fprintf f "%s}\n" indent
    | P_if_else (cond, body_t, body_f) ->
      fprintf f "%sif (%a) {\n" indent pp_expr cond;
      body_t |> List.iter (pp_pstmt' (indent^"\t") f);
      fprintf f "%s} else {\n" indent;
      body_f |> List.iter (pp_pstmt' (indent^"\t") f);
      fprintf f "%s}\n" indent
    | P_do_while (body, cond) ->
      fprintf f "%sdo {\n" indent;
      body |> List.iter (pp_pstmt' (indent^"\t") f);
      fprintf f "%s} while (%a)\n" indent pp_expr cond
    | P_label va ->
      (* no indent *)
      fprintf f "%nx:\n" va
    | P_comment s ->
      fprintf f "%s/* %s */\n" indent s

  let pp_pstmt f stmt = pp_pstmt' "" f stmt

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
