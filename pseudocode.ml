open Batteries
open Cfg
open Control_flow
open Semant
open Format

module Make(V : VarType) = struct

  module Sem = Make(V)
  open Sem

  type lvalue =
    | L_var of var
    | L_mem of expr * int

  type pstmt =
    | P_set of lvalue * expr
    | P_setpart of lvalue * reg_part * expr
    | P_goto of expr
    | P_if of expr * pstmt list
    | P_if_else of expr * pstmt list * pstmt list
    | P_do_while of pstmt list * expr
    | P_label of nativeint
    | P_comment of string
    | P_call of expr * (Inst.reg * expr) list * (Inst.reg * V.t) list
    | P_return of expr * (Inst.reg * expr) list

  let rec convert_stmt = function
    | S_set (var, e) ->
      P_set (L_var var, e)
    | S_setpart (var, p, e) ->
      P_setpart (L_var var, p, e)
    | S_store (size, off, data) ->
      let lv = L_mem (off, size) in
      P_set (lv, data)
    | S_jump (cond_opt, dst) ->
      begin match cond_opt with
        | Some cond ->
          P_if (cond, [P_goto dst])
        | None ->
          P_goto dst
      end
    | S_jumpout (dst, _) ->
      P_goto dst
    | S_jumpout_call (dst, ins, outs) ->
      P_call (dst, ins, outs)
    | S_jumpout_ret (dst, ins) ->
      P_return (dst, ins)
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

  let conclude emit next_opt succ =
    match next_opt with
    | Some next ->
      if next <> succ then P_goto (make_lit 32 succ) |> emit
    | None -> ()

  let rec convert_seq emit next_opt = function
    | BB (bb, succ_opt) ->
      begin match succ_opt with
        | None -> convert_bb emit None bb 0n
        | Some succ -> convert_bb emit next_opt bb succ
      end
    | Seq (v1, v2) ->
      convert_seq emit (Some (start_of_ctlstruct v2)) v1;
      convert_seq emit next_opt v2
    | If (cond, t, body, succ) ->
      let cond_expr = convert_cond emit cond in
      let body' = convert_seq' (Some succ) body in
      P_if (make_cond cond_expr t, body') |> emit;
      conclude emit next_opt succ
    | IfElse (cond, t, body_t, body_f, succ) ->
      let cond_expr = convert_cond emit cond in
      let body_t' = convert_seq' (Some succ) body_t in
      let body_f' = convert_seq' (Some succ) body_f in
      P_if_else (make_cond cond_expr t, body_t', body_f') |> emit;
      conclude emit next_opt succ
    | DoWhile (cond, t, succ) ->
      let cond_stmts, cond_expr =
        let temp = ref [] in
        let emit' s = temp := s :: !temp in
        let cond_expr = convert_cond emit' cond in
        !temp, cond_expr
      in
      P_do_while (cond_stmts, make_cond cond_expr t) |> emit;
      conclude emit next_opt succ
    | Generic l ->
      let n = Array.length l in
      let next =
        Array.init n begin fun i ->
          if i+1<n then
            Some (start_of_ctlstruct l.(i+1))
          else
            next_opt
        end
      in
      l |> Array.iteri (fun i cs -> convert_seq emit next.(i) cs)

  and convert_cond emit = function
    | BB (bb, _) ->
      let stmts_rev = List.rev bb.stmts in
      begin match List.hd stmts_rev with
      | S_jump (Some cond, e) ->
        let stmts = stmts_rev |> List.tl |> List.rev in
        let bb' = { bb with stmts } in
        convert_bb emit None bb' 0n;
        cond
      | _ -> failwith "convert_cond: no conditional jump at end of basic block"
      end
    | Seq (v1, v2) ->
      convert_seq emit (Some (start_of_ctlstruct v2)) v1;
      convert_cond emit v2
    | _ -> failwith "convert_cond"

  and convert_bb emit next_opt bb succ =
    P_comment (sprintf "%nx" bb.start) |> emit;
    let stmts' =
      match next_opt with
      | Some next ->
        if next = succ then begin
          if bb.has_final_jump then
            match List.rev bb.stmts with
            | S_jump (None, _) :: rest -> rest |> List.rev
            | _ -> failwith "convert_bb: no final jump"
          else bb.stmts
        end else begin
          if bb.has_final_jump then bb.stmts else
            bb.stmts @ [S_jump (None, make_lit 32 succ)]
        end
      | None -> bb.stmts
    in
    stmts' |> convert_stmt_list |> List.iter emit

  and convert_seq' next_opt cs =
    let l = ref [] in
    let emit s = l := s :: !l in
    convert_seq emit next_opt cs;
    List.rev !l

  let convert cs = convert_seq' None cs

  let pp_lvalue f = function
    | L_var var -> V.pp f var
    | L_mem (off, size) -> pp_expr f (E_load (size, off), size*8)

  let pp_label_expr f (ep, _ as e) =
    match ep with
    | E_lit bv -> fprintf f "%nx" (Bitvec.to_nativeint bv)
    | _ -> pp_expr f e

  let rec pp_pstmt' indent f = function
    | P_set (lv, e) ->
      fprintf f "%s%a = %a;\n" indent pp_lvalue lv pp_expr e
    | P_setpart (lv, p, e) ->
      fprintf f "%s%s(%a) = %a;\n" indent (string_of_reg_part p)
        pp_lvalue lv pp_expr e
    | P_goto e ->
      fprintf f "%sgoto %a;\n" indent pp_label_expr e
    | P_call (dst, ins, outs) ->
      pp_print_string f indent;
      outs |> List.iter begin fun (r,v) ->
        fprintf f "%a=%s " V.pp v (Inst.string_of_reg r)
      end;
      fprintf f "call %a" pp_expr dst;
      let pp_pair f (r, v) =
        fprintf f "%s=%a" (Inst.string_of_reg r) pp_expr v
      in
      begin match ins with
        | [] -> ()
        | hd::tl ->
          fprintf f " {%a" pp_pair hd;
          tl |> List.iter (fprintf f ", %a" pp_pair);
          fprintf f "}"
      end;
      pp_print_string f "\n"
    | P_return (dst, ins) ->
      fprintf f "%sreturn_to %a" indent pp_expr dst;
      let pp_pair f (r, v) =
        fprintf f "%s=%a" (Inst.string_of_reg r) pp_expr v
      in
      ins |> begin function
        | [] -> ()
        | hd::tl ->
          fprintf f " {%a" pp_pair hd;
          tl |> List.iter (fprintf f ", %a" pp_pair);
          fprintf f "}"
      end;
      pp_print_string f "\n"
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
      fprintf f "%s} while (%a);\n" indent pp_expr cond
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
