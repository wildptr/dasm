open Core_kernel.Std
open Semant
open Spec_ast

(* "%s takes exactly %d arguments" *)
exception Wrong_arity of string * int
exception Index_out_of_bounds of (expr * int) * int
exception Width_mismatch
exception Unbound_local of string
exception Unbound_global of string
exception Unbound_func of string
exception Set_const of string

let prim_of_unary_op (op, e) =
  match op with
  | Not -> P_not e

let width_of_unary_op (op, w) =
  match op with
  | Not -> w

let prim_of_binary_op (op, e1, e2) =
  match op with
  | Concat -> P_concat [e1;e2]
  | Add -> P_add [e1;e2]
  | Sub -> P_sub (e1,e2)
  | Eq -> P_eq (e1,e2)
  | And -> P_and [e1;e2]
  | Xor -> P_xor [e1;e2]
  | Or -> P_or [e1;e2]

let width_of_binary_op (op, w1, w2) =
  match op with
  | Concat ->
      w1 + w2
  | Add | Sub | And | Xor | Or ->
      if w1 <> w2 then raise Width_mismatch; w1
  | Eq ->
      if w1 <> w2 then raise Width_mismatch; 1

type env = {
  env_local_alist : (string * int) list;
  env_global_map : (reg * int) String.Map.t;
  env_func_map : (Semant.expr * int list * int) String.Map.t;
}

let env_func_map env = env.env_func_map

let init_env =
  let env_global_map = [
    "CF", (Flag_C, 1);
    "PF", (Flag_P, 1);
    "AF", (Flag_A, 1);
    "ZF", (Flag_Z, 1);
    "SF", (Flag_S, 1);
    "DF", (Flag_D, 1);
    "OF", (Flag_O, 1);
  ] |> String.Map.of_alist_exn in
  { env_local_alist = [];
    env_global_map;
    env_func_map = String.Map.empty }

let extend_env (key, value) env =
  { env with env_local_alist = (key, value) :: env.env_local_alist }

let extend_env_func (key, data) env =
  { env with env_func_map = String.Map.add env.env_func_map ~key ~data }

let lookup_local env name =
  match List.findi env.env_local_alist ~f:(fun _ (k, _) -> k = name) with
  | None -> raise (Unbound_local name)
  | Some (i, (_, width)) -> i, width

let lookup_global env name =
  match String.Map.find env.env_global_map name with
  | None -> raise (Unbound_global name)
  | Some (reg, width) -> reg, width

let lookup_func env key =
  match String.Map.find env.env_func_map key with
  | None -> raise (Unbound_func key)
  | Some data -> data

let rec translate_expr env = function
  | Expr_local_sym s ->
      let i, w = lookup_local env s in
      E_local i, w
  | Expr_global_sym s ->
      let r, w = lookup_global env s in
      E_global r, w
  | Expr_literal bv -> E_literal bv, Bitvec.length bv
  | Expr_index (e, i) ->
      let e', w = translate_expr env e in
      begin match i with
      | Index_bit b ->
          if b >= w then raise (Index_out_of_bounds ((e,w),b));
          E_part (e', (b, b+1)), 1
      | Index_part (hi', lo) ->
          let hi = hi'+1 in
          if hi > w then raise (Index_out_of_bounds ((e,w),hi'));
          E_part (e', (lo, hi)), hi-lo
      end
  | Expr_apply (func_name, args) ->
      (* handle built-in functions *)
      begin match func_name with
      | "add_ex" ->
          let a1, a2, a3 =
            match args with
            | [a1;a2;a3] -> a1, a2, a3
            | _ -> raise (Wrong_arity (func_name, 3))
          in
          let a1', w1 = translate_expr env a1 in
          let a2', w2 = translate_expr env a2 in
          let a3', w3 = translate_expr env a3 in
          if w1 <> w2 then raise Width_mismatch;
          if w3 <> 1 then raise Width_mismatch;
          E_prim (P_add_ex (a1', a2', a3')), w1+1
      | _ ->
          let func_body, param_widths, result_width = lookup_func env func_name in
          let args'_widths = List.map ~f:(translate_expr env) args in
          let n_param = List.length param_widths in
          let n_arg = List.length args in
          if n_param <> n_arg then raise (Wrong_arity (func_name, n_param));
          begin
            List.iter (List.zip_exn param_widths args'_widths)
            ~f:(fun (param_width, (arg', arg_width)) ->
              if param_width <> arg_width then raise Width_mismatch)
          end;
          (* function that translates arguments *)
          let rec f = function
            | [] -> func_body
            | (arg, _) :: args'_widths' -> E_let (arg, (f args'_widths'))
          in
          f args'_widths, result_width
      end
  | Expr_unary (op, e) ->
      let e', w = translate_expr env e in
      E_prim (prim_of_unary_op (op, e')), width_of_unary_op (op, w)
  | Expr_binary (op, e1, e2) ->
      let e1', w1 = translate_expr env e1 in
      let e2', w2 = translate_expr env e2 in
      E_prim (prim_of_binary_op (op, e1', e2')), width_of_binary_op (op, w1, w2)
  | Expr_let (name, value, body) ->
      let value', value_width = translate_expr env value in
      let body', body_width = translate_expr (extend_env (name, value_width) env) body in
      E_let (value', body'), body_width
  | Expr_set (name, value) ->
      let r, w = lookup_global env name in
      let value', value_width = translate_expr env value in
      if w <> value_width then raise Width_mismatch;
      E_set (r, value'), 0
  | Expr_seq (e1, e2) ->
      let e1', w1 = translate_expr env e1 in
      if w1 <> 0 then raise Width_mismatch;
      let e2', w2 = translate_expr env e2 in
      E_seq (e1', e2'), w2

let translate_ast ast =
  List.fold ast ~init:init_env ~f:begin fun env (Decl_func func) ->
    (* construct static environment to translate function body in *)
    let body_env =
      List.fold func.func_params ~init:env
      ~f:(fun env' (param_name, param_width) ->
        extend_env (param_name, param_width) env')
    in
    let param_widths = List.map func.func_params ~f:snd in
    let func_body', result_width = translate_expr body_env func.func_body in
    extend_env_func (func.func_name, (func_body', param_widths, result_width)) env
  end
