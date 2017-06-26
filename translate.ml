open Core
open Semant
open Spec_ast

let prim_of_unary_op = function
  | Not -> P_not

let prim_of_binary_op = function
  | Concat -> P_concat
  | Add -> P_add
  | Sub -> P_sub
  | Eq -> P_eq
  | And -> P_and
  | Xor -> P_xor
  | Or -> P_or

type entry = reg option
  (* | Local (* index is position in association list *)
  | Global of reg *)

type lookup_result =
  | Local of int
  | Global of reg

type env = (string * entry) list

let init_env =
  []

let extend_env (key, value) env =
  (key, value) :: env

exception Unbound_variable of string

let lookup env key =
  match List.findi env ~f:(fun _ (k, _) -> k = key) with
  | None -> raise (Unbound_variable key)
  | Some (i, (_, value)) ->
      begin match value with
      | None -> Local i
      | Some r -> Global r
      end

let lookup_func env key =
  failwith "not implemented"

let rec translate_expr env = function
  | Expr_sym s ->
      begin match lookup env s with
      | Local i -> E_local i
      | Global r -> E_global r
      end
  | Expr_literal bv -> E_literal bv
  | Expr_index (e, i) ->
      let e' = translate_expr env e in
      begin match i with
      | Index_bit b -> E_part (e', (b, b+1))
      | Index_part (hi, lo) -> E_part (e', (lo, hi+1))
      end
  | Expr_apply (func_name, args) ->
      let func_body = lookup_func env func_name in
      let args' = List.map ~f:(translate_expr env) args in
      let rec f = function
        | [] -> func_body
        | arg :: args' -> E_let (arg, (f args'))
      in
      f args'
  | Expr_unary (op, e) ->
      E_prim (prim_of_unary_op op, [translate_expr env e])
  | Expr_binary (op, e1, e2) ->
      E_prim (prim_of_binary_op op, [translate_expr env e1; translate_expr env e2]);
  | Expr_let (name, value, body) ->
      let value' = translate_expr env value in
      let body' = translate_expr (extend_env (name, None) env) body in
      E_let (value', body')
