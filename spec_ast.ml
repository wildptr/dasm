open Core
open Printf

type index =
  | Index_bit of int
  | Index_part of int * int

let string_of_index = function
  | Index_bit i -> sprintf "[%d]" i
  | Index_part (hi, lo) -> sprintf "[%d:%d]" hi lo

type unary_op =
  | Not

let string_of_unary_op = function
  | Not -> "~"

type binary_op =
  | Concat
  | Add | Sub
  | Eq
  | And
  | Xor
  | Or

let string_of_binary_op = function
  | Concat -> "."
  | Add -> "+"
  | Sub -> "-"
  | Eq -> "=="
  | And -> "&"
  | Xor -> "^"
  | Or -> "|"

type expr =
  | Expr_sym of string
  | Expr_literal of Bitvec.t
  | Expr_index of expr * index
  | Expr_apply of string * expr list
  | Expr_unary of unary_op * expr
  | Expr_binary of binary_op * expr * expr
  | Expr_let of string * expr * expr
  | Expr_set of string * expr
  | Expr_seq of expr * expr

let rec string_of_expr = function
  | Expr_sym s -> s
  | Expr_literal bv -> sprintf "'%s'" (Bitvec.to_string bv)
  | Expr_index (e, i) -> (string_of_expr e) ^ (string_of_index i)
  | Expr_apply (func_name, args) ->
      sprintf "%s(%s)" func_name (String.concat ~sep:"," (List.map ~f:string_of_expr args))
  | Expr_unary (op, e) ->
      sprintf "(%s%s)" (string_of_unary_op op) (string_of_expr e)
  | Expr_binary (op, e1, e2) ->
      sprintf "(%s%s%s)" (string_of_expr e1) (string_of_binary_op op) (string_of_expr e2)
  | Expr_let (name, value, body) ->
      sprintf "(let %s=%s in %s)" name (string_of_expr value) (string_of_expr body)
  | Expr_set (name, value) ->
      sprintf "(%s=%s)" name (string_of_expr value)
  | Expr_seq (e1, e2) ->
      sprintf "(%s;%s)" (string_of_expr e1)  (string_of_expr e2)

type param_list = (string * int) list

let string_of_param_list params =
  (String.concat ~sep:"," (List.map ~f:(fun (name, width) -> sprintf "%s:%d" name width) params))

type func = {
  func_name : string;
  func_params : param_list;
  func_body : expr;
}

let string_of_func func =
  sprintf "let %s(%s)=%s" func.func_name
    (string_of_param_list func.func_params)
    (string_of_expr func.func_body)

type decl =
  | Decl_func of func

let string_of_decl = function
  | Decl_func func -> string_of_func func

type ast = decl list

let string_of_ast ast =
  String.concat ~sep:" " (List.map ~f:string_of_decl ast)
