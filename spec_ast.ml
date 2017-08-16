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

type call = string * expr list

and expr =
  | Expr_sym of string
  | Expr_literal of Bitvec.t
  | Expr_index of expr * index
  | Expr_call of call
  | Expr_unary of unary_op * expr
  | Expr_binary of binary_op * expr * expr

type stmt =
  (* Variables created by let statements are immutable. *)
  | Stmt_let of string * expr
  | Stmt_set of string * expr
  | Stmt_call of call
  | Stmt_return of expr

let rec string_of_call (proc_name, args) =
  sprintf "%s(%s)" proc_name (String.concat ~sep:"," (List.map ~f:string_of_expr args))

and string_of_expr = function
  | Expr_sym s -> s
  | Expr_literal bv -> sprintf "'%s'" (Bitvec.to_string bv)
  | Expr_index (e, i) -> (string_of_expr e) ^ (string_of_index i)
  | Expr_call c ->
      string_of_call c
  | Expr_unary (op, e) ->
      sprintf "(%s%s)" (string_of_unary_op op) (string_of_expr e)
  | Expr_binary (op, e1, e2) ->
      sprintf "(%s%s%s)" (string_of_expr e1) (string_of_binary_op op) (string_of_expr e2)

let string_of_stmt = function
  | Stmt_let (name, value) ->
      sprintf "let %s = %s;" name (string_of_expr value)
  | Stmt_set (name, value) ->
      sprintf "%s = %s;" name (string_of_expr value)
  | Stmt_call c ->
      sprintf "%s;" (string_of_call c)
  | Stmt_return e ->
      sprintf "return %s;" (string_of_expr e)

type param_list = (string * int) list

let string_of_param_list params =
  (String.concat ~sep:"," (List.map ~f:(fun (name, width) -> sprintf "%s:%d" name width) params))

type proc = {
  proc_name : string;
  proc_params : param_list;
  proc_body : stmt list;
}

let string_of_proc proc =
  sprintf "proc %s(%s) {%s}" proc.proc_name
    (string_of_param_list proc.proc_params)
    (String.concat (List.map proc.proc_body ~f: string_of_stmt))

type decl =
  | Decl_proc of proc

let string_of_decl = function
  | Decl_proc proc -> string_of_proc proc

type ast = decl list

let string_of_ast ast =
  String.concat ~sep:" " (List.map ~f:string_of_decl ast)
