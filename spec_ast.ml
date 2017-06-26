open Core
open Printf

type bitvec = bool list

let string_of_bitvec bv =
  "'" ^ String.of_char_list (List.map ~f:(fun b -> if b then '1' else '0') bv) ^ "'"

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
  | Expr_literal of bitvec
  | Expr_index of expr * index
  | Expr_call of string * expr list
  | Expr_unary of unary_op * expr
  | Expr_binary of binary_op * expr * expr

let rec string_of_expr = function
  | Expr_sym s -> s
  | Expr_literal bv -> string_of_bitvec bv
  | Expr_index (e, i) -> (string_of_expr e) ^ (string_of_index i)
  | Expr_call (proc_name, args) ->
      sprintf "%s(%s)" proc_name (String.concat ~sep:"," (List.map ~f:string_of_expr args))
  | Expr_unary (op, e) ->
      sprintf "(%s%s)" (string_of_unary_op op) (string_of_expr e)
  | Expr_binary (op, e1, e2) ->
      sprintf "(%s%s%s)" (string_of_expr e1) (string_of_binary_op op) (string_of_expr e2)

type stmt =
  | Stmt_let of string * expr
  | Stmt_set of string * expr
  | Stmt_return of expr
  | Stmt_comp of stmt list

let rec string_of_stmt = function
  | Stmt_let (lhs, rhs) -> sprintf "let %s=%s;" lhs (string_of_expr rhs)
  | Stmt_set (lhs, rhs) -> sprintf "%s=%s;" lhs (string_of_expr rhs)
  | Stmt_return e -> sprintf "return %s;" (string_of_expr e)
  | Stmt_comp stmts -> sprintf "{%s}" (String.concat (List.map ~f:string_of_stmt stmts))

type proc = {
  proc_name : string;
  proc_params : (string * int) list;
  proc_width_opt : int option;
  proc_body : stmt;
}

let string_of_proc proc =
  sprintf "proc %s(%s)%s%s" proc.proc_name
    (String.concat ~sep:"," (List.map ~f:(fun (name, width) -> sprintf "%s:%d" name width) proc.proc_params))
    begin
      match proc.proc_width_opt with
      | Some width -> ":" ^ string_of_int width
      | None -> ""
    end
    (string_of_stmt proc.proc_body)

type ast = proc list

let string_of_ast ast =
  String.concat (List.map ~f:string_of_proc ast)
