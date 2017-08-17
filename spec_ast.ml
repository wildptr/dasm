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

type astexpr =
  | Expr_sym of string
  | Expr_literal of Bitvec.t
  | Expr_index of astexpr * index
  | Expr_unary of unary_op * astexpr
  | Expr_binary of binary_op * astexpr * astexpr
  | Expr_apply of string * astexpr list

type aststmt =
  (* Variables created by let statements are immutable. *)
  | Stmt_set of string * astexpr
  | Stmt_call of string * astexpr list * string option
  | Stmt_return of astexpr

let rec string_of_astexpr = function
  | Expr_sym s -> s
  | Expr_literal bv -> sprintf "'%s'" (Bitvec.to_string bv)
  | Expr_index (e, i) -> (string_of_astexpr e) ^ (string_of_index i)
  | Expr_unary (op, e) ->
      sprintf "(%s%s)" (string_of_unary_op op) (string_of_astexpr e)
  | Expr_binary (op, e1, e2) ->
      sprintf "(%s%s%s)" (string_of_astexpr e1) (string_of_binary_op op) (string_of_astexpr e2)
  | Expr_apply (func_name, args) ->
      sprintf "%s(%s)" func_name
        (String.concat ~sep:"," (List.map ~f:string_of_astexpr args))

let string_of_aststmt = function
  | Stmt_set (name, value) ->
      sprintf "%s = %s;" name (string_of_astexpr value)
  | Stmt_call (proc_name, args, result_name_opt) ->
      sprintf "%scall %s(%s);"
        (match result_name_opt with None -> "" | Some s -> sprintf "%s = " s)
        proc_name
        (String.concat ~sep:"," (List.map ~f:string_of_astexpr args))
  | Stmt_return e ->
      sprintf "return %s;" (string_of_astexpr e)

type param_list = (string * int) list

let string_of_param_list params =
  (String.concat ~sep:"," (List.map ~f:(fun (name, width) -> sprintf "%s:%d" name width) params))

type astproc = {
  ap_name : string;
  ap_params : param_list;
  ap_body : aststmt list;
  ap_result_width : int;
}

let string_of_proc astproc =
  sprintf "proc %s(%s):%d {%s}" astproc.ap_name
    (string_of_param_list astproc.ap_params)
    astproc.ap_result_width
    (String.concat (List.map astproc.ap_body ~f: string_of_aststmt))

type decl =
  | Decl_proc of astproc

let string_of_decl = function
  | Decl_proc proc -> string_of_proc proc

type ast = decl list

let string_of_ast ast =
  String.concat ~sep:" " (List.map ~f:string_of_decl ast)
