open Core
open Format
open Printf

(* constant expressions *)

type c_binop =
  | CB_add | CB_sub | CB_mul | CB_div | CB_and | CB_or | CB_xor

let string_of_c_binop = function
  | CB_add -> "+"
  | CB_sub -> "-"
  | CB_mul -> "*"
  | CB_div -> "/"
  | CB_and -> "&"
  | CB_or  -> "|"
  | CB_xor -> "^"

type c_unop =
  | CU_not

let string_of_c_unop = function
  | CU_not -> "~"

type cexpr =
  | C_int of int
  | C_sym of string
  | C_binary of c_binop * cexpr * cexpr
  | C_unary of c_unop * cexpr

let rec string_of_cexpr = function
  | C_int i -> sprintf "%d" i
  | C_sym s -> s
  | C_binary (op, e1, e2) ->
      sprintf "(%s%s%s)"
        (string_of_cexpr e1) (string_of_c_binop op) (string_of_cexpr e2)
  | C_unary (op, e) ->
      sprintf "(%s%s)" (string_of_c_unop op) (string_of_cexpr e)

(* ---- *)

type index =
  | Index_bit of cexpr
  | Index_part of cexpr * cexpr

let string_of_index = function
  | Index_bit i -> sprintf "[%s]" (string_of_cexpr i)
  | Index_part (hi, lo) ->
      sprintf "[%s:%s]" (string_of_cexpr hi) (string_of_cexpr lo)

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
  | Expr_literal2 of cexpr * cexpr (* value, width *)
  | Expr_index of astexpr * index
  | Expr_unary of unary_op * astexpr
  | Expr_binary of binary_op * astexpr * astexpr
  | Expr_apply of string * astexpr list
  | Expr_undef of cexpr
  | Expr_repeat of astexpr * cexpr

type aststmt =
  (* Variables created by let statements are immutable. *)
  | Stmt_set of string * astexpr
  | Stmt_call of string * astexpr list * string option
  | Stmt_return of astexpr
  | Stmt_load of cexpr * astexpr * string
  | Stmt_store of cexpr * astexpr * astexpr
  | Stmt_jump of astexpr

let rec string_of_astexpr = function
  | Expr_sym s -> s
  | Expr_literal bv -> sprintf "'%s'" (Bitvec.to_string bv)
  | Expr_literal2 (v, w) -> sprintf "{%s:%s}" (string_of_cexpr v) (string_of_cexpr w)
  | Expr_index (e, i) -> (string_of_astexpr e) ^ (string_of_index i)
  | Expr_unary (op, e) ->
      sprintf "(%s%s)" (string_of_unary_op op) (string_of_astexpr e)
  | Expr_binary (op, e1, e2) ->
      sprintf "(%s%s%s)" (string_of_astexpr e1) (string_of_binary_op op) (string_of_astexpr e2)
  | Expr_apply (func_name, args) ->
      sprintf "%s(%s)" func_name
        (String.concat ~sep:"," (List.map ~f:string_of_astexpr args))
  | Expr_undef width ->
      sprintf "undefined(%s)" (string_of_cexpr width)
  | Expr_repeat (data, n) ->
      sprintf "repeat(%s, %s)" (string_of_astexpr data) (string_of_cexpr n)

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
  | Stmt_load (size, addr, name) ->
      sprintf "%s = load %s, %s;" name
        (string_of_cexpr size) (string_of_astexpr addr)
  | Stmt_store (size, addr, data) ->
      sprintf "store %s, %s, %s;" (string_of_cexpr size)
        (string_of_astexpr addr) (string_of_astexpr data)
  | Stmt_jump addr ->
      sprintf "jump %s;" (string_of_astexpr addr)

type param_list = (string * cexpr) list

let string_of_param_list params =
  (String.concat ~sep:"," (List.map ~f:(fun (name, width) ->
    sprintf "%s:%s" name (string_of_cexpr width)) params))

type astproc = {
  ap_name : string;
  ap_params : param_list;
  ap_body : aststmt list;
  ap_result_width : cexpr;
}

let string_of_astproc astproc =
  sprintf "proc %s(%s):%s {%s}" astproc.ap_name
    (string_of_param_list astproc.ap_params)
    (string_of_cexpr astproc.ap_result_width)
    (String.concat (List.map astproc.ap_body ~f: string_of_aststmt))

type templ_arg =
  | TA_int of int
  | TA_bitvec of Bitvec.t
  | TA_prim of string

type proc_templ = {
  pt_name : string;
  pt_templ_params : string list;
  pt_proc_params : param_list;
  pt_body : aststmt list;
  pt_result_width : cexpr;
}

let string_of_proc_templ pt =
  sprintf "template proc %s<%s>(%s):%s {%s}" pt.pt_name
    (String.concat ~sep:"," pt.pt_templ_params)
    (string_of_param_list pt.pt_proc_params)
    (string_of_cexpr pt.pt_result_width)
    (String.concat (List.map pt.pt_body ~f:string_of_aststmt))

type proc_inst = {
  pi_inst_name : string;
  pi_templ_name : string;
  pi_templ_args : templ_arg list;
}

let string_of_templ_arg = function
  | TA_int i -> string_of_int i
  | TA_bitvec bv -> Bitvec.to_string bv
  | TA_prim s -> s

let string_of_proc_inst pi =
  let args_s =
    String.concat ~sep:"," (List.map pi.pi_templ_args ~f:string_of_templ_arg)
  in
  sprintf "proc %s = %s<%s>;" pi.pi_inst_name
    pi.pi_templ_name args_s

type decl =
  | Decl_proc of astproc
  | Decl_proc_templ of proc_templ
  | Decl_proc_inst of proc_inst

let string_of_decl = function
  | Decl_proc proc -> string_of_astproc proc
  | Decl_proc_templ templ -> string_of_proc_templ templ
  | Decl_proc_inst inst -> string_of_proc_inst inst

type ast = decl list

let string_of_ast ast =
  String.concat ~sep:" " (List.map ~f:string_of_decl ast)
