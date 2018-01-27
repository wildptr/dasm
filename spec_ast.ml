open Format

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

let rec pp_cexpr f = function
  | C_int i -> fprintf f "%d" i
  | C_sym s -> pp_print_string f s
  | C_binary (op, e1, e2) ->
    fprintf f "(%a%s%a)" pp_cexpr e1 (string_of_c_binop op) pp_cexpr e2
  | C_unary (op, e) ->
    fprintf f "(%s%a)" (string_of_c_unop op) pp_cexpr e

(* ---- *)

type index =
  | Index_bit of cexpr
  | Index_part of cexpr * cexpr

let pp_index f = function
  | Index_bit i -> fprintf f "[%a]" pp_cexpr i
  | Index_part (hi, lo) -> fprintf f "[%a:%a]" pp_cexpr hi pp_cexpr lo

type unary_op =
  | Not
  | Reduce_and
  | Reduce_xor
  | Reduce_or

let string_of_unary_op = function
  | Not -> "~"
  | Reduce_and -> "&"
  | Reduce_xor -> "^"
  | Reduce_or -> "|"

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
  | Expr_load of cexpr * astexpr

type astloc =
  | Loc_var of string
  (*| Loc_part of string * cexpr * cexpr*)
  | Loc_newvar of string

type aststmt =
  (* Variables created by let statements are immutable. *)
  | Stmt_set of astloc * astexpr
  | Stmt_call of string * astexpr list * astloc option
  | Stmt_output of astexpr
  (*| Stmt_load of cexpr * astexpr * string*)
  | Stmt_store of cexpr * astexpr * astexpr
  | Stmt_jump of astexpr

let pp_comma_separated_list pp f = function
  | [] -> ()
  | hd::tl -> pp f hd; pp_print_string f ","; List.iter (pp f) tl

let pp_list pp f = List.iter (pp f)

let rec pp_astexpr f = function
  | Expr_sym s -> pp_print_string f s
  | Expr_literal bv -> fprintf f "'%a'" Bitvec.pp bv
  | Expr_literal2 (v, w) -> fprintf f "{%a:%a}" pp_cexpr v pp_cexpr w
  | Expr_index (e, i) -> fprintf f "%a%a" pp_astexpr e pp_index i
  | Expr_unary (op, e) ->
    fprintf f "(%s%a)" (string_of_unary_op op) pp_astexpr e
  | Expr_binary (op, e1, e2) ->
    fprintf f "(%a%s%a)" pp_astexpr e1 (string_of_binary_op op) pp_astexpr e2
  | Expr_apply (func_name, args) ->
    fprintf f "%s(%a)" func_name (pp_comma_separated_list pp_astexpr) args;
  | Expr_undef width -> fprintf f "undefined(%a)" pp_cexpr width
  | Expr_repeat (data, n) ->
    fprintf f "repeat(%a, %a)" pp_astexpr data pp_cexpr n
  | Expr_load (size, addr) ->
    fprintf f "load(%a, %a)" pp_cexpr size pp_astexpr addr

let pp_astloc f = function
  | Loc_var name -> pp_print_string f name
  (*| Loc_part (name, hi, lo) ->
    fprintf f "%s[%a:%a]" name pp_cexpr hi pp_cexpr lo*)
  | Loc_newvar name -> fprintf f "let %s" name

let pp_aststmt f = function
  | Stmt_set (loc, value) ->
    fprintf f "%a = %a;" pp_astloc loc pp_astexpr value
  | Stmt_call (proc_name, args, result_loc_opt) ->
    begin match result_loc_opt with
      | None -> ()
      | Some loc -> fprintf f "%a = " pp_astloc loc
    end;
    fprintf f "call %s(%a);"
      proc_name (pp_comma_separated_list pp_astexpr) args;
  | Stmt_output e ->
    fprintf f "output %a;" pp_astexpr e
  (*| Stmt_load (size, addr, name) ->
    fprintf f "%s = load %a, %a;" name pp_cexpr size pp_astexpr addr*)
  | Stmt_store (size, addr, data) ->
    fprintf f "store %a, %a, %a;"
      pp_cexpr size pp_astexpr addr pp_astexpr data
  | Stmt_jump addr ->
    fprintf f "jump %a;" pp_astexpr addr

type param_list = (string * cexpr) list

let pp_param f (name, width) = fprintf f "%s:%a" name pp_cexpr width

type astproc = {
  ap_name : string;
  ap_params : param_list;
  ap_body : aststmt list;
  ap_result_width : cexpr;
}

let pp_astproc f astproc =
  fprintf f "proc %s(%a):%a {%a}"
    astproc.ap_name
    (pp_comma_separated_list pp_param) astproc.ap_params
    pp_cexpr astproc.ap_result_width
    (pp_list pp_aststmt) astproc.ap_body

type templ_arg =
  | TA_int of int
  | TA_bitvec of Bitvec.t
  | TA_prim of string
  | TA_var of string

type proc_templ = {
  pt_name : string;
  pt_templ_params : string list;
  pt_proc_params : param_list;
  pt_body : aststmt list;
  pt_result_width : cexpr;
}

let pp_proc_templ f pt =
  fprintf f "template proc %s<%a>(%a):%a {%a}"
    pt.pt_name
    (pp_comma_separated_list pp_print_string) pt.pt_templ_params
    (pp_comma_separated_list pp_param) pt.pt_proc_params
    pp_cexpr pt.pt_result_width
    (pp_list pp_aststmt) pt.pt_body

type proc_inst = {
  pi_inst_name : string;
  pi_templ_name : string;
  pi_templ_args : templ_arg list;
}

let pp_templ_arg f = function
  | TA_int i -> pp_print_int f i
  | TA_bitvec bv -> Bitvec.pp f bv
  | TA_prim s -> pp_print_string f s
  | TA_var s -> pp_print_string f s

let pp_proc_inst f pi =
  fprintf f "proc %s = %s<%a>;"
    pi.pi_inst_name
    pi.pi_templ_name
    (pp_comma_separated_list pp_templ_arg) pi.pi_templ_args

type decl =
  | Decl_proc of astproc
  | Decl_proc_templ of proc_templ
  | Decl_proc_inst of proc_inst

let pp_decl f = function
  | Decl_proc proc -> pp_astproc f proc
  | Decl_proc_templ templ -> pp_proc_templ f templ
  | Decl_proc_inst inst -> pp_proc_inst f inst

type ast = decl list

let pp_ast = pp_list pp_decl
