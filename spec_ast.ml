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

type unary_op =
  | Not
  | Neg
  | Reduce_and
  | Reduce_xor
  | Reduce_or

let string_of_unary_op = function
  | Not -> "~"
  | Neg -> "-"
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
  | Expr_unary of unary_op * astexpr
  | Expr_binary of binary_op * astexpr * astexpr
  | Expr_apply of string * astexpr list
  | Expr_undef of cexpr
  | Expr_load of memloc
  | Expr_extend of bool * astexpr * cexpr
  | Expr_pc

and memloc = astexpr * astexpr * cexpr (* seg, offset, size *)

type lhs =
  | Lhs_var of string
  (*| Loc_part of string * cexpr * cexpr*)
  | Lhs_mem of memloc

type aststmt =
  (* Variables created by let statements are immutable. *)
  | Stmt_set of lhs * astexpr
  | Stmt_return of astexpr
  (*| Stmt_load of cexpr * astexpr * string*)
  | Stmt_jump of astexpr
  | Stmt_call of string * astexpr list

let pp_comma_separated_list pp f = function
  | [] -> ()
  | hd::tl -> pp f hd; pp_print_string f ","; List.iter (pp f) tl

let pp_list pp f = List.iter (pp f)

let rec pp_astexpr f = function
  | Expr_sym s -> pp_print_string f s
  | Expr_literal bv -> fprintf f "'%a'" Bitvec.pp bv
  | Expr_literal2 (v, w) -> fprintf f "{%a:%a}" pp_cexpr v pp_cexpr w
  | Expr_unary (op, e) ->
    fprintf f "(%s%a)" (string_of_unary_op op) pp_astexpr e
  | Expr_binary (op, e1, e2) ->
    fprintf f "(%a%s%a)" pp_astexpr e1 (string_of_binary_op op) pp_astexpr e2
  | Expr_apply (func_name, args) ->
    fprintf f "%s(%a)" func_name (pp_comma_separated_list pp_astexpr) args;
  | Expr_undef width -> fprintf f "undefined(%a)" pp_cexpr width
  | Expr_load memloc -> pp_memloc f memloc
  | Expr_extend (sign, data, n) -> () (* TODO *)
  | Expr_pc -> pp_print_string f "pc"

and pp_memloc f (seg, off, size) =
  fprintf f "[%a:%a]:%a" pp_astexpr seg pp_astexpr off pp_cexpr size

let pp_lhs f = function
  | Lhs_var name -> pp_print_string f name
  (*| Loc_part (name, hi, lo) ->
    fprintf f "%s[%a:%a]" name pp_cexpr hi pp_cexpr lo*)
  | Lhs_mem memloc -> pp_memloc f memloc

let pp_aststmt f = function
  | Stmt_set (lhs, value) ->
    fprintf f "%a = %a;" pp_lhs lhs pp_astexpr value
  | Stmt_call (proc_name, args) ->
    fprintf f "%s(%a);"
      proc_name (pp_comma_separated_list pp_astexpr) args;
  | Stmt_return e ->
    fprintf f "return %a;" pp_astexpr e
  (*| Stmt_load (size, addr, name) ->
    fprintf f "%s = load %a, %a;" name pp_cexpr size pp_astexpr addr*)
  | Stmt_jump addr ->
    fprintf f "jump %a;" pp_astexpr addr

type param_list = (string * cexpr) list

let pp_param f (name, width) = fprintf f "%s:%a" name pp_cexpr width

type vardecl = string * cexpr
type astblock = vardecl list * aststmt list

type astproc = {
  ap_name : string;
  ap_params : param_list;
  ap_body : astblock;
  ap_result_width : cexpr;
}

let pp_astblock f (decls, stmts) =
  () (* TODO *)

let pp_astproc f astproc =
  fprintf f "proc %s(%a):%a {%a}"
    astproc.ap_name
    (pp_comma_separated_list pp_param) astproc.ap_params
    pp_cexpr astproc.ap_result_width
    pp_astblock astproc.ap_body

type templ_arg =
  | TA_int of int
  | TA_bitvec of Bitvec.t
  | TA_prim of string
  | TA_var of string

type proc_templ = {
  pt_name : string;
  pt_templ_params : string list;
  pt_proc_params : param_list;
  pt_body : astblock;
  pt_result_width : cexpr;
}

let pp_proc_templ f pt =
  fprintf f "template proc %s<%a>(%a):%a {%a}"
    pt.pt_name
    (pp_comma_separated_list pp_print_string) pt.pt_templ_params
    (pp_comma_separated_list pp_param) pt.pt_proc_params
    pp_cexpr pt.pt_result_width
    pp_astblock pt.pt_body

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
