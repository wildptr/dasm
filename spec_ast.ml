open Format

(* constant expressions *)

type c_binop =
  | C_add | C_sub | C_mul | C_div | C_and | C_or | C_xor

let string_of_c_binop = function
  | C_add -> "+"
  | C_sub -> "-"
  | C_mul -> "*"
  | C_div -> "/"
  | C_and -> "&"
  | C_or  -> "|"
  | C_xor -> "^"

type c_unop =
  | C_not

let string_of_c_unop = function
  | C_not -> "~"

type cexpr =
  | CE_int of int
  | CE_sym of string
  | CE_binary of c_binop * cexpr * cexpr
  | CE_unary of c_unop * cexpr

let rec pp_cexpr f = function
  | CE_int i -> fprintf f "%d" i
  | CE_sym s -> pp_print_string f s
  | CE_binary (op, e1, e2) ->
    fprintf f "(%a%s%a)" pp_cexpr e1 (string_of_c_binop op) pp_cexpr e2
  | CE_unary (op, e) ->
    fprintf f "(%s%a)" (string_of_c_unop op) pp_cexpr e

type texpr =
  | Typ_bool
  | Typ_bitvec of cexpr

let pp_texpr f = function
  | Typ_bool -> pp_print_string f "bool"
  | Typ_bitvec c -> pp_cexpr f c

(* ---- *)

type unary_op =
  | Not
  | Neg
  | Reduce_and
  | Reduce_or

let string_of_unary_op = function
  | Not -> "~"
  | Neg -> "-"
  | Reduce_and -> "&"
  | Reduce_or -> "|"

type binary_op =
  | Concat
  | Mul
  | Add | Sub
  | Eq | NotEq
  | And
  | Xor
  | Or

let string_of_binary_op = function
  | Concat -> "."
  | Mul -> "*"
  | Add -> "+"
  | Sub -> "-"
  | Eq -> "=="
  | NotEq -> "!="
  | And -> "&"
  | Xor -> "^"
  | Or -> "|"

type astexpr =
  | SE_sym of string
  | SE_literal of Bitvec.t
  | SE_literal2 of cexpr * cexpr (* value, width *)
  | SE_literal_bool of bool
  | SE_unary of unary_op * astexpr
  | SE_binary of binary_op * astexpr * astexpr
  | SE_apply of string * astexpr list
  | SE_undef of texpr
  | SE_load of memloc
  | SE_extend of bool * astexpr * cexpr
  | SE_pc
  | SE_extract of astexpr * cexpr * cexpr

and memloc = astexpr * astexpr * cexpr (* seg, offset, size *)

type lhs =
  | Loc_Var of string
  | Loc_Mem of memloc

type aststmt =
  | SS_set of lhs * astexpr
  | SS_jump of astexpr
  | SS_call of string * astexpr list

let pp_comma_separated_list pp f = function
  | [] -> ()
  | hd::tl -> pp f hd; List.iter (fun x -> pp_print_string f ","; pp f x) tl

let pp_list pp f = List.iter (pp f)

let rec pp_astexpr f = function
  | SE_sym s -> pp_print_string f s
  | SE_literal bv -> fprintf f "'%a'" Bitvec.pp bv
  | SE_literal2 (v, w) -> fprintf f "#%a:%a" pp_cexpr v pp_cexpr w
  | SE_literal_bool b -> pp_print_bool f b;
  | SE_unary (op, e) ->
    fprintf f "(%s%a)" (string_of_unary_op op) pp_astexpr e
  | SE_binary (op, e1, e2) ->
    fprintf f "(%a%s%a)" pp_astexpr e1 (string_of_binary_op op) pp_astexpr e2
  | SE_apply (func_name, args) ->
    fprintf f "%s(%a)" func_name (pp_comma_separated_list pp_astexpr) args;
  | SE_undef texpr -> fprintf f "undefined(%a)" pp_texpr texpr
  | SE_load memloc -> pp_memloc f memloc
  | SE_extend (sign, data, n) -> () (* TODO *)
  | SE_pc -> pp_print_string f "pc"
  | SE_extract (e, lo, hi) ->
    fprintf f "extract(%a, %a, %a)" pp_astexpr e pp_cexpr lo pp_cexpr hi

and pp_memloc f (seg, off, size) =
  fprintf f "[%a:%a]:%a" pp_astexpr seg pp_astexpr off pp_cexpr size

let pp_lhs f = function
  | Loc_Var name -> pp_print_string f name
  | Loc_Mem memloc -> pp_memloc f memloc

let pp_aststmt f = function
  | SS_set (lhs, value) ->
    fprintf f "%a = %a;" pp_lhs lhs pp_astexpr value
  | SS_call (proc_name, args) ->
    fprintf f "%s(%a);"
      proc_name (pp_comma_separated_list pp_astexpr) args;
  | SS_jump addr ->
    fprintf f "jump %a;" pp_astexpr addr

type param_list = (string * texpr) list

let pp_param f (name, texpr) = fprintf f "%s:%a" name pp_texpr texpr

type vardecl = string * texpr
type astblock = vardecl list * aststmt list

type astproc = {
  p_name : string;
  p_params : param_list;
  p_body : astblock;
  p_results : (string * texpr) list;
}

let pp_astblock f (decls, stmts) =
  () (* TODO *)

let pp_astproc f astproc =
  fprintf f "proc %s(%a) -> ... {%a}" (* TODO: see the ellipsis *)
    astproc.p_name
    (pp_comma_separated_list pp_param) astproc.p_params
    pp_astblock astproc.p_body

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
  pt_results : (string * texpr) list;
}

let pp_proc_templ f pt =
  fprintf f "template proc %s<%a>(%a) -> ... {%a}" (* TODO *)
    pt.pt_name
    (pp_comma_separated_list pp_print_string) pt.pt_templ_params
    (pp_comma_separated_list pp_param) pt.pt_proc_params
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
  | D_Proc of astproc
  | D_Proc_Templ of proc_templ
  | D_Proc_Inst of proc_inst

let pp_decl f = function
  | D_Proc proc -> pp_astproc f proc
  | D_Proc_Templ templ -> pp_proc_templ f templ
  | D_Proc_Inst inst -> pp_proc_inst f inst

type ast = decl list

let pp_ast = pp_list pp_decl
