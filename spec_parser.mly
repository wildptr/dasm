%{
open Spec_ast
%}

%token EOF
%token <string> Ident
%token <int> Int
%token <Bitvec.t> Bitvec
%token Arrow
%token EqEq
%token BangEq
(*%token Dollar*)
%token Hash
%token Amp
%token LParen
%token RParen
%token Star
%token Plus
%token Comma
%token Minus
%token Dot
%token Slash
%token Colon
%token Semi
%token LAngle
%token Eq
%token RAngle
(*%token At*)
%token LBrack
%token RBrack
%token Caret
%token LBrace
%token Bar
%token RBrace
%token Tilde

%token BOOL
%token EXTRACT
%token FALSE
%token JUMP
%token PC
%token PROC
%token SIGN_EXTEND
%token TEMPLATE
%token TRUE
%token UNDEFINED
%token VAR

%left Bar
%left Caret
%left Amp
%left EqEq BangEq
%left Star Slash
%left Plus Minus
%left Dot

%start <Spec_ast.ast> top
%start <Spec_ast.astexpr> expr_top

%%

top:
  | decl*; EOF { $1 }

decl:
  | proc_def    { D_Proc $1 }
  | proc_templ  { D_Proc_Templ $1 }
  | proc_inst   { D_Proc_Inst $1 }

localdecl:
  | VAR; name = Ident; Colon; typ = typ; Semi
    { name, typ }

block:
  | LBrace; decls = list(localdecl); stmts = list(stmt); RBrace
    { decls, stmts }

name_type_pair:
  | name = Ident; Colon; typ = typ { name, typ }

proc_def:
  | PROC; p_name = Ident;
    LParen; p_params = separated_list(Comma, name_type_pair); RParen;
    p_results = loption(preceded(Arrow, separated_nonempty_list(Comma, name_type_pair)));
    p_body = block
    {{ p_name; p_params; p_body; p_results }}

primary_expr:
  | name = Ident
    { SE_sym name }
  | Bitvec
    { SE_literal $1 }
  | FALSE { SE_literal_bool false }
  | TRUE { SE_literal_bool true }
  | Hash; v = primary_cexpr; Colon; w = primary_cexpr
    { SE_literal2 (v, w) }
  | LParen; e = expr; RParen { e }
  | func_name = Ident; LParen; args = separated_list(Comma, expr); RParen
    { SE_apply (func_name, args) }
  | UNDEFINED; LParen; typ = typ; RParen
    { SE_undef typ }
  | memloc
    { SE_load $1 }
  | LParen; e = expr; Colon; w = primary_cexpr; RParen
    { SE_extend (false, e, w) }
  | SIGN_EXTEND; LParen; e = expr; Comma; w = cexpr; RParen
    { SE_extend (true, e, w) }
  | PC { SE_pc }
  | EXTRACT; LParen; e = expr; Comma; lo = cexpr; Comma; hi = cexpr; RParen
    { SE_extract (e, lo, hi) }

memloc:
  | LBrack; seg = primary_expr; Colon; off = primary_expr; RBrack; Colon;
    size = primary_cexpr
    { seg, off, size }

unary_op:
  | Tilde { Not }
  | Amp { Reduce_and }
  | Bar { Reduce_or }
  | Minus { Neg }

prefix_expr:
  | primary_expr {$1}
  | op = unary_op; e = prefix_expr
    { SE_unary (op, e) }

binary_expr:
  | prefix_expr {$1}
  | e1 = binary_expr; Dot; e2 = binary_expr
    { SE_binary (Concat, e1, e2) }
  | e1 = binary_expr; Star; e2 = binary_expr
    { SE_binary (Mul, e1, e2) }
  | e1 = binary_expr; Plus; e2 = binary_expr
    { SE_binary (Add, e1, e2) }
  | e1 = binary_expr; Minus; e2 = binary_expr
    { SE_binary (Sub, e1, e2) }
  | e1 = binary_expr; EqEq; e2 = binary_expr
    { SE_binary (Spec_ast.Eq, e1, e2) }
  | e1 = binary_expr; BangEq; e2 = binary_expr
    { SE_binary (Spec_ast.NotEq, e1, e2) }
  | e1 = binary_expr; Amp; e2 = binary_expr
    { SE_binary (And, e1, e2) }
  | e1 = binary_expr; Caret; e2 = binary_expr
    { SE_binary (Xor, e1, e2) }
  | e1 = binary_expr; Bar; e2 = binary_expr
    { SE_binary (Or, e1, e2) }

expr: binary_expr {$1}

lhs:
  | Ident
    { Loc_Var $1 }
  | memloc
    { Loc_Mem $1 }

stmt:
  | lhs = lhs; Eq; value = expr; Semi
    { SS_set (lhs, value) }
  | proc_name = Ident; LParen; args = separated_list(Comma, expr); RParen; Semi
    { SS_call (proc_name, args) }
  | JUMP; addr = expr; Semi
    { SS_jump addr }

expr_top:
  | expr EOF {$1}

c_unop:
  | Tilde { C_not }

primary_cexpr:
  | i = Int
    { CE_int i }
  | s = Ident
    { CE_sym s }
  | LParen; e = cexpr; RParen {e}

prefix_cexpr:
  | primary_cexpr {$1}
  | op = c_unop; e = prefix_cexpr
    { CE_unary (op, e) }

binary_cexpr:
  | prefix_cexpr {$1}
  | e1 = binary_cexpr; Plus; e2 = binary_cexpr
    { CE_binary (C_add, e1, e2) }
  | e1 = binary_cexpr; Minus; e2 = binary_cexpr
    { CE_binary (C_sub, e1, e2) }
  | e1 = binary_cexpr; Star; e2 = binary_cexpr
    { CE_binary (C_mul, e1, e2) }
  | e1 = binary_cexpr; Slash; e2 = binary_cexpr
    { CE_binary (C_div, e1, e2) }
  | e1 = binary_cexpr; Amp; e2 = binary_cexpr
    { CE_binary (C_and, e1, e2) }
  | e1 = binary_cexpr; Caret; e2 = binary_cexpr
    { CE_binary (C_xor, e1, e2) }
  | e1 = binary_cexpr; Bar; e2 = binary_cexpr
    { CE_binary (C_or, e1, e2) }

cexpr: binary_cexpr {$1}

typ:
  | cexpr { Typ_bitvec $1 }
  | BOOL { Typ_bool }

proc_templ:
  | TEMPLATE; PROC; pt_name = Ident;
    LAngle; pt_templ_params = separated_list(Comma, Ident); RAngle;
    LParen; pt_proc_params = separated_list(Comma, name_type_pair); RParen;
    pt_results = loption(preceded(Arrow, separated_nonempty_list(Comma, name_type_pair)));
    pt_body = block
    {{ pt_name; pt_templ_params; pt_proc_params; pt_body; pt_results }}

proc_inst:
  | PROC; pi_inst_name = Ident; Eq; pi_templ_name = Ident;
    LAngle; pi_templ_args = separated_nonempty_list(Comma, templ_arg); RAngle; Semi
    {{ pi_inst_name; pi_templ_name; pi_templ_args }}

templ_arg:
  | Int { TA_int $1 }
  | Bitvec { TA_bitvec $1 }
  | s = Ident { match s.[0] with 'A'..'Z' -> TA_var s | _ -> TA_prim s }
