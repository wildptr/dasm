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
  | proc_def { Decl_proc $1 }
  | proc_templ { Decl_proc_templ $1 }
  | proc_inst { Decl_proc_inst $1 }

localdecl:
  | VAR; name = Ident; Colon; typ = typ; Semi
    { name, typ }

block:
  | LBrace; decls = list(localdecl); stmts = list(stmt); RBrace
    { decls, stmts }

name_type_pair:
  | name = Ident; Colon; typ = typ { name, typ }

proc_def:
  | PROC; ap_name = Ident;
    LParen; ap_params = separated_list(Comma, name_type_pair); RParen;
    ap_results = loption(preceded(Arrow, separated_nonempty_list(Comma, name_type_pair)));
    ap_body = block
    {{ ap_name; ap_params; ap_body; ap_results }}

primary_expr:
  | name = Ident
    { Expr_sym name }
  | Bitvec
    { Expr_literal $1 }
  | FALSE { Expr_literal_bool false }
  | TRUE { Expr_literal_bool true }
  | Hash; v = primary_cexpr; Colon; w = primary_cexpr
    { Expr_literal2 (v, w) }
  | LParen; e = expr; RParen { e }
  | func_name = Ident; LParen; args = separated_list(Comma, expr); RParen
    { Expr_apply (func_name, args) }
  | UNDEFINED; LParen; typ = typ; RParen
    { Expr_undef typ }
  | memloc
    { Expr_load $1 }
  | LParen; e = expr; Colon; w = primary_cexpr; RParen
    { Expr_extend (false, e, w) }
  | SIGN_EXTEND; LParen; e = expr; Comma; w = cexpr; RParen
    { Expr_extend (true, e, w) }
  | PC { Expr_pc }
  | EXTRACT; LParen; e = expr; Comma; lo = cexpr; Comma; hi = cexpr; RParen
    { Expr_extract (e, lo, hi) }

memloc:
  | LBrack; seg = primary_expr; Colon; off = primary_expr; RBrack; Colon;
    size = primary_cexpr
    { seg, off, size }

unary_op:
  | Tilde { Not }
  | Amp { Reduce_and }
  | Caret { Reduce_xor }
  | Bar { Reduce_or }
  | Minus { Neg }

prefix_expr:
  | primary_expr {$1}
  | op = unary_op; e = prefix_expr
    { Expr_unary (op, e) }

binary_expr:
  | prefix_expr {$1}
  | e1 = binary_expr; Dot; e2 = binary_expr
    { Expr_binary (Concat, e1, e2) }
  | e1 = binary_expr; Star; e2 = binary_expr
    { Expr_binary (Mul, e1, e2) }
  | e1 = binary_expr; Plus; e2 = binary_expr
    { Expr_binary (Add, e1, e2) }
  | e1 = binary_expr; Minus; e2 = binary_expr
    { Expr_binary (Sub, e1, e2) }
  | e1 = binary_expr; EqEq; e2 = binary_expr
    { Expr_binary (Spec_ast.Eq, e1, e2) }
  | e1 = binary_expr; BangEq; e2 = binary_expr
    { Expr_binary (Spec_ast.NotEq, e1, e2) }
  | e1 = binary_expr; Amp; e2 = binary_expr
    { Expr_binary (And, e1, e2) }
  | e1 = binary_expr; Caret; e2 = binary_expr
    { Expr_binary (Xor, e1, e2) }
  | e1 = binary_expr; Bar; e2 = binary_expr
    { Expr_binary (Or, e1, e2) }

expr: binary_expr {$1}

lhs:
  | Ident
    { Lhs_var $1 }
  | memloc
    { Lhs_mem $1 }

stmt:
  | lhs = lhs; Eq; value = expr; Semi
    { Stmt_set (lhs, value) }
  | proc_name = Ident; LParen; args = separated_list(Comma, expr); RParen; Semi
    { Stmt_call (proc_name, args) }
  | JUMP; addr = expr; Semi
    { Stmt_jump addr }

expr_top:
  | expr EOF {$1}

c_unop:
  | Tilde { CU_not }

primary_cexpr:
  | i = Int
    { C_int i }
  | s = Ident
    { C_sym s }
  | LParen; e = cexpr; RParen {e}

prefix_cexpr:
  | primary_cexpr {$1}
  | op = c_unop; e = prefix_cexpr
    { C_unary (op, e) }

binary_cexpr:
  | prefix_cexpr {$1}
  | e1 = binary_cexpr; Plus; e2 = binary_cexpr
    { C_binary (CB_add, e1, e2) }
  | e1 = binary_cexpr; Minus; e2 = binary_cexpr
    { C_binary (CB_sub, e1, e2) }
  | e1 = binary_cexpr; Star; e2 = binary_cexpr
    { C_binary (CB_mul, e1, e2) }
  | e1 = binary_cexpr; Slash; e2 = binary_cexpr
    { C_binary (CB_div, e1, e2) }
  | e1 = binary_cexpr; Amp; e2 = binary_cexpr
    { C_binary (CB_and, e1, e2) }
  | e1 = binary_cexpr; Caret; e2 = binary_cexpr
    { C_binary (CB_xor, e1, e2) }
  | e1 = binary_cexpr; Bar; e2 = binary_cexpr
    { C_binary (CB_or, e1, e2) }

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
