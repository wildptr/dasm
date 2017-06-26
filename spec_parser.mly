%{
open Spec_ast
%}

%token EOF
%token <string> Ident
%token <int> Int
%token <Bitvec.t> Bitvec
%token EqEq
%token Amp
%token LParen
%token RParen
%token Plus
%token Comma
%token Minus
%token Dot
%token Colon
%token Semi
%token Eq
%token LBrack
%token RBrack
%token Caret
%token LBrace
%token Bar
%token RBrace
%token Tilde

%token K_func
%token K_in
%token K_let
%token K_proc
%token K_return

%left Bar
%left Caret
%left Amp
%left EqEq
%left Plus Minus
%left Dot

%type <proc> proc_def
%start <Spec_ast.ast> top
%start <Spec_ast.expr> expr_top

%%

top:
  | decls = list(decl); EOF { decls }

decl:
  | func_def { Decl_func $1 }
  | proc_def { Decl_proc $1 }

func_def:
  | K_func; func_name = Ident;
    LParen; func_params = separated_nonempty_list(Comma, name_length_pair); RParen;
    Eq; func_body = expr
    {{ func_name; func_params; func_body }}

proc_def:
  | K_proc; proc_name = Ident;
    LParen; proc_params = separated_nonempty_list(Comma, name_length_pair); RParen;
    proc_width_opt = option(preceded(Colon, Int)); proc_body = comp_stmt
    {{ proc_name; proc_params; proc_width_opt; proc_body }}

name_length_pair:
  | name = Ident; Colon; len = Int { name, len }

comp_stmt:
  | LBrace; stmts = list(stmt); RBrace { Stmt_comp stmts }

stmt:
  | K_let; lhs = Ident; Eq; rhs = expr; Semi
    { Stmt_let (lhs, rhs) }
  | lhs = Ident; Eq; rhs = expr; Semi
    { Stmt_set (lhs, rhs) }
  | K_return; e = expr; Semi
    { Stmt_return e }
  | comp_stmt {$1}

primary_expr:
  | name = Ident
    { Expr_sym name }
  | bv = Bitvec
    { Expr_literal bv }
  | LParen; e = expr; RParen { e }
  | func_name = Ident; LParen; args = separated_list(Comma, expr); RParen
    { Expr_apply (func_name, args) }

index:
  | LBrack; i = Int; RBrack
    { Index_bit i }
  | LBrack; hi = Int; Colon; lo = Int; RBrack
    { Index_part (hi, lo) }

postfix_expr:
  | primary_expr {$1}
  | e = postfix_expr; i = index
    { Expr_index (e, i) }

unary_op:
  | Tilde { Not }

prefix_expr:
  | postfix_expr {$1}
  | op = unary_op; e = prefix_expr
    { Expr_unary (op, e) }

binary_expr:
  | prefix_expr {$1}
  | e1 = binary_expr; Dot; e2 = binary_expr
    { Expr_binary (Concat, e1, e2) }
  | e1 = binary_expr; Plus; e2 = binary_expr
    { Expr_binary (Add, e1, e2) }
  | e1 = binary_expr; Minus; e2 = binary_expr
    { Expr_binary (Sub, e1, e2) }
  | e1 = binary_expr; EqEq; e2 = binary_expr
    { Expr_binary (Spec_ast.Eq, e1, e2) }
  | e1 = binary_expr; Amp; e2 = binary_expr
    { Expr_binary (And, e1, e2) }
  | e1 = binary_expr; Caret; e2 = binary_expr
    { Expr_binary (Xor, e1, e2) }
  | e1 = binary_expr; Bar; e2 = binary_expr
    { Expr_binary (Or, e1, e2) }

let_expr:
  | binary_expr {$1}
  | K_let; name = Ident; Eq; value = expr; K_in; body = expr
    { Expr_let (name, value, body) }

expr:
  | let_expr {$1}

expr_top:
  | expr EOF {$1}
