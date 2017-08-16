%{
open Core_kernel.Std
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

%token K_if
%token K_let
%token K_proc
%token K_return

%left Bar
%left Caret
%left Amp
%left EqEq
%left Plus Minus
%left Dot

%start <Spec_ast.ast> top
%start <Spec_ast.expr> expr_top

%%

top:
  | decl*; EOF { $1 }

decl:
  | proc_def { Decl_proc $1 }

proc_def:
  | K_proc; proc_name = Ident;
    LParen; proc_params = separated_list(Comma, name_length_pair); RParen;
    LBrace; proc_body = list(stmt); RBrace
    {{ proc_name; proc_params; proc_body }}

name_length_pair:
  | name = Ident; Colon; len = Int { name, len }

primary_expr:
  | name = Ident
    { Expr_sym name }
    (*{ if Char.is_uppercase name.[0]
      then Expr_global_sym name
      else Expr_local_sym name }*)
  | bv = Bitvec
    { Expr_literal bv }
  | LParen; e = expr; RParen { e }
  | proc_name = Ident; LParen; args = separated_list(Comma, expr); RParen
    { Expr_call (proc_name, args) }

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

expr:
  | binary_expr {$1}

stmt:
  | name = Ident; Eq; value = expr; Semi
    { Stmt_set (name, value) }
  | K_let; name = Ident; Eq; value = expr; Semi
    { Stmt_let (name, value) }
  | proc_name = Ident; LParen; args = separated_list(Comma, expr); RParen; Semi
    { Stmt_call (proc_name, args) }
  | K_return; value = expr; Semi
    { Stmt_return value }

expr_top:
  | expr EOF {$1}
