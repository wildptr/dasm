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
(* %token LBrace *)
%token Bar
(* %token RBrace *)
%token Tilde

%token K_in
%token K_let

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
  | func_def { Decl_func $1 }

func_def:
  | K_let; func_name = Ident;
    LParen; func_params = separated_list(Comma, name_length_pair); RParen;
    Eq; func_body = expr
    {{ func_name; func_params; func_body }}

name_length_pair:
  | name = Ident; Colon; len = Int { name, len }

primary_expr:
  | name = Ident
    { if Char.is_uppercase name.[0]
      then Expr_global_sym name
      else Expr_local_sym name }
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

set_expr:
  | binary_expr {$1}
  | lhs = Ident; Eq; rhs = binary_expr
    { Expr_set (lhs, rhs) }

seq_expr:
  | set_expr {$1}
  | e1 = seq_expr; Semi; e2 = set_expr
    { Expr_seq (e1, e2) }

let_expr:
  | seq_expr {$1}
  | K_let; name = Ident; Eq; value = expr; K_in; body = expr
    { Expr_let (name, value, body) }

expr:
  | let_expr {$1}

expr_top:
  | expr EOF {$1}
