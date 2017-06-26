%{
%}

%token EOF
%token <string> Ident
%token <int> Int
%token <bool list> Bitvec
%token EqEq
%token LParen
%token RParen
%token Comma
%token Colon
%token Semi
%token Eq
%token LBrack
%token RBrack
%token LBrace
%token RBrace

%token K_let
%token K_proc
%token K_return

%%

top:
  | list(proc_def); EOF { () }

proc_def:
  | K_proc; name = Ident;
    LParen; params = separated_nonempty_list(Comma, name_length_pair); RParen;
    Colon; Int; body = comp_stmt
    { name, params, body }

name_length_pair:
  | name = Ident; Colon; len = Int { name, len }

comp_stmt:
  | LBrace; stmts = list(stmt); RBrace { stmts }

stmt:
  | K_let; lhs = Ident; rhs = expr
    { Stmt_let (lhs, rhs) }
  | lhs = Ident; rhs = expr
    { Stmt_set (lhs, rhs) }
  | K_return; e = expr
    { Stmt_return e }
  | comp_stmt {$1}

primary_expr:
  | name = Ident
    { Expr_sym name }
  | bv = Bitvec
    { Expr_literal bv }

expr:
  | primary_expr {$1}
