%{
open Spec_ast
%}

%token EOF
%token <string> Ident
%token <int> Int
%token <Bitvec.t> Bitvec
%token EqEq
(*%token Dollar*)
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
%token LBrack
%token RBrack
%token Caret
%token LBrace
%token Bar
%token RBrace
%token Tilde

%token K_call
%token K_jump
%token K_let
%token K_load
%token K_output
%token K_proc
%token K_repeat
%token K_store
%token K_template
%token K_undefined

%left Bar
%left Caret
%left Amp
%left EqEq
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

proc_def:
  | K_proc; ap_name = Ident;
    LParen; ap_params = separated_list(Comma, name_length_pair); RParen;
    result_width_opt = option(preceded(Colon, cexpr));
    LBrace; ap_body = list(stmt); RBrace
    {{ ap_name; ap_params; ap_body;
       ap_result_width =
         match result_width_opt with None -> C_int 0 | Some width -> width }}

name_length_pair:
  | name = Ident; Colon; len = cexpr { name, len }

primary_expr:
  | name = Ident
    { Expr_sym name }
    (*{ if Char.is_uppercase name.[0]
      then Expr_global_sym name
      else Expr_local_sym name }*)
  | bv = Bitvec
    { Expr_literal bv }
  | LBrace; v = cexpr; Colon; w = cexpr; RBrace
    { Expr_literal2 (v, w) }
  | LParen; e = expr; RParen { e }
  | func_name = Ident; LParen; args = separated_list(Comma, expr); RParen
    { Expr_apply (func_name, args) }
  | K_undefined; LParen; width = cexpr; RParen
    { Expr_undef width }
  | K_repeat; LParen; data = expr; Comma; n = cexpr; RParen
    { Expr_repeat (data, n) }
  | K_load; LParen; size = cexpr; Comma; addr = expr; RParen
    { Expr_load (size, addr) }

index:
  | LBrack; i = cexpr; RBrack
    { Index_bit i }
  | LBrack; hi = cexpr; Colon; lo = cexpr; RBrack
    { Index_part (hi, lo) }

postfix_expr:
  | primary_expr {$1}
  | e = postfix_expr; i = index
    { Expr_index (e, i) }

unary_op:
  | Tilde { Not }
  | Amp { Reduce_and }
  | Caret { Reduce_xor }
  | Bar { Reduce_or }

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

expr: binary_expr {$1}

loc:
  | name = Ident
    { Loc_var name }
  (*| name = Ident; LBrack; hi = cexpr; Colon; lo = cexpr; RBrack
    { Loc_part (name, hi, lo) }*)
  | K_let; name = Ident
    { Loc_newvar name }

stmt:
  | loc = loc; Eq; value = expr; Semi
    { Stmt_set (loc, value) }
  (*| name = Ident; LBrack; hi = cexpr; Colon; lo = cexpr; RBrack; Eq; value = expr; Semi
    { Stmt_set_part (name, hi, lo, value) }*)
  | K_call; proc_name = Ident;
    LParen; args = separated_list(Comma, expr); RParen; Semi
    { Stmt_call (proc_name, args, None) }
  | loc = loc; Eq; K_call; proc_name = Ident;
    LParen; args = separated_list(Comma, expr); RParen; Semi
    { Stmt_call (proc_name, args, Some loc) }
  | K_output; value = expr; Semi
    { Stmt_output value }
  (*| name = Ident; Eq; K_load; size = cexpr; Comma; addr = expr; Semi
    { Stmt_load (size, addr, name) }*)
  | K_store; size = cexpr; Comma; addr = expr; Comma; data = expr; Semi
    { Stmt_store (size, addr, data) }
  | K_jump; addr = expr; Semi
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

proc_templ:
  | K_template; K_proc; pt_name = Ident;
    LAngle; pt_templ_params = separated_list(Comma, Ident); RAngle;
    LParen; pt_proc_params = separated_list(Comma, name_length_pair); RParen;
    result_width_opt = option(preceded(Colon, cexpr));
    LBrace; pt_body = list(stmt); RBrace
    {{ pt_name; pt_templ_params; pt_proc_params; pt_body;
       pt_result_width =
         match result_width_opt with Some width -> width | None -> C_int 0 }}

proc_inst:
  | K_proc; pi_inst_name = Ident; Eq; pi_templ_name = Ident;
    LAngle; pi_templ_args = separated_nonempty_list(Comma, templ_arg); RAngle; Semi
    {{ pi_inst_name; pi_templ_name; pi_templ_args }}

templ_arg:
  | Int { TA_int $1 }
  | Bitvec { TA_bitvec $1 }
  | s = Ident { match s.[0] with 'A'..'Z' -> TA_var s | _ -> TA_prim s }
