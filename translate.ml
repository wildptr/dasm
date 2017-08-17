open Core_kernel.Std
open Format
open Semant
open Spec_ast

(* "%s takes exactly %d arguments" *)
exception Wrong_arity of string * int
exception Index_out_of_bounds of (astexpr * int) * int
exception Width_mismatch
exception Unbound_local of string
exception Unbound_global of string
exception Unbound_proc of string
exception Set_const of string
exception Unknown_primitive of string

let prim_of_unary_op (op, e) =
  match op with
  | Not -> P_not e

let width_of_unary_op (op, w) =
  match op with
  | Not -> w

let prim_of_binary_op (op, e1, e2) =
  match op with
  | Concat -> P_concat [e1;e2]
  | Add -> P_add [e1;e2]
  | Sub -> P_sub (e1,e2)
  | Eq -> P_eq (e1,e2)
  | And -> P_and [e1;e2]
  | Xor -> P_xor [e1;e2]
  | Or -> P_or [e1;e2]

let width_of_binary_op (op, w1, w2) =
  match op with
  | Concat ->
      w1 + w2
  | Add | Sub | And | Xor | Or ->
      if w1 <> w2 then raise Width_mismatch; w1
  | Eq ->
      if w1 <> w2 then raise Width_mismatch; 1

let global_map : (reg * int) String.Map.t = [
  "CF", (Flag_C, 1);
  "PF", (Flag_P, 1);
  "AF", (Flag_A, 1);
  "ZF", (Flag_Z, 1);
  "SF", (Flag_S, 1);
  "DF", (Flag_D, 1);
  "OF", (Flag_O, 1);
] |> String.Map.of_alist_exn

let env_proc_map env = env.env_proc_map

let init_env =
  { env_local_map = String.Map.empty;
    env_proc_map = String.Map.empty }

let extend_env (name, width) env =
  let id = String.Map.length env.env_local_map in
  let env_local_map =
    String.Map.add env.env_local_map ~key:name ~data:(id, width)
  in
  { env with env_local_map }, id

let extend_env_proc (key, data) env =
  { env with env_proc_map = String.Map.add env.env_proc_map ~key ~data }

let lookup_local env name =
  match String.Map.find env.env_local_map name with
  | None -> raise (Unbound_local name)
  | Some (i, width) -> i, width

let try_lookup_global name =
  String.Map.find global_map name

let lookup_global name =
  match try_lookup_global name with
  | None -> raise (Unbound_global name)
  | Some (reg, width) -> reg, width

let lookup_proc env key =
  match String.Map.find env.env_proc_map key with
  | None -> raise (Unbound_proc key)
  | Some data -> data

let rec translate_expr env = function
  | Expr_sym s ->
      begin match try_lookup_global s with
      | None ->
          let i, w = lookup_local env s in
          E_local i, w
      | Some (r, w) ->
          E_global r, w
      end
  | Expr_literal bv -> E_literal bv, Bitvec.length bv
  | Expr_index (e, i) ->
      let e', w = translate_expr env e in
      begin match i with
      | Index_bit b ->
          if b >= w then raise (Index_out_of_bounds ((e,w),b));
          E_part (e', (b, b+1)), 1
      | Index_part (hi', lo) ->
          let hi = hi'+1 in
          if hi > w then raise (Index_out_of_bounds ((e,w),hi'));
          E_part (e', (lo, hi)), hi-lo
      end
  | Expr_apply (func_name, args) ->
      (* handle built-in functions *)
      begin match func_name with
      | "add_ex" ->
          let a1, a2, a3 =
            match args with
            | [a1;a2;a3] -> a1, a2, a3
            | _ -> raise (Wrong_arity (func_name, 3))
          in
          let a1', w1 = translate_expr env a1 in
          let a2', w2 = translate_expr env a2 in
          let a3', w3 = translate_expr env a3 in
          if w1 <> w2 then raise Width_mismatch;
          if w3 <> 1 then raise Width_mismatch;
          E_prim (P_add_ex (a1', a2', a3')), w1+1
      | _ -> raise (Unknown_primitive func_name)
      end
  | Expr_unary (op, e) ->
      let e', w = translate_expr env e in
      E_prim (prim_of_unary_op (op, e')), width_of_unary_op (op, w)
  | Expr_binary (op, e1, e2) ->
      let e1', w1 = translate_expr env e1 in
      let e2', w2 = translate_expr env e2 in
      E_prim (prim_of_binary_op (op, e1', e2')), width_of_binary_op (op, w1, w2)
  (*| Expr_let (name, value, body) ->
      let value', value_width = translate_expr env value in
      let body', body_width = translate_expr (extend_env (name, value_width) env) body in
      E_let (value', body'), body_width
  | Expr_set (name, value) ->
      let r, w = lookup_global env name in
      let value', value_width = translate_expr env value in
      if w <> value_width then raise Width_mismatch;
      E_set (r, value'), 0
  | Expr_seq (e1, e2) ->
      let e1', w1 = translate_expr env e1 in
      if w1 <> 0 then raise Width_mismatch;
      let e2', w2 = translate_expr env e2 in
      E_seq (e1', e2'), w2*)

let translate_stmt env = function
  | Stmt_set (name, e) ->
      begin match try_lookup_global name with
      | None ->
          let e', width = translate_expr env e in
          let env', id = extend_env (name, width) env in
          env', S_setlocal (id, e')
      | Some (r, r_width) ->
          let e', e_width = translate_expr env e in
          if r_width <> e_width then raise Width_mismatch;
          env, S_setglobal (r, e')
      end
  | Stmt_call (proc_name, args, result_name_opt) ->
      let proc = lookup_proc env proc_name in
      let args, arg_widths =
        List.unzip (List.map ~f:(translate_expr env) args)
      in
      let n_param = List.length proc.p_param_widths in
      let n_arg = List.length args in
      if n_param <> n_arg then raise (Wrong_arity (proc_name, n_param));
      (* check arg width *)
      List.iter (List.zip_exn proc.p_param_widths arg_widths)
        ~f:(fun (param_width, arg_width) ->
          if param_width <> arg_width then raise Width_mismatch);
      (* function that translates arguments *)
      (*let rec f = function
        | [] -> proc_body
        | (arg, _) :: args'_widths' -> E_let (arg, (f args'_widths'))
      in
      f args'_widths, result_width*)
      let env', result_opt =
        match result_name_opt with
        | None -> env, None
        | Some name ->
            let env', id = extend_env (name, proc.p_result_width) env in
            env', Some id
      in
      env', S_call (proc_name, args, result_opt)
  | Stmt_return e ->
      let e', _ = translate_expr env e in
      env, S_return e'

let translate_proc env proc =
  (* construct static environment to translate function body in *)
  let body_env =
    List.fold proc.ap_params ~init:env
    ~f:(fun env (param_name, param_width) ->
      fst (extend_env (param_name, param_width) env))
  in
  let param_widths = List.map proc.ap_params ~f:snd in
  let env', low_stmts_rev =
    List.fold proc.ap_body ~init:(body_env, []) ~f:(fun (env, low_stmts_rev) stmt ->
      let env', low_stmt = translate_stmt env stmt in
      env', low_stmt :: low_stmts_rev)
  in
  { p_body = List.rev low_stmts_rev;
    p_param_widths = param_widths;
    p_result_width = proc.ap_result_width;
    p_env = env' }

let translate_ast ast =
  List.fold ast ~init:init_env ~f:begin fun env (Decl_proc proc) ->
    let proc' = translate_proc env proc in
    extend_env_proc (proc.ap_name, proc') env
  end
