open Format
open Semant
open Spec_ast
open Util

(* "%s takes exactly %d arguments" *)
exception Wrong_arity of string * int
exception Index_out_of_bounds of (astexpr * int) * int
exception Width_mismatch of int * int
exception Unbound_symbol of string
exception Invalid_assignment of string
exception Unknown_primitive of string
exception Redefinition of string

let check_width w1 w2 =
  if w1 <> w2 then raise (Width_mismatch (w1, w2)) else ()

type value =
  | Var of string * int (* name, width *)
  | Proc of proc
  | Templ of proc_templ
  | IConst of int
  | BVConst of Bitvec.t
  | Prim of string

type symtab = value StringMap.t

let prim_of_unary_op (op, e) =
  match op with
  | Not -> P_not e
  | Reduce_and -> P_reduce_and e
  | Reduce_xor -> P_reduce_xor e
  | Reduce_or -> P_reduce_or e

let width_of_unary_op (op, w) =
  match op with
  | Not -> w
  | Reduce_and | Reduce_xor | Reduce_or -> 1

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
    check_width w1 w2; w1
  | Eq ->
    check_width w1 w2; 1

(* 32 just for now *)
let init_symtab = [
  "AX", 32;
  "CX", 32;
  "DX", 32;
  "BX", 32;
  "SP", 32;
  "BP", 32;
  "SI", 32;
  "DI", 32;
  "CF",  1;
  "PF",  1;
  "AF",  1;
  "ZF",  1;
  "SF",  1;
  "DF",  1;
  "OF",  1;
] |> List.fold_left (fun map (name, w) ->
    StringMap.add name (Var (name, w)) map) StringMap.empty

let extend_symtab (name, value) st =
  if StringMap.mem name st
  then raise (Redefinition name)
  else StringMap.add name value st

let try_lookup st name = StringMap.find_opt name st

let lookup st name =
  match try_lookup st name with
  | None -> raise (Unbound_symbol name)
  | Some value -> value

let rec translate_cexpr st = function
  | C_int i -> i
  | C_sym s ->
    begin match lookup st s with
      | IConst i -> i
      | _ -> failwith ("not an IConst value: "^s)
    end
  | C_binary (op, e1, e2) ->
    let e1' = translate_cexpr st e1 in
    let e2' = translate_cexpr st e2 in
    let f =
      match op with
      | CB_add -> (+)
      | CB_sub -> (-)
      | CB_mul -> ( * )
      | CB_div -> (/)
      | CB_and -> (land)
      | CB_or  -> (lor)
      | CB_xor -> (lxor)
    in
    f e1' e2'
  | C_unary (op, e) ->
    let e' = translate_cexpr st e in
    let f =
      match op with
      | CU_not -> (lnot)
    in
    f e'

let rec translate_expr st = function
  | Expr_sym s ->
    begin match lookup st s with
      | Var (name, w) -> E_var name, w
      | BVConst bv -> E_literal bv, Bitvec.length bv
      | _ -> failwith ("not a Var or BVConst value: "^s)
    end
  | Expr_literal bv -> E_literal bv, Bitvec.length bv
  | Expr_literal2 (c_v, c_w) ->
    let v = translate_cexpr st c_v in
    let w = translate_cexpr st c_w in
    E_literal (Bitvec.of_int w v), w
  | Expr_index (e, i) ->
    let e', w = translate_expr st e in
    begin match i with
      | Index_bit c_b ->
        let b = translate_cexpr st c_b in
        if b >= w then raise (Index_out_of_bounds ((e,w),b));
        E_part (e', (b, b+1)), 1
      | Index_part (c_hi', c_lo) ->
        let hi' = translate_cexpr st c_hi' in
        let lo = translate_cexpr st c_lo in
        let hi = hi'+1 in
        if hi > w then raise (Index_out_of_bounds ((e,w),hi'));
        E_part (e', (lo, hi)), hi-lo
    end
  | Expr_apply (func_name, args) ->
    let handle_builtin func_name =
      let f1 prim =
        let args', arg_widths =
          unzip (args |> List.map (translate_expr st))
        in
        let w = List.hd arg_widths in
        arg_widths |> List.iter (check_width w);
        E_prim (prim args'), w
      in
      let f_shift prim =
        let a1, a2 =
          match args with
          | [a1;a2] -> a1, a2
          | _ -> raise (Wrong_arity (func_name, 2))
        in
        let a1', w1 = translate_expr st a1 in
        let a2', _ = translate_expr st a2 in
        E_prim (prim a1' a2'), w1
      in
      match func_name with
      | "add_ex" ->
        let a1, a2, a3 =
          match args with
          | [a1;a2;a3] -> a1, a2, a3
          | _ -> raise (Wrong_arity (func_name, 3))
        in
        let a1', w1 = translate_expr st a1 in
        let a2', w2 = translate_expr st a2 in
        let a3', w3 = translate_expr st a3 in
        check_width w1 w2;
        check_width w3 1;
        E_prim (P_add_ex (a1', a2', a3')), w1+1
      | "and" -> f1 (fun args -> P_and args)
      | "or"  -> f1 (fun args -> P_or  args)
      | "xor" -> f1 (fun args -> P_xor args)
      | "shift_left" -> f_shift (fun a1' a2' -> P_shiftleft (a1', a2'))
      | "log_shift_right" -> f_shift (fun a1' a2' -> P_logshiftright (a1', a2'))
      | "ari_shift_right" -> f_shift (fun a1' a2' -> P_arishiftright (a1', a2'))
      | _ -> raise (Unknown_primitive func_name)
    in
    begin match try_lookup st func_name with
      | None -> handle_builtin func_name
      | Some (Prim func_name) -> handle_builtin func_name
      | _ -> raise (Unknown_primitive func_name)
    end
  | Expr_unary (op, e) ->
    let e', w = translate_expr st e in
    E_prim (prim_of_unary_op (op, e')), width_of_unary_op (op, w)
  | Expr_binary (op, e1, e2) ->
    let e1', w1 = translate_expr st e1 in
    let e2', w2 = translate_expr st e2 in
    E_prim (prim_of_binary_op (op, e1', e2')), width_of_binary_op (op, w1, w2)
  | Expr_undef c_width ->
    let width = translate_cexpr st c_width in
    E_prim (P_undef width), width
  | Expr_repeat (data, c_n) ->
    let data', w = translate_expr st data in
    let n = translate_cexpr st c_n in
    E_prim (P_repeat (data', n)), w*n
  | Expr_load (size, addr) ->
    let size' = translate_cexpr st size in
    let addr', w = translate_expr st addr in
    E_load (size', addr'), w

(* TODO: comment *)
let translate_stmt st_ref env stmt =
  let st = !st_ref in
  let do_assign loc f w =
    begin match loc with
      | Loc_var name ->
        begin match try_lookup st name with
          | None -> raise (Unbound_symbol name)
          | Some (Var (r, r_width)) ->
            append_stmt env (f (L_var r))
          | _ -> raise (Invalid_assignment name)
        end
      | Loc_part (name, hi, lo) ->
        begin match try_lookup st name with
          | None -> raise (Unbound_symbol name)
          | Some (Var (r, r_width)) ->
            let hi' = translate_cexpr st hi + 1 in
            let lo' = translate_cexpr st lo in
            assert (lo' >= 0);
            assert (hi' <= r_width);
            append_stmt env (f (L_part (r, lo', hi')))
          | _ -> raise (Invalid_assignment name)
        end
      | Loc_newvar name ->
        begin match try_lookup st name with
          | None ->
            st_ref := extend_symtab (name, Var (name, w)) st;
            append_stmt env (f (L_var name))
          | Some _ -> raise (Redefinition name)
        end
    end
  in
  match stmt with
  | Stmt_set (loc, e) ->
    let e', e_width = translate_expr st e in
    do_assign loc (fun loc' -> S_set (loc', e')) e_width
  | Stmt_call (proc_name, args, result_loc_opt) ->
    let proc =
      match lookup st proc_name with
      | Proc p -> p
      | _ -> failwith ("not a Proc value: "^proc_name)
    in
    let args, arg_widths =
      unzip (List.map (translate_expr st) args)
    in
    let n_param = List.length proc.p_param_names in
    let n_arg = List.length args in
    if n_param <> n_arg then raise (Wrong_arity (proc_name, n_param));
    (* check arg width *)
    zip proc.p_param_names arg_widths |> List.iter
      (fun (param_name, arg_width) ->
         let param_width = Hashtbl.find proc.p_var_tab param_name in
         check_width param_width arg_width);
    (* function that translates arguments *)
    (*let rec f = function
      | [] -> proc_body
      | (arg, _) :: args'_widths' -> E_let (arg, (f args'_widths'))
      in
      f args'_widths, result_width*)
    begin match result_loc_opt with
      | None -> append_stmt env (S_call (proc, args, None))
      | Some loc ->
        let rhs_width = proc.p_result_width in
        do_assign loc (fun loc' -> S_call (proc, args, Some loc')) rhs_width
    end
  | Stmt_return e ->
    let e', _ = translate_expr st e in
    append_stmt env (S_return e')
  (*| Stmt_load (c_size, addr, name) ->
    let size = translate_cexpr st c_size in
    let w = size*8 in
    st_ref := extend_symtab (name, Var (name, w)) st;
    let addr', _ = translate_expr st addr in
    append_stmt env (S_load (size, addr', name))*)
  | Stmt_store (c_size, addr, data) ->
    let size = translate_cexpr st c_size in
    let addr', _ = translate_expr st addr in
    let data', data_width = translate_expr st data in
    check_width (size*8) data_width;
    append_stmt env (S_store (size, addr', data'))
  | Stmt_jump addr ->
    let addr', w = translate_expr st addr in
    check_width w 32;
    append_stmt env (S_jump_var addr')

let translate_proc st proc =
  (* construct static environment to translate function body in *)
  let proc_st = ref st in
  let proc_env = new_env () in
  proc.ap_params |> List.iter
    begin fun (param_name, c_param_width) ->
      let param_width = translate_cexpr !proc_st c_param_width in
      proc_st :=
        extend_symtab (param_name, Var (param_name, param_width)) !proc_st;
      Hashtbl.add proc_env.var_tab param_name param_width
    end;
  let param_names = proc.ap_params |> List.map fst in
  let result_width = translate_cexpr st proc.ap_result_width in
  proc.ap_body |> List.iter (translate_stmt proc_st proc_env);
  (*Printf.printf "%s: %d statements\n" proc.ap_name (List.length proc_env.stmts_rev);*)
  { p_name = proc.ap_name;
    p_body = get_stmts proc_env;
    p_param_names = param_names;
    p_result_width = result_width;
    p_var_tab = proc_env.var_tab }

let translate_ast ast =
  ast |> List.fold_left begin fun st decl ->
    match decl with
    | Decl_proc proc ->
      let proc' = translate_proc st proc in
      extend_symtab (proc.ap_name, Proc proc') st
    | Decl_proc_templ pt ->
      extend_symtab (pt.pt_name, Templ pt) st
    | Decl_proc_inst pi ->
      let pt =
        match lookup st pi.pi_templ_name with
        | Templ pt -> pt
        | _ -> failwith ("not a Templ value: "^pi.pi_templ_name)
      in
      let named_args = zip pt.pt_templ_params pi.pi_templ_args in
      let inst_st =
        named_args |> List.fold_left begin fun st (name, arg) ->
          let value =
            match arg with
            | TA_int i -> IConst i
            | TA_bitvec v -> BVConst v
            | TA_prim s -> Prim s
            | TA_var s -> lookup init_symtab s
          in
          extend_symtab (name, value) st
        end (* init: *) st
      in
      let proc =
        { ap_name = pi.pi_inst_name;
          ap_params = pt.pt_proc_params;
          ap_body = pt.pt_body;
          ap_result_width = pt.pt_result_width }
      in
      let proc' = translate_proc inst_st proc in
      extend_symtab (proc.ap_name, Proc proc') st
  end (* init: *) init_symtab

let pp_value f = function
  | Var (name, w) ->
    fprintf f "Var %s:%d" name w
  | Proc p ->
    fprintf f "Proc %a" pp_proc p
  | Templ _ ->
    fprintf f "Templ"
  | IConst i ->
    fprintf f "IConst %d" i
  | BVConst bv ->
    fprintf f "BVConst %a" Bitvec.pp bv
  | Prim s ->
    fprintf f "Prim %s" s

let pp_symtab f st =
  fprintf f "@[<v>";
  st |> StringMap.iter (fun key data ->
      fprintf f "%s: %a@ " key pp_value data);
  fprintf f "@]"
