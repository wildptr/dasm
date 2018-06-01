open Format
open Semant
open Spec_ast

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

type symtab = value BatMap.String.t

type env = {
  mutable symtab : symtab;
  var_tab : (string, int) Hashtbl.t;
  mutable stmts_rev : stmt list;
}

let new_env symtab =
  let var_tab = Hashtbl.create 0 in
  { symtab; var_tab; stmts_rev = [] }

let append_stmt env stmt = env.stmts_rev <- stmt :: env.stmts_rev

let new_temp env width =
  let n = Hashtbl.length env.var_tab in
  let id = Printf.sprintf "$%d" n in
  Hashtbl.add env.var_tab id width;
  id

let prim_of_unary_op = function
  | Not -> P1_not
  | Neg -> P1_neg
  | Reduce_and -> P1_foldand
  | Reduce_xor -> P1_foldxor
  | Reduce_or -> P1_foldor

let width_of_unary_op (op, w) =
  match op with
  | Not | Neg -> w
  | Reduce_and | Reduce_xor | Reduce_or -> 1

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
  "EAX", 32;
  "ECX", 32;
  "EDX", 32;
  "EBX", 32;
  "ESP", 32;
  "EBP", 32;
  "ESI", 32;
  "EDI", 32;
  "AX", 16;
  "CX", 16;
  "DX", 16;
  "BX", 16;
  "SP", 16;
  "BP", 16;
  "SI", 16;
  "DI", 16;
  "AL",  8;
  "CL",  8;
  "DL",  8;
  "BL",  8;
  "AH",  8;
  "CH",  8;
  "DH",  8;
  "BH",  8;
  "ES", 16;
  "CS", 16;
  "SS", 16;
  "DS", 16;
  "FS", 16;
  "GS", 16;
  "CF",  1;
  "PF",  1;
  "AF",  1;
  "ZF",  1;
  "SF",  1;
  "DF",  1;
  "OF",  1;
] |> List.fold_left (fun map (name, w) ->
    BatMap.String.add name (Var (name, w)) map) BatMap.String.empty

let extend_symtab (name, value) st =
  if BatMap.String.mem name st
  then raise (Redefinition name)
  else BatMap.String.add name value st

let try_lookup st name =
  try Some (BatMap.String.find name st) with Not_found -> None

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

let rec translate_expr env expr =
  let st = env.symtab in
  match expr with
  | Expr_sym s ->
    begin match lookup st s with
      | Var (name, w) -> E_var name, w
      | BVConst bv -> E_lit bv, Bitvec.length bv
      | _ -> failwith ("not a Var or BVConst value: "^s)
    end
  | Expr_literal bv -> E_lit bv, Bitvec.length bv
  | Expr_literal2 (c_v, c_w) ->
    let v = translate_cexpr st c_v in
    let w = translate_cexpr st c_w in
    E_lit (Bitvec.of_int w v), w
  | Expr_index (e, i) ->
    let e', w = translate_expr env e in
    begin match i with
      | Index_bit c_b ->
        let b = translate_cexpr st c_b in
        if b >= w then raise (Index_out_of_bounds ((e,w),b));
        E_part (e', b, b+1), 1
      | Index_part (c_hi', c_lo) ->
        let hi' = translate_cexpr st c_hi' in
        let lo = translate_cexpr st c_lo in
        let hi = hi'+1 in
        if hi > w then raise (Index_out_of_bounds ((e,w),hi'));
        E_part (e', lo, hi), hi-lo
    end
  | Expr_apply (func_name, args) ->
    let handle_builtin func_name =
      let f1 prim =
        let args', arg_widths =
          List.split (args |> List.map (translate_expr env))
        in
        let w = List.hd arg_widths in
        arg_widths |> List.iter (check_width w);
        E_primn (prim, args'), w
      in
      let f_shift prim =
        let a1, a2 =
          match args with
          | [a1;a2] -> a1, a2
          | _ -> raise (Wrong_arity (func_name, 2))
        in
        let a1', w1 = translate_expr env a1 in
        let a2', _ = translate_expr env a2 in
        E_prim2 (prim, a1', a2'), w1
      in
      let f_pred prim =
        let a1, a2 =
          match args with
          | [a1;a2] -> a1, a2
          | _ -> raise (Wrong_arity (func_name, 2))
        in
        let a1', w1 = translate_expr env a1 in
        let a2', w2 = translate_expr env a2 in
        check_width w1 w2;
        E_prim2 (prim, a1', a2'), 1
      in
      match func_name with
      | "carry" ->
        let a1, a2, a3 =
          match args with
          | [a1;a2;a3] -> a1, a2, a3
          | _ -> raise (Wrong_arity (func_name, 3))
        in
        let a1', w1 = translate_expr env a1 in
        let a2', w2 = translate_expr env a2 in
        let a3', w3 = translate_expr env a3 in
        check_width w1 w2;
        check_width w3 1;
        E_prim3 (P3_carry, a1', a2', a3'), 1
      | "and" -> f1 Pn_and
      | "xor" -> f1 Pn_xor
      | "or"  -> f1 Pn_or
      | "shift_left" -> f_shift P2_shiftleft
      | "log_shift_right" -> f_shift P2_logshiftright
      | "ari_shift_right" -> f_shift P2_arishiftright
      | "less" -> f_pred P2_less
      | "below" -> f_pred P2_below
      | _ -> raise (Unknown_primitive func_name)
    in
    begin match try_lookup st func_name with
      | None -> handle_builtin func_name
      | Some (Prim func_name) -> handle_builtin func_name
      | Some (Proc proc) ->
        let w = proc.p_result_width in
        let temp = new_temp env w in
        translate_call env proc args (Some temp);
        E_var temp, w
      | _ -> raise (Unknown_primitive func_name)
    end
  | Expr_unary (op, e) ->
    let e', w = translate_expr env e in
    E_prim1 (prim_of_unary_op op, e'), width_of_unary_op (op, w)
  | Expr_binary (op, e1, e2) ->
    let e1', w1 = translate_expr env e1 in
    let e2', w2 = translate_expr env e2 in
    let e' = match op with
      | Concat -> E_primn (Pn_concat, [e1';e2'])
      | Add -> E_primn (Pn_add, [e1';e2'])
      | Sub -> E_prim2 (P2_sub, e1', e2')
      | Eq -> E_prim2 (P2_eq, e1', e2')
      | And -> E_primn (Pn_and, [e1';e2'])
      | Xor -> E_primn (Pn_xor, [e1';e2'])
      | Or -> E_primn (Pn_or, [e1';e2'])
    in
    e', width_of_binary_op (op, w1, w2)
  | Expr_undef c_width ->
    let width = translate_cexpr st c_width in
    E_nondet (width, 0), width (* TODO: nondet id *)
  | Expr_load memloc ->
    let seg', off', w = translate_memloc env memloc in
    E_load (w lsr 3, seg', off'), w
  | Expr_extend (sign, data, size) ->
    let data', _ = translate_expr env data in
    let size' = translate_cexpr st size in
    E_extend (sign, data', size'), size'

and translate_call env proc args result_opt =
  let args, arg_widths =
    List.split (List.map (translate_expr env) args)
  in
  let n_param = List.length proc.p_param_names in
  let n_arg = List.length args in
  if n_param <> n_arg then raise (Wrong_arity ("???", n_param)); (* TODO *)
  (* check arg width *)
  List.combine proc.p_param_names arg_widths |> List.iter
    (fun (param_name, arg_width) ->
       let param_width = Hashtbl.find proc.p_var_tab param_name in
       check_width param_width arg_width);
  (* function that translates arguments *)
  append_stmt env (S_call (proc, args, result_opt))

and translate_memloc env (seg, off, size) =
  let seg', segw = translate_expr env seg in
  check_width segw 16;
  let off', offw = translate_expr env off in
  (* TODO: check offset width *)
  let w = translate_cexpr env.symtab size in
  seg', off', w

let translate_stmt env stmt =
  let st = env.symtab in
  let emit = append_stmt env in
  let do_assign loc (data, w) =
    begin match loc with
      | Lhs_var name ->
        begin match try_lookup st name with
          | None -> raise (Unbound_symbol name)
          | Some (Var (r, r_width)) ->
            emit (S_set (r, data))
          | _ -> raise (Invalid_assignment name)
        end
      | Lhs_mem memloc ->
        let seg, off, mw = translate_memloc env memloc in
        check_width mw w;
        if w land 7 <> 0 then
          failwith "width of memory location is not multiple of 8";
        emit (S_store (w lsr 3, seg, off, data))
    end
  in
  match stmt with
  | Stmt_set (loc, e) ->
    do_assign loc (translate_expr env e)
  | Stmt_call (proc_name, args) ->
    let proc =
      match lookup st proc_name with
      | Proc p -> p
      | _ -> failwith ("not a Proc value: "^proc_name)
    in
    translate_call env proc args None
  | Stmt_return e ->
    let e', _ = translate_expr env e in
    emit (S_return e')
  | Stmt_jump addr -> assert false

let translate_proc st proc =
  (* construct static environment to translate function body in *)
  let proc_env = new_env st in
  let register_var (name, c_width) =
    let width = translate_cexpr proc_env.symtab c_width in
    proc_env.symtab <-
      extend_symtab (name, Var (name, width))
        proc_env.symtab;
    Hashtbl.add proc_env.var_tab name width
  in
  proc.ap_params |> List.iter register_var;
  let vardecls, stmts = proc.ap_body in
  vardecls |> List.iter register_var;
  let param_names = proc.ap_params |> List.map fst in
  let result_width = translate_cexpr st proc.ap_result_width in
  stmts |> List.iter (translate_stmt proc_env);
  (*Printf.printf "%s: %d statements\n" proc.ap_name (List.length proc_env.stmts_rev);*)
  { p_name = proc.ap_name;
    p_body = List.rev proc_env.stmts_rev;
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
      let named_args = List.combine pt.pt_templ_params pi.pi_templ_args in
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
  st |> BatMap.String.iter (fun key data ->
      fprintf f "%s: %a@ " key pp_value data);
  fprintf f "@]"
