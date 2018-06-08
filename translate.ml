open Batteries
open Format
open Semant
open Plain
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
  | Var of var * int
  | Proc of proc
  | Templ of proc_templ
  | IConst of int
  | BVConst of Bitvec.t
  | Prim of string

type symtab = value Map.String.t

type env = {
  mutable symtab : symtab;
  var_tab : (string, int) Hashtbl.t;
  mutable stmts_rev : stmt list;
}

let new_env symtab =
  let var_tab = Hashtbl.create 0 in
  { symtab; var_tab; stmts_rev = [] }

let emit env stmt = env.stmts_rev <- stmt :: env.stmts_rev

let new_temp env width =
  let n = Hashtbl.length env.var_tab in
  let id = Printf.sprintf "_%d" n in
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

let init_symtab = [
  Inst.R_EAX;
  Inst.R_ECX;
  Inst.R_EDX;
  Inst.R_EBX;
  Inst.R_ESP;
  Inst.R_EBP;
  Inst.R_ESI;
  Inst.R_EDI;
  Inst.R_AX;
  Inst.R_CX;
  Inst.R_DX;
  Inst.R_BX;
  Inst.R_SP;
  Inst.R_BP;
  Inst.R_SI;
  Inst.R_DI;
  Inst.R_AL;
  Inst.R_CL;
  Inst.R_DL;
  Inst.R_BL;
  Inst.R_AH;
  Inst.R_CH;
  Inst.R_DH;
  Inst.R_BH;
  Inst.R_ES;
  Inst.R_CS;
  Inst.R_SS;
  Inst.R_DS;
  Inst.R_FS;
  Inst.R_GS;
  Inst.R_CF;
  Inst.R_PF;
  Inst.R_AF;
  Inst.R_ZF;
  Inst.R_SF;
  Inst.R_DF;
  Inst.R_OF;
] |> List.fold_left begin fun map reg ->
    Map.String.add (Inst.string_of_reg reg)
      (Var (Var.Global reg, Inst.size_of_reg reg)) map
  end Map.String.empty

let extend_symtab (name, value) st =
  if Map.String.mem name st
  then raise (Redefinition name)
  else Map.String.add name value st

let try_lookup st name =
  try Some (Map.String.find name st) with Not_found -> None

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
      | Var (var, w) -> E_var var, w
      | BVConst bv -> E_lit bv, Bitvec.length bv
      | _ -> failwith ("not a Var or BVConst value: "^s)
    end
  | Expr_literal bv -> E_lit bv, Bitvec.length bv
  | Expr_literal2 (c_v, c_w) ->
    let v = translate_cexpr st c_v in
    let w = translate_cexpr st c_w in
    E_lit (Bitvec.of_int w v), w
  | Expr_apply (func_name, args) ->
    let handle_builtin func_name =
      let f1 prim =
        let args' = args |> List.map (translate_expr env) in
        let arg_widths = args' |> List.map snd in
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
        let (_, w1 as a1') = translate_expr env a1 in
        let (_, _  as a2') = translate_expr env a2 in
        E_prim2 (prim, a1', a2'), w1
      in
      let f_pred prim =
        let a1, a2 =
          match args with
          | [a1;a2] -> a1, a2
          | _ -> raise (Wrong_arity (func_name, 2))
        in
        let (_, w1) as a1' = translate_expr env a1 in
        let (_, w2) as a2' = translate_expr env a2 in
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
        let (_, w1 as a1') = translate_expr env a1 in
        let (_, w2 as a2') = translate_expr env a2 in
        let (_, w3 as a3') = translate_expr env a3 in
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
        let temp = Var.Local (new_temp env w) in
        translate_call env proc args (Some temp);
        E_var temp, w
      | _ -> raise (Unknown_primitive func_name)
    end
  | Expr_unary (op, e) ->
    let (_, w as e') = translate_expr env e in
    E_prim1 (prim_of_unary_op op, e'), width_of_unary_op (op, w)
  | Expr_binary (op, e1, e2) ->
    let (_, w1 as e1') = translate_expr env e1 in
    let (_, w2 as e2') = translate_expr env e2 in
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
    E_var (Var.Nondet width), width
  | Expr_load memloc ->
    let seg', off', w = translate_memloc env memloc in
    E_load (w lsr 3, seg', off'), w
  | Expr_extend (sign, data, size) ->
    let data' = translate_expr env data in
    let size' = translate_cexpr st size in
    E_extend (sign, data', size'), size'
  | Expr_pc -> E_var Var.PC, 32 (* TODO *)

and translate_call env proc args result_opt =
  let args' = List.map (translate_expr env) args in
  let arg_widths = args' |> List.map snd in
  let n_param = List.length proc.p_param_names in
  let n_arg = List.length args in
  if n_param <> n_arg then raise (Wrong_arity ("???", n_param)); (* TODO *)
  (* check arg width *)
  List.combine proc.p_param_names arg_widths |> List.iter
    (fun (param_name, arg_width) ->
       let param_width = Hashtbl.find proc.p_var_tab param_name in
       check_width param_width arg_width);
  (* function that translates arguments *)
  emit env (S_call (proc, args', result_opt))

and translate_memloc env (seg, off, size) =
  let (_, segw as seg') = translate_expr env seg in
  check_width segw 16;
  let (_, offw as off') = translate_expr env off in
  (* TODO: check offset width *)
  let w = translate_cexpr env.symtab size in
  seg', off', w

let translate_stmt env stmt =
  let st = env.symtab in
  let do_assign loc (_, w as data) =
    begin match loc with
      | Lhs_var name ->
        begin match try_lookup st name with
          | None -> raise (Unbound_symbol name)
          | Some (Var (r, r_width)) ->
            emit env (S_set (r, data))
          | _ -> raise (Invalid_assignment name)
        end
      | Lhs_mem memloc ->
        let seg, off, mw = translate_memloc env memloc in
        check_width mw w;
        if w land 7 <> 0 then
          failwith "width of memory location is not multiple of 8";
        emit env (S_store (w lsr 3, seg, off, data))
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
    let e' = translate_expr env e in
    emit env (S_return e')
  | Stmt_jump addr ->
    let addr' = translate_expr env addr in
    emit env (S_jump (None, addr'))

let translate_proc st proc =
  (* construct static environment to translate function body in *)
  let proc_env = new_env st in
  let register_var (name, c_width) =
    let width = translate_cexpr proc_env.symtab c_width in
    proc_env.symtab <-
      extend_symtab (name, Var (Var.Local name, width))
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
  | Var (var, w) ->
    fprintf f "Var %a:%d" Var.pp var w
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
  st |> Map.String.iter (fun key data ->
      fprintf f "%s: %a@ " key pp_value data);
  fprintf f "@]"
