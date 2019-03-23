open Batteries
open Format
open Semant
open Template
open Spec_ast
open Trans_env

(* "%s takes exactly %d arguments" *)
exception Wrong_arity of string * int
exception Index_out_of_bounds of (astexpr * int) * int
exception Unbound_symbol of string
exception Invalid_assignment of string
exception Unknown_primitive of string
exception Redefinition of string

let check_width w1 w2 =
  if w1 <> w2 then failwith "type mismatch"

let prim_of_unary_op = function
  | Not -> P1_not
  | Neg -> P1_neg
  | Reduce_and -> P1_foldand
  | Reduce_xor -> P1_foldxor
  | Reduce_or -> P1_foldor

let type_of_unary_op (op, t) =
  match op with
  | Not | Neg -> t
  | Reduce_and | Reduce_xor | Reduce_or -> T_bitvec 1

let type_of_binary_op (op, t1, t2) =
  match op with
  | Concat ->
    begin
      let T_bitvec w1 = t1 in
      let T_bitvec w2 = t2 in
      T_bitvec (w1 + w2)
    end [@warning "-8"]
  | Mul | Add | Sub | And | Xor | Or ->
    check_width t1 t2; t1
  | Eq | NotEq ->
    check_width t1 t2; T_bool

let init_symtab =
  let open Inst in
  [
    R_AL ; R_CL ; R_DL ; R_BL ; R_AH ; R_CH ; R_DH ; R_BH ;
    R_AX ; R_CX ; R_DX ; R_BX ; R_SP ; R_BP ; R_SI ; R_DI ;
    R_EAX; R_ECX; R_EDX; R_EBX; R_ESP; R_EBP; R_ESI; R_EDI;
    R_ES; R_CS; R_SS; R_DS;
    R_CF; R_PF; R_AF; R_ZF; R_SF; R_IF; R_DF; R_OF;
  ] |> List.fold_left begin fun m r ->
    let g, part_opt = global_of_reg' r in
    let value =
      match part_opt with
      | None -> Var (TV_Global g, type_of_global g)
      | Some part -> PartialReg (g, part)
    in
    Map.String.add (string_of_reg r) value m
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

let translate_typ st = function
  | Typ_bool -> T_bool
  | Typ_bitvec c -> T_bitvec (translate_cexpr st c)

let debug = false

(* TODO: handle segment selectors *)

let rec translate_expr env expr =
  let st = env.symtab in
  match expr with
  | Expr_sym s ->
    begin match lookup st s with
      | Var (var, w) -> E_var var, w
      | PartialReg (g, part) ->
        E_prim1 (P1_part part, E_var (TV_Global g)),
        T_bitvec (size_of_reg_part part)
      | BVConst bv -> E_lit (BitvecLit, bv), T_bitvec (Bitvec.length bv)
      | _ -> failwith ("not a Var or BVConst value: "^s)
    end
  | Expr_literal bv -> E_lit (BitvecLit, bv), T_bitvec (Bitvec.length bv)
  | Expr_literal2 (c_v, c_w) ->
    let v = translate_cexpr st c_v in
    let w = translate_cexpr st c_w in
    E_lit (BitvecLit, Bitvec.of_int w v), T_bitvec w
  | Expr_literal_bool b -> E_lit (BoolLit, b), T_bool
  | Expr_apply (func_name, args) ->
    let handle_builtin func_name =
      let f_bin prim =
        let a1, a2 =
          match args with
          | [a1;a2] -> a1, a2
          | _ -> raise (Wrong_arity (func_name, 2))
        in
        let a1', w1 = translate_expr env a1 in
        let a2', w2 = translate_expr env a2 in
        check_width w1 w2;
        E_prim2 (prim, a1', a2'), w1
      in
      let f_pred prim =
        let a1, a2 =
          match args with
          | [a1;a2] -> a1, a2
          | _ -> raise (Wrong_arity (func_name, 2))
        in
        let (a1', w1) = translate_expr env a1 in
        let (a2', w2) = translate_expr env a2 in
        check_width w1 w2;
        E_prim2 (prim, a1', a2'), T_bool
      in
      match func_name with
      | "carry" ->
        let a1, a2, a3 =
          match args with
          | [a1;a2;a3] -> a1, a2, a3
          | _ -> raise (Wrong_arity (func_name, 3))
        in
        let (a1', w1) = translate_expr env a1 in
        let (a2', w2) = translate_expr env a2 in
        let (a3', w3) = translate_expr env a3 in
        check_width w1 w2;
        check_width w3 T_bool;
        E_prim3 (P3_carry, a1', a2', a3'), T_bool
      | "ite" ->
        let a1, a2, a3 =
          match args with
          | [a1;a2;a3] -> a1, a2, a3
          | _ -> raise (Wrong_arity (func_name, 3))
        in
        let (a1', w1) = translate_expr env a1 in
        let (a2', w2) = translate_expr env a2 in
        let (a3', w3) = translate_expr env a3 in
        check_width w1 T_bool;
        check_width w2 w3;
        E_prim3 (P3_ite, a1', a2', a3'), w2
      | "and" -> f_bin P2_and
      | "xor" -> f_bin P2_xor
      | "or"  -> f_bin P2_or
      | "shl" -> f_bin P2_shiftleft
      | "lshr" -> f_bin P2_logshiftright
      | "ashr" -> f_bin P2_arishiftright
      | "less" -> f_pred P2_less
      | "below" -> f_pred P2_below
      | _ -> raise (Unknown_primitive func_name)
    in
    begin match try_lookup st func_name with
      | None -> handle_builtin func_name
      | Some (Prim prim_name) -> handle_builtin prim_name
      | Some (Proc proc) ->
        let typ =
          match proc.ret_types with
          | [t] -> t
          | _ -> failwith "number of return values is not 1"
        in
        let temp = (acquire_temp env typ) in
        translate_call env proc args [temp];
        E_var temp, typ
      | _ -> raise (Unknown_primitive func_name)
    end
  | Expr_unary (op, e) ->
    let (e', w) = translate_expr env e in
    E_prim1 (prim_of_unary_op op, e'), type_of_unary_op (op, w)
  | Expr_binary (op, e1, e2) ->
    let (e1', w1) = translate_expr env e1 in
    let (e2', w2) = translate_expr env e2 in
    let e' = match op with
      | Concat -> E_prim2 (P2_concat, e1', e2')
      | Mul -> E_prim2 (P2_mul, e1', e2')
      | Add -> E_prim2 (P2_add, e1', e2')
      | Sub -> E_prim2 (P2_sub, e1', e2')
      | Eq -> E_prim2 (P2_eq, e1', e2')
      | NotEq -> E_prim1 (P1_not, E_prim2 (P2_eq, e1', e2'))
      | And -> E_prim2 (P2_and, e1', e2')
      | Xor -> E_prim2 (P2_xor, e1', e2')
      | Or -> E_prim2 (P2_or, e1', e2')
    in
    e', type_of_binary_op (op, w1, w2)
  | Expr_undef typ ->
    let typ' = translate_typ st typ in
    E_var (TV_Nondet typ'), typ'
  | Expr_load memloc ->
    let seg', off', w = translate_memloc env memloc in
    E_prim2 (P2_load (w lsr 3), E_var (TV_Global Memory), off'), T_bitvec w
  | Expr_extend (sign, data, size) ->
    let data' = translate_expr env data |> fst in
    let size' = translate_cexpr st size in
    E_prim1 (P1_extend (sign, size'), data'), T_bitvec size'
  | Expr_pc -> E_var TV_PC, T_bitvec 32 (* TODO *)
  | Expr_extract (e, lo, hi) ->
    let lo' = translate_cexpr st lo
    and hi' = translate_cexpr st hi
    and e', _ = translate_expr env e in (* TODO *)
    E_prim1 (P1_extract (lo', hi'), e'), T_bitvec (hi'-lo')

and translate_call env proc args rets =
  let module T = Transform(TemplVar)(TemplVar) in
  let args', arg_types =
    args |> List.map (translate_expr env) |> List.split
  in
  if arg_types <> proc.arg_types then failwith "type error in procedure call";
  let arg_tab = Array.of_list args' in
  let ret_tab = Array.of_list rets in
  if List.length rets <> List.length proc.ret_types then
    failwith "wrong number of return values";
  let local_tab =
    proc.local_types |> List.map (acquire_temp env) |> Array.of_list
  in
  if debug then begin
    print_endline "local_tab:";
    local_tab |> Array.iter (fun tv -> print_endline (string_of_templ_var tv));
    print_endline "ret_tab:";
    ret_tab |> Array.iter (fun tv -> print_endline (string_of_templ_var tv))
  end;
  let map_lvar = function
    | TV_Local i -> local_tab.(i)
    | TV_Input _ -> failwith "assignment to argument"
    | TV_Output i -> ret_tab.(i)
    | v -> v
  in
  let map_rvar = function
    | TV_Local i -> E_var local_tab.(i)
    | TV_Input i -> arg_tab.(i)
    | TV_Output i -> E_var ret_tab.(i)
    | v -> E_var v
  in
  proc.body |> List.iter begin fun s ->
    s |> T.map_stmt map_lvar (T.subst map_rvar) |> emit env
  end;
  local_tab |> Array.iter (release_temp env)

and translate_memloc env (seg, off, size) =
  let (seg', segw) = translate_expr env seg in
  check_width segw (T_bitvec 16);
  let (off', offw) = translate_expr env off in
  (* TODO: check offset width *)
  let w = translate_cexpr env.symtab size in
  seg', off', w

let translate_stmt env stmt =
  if debug then
    Format.printf "translating statement %a@." pp_aststmt stmt;
  let st = env.symtab in
  let do_assign loc (data, t) =
    begin match loc with
      | Lhs_var name ->
        begin match try_lookup st name with
          | None -> raise (Unbound_symbol name)
          | Some (Var (r, r_width)) ->
            emit env (S_set (r, data))
          | Some (PartialReg (g, part)) ->
            emit env (S_set (TV_Global g, E_prim2 (P2_updatepart part, E_var (TV_Global g), data)))
          | _ -> raise (Invalid_assignment name)
        end
      | Lhs_mem memloc ->
        let seg, off, mw = translate_memloc env memloc in
        let [@warning "-8"] T_bitvec w = t in
        check_width mw w;
        if w land 7 <> 0 then
          failwith "width of memory location is not multiple of 8";
        S_set (TV_Global Memory,
               E_prim3 (P3_store (w lsr 3), E_var (TV_Global Memory),
                        off, data)) |> emit env
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
    translate_call env proc args []
  | Stmt_jump addr ->
    let addr' = translate_expr env addr |> fst in
    emit env (S_jump (None, addr'))

let translate_proc st proc =
  if debug then
    Format.printf "translating procedure %s@." proc.ap_name;
  (* construct static environment to translate function body in *)
  let args =
    proc.ap_params |> List.map begin fun (name, te) ->
      let t = translate_typ st te in name, t
    end
  in
  let rets =
    proc.ap_results |> List.map begin fun (name, te) ->
      let t = translate_typ st te in name, t
    end
  in
  let ast_locals, stmts = proc.ap_body in
  let locals =
    ast_locals |> List.map begin fun (name, te) ->
      let t = translate_typ st te in name, t
    end
  in
  let env =
    st |>
    List.fold_right begin fun (i, name, typ) ->
      extend_symtab (name, Var (TV_Input i, typ))
    end (args |> List.mapi (fun i (name, typ) -> i, name, typ)) |>
    List.fold_right begin fun (i, name, typ) ->
      extend_symtab (name, Var (TV_Output i, typ))
    end (rets |> List.mapi (fun i (name, typ) -> i, name, typ)) |>
    List.fold_right begin fun (i, name, typ) ->
      extend_symtab (name, Var (TV_Local i, typ))
    end (locals |> List.mapi (fun i (name, typ) -> i, name, typ)) |>
    create
  in
  (* TODO: fix this mess *)
  let _ = locals |> List.map (fun (_, typ) -> acquire_temp env typ) in
  stmts |> List.iter (translate_stmt env);
  let temp_types =
    Array.sub env.temp_type_tab 0 (temp_count env) |> Array.to_list
  in
  let local_types = List.map snd locals @ temp_types in
  (* if debug then begin
    (* env.symtab |> Map.String.iter begin fun name value ->
      match value with
      | Var (tv, _) ->
        Printf.printf "%s → %s\n" name (string_of_templ_var tv)
      | _ -> ()
    end; *)
    local_types |> List.iter begin fun typ ->
      Format.printf "%a@." pp_typ typ
    end
  end; *)
  let split_snd l = l |> List.split |> snd in
  let body = List.rev env.stmts_rev in
  if debug then begin
    let open Format in
    printf "proc %s {\n" proc.ap_name;
    body |> List.iter (printf "\t%a\n" pp_stmt);
    printf "}@."
  end;
  { name = proc.ap_name; body;
    arg_types = split_snd args; ret_types = split_snd rets;
    local_types }

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
          ap_results = pt.pt_results }
      in
      let proc' = translate_proc inst_st proc in
      extend_symtab (proc.ap_name, Proc proc') st
  end (* init: *) init_symtab
