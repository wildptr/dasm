open Batteries
open Semant
open Plain
open Pseudocode.Plain
open Cfg

let rec scan db va =
  if not (Database.has_proc db va) then begin
    let cfg = Build_cfg.build_cfg db va in
    let proc = Database.create_proc db va cfg in
    let is_complete = ref true in
    let is_leaf = ref true in
    let n = Array.length cfg.node in
    for i=0 to n-1 do
      cfg.node.(i).stmts |> List.iter begin fun inst ->
        match inst.Inst.operation with
        | I_CALL ->
          is_leaf := false;
          begin match List.hd inst.Inst.operands with
            | O_imm (dst, _) ->
              Printf.printf "%nx calls %nx\n" va dst;
              scan db dst
            | _ -> ()
          end
        | _ -> ()
      end
    done;
    cfg.exits |> Set.Int.iter begin fun i ->
      let last_inst = List.last cfg.node.(i).stmts in
      match last_inst.operation with
      | I_RET | I_RETN -> ()
      | _ -> is_complete := false
    end;
    proc.is_complete <- !is_complete;
    proc.is_leaf <- !is_leaf
  end

let find_stack_ref il =
  let module S = Set.Nativeint in
  let set = ref S.empty in
  let rec visit_addr_expr e =
    visit_expr e;
    match e with
    | E_prim2 (P2_add, (E_var (Var.Global R_ESP)), (E_lit bv)) ->
      set := S.add (Bitvec.to_nativeint bv) !set
    | E_var (Var.Global R_ESP) ->
      set := S.add 0n !set
    | _ -> ()
  and visit_expr = function
    | E_lit _ -> ()
    | E_lit_bool _ -> ()
    | E_const _ -> ()
    | E_var _ -> ()
    | E_prim1 (_, e) -> visit_expr e
    | E_prim2 (_, e1, e2) -> visit_expr e1; visit_expr e2
    | E_prim3 (_, e1, e2, e3) -> visit_expr e1; visit_expr e2; visit_expr e3
    | E_load (_, off) -> visit_addr_expr off
    | E_nondet _ -> ()
    | E_extend (_, e, _) -> visit_expr e
    | E_shrink (e, _) -> visit_expr e
  in
  let rec visit = function
    | P_set (lv, e) ->
      begin match lv with
        | L_var _ -> ()
        | L_mem (off, _) -> visit_addr_expr off
      end;
      visit_expr e
    | P_goto e -> visit_expr e
    | P_if (cond, body) -> visit_expr cond; List.iter visit body
    | P_if_else (cond, body1, body2) ->
      visit_expr cond; List.iter visit body1; List.iter visit body2
    | P_do_while (body, cond) ->
      List.iter visit body; visit_expr cond
    | _ -> ()
  in
  il |> List.iter visit;
  !set

let plain_il cfg =
  Dataflow.remove_dead_code_plain cfg;
  let cs = Fold_cfg.fold_cfg cfg in
  Pseudocode.Plain.(convert cs)

let simplify_ssa_cfg cfg =
  let changed = ref false in
  let rec loop () =
    if Dataflow.auto_subst cfg then changed := true;
    if Simplify.SSA.simplify_cfg cfg then changed := true;
    if Dataflow.remove_dead_code_ssa cfg then changed := true;
    if !changed then begin
      changed := false;
      loop ()
    end
  in
  loop ()

let ssa db cfg =
  let ssa_cfg = Dataflow.convert_to_ssa db cfg in
  simplify_ssa_cfg ssa_cfg;
  let final_cfg = Dataflow.convert_from_ssa ssa_cfg in
  let final_cs = Fold_cfg.fold_cfg final_cfg in
  Pseudocode.Plain.(convert final_cs)

let print_il il =
  il |> List.iter (Pseudocode.Plain.pp_pstmt Format.std_formatter)

let get_stack_offset e =
  let open SSA in
  match e with
  | E_prim2 (P2_add, (E_var { orig = Var.Global R_ESP; ver = 0; _ }),
             (E_lit offset)) -> Some (Bitvec.to_nativeint offset)
  | E_prim2 (P2_add, E_lit offset,
             E_var { orig = Var.Global R_ESP; ver = 0; _ }) ->
    Some (Bitvec.to_nativeint offset)
  | _ -> None

let def_stmt_table (cfg : SSA.stmt cfg) =
  let nvar = Array.length cfg.temp_tab in
  let tab = Array.create nvar None in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin fun s ->
      Dataflow.SSADefUse.def_of_stmt s |> Set.Int.iter begin fun uid ->
        tab.(uid) <- Some s
      end
    end
  done;
  tab

let preserved_registers (cfg : SSA.stmt cfg) =
  let open SSA in
  let n = Array.length cfg.node in
  let offset_table = Array.create Inst.number_of_registers 0n in
  let ok = Array.create Inst.number_of_registers false in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | S_store (_, addr, (E_var { orig = Var.Global r; ver = 0; _ })) ->
        begin match get_stack_offset addr with
          | Some offset ->
            Printf.printf "%s is stored at %nd\n" (Inst.string_of_reg r) offset;
            let rid = Inst.int_of_reg r in
            offset_table.(rid) <- offset;
            ok.(rid) <- true
          | None -> ()
        end
      | _ -> ()
    end
  done;
  let deftab = def_stmt_table cfg in
  let rec ok' rid e =
    match e with
    | E_var v ->
      begin match deftab.(SSAVar.to_int v) with
        | Some (S_set (_, e')) -> ok' rid e'
        | _ -> false
      end
    | E_load (_, addr) ->
      begin match get_stack_offset addr with
        | Some offset -> offset_table.(rid) = offset
        | None -> false
      end
    | _ -> false
  in
  cfg.exits |> Set.Int.iter begin fun i ->
    match List.last cfg.node.(i).stmts with
    | S_jumpout_ret (_, arglist) ->
      arglist |> List.iter begin fun (r,e) ->
        let rid = Inst.int_of_reg r in
        if ok.(rid) then begin
          Format.printf "final value of %s is %a@." (Inst.string_of_reg r)
            pp_expr e;
          ok.(rid) <- ok' rid e
        end
      end
    | _ -> failwith "last statement is not jumpout"
  end;
  Inst.all_registers |> List.filter_map begin fun r ->
    let i = Inst.int_of_reg r in
    if ok.(i) then Some (Inst.reg_of_int i) else None
  end

let defuse_of_proc (cfg : SSA.stmt cfg) =
  let open SSA in
  let def = Array.create Inst.number_of_registers false in
  let use = Array.create Inst.number_of_registers false in
  cfg.exits |> Set.Int.iter begin fun i ->
    match List.last cfg.node.(i).stmts with
    | S_jumpout_ret (_, arglist) ->
      arglist |> List.iter begin fun (r,e) ->
        let rid = Inst.int_of_reg r in
        match e with
        | E_var { orig; ver = 0; _ } when orig = Var.Global r -> ()
        | _ -> def.(rid) <- true
      end
    | _ -> failwith "last statement is not jumpout"
  end;
  let n = Array.length cfg.node in
  (* TODO: reduce code duplication *)
  let rec update_use (ep) =
    match ep with
    | E_lit _ -> ()
    | E_lit_bool _ -> ()
    | E_const _ -> ()
    | E_var sv ->
      begin match sv with
        | { orig = Var.Global r; ver = 0; _ } ->
          use.(Inst.int_of_reg r) <- true
        | _ -> ()
      end
    | E_prim1 (_, e) -> update_use e
    | E_prim2 (_, e1, e2) ->
      update_use e1; update_use e2
    | E_prim3 (_, e1, e2, e3) ->
      update_use e1; update_use e2; update_use e3
    | E_nondet _ -> ()
    | E_extend (_, e, _) -> update_use e
    | E_shrink (e, _) -> update_use e
    | E_load (_, off) ->
      update_use off
  in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | S_set (_, e) -> update_use e
      | S_store (_, off, data) ->
        update_use off; update_use data
      | S_jump (cond_opt, e) ->
        begin match cond_opt with
          | Some cond -> update_use cond
          | None -> ()
        end;
        update_use e
      | S_jumpout_call (e, arglist, _) ->
        update_use e;
        arglist |> List.iter (fun (r,v) -> update_use v)
      | S_jumpout_ret _ -> ()
      | S_phi (_, rhs) ->
        rhs |> Array.iter update_use
      | _ -> assert false
    end
  done;
  preserved_registers cfg |> List.iter begin fun r ->
    let rid = Inst.int_of_reg r in
    def.(rid) <- false;
    use.(rid) <- false
  end;
  let deflist =
    Inst.all_registers |> List.filter_map begin fun r ->
      let i = Inst.int_of_reg r in
      if def.(i) then Some r else None
    end
  in
  let uselist =
    Inst.all_registers |> List.filter_map begin fun r ->
      let i = Inst.int_of_reg r in
      if use.(i) then Some r else None
    end
  in
  deflist, uselist

let auto_analyze db entry =
  scan db entry;
  Database.get_proc_entry_list db |> List.iter begin fun va ->
    let proc = Database.get_proc db va in
    if proc.is_complete && proc.is_leaf then begin
      let ssa_cfg =
        proc.inst_cfg |>
        Elaborate.elaborate_cfg db |>
        Dataflow.convert_to_ssa db
      in
      simplify_ssa_cfg ssa_cfg;
      let defs, uses = defuse_of_proc ssa_cfg in
      proc.defs <- defs;
      proc.uses <- uses
    end
  end

let () =
  Elaborate.load_spec "spec"
