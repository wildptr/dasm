open Batteries
open Semant
open Normal
open Pseudocode
open CFG

let rec scan db va =
  if not (Database.has_proc db va) then begin
    let cfg = Build_cfg.build_cfg db va in
    let proc = Database.create_proc db va cfg in
    let is_complete = ref true in
    let is_leaf = ref true in
    cfg |> iter_stmt begin fun inst ->
      match inst.Inst.operation with
      | I_CALL ->
        is_leaf := false;
        begin match List.hd inst.Inst.operands with
          | O_imm (dst, _) ->
            (* Printf.printf "%nx calls %nx\n" va dst; *)
            scan db dst
          | _ -> ()
        end
      | _ -> ()
    end;
    cfg.exits |> Set.Int.iter begin fun i ->
      let last_inst = List.last cfg.node.(i).stmts in
      match last_inst.operation with
      | I_RET | I_RETN -> ()
      | _ -> is_complete := false
    end;
    proc.is_complete <- !is_complete;
    proc.is_leaf <- !is_leaf;
    proc.has_loop <- has_loop cfg
  end

(*
let find_stack_ref il =
  let module S = Set.Nativeint in
  let set = ref S.empty in
  let rec visit_addr_expr e =
    visit_expr e;
    match e with
    | E_prim2 (P2_add, (E_var (Global ESP)), (E_lit (BitvecLit, bv))) ->
      set := S.add (Bitvec.to_nativeint bv) !set
    | E_var (Global ESP) ->
      set := S.add 0n !set
    | _ -> ()
  and visit_expr = function
    | E_lit _ -> ()
    | E_const _ -> ()
    | E_var _ -> ()
    | E_nondet _ -> ()
    | E_prim1 (_, e) -> visit_expr e
    | E_prim2 (_, e1, e2) -> visit_expr e1; visit_expr e2
    | E_prim3 (_, e1, e2, e3) -> visit_expr e1; visit_expr e2; visit_expr e3
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
*)

let plain_il cfg =
  Dataflow.remove_dead_code_plain cfg;
  let cs = Fold_cfg.fold_cfg cfg in
  Pseudocode.convert cs

let simplify_ssa_cfg cfg =
  let changed = ref false in
  let rec loop () =
    if Dataflow.auto_subst cfg then changed := true;
(*     if Simplify.simplify_cfg cfg then changed := true; *)
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
  Pseudocode.convert final_cs

let print_il il =
  il |> List.iter (Pseudocode.pp_pstmt Format.std_formatter)

let get_stack_offset e =
  match e with
  | E_prim2 (P2_add, (E_var (Global ESP)),
             (E_lit (BitvecLit, offset))) -> Some (Bitvec.to_nativeint offset)
  | E_prim2 (P2_add, E_lit (BitvecLit, offset),
             E_var (Global ESP)) ->
    Some (Bitvec.to_nativeint offset)
  | _ -> None

let def_stmt_table (cfg : stmt cfg) =
  let tab = Array.create (var_count cfg) None in
  cfg |> iter_stmt begin fun s ->
    Dataflow.def_of_stmt s |> Set.Int.iter begin fun uid ->
      tab.(uid) <- Some s
    end
  end;
  tab

(*
let preserved_registers (cfg : stmt cfg) =
  let offset_table = Array.create number_of_globals 0n in
  let ok = Array.create number_of_globals false in
  cfg |> iter_stmt begin function
    | S_set (_, E_prim3 (P3_store _, _, addr, E_var (Global r))) ->
      begin match get_stack_offset addr with
        | Some offset ->
          Printf.printf "%s is stored at %nd\n" (string_of_global r) offset;
          let rid = int_of_global r in
          offset_table.(rid) <- offset;
          ok.(rid) <- true
        | None -> ()
      end
    | _ -> ()
  end;
  let deftab = def_stmt_table cfg in
  let rec ok' rid e =
    match e with
    | E_var v ->
      begin match deftab.(int_of_var v) with
        | Some (S_set (_, e')) -> ok' rid e'
        | _ -> false
      end
    | E_prim2 (P2_load _,  _, addr) ->
      begin match get_stack_offset addr with
        | Some offset -> offset_table.(rid) = offset
        | None -> false
      end
    | _ -> false
  in
  cfg.exits |> Set.Int.iter begin fun i ->
    match List.last cfg.node.(i).stmts with
    | S_ret (_, arglist) ->
      arglist |> List.iter begin fun (r,e) ->
        let rid = int_of_global r in
        if ok.(rid) then begin
          Format.printf "final value of %s is %a@." (string_of_global r)
            pp_expr e;
          ok.(rid) <- ok' rid e
        end
      end
    | _ -> failwith "last statement is not jumpout"
  end;
  all_globals |> List.filter_map begin fun r ->
    let i = int_of_global r in
    if ok.(i) then Some (global_of_int i) else None
  end

let defuse_of_proc (cfg : stmt cfg) =
  let def = Array.create number_of_globals false in
  let use = Array.create number_of_globals false in
  cfg.exits |> Set.Int.iter begin fun i ->
    match List.last cfg.node.(i).stmts with
    | S_ret (_, arglist) ->
      arglist |> List.iter begin fun (r,e) ->
        let rid = int_of_global r in
        match e with
        | E_var (Global r') when r = r' -> ()
        | _ -> def.(rid) <- true
      end
    | _ -> failwith "last statement is not jumpout"
  end;
  (* TODO: reduce code duplication *)
  let rec update_use (ep) =
    match ep with
    | E_lit _ -> ()
    | E_const _ -> ()
    | E_var sv ->
      begin match sv with
        | Global r ->
          use.(int_of_global r) <- true
        | _ -> ()
      end
    | E_nondet _ -> ()
    | E_prim1 (_, e) -> update_use e
    | E_prim2 (_, e1, e2) ->
      update_use e1; update_use e2
    | E_prim3 (_, e1, e2, e3) ->
      update_use e1; update_use e2; update_use e3
  in
  cfg |> iter_stmt begin function
    | S_set (_, e) -> update_use e
    | S_jump (cond_opt, e) ->
      begin match cond_opt with
        | Some cond -> update_use cond
        | None -> ()
      end;
      update_use e
    | S_call (e, arglist, _) ->
      update_use e;
      arglist |> List.iter (fun (r,v) -> update_use v)
    | S_ret _ -> ()
    | S_phi (_, rhs) ->
      rhs |> Hashtbl.iter (fun _ e -> update_use e)
    | _ -> assert false
  end;
  preserved_registers cfg |> List.iter begin fun r ->
    let rid = int_of_global r in
    def.(rid) <- false;
    use.(rid) <- false
  end;
  let deflist =
    all_globals |> List.filter_map begin fun r ->
      let i = int_of_global r in
      if def.(i) then Some r else None
    end
  in
  let uselist =
    all_globals |> List.filter_map begin fun r ->
      let i = int_of_global r in
      if use.(i) then Some r else None
    end
  in
  deflist, uselist
*)

let auto_analyze db entry =
  scan db entry;
  Database.get_proc_entry_list db |> List.iter begin fun va ->
    let proc = Database.get_proc db va in
    if proc.is_complete && proc.is_leaf then begin
      let ssa_cfg =
        proc.inst_cfg |>
        Elaborate.elaborate_cfg (Some db) |>
        Dataflow.convert_to_ssa db
      in
      simplify_ssa_cfg ssa_cfg
      (* let defs, uses = defuse_of_proc ssa_cfg in
      proc.defs <- defs;
      proc.uses <- uses *)
    end
  end

let () =
  Elaborate.load_spec "spec"
