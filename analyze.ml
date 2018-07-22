open Batteries
open Semant
open Plain
open Pseudocode.Plain
open Cfg

let rec scan db va =
  if not (Database.has_cfg db va) then begin
    let cfg = Build_cfg.build_cfg db va in
    Database.set_cfg db va cfg;
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
    if !is_leaf then begin
      Printf.printf "leaf function: %nx\n" va
    end
  end

let find_stack_ref il =
  let module S = Set.Nativeint in
  let set = ref S.empty in
  let rec visit_addr_expr (ep, _ as e) =
    visit_expr e;
    match ep with
    | E_primn (Pn_add, [E_var (Var.Global R_ESP), _; E_lit bv, _]) ->
      set := S.add (Bitvec.to_nativeint bv) !set
    | E_var (Var.Global R_ESP) ->
      set := S.add 0n !set
    | _ -> ()
  and visit_expr (ep, _) =
    match ep with
    | E_lit _ -> ()
    | E_var _ -> ()
    | E_prim1 (_, e) -> visit_expr e
    | E_prim2 (_, e1, e2) -> visit_expr e1; visit_expr e2
    | E_prim3 (_, e1, e2, e3) -> visit_expr e1; visit_expr e2; visit_expr e3
    | E_primn (_, es) -> List.iter visit_expr es
    | E_load (_, _, off) -> visit_addr_expr off
    | E_nondet _ -> ()
    | E_extend (_, e, _) -> visit_expr e
    | E_shrink (e, _) -> visit_expr e
  in
  let rec visit = function
    | P_set (lv, e) ->
      begin match lv with
        | L_var _ -> ()
        | L_mem (_, off, _) -> visit_addr_expr off
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

let ssa cfg =
  let ssa_cfg = Dataflow.convert_to_ssa cfg in
  let changed = ref false in
  let rec loop () =
    if Dataflow.auto_subst ssa_cfg then changed := true;
    if Simplify.SSA.simplify_cfg ssa_cfg then changed := true;
    if Dataflow.remove_dead_code_ssa ssa_cfg then changed := true;
    if !changed then begin
      changed := false;
      loop ()
    end
  in
  loop ();
  let final_cfg = Dataflow.convert_from_ssa ssa_cfg in
  let final_cs = Fold_cfg.fold_cfg final_cfg in
  Pseudocode.Plain.(convert final_cs)

let print_il il =
  il |> List.iter (Pseudocode.Plain.pp_pstmt Format.std_formatter)

let get_stack_offset e =
  let open SSA in
  match e with
  | E_primn (Pn_add, [E_var { orig = Var.Global R_ESP; ver = 0; _ }, _;
                      E_lit offset, _]), _ -> Some (Bitvec.to_nativeint offset)
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
      | S_store (_, _, addr, (E_var { orig = Var.Global r; ver = 0; _ }, _)) ->
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
  cfg.exits |> Set.Int.iter begin fun i ->
    match List.last cfg.node.(i).stmts with
    | S_jumpout (_, arglist, _) ->
      arglist |> List.iter begin fun (r,e) ->
        let rid = Inst.int_of_reg r in
        if ok.(rid) then begin
          Format.printf "final value of %s is %a@." (Inst.string_of_reg r)
            pp_expr e;
          let ok' =
            match fst e with
            | E_var v ->
              begin match deftab.(SSAVar.to_int v) with
                | Some (S_set (_, (E_load (_, _, addr), _))) ->
                  begin match get_stack_offset addr with
                    | Some offset -> offset_table.(rid) = offset
                    | None -> false
                  end
                | _ -> false
              end
            | _ -> false
          in
          ok.(rid) <- ok'
        end
      end
    | _ -> failwith "last statement is not jumpout"
  end;
  List.range 0 `To (Inst.number_of_registers-1) |>
  List.filter_map begin fun i ->
    if ok.(i) then Some (Inst.reg_of_int i) else None
  end

let () =
  Elaborate.load_spec "spec"
