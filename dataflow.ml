open Batteries
open Cfg
open List
open Semant

module S = Set.String

let all_register_names = S.of_array Inst.reg_name_table

let defs = function
  | S_set (lhs, _) -> Some lhs
  | S_phi (lhs, _) -> Some lhs
  | _ -> None

let defs' = function
  | S_set (lhs, _) -> S.singleton lhs
  | S_phi (lhs, _) -> S.singleton lhs
  | _ -> S.empty (* TODO: S_jump *)

let rec uses_expr = function
  | E_lit _ -> S.empty
  | E_var name -> S.singleton name
  | E_part (e, _, _) -> uses_expr e
  | E_prim1 (_, e) -> uses_expr e
  | E_prim2 (_, e1, e2) -> S.union (uses_expr e1) (uses_expr e2)
  | E_prim3 (_, e1, e2, e3) ->
    (uses_expr e3) |> S.union (uses_expr e2) |> S.union (uses_expr e1)
  | E_primn (_, es) -> uses_expr_list es
  | E_nondet _ -> S.empty
  | E_extend (_, e, _) -> uses_expr e
  | E_load (_, seg, off) -> S.union (uses_expr seg) (uses_expr off)

and uses_expr_list es =
  es |> map uses_expr |> fold_left S.union S.empty

let uses = function
  | S_set (_, e) -> uses_expr e
  | S_store (_, seg, off, data) ->
    uses_expr data |>
    S.union (uses_expr off) |>
    S.union (uses_expr seg)
  | S_jump (cond_opt, e) ->
    begin match cond_opt with
      | Some cond -> S.union (uses_expr cond) (uses_expr e)
      | None -> uses_expr e
    end (* TODO: use set is incomplete *)
  | S_phi (_, rhs) -> Array.to_list rhs |> uses_expr_list
  | _ -> assert false

let count_uses cfg =
  let use_count = Hashtbl.create 0 in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
(*     Format.eprintf "=== Basic block %d ===@." i; *)
    cfg.node.(i).stmts |> iter begin fun stmt ->
(*       Format.eprintf "%a uses [" pp_stmt stmt; *)
      uses stmt |> S.iter begin fun name ->
(*         Format.eprintf " %s" name; *)
        if Hashtbl.mem use_count name then
          Hashtbl.replace use_count name (Hashtbl.find use_count name + 1)
        else
          Hashtbl.add use_count name 1
      end;
(*       Format.eprintf " ]@." *)
    end
  done;
  fun name ->
    if Hashtbl.mem use_count name then Hashtbl.find use_count name else 0

let auto_subst cfg =
  let n = Array.length cfg.node in
(*   let use_count = count_uses cfg in *)
  let t = Hashtbl.create 0 in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter begin function
      | S_set (lhs, rhs) ->
        let subst =
          begin match rhs with
            | E_var _ | E_lit _ | E_part (E_var _, _, _) -> true
            | _ ->
              (*use_count lhs <= 1 ||*)
              String.length lhs >= 3 && String.sub lhs 0 3 = "ESP"
          end
        in
        if subst then begin
          let rhs' =
            rhs |> subst_expr begin fun name ->
              Hashtbl.find_option t name |> Option.default rhs
            end
          in
          Hashtbl.add t lhs rhs'
        end
      | _ -> ()
    end;
  done;

  if Hashtbl.is_empty t then false
  else begin
    let f name =
      if Hashtbl.mem t name then Hashtbl.find t name else (E_var name)
    in
    for i=0 to n-1 do
      cfg.node.(i).stmts <-
        cfg.node.(i).stmts |> filter_map begin fun stmt ->
          match stmt with
          | S_set (lhs, rhs) ->
            if Hashtbl.mem t lhs then None else Some (subst_stmt f stmt)
          | _ -> Some (subst_stmt f stmt)
        end
    done;
    true
  end

let remove_dead_code cfg =
  let n = Array.length cfg.node in
  let changed = ref false in
  let use_count = count_uses cfg in
  for i=0 to n-1 do
    cfg.node.(i).stmts <- begin
      cfg.node.(i).stmts |> filter begin fun stmt ->
        let live =
          match stmt with
          | S_jump _ | S_store _ -> true
          | _ ->
            begin match defs stmt with
              | Some name -> use_count name > 0
              | None -> true
            end
        in
        if not live then changed := true;
        live
      end
    end
  done;
  !changed

let get_rmid name = Inst.index_of_reg (Inst.lookup_reg name)

let get_rm_name rmid = Inst.reg_name_table.(rmid)

let compute_defs cfg =
  let size = Array.length cfg.node in
  let defs = Array.make Inst.number_of_registers Set.Int.empty in
  for i=0 to size-1 do
    cfg.node.(i).stmts |> iter begin fun stmt ->
      defs' stmt |> S.iter begin fun name ->
        begin match name.[0] with
          | 'A'..'Z' ->
            let rmid = get_rmid name in
            defs.(rmid) <- Set.Int.add i defs.(rmid)
          | _ -> ()
        end
      end
    end
  done;
  defs

exception Break

let convert_to_ssa cfg =
  (* place phi functions *)
  let size = Array.length cfg.node in
  let idom = Control_flow.compute_idom cfg.succ cfg.pred in
  let children = Array.make size [] in
  let df = Array.make size [] in
  let rec dominates x y =
    if x = y then true
    else
      let dy = idom.(y) in
      if dy < 0 then false
      else dominates x dy
  in
  idom |> Array.iteri begin fun n p ->
    if p >= 0 then children.(p) <- n :: children.(p)
  end;
  let rec compute_df n =
    let s = ref [] in
    cfg.succ.(n) |> iter (fun y -> if idom.(y) <> n then s := y :: !s);
    children.(n) |> iter begin fun c ->
      compute_df c;
      df.(c) |> iter (fun w -> if not (dominates n w) then s := w :: !s)
    end;
    df.(n) <- !s
  in
  compute_df 0;
  let defs = compute_defs cfg in
  for rmid = 0 to Inst.number_of_registers - 1 do
    let phi_inserted_at = Array.make size false in
    let worklist = Queue.create () in
    defs.(rmid) |> Set.Int.iter (fun defsite -> Queue.add defsite worklist);
    while not (Queue.is_empty worklist) do
      let n = Queue.pop worklist in
      df.(n) |> iter begin fun y ->
        if not phi_inserted_at.(y) then begin
          let n_pred = length cfg.pred.(y) in
          let phi =
            S_phi (get_rm_name rmid, Array.make n_pred (E_var (get_rm_name rmid)))
          in
          cfg.node.(y).stmts <- phi :: cfg.node.(y).stmts;
          phi_inserted_at.(y) <- true;
          if not (Set.Int.mem y defs.(rmid)) then Queue.push y worklist
        end
      end
    done
  done;
  (* rename variables *)
  let count = Array.make Inst.number_of_registers 0 in
  let stack = Array.make Inst.number_of_registers [0] in
  let rename_rhs name =
    match name.[0] with
    | 'A'..'Z' ->
      let rmid = get_rmid name in
      let i = hd stack.(rmid) in
      name ^ "_" ^ string_of_int i
    | _ -> name
  in
  let rec rename n =
    (*Format.(fprintf err_formatter "[%d]@." n);*)
    let rename_lhs name =
      match name.[0] with
      | 'A'..'Z' ->
        let rmid = get_rmid name in
        let i = count.(rmid) + 1 in
        count.(rmid) <- i;
        stack.(rmid) <- i :: stack.(rmid);
        name ^ "_" ^ string_of_int i
      | _ -> name
    in
    let new_stmts = ref [] in
    cfg.node.(n).stmts |> iter begin fun stmt ->
      let new_stmt =
        match stmt with
        | S_set (name, e) ->
          let e' = rename_variables rename_rhs e in
          let name' = rename_lhs name in
          S_set (name', e')
        | S_store (size, seg, off, data) ->
          let seg' = rename_variables rename_rhs seg in
          let off' = rename_variables rename_rhs off in
          let data' = rename_variables rename_rhs data in
          S_store (size, seg', off', data')
        | S_jump (c, dst) ->
          let c' = Option.map (rename_variables rename_rhs) c in
          let dst' = rename_variables rename_rhs dst in
          S_jump (c', dst')
        | S_phi (lhs, rhs) -> S_phi (rename_lhs lhs, rhs)
        | _ -> assert false
      in
      (*Format.(fprintf err_formatter "%a -> %a@." pp_stmt stmt pp_stmt new_stmt);*)
      new_stmts := new_stmt :: !new_stmts
    end;
    let old_stmts = cfg.node.(n).stmts in
    cfg.node.(n).stmts <- rev !new_stmts;
    (* rename variables in RHS of phi-functions *)
    cfg.succ.(n) |> iter begin fun y ->
      (* n is the j-th predecessor of y *)
      let j =
        match index_of n cfg.pred.(y) with
        | Some i -> i
        | None -> assert false
      in
      begin
        try
          cfg.node.(y).stmts |> iter begin function
            | S_phi (_, rhs) -> rhs.(j) <- rename_variables rename_rhs rhs.(j)
            | _ -> raise Break
          end;
        with Break -> ()
      end
    end;
    children.(n) |> iter rename;
    old_stmts |> iter begin fun stmt ->
      defs' stmt |> S.iter begin fun name ->
        begin match name.[0] with
          | 'A'..'Z' ->
            let rmid = get_rmid name in
            stack.(rmid) <- tl stack.(rmid)
          | _ -> ()
        end
      end
    end
  in
  rename 0
