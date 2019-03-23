open Batteries
open Cfg
open Semant
open Normal

module Trans = Transform(Var)(Var)
open Trans

module S = Set.Int

let def_of_stmt = function
  | S_set (v, _) -> S.singleton (int_of_var v)
  | S_phi (v, _) -> S.singleton (int_of_var v)
  | S_call (_, _, retlist) ->
    retlist |> List.map (fun (r,v) -> int_of_var v) |> S.of_list
  | S_ret _ -> S.empty
  | S_jump _ -> S.empty
  | S_jumpout _ -> S.empty

let count_uses_in_expr =
  let rec count t = function
    | E_lit _ -> ()
    | E_const _ -> ()
    | E_var v ->
      let vi = int_of_var v in
      t.(vi) <- t.(vi) + 1
    | E_nondet _ -> ()
    | E_prim1 (_, e) -> count t e
    | E_prim2 (_, e1, e2) -> count t e1; count t e2
    | E_prim3 (_, e1, e2, e3) -> count t e1; count t e2; count t e3
  in
  count

let rec use_of_expr = function
  | E_lit _ -> S.empty
  | E_const _ -> S.empty
  | E_var var -> S.singleton (int_of_var var)
  | E_nondet _ -> S.empty
  | E_prim1 (_, e) -> use_of_expr e
  | E_prim2 (_, e1, e2) -> S.union (use_of_expr e1) (use_of_expr e2)
  | E_prim3 (_, e1, e2, e3) ->
    (use_of_expr e3) |> S.union (use_of_expr e2) |> S.union (use_of_expr e1)

and uses_expr_list es =
  es |> List.map (use_of_expr) |> List.fold_left S.union S.empty

let use_of_stmt = function
  | S_set (_, e) -> use_of_expr e
  | S_call (e, l, _) ->
    l |> List.fold_left (fun acc (_, v) -> S.union acc (use_of_expr v))
      (use_of_expr e)
  | S_ret (e, l) ->
    l |> List.fold_left (fun acc (_, v) -> S.union acc (use_of_expr v))
      (use_of_expr e)
  | S_phi (_, rhs) ->
    rhs |> Hashtbl.values |> List.of_enum |> uses_expr_list
  | S_jump (e_opt, e) ->
    e_opt |> (function Some e -> use_of_expr e | None -> S.empty) |>
    S.union (use_of_expr e)
  | S_jumpout _ -> failwith "use_of_stmt: S_jumpout"

let count_uses_in_cfg cfg =
  let t = Array.make (var_count cfg) 0 in
  cfg |> iter_stmt begin function
    | S_set (_, e) -> count_uses_in_expr t e
    | S_call (dest, args, rets) ->
      count_uses_in_expr t dest;
      args |> List.iter (fun (_,e) -> count_uses_in_expr t e)
    | S_ret (dest, args) ->
      count_uses_in_expr t dest;
      args |> List.iter (fun (_,e) -> count_uses_in_expr t e)
    | S_phi (_, rhs) ->
      rhs |> Hashtbl.iter (fun _ e -> count_uses_in_expr t e)
    | S_jump (cond, dest) ->
      cond |> (function Some e -> count_uses_in_expr t e | _ -> ());
      count_uses_in_expr t dest
    | _ -> assert false
  end;
  t

let remove_dead_code_bb bb live_out =
  let stmt_arr = Array.of_list bb.stmts in
  let n = Array.length stmt_arr in
  let new_stmts = ref [] in
  let emit s = new_stmts := s :: !new_stmts in
  begin
    let live = Array.copy live_out in
    for i=n-1 downto 0 do
      let s = stmt_arr.(i) in
      s |> begin function
        | S_set (v, _) ->
          let uid = int_of_var v in
          if live.(uid) then emit s
        | S_phi (v, _) ->
          let uid = int_of_var v in
          if live.(uid) then emit s
        | S_call (dst, arglist, retlist) ->
          let retlist' =
            retlist |> List.filter begin fun (r,v) ->
              let uid = int_of_var v in live.(uid)
            end
          in
          S_call (dst, arglist, retlist') |> emit
        | _ -> emit s
      end;
      def_of_stmt s |> S.iter begin fun uid ->
        live.(uid) <- false
      end;
      use_of_stmt s |> S.iter (fun uid -> live.(uid) <- true)
    done
  end;
  bb.stmts <- !new_stmts

let compute_defsites cfg =
  let n = basic_block_count cfg in
  let n_var = var_count cfg in
  let defsites = Array.make n_var S.empty in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin fun stmt ->
      def_of_stmt stmt |> S.iter begin fun uid ->
        defsites.(uid) <- S.add i defsites.(uid)
      end
    end
  done;
  defsites

let defuse_of_bb stmts =
  let defs = ref S.empty in
  let uses = ref S.empty in
  stmts |> List.iter begin fun s ->
    uses := S.union !uses (S.diff (use_of_stmt s) !defs);
    def_of_stmt s |> S.iter (fun v -> defs := S.add v !defs);
  end;
  !defs, !uses

let postorder f cfg =
  let n = basic_block_count cfg in
  let vis = Array.make n false in
  let rec visit i =
    if not vis.(i) then begin
      vis.(i) <- true;
      cfg.succ.(i) |> List.iter visit;
      f i
    end
  in
  visit 0

let liveness cfg =
  let n = basic_block_count cfg in
  let defs = Array.make n S.empty in
  let uses = Array.make n S.empty in
  for i=0 to n-1 do
    let d, u = defuse_of_bb cfg.node.(i).stmts in
    defs.(i) <- d;
    uses.(i) <- u
  done;
  let live_in = Array.make n [||] in
  let live_out = Array.make n [||] in
  let n_var = var_count cfg in
  for i=0 to n-1 do
    live_in.(i) <- Array.make n_var false;
(*     live_out.(i) <- Array.make n_var (S.mem i cfg.exits) *)
    live_out.(i) <- Array.make n_var false;
  done;
  cfg.exits |> S.iter begin fun i ->
    for rid = 0 to number_of_globals - 1 do
      live_out.(i).(rid) <- true
    done
  end;
  let changed = ref false in
  let rec loop () =
    cfg |> postorder begin fun i ->
      let live_in_i = live_in.(i) in
      let live_out_i = live_out.(i) in
      for v=0 to n_var-1 do
        let lo =
          let temp = ref live_out_i.(v) in
          cfg.succ.(i) |> List.iter begin fun j ->
            if live_in.(j).(v) then temp := true
          end;
          !temp
        in
        if live_out_i.(v) <> lo then begin
          changed := true;
          live_out_i.(v) <- lo
        end;
        let li =
          S.mem v uses.(i) || (live_out_i.(v) && not (S.mem v defs.(i)))
        in
        if live_in_i.(v) <> li then begin
          changed := true;
          live_in_i.(v) <- li
        end
      done
    end;
    if !changed then begin
      changed := false;
      loop ()
    end
  in
  loop ();
  live_in, live_out

let remove_dead_code_plain cfg =
  let live_in, live_out = liveness cfg in
  for i = 0 to basic_block_count cfg - 1 do
    remove_dead_code_bb cfg.node.(i) live_out.(i)
  done

let auto_subst cfg =
  let n_var = var_count cfg in
  let def = Array.init n_var (fun i -> E_var (var_of_int i)) in
  let use_count = count_uses_in_cfg cfg in
  cfg |> iter_stmt begin function
    | S_set (v, e) ->
      let vi = int_of_var v in
      if
        use_count.(vi) = 1 ||
        begin match e with
          | E_var _ | E_lit _
          | E_prim1 (_, (E_var _ | E_lit _))
          | E_prim2 (_, (E_var _ | E_lit _), E_lit _)
          | E_prim2 (_, E_lit _, E_var _) -> true
          | _ -> false
        end
      then def.(vi) <- e
    | _ -> ()
  end;

  (* does not use another eliminated variable *)
  let expanded = Array.make n_var false in

  let rec replace v =
    let vi = int_of_var v in
    if expanded.(vi) then def.(vi)
    else begin
      let e = def.(vi) in
      if e = E_var v || use_of_expr e |> S.for_all (Array.get expanded) then
        (expanded.(vi) <- true; e)
      else
        let rec rec_subst e =
          let e' = subst replace e in
          if
            use_of_expr e |>
            S.for_all (fun i -> def.(i) = E_var (var_of_int i))
          then e' else rec_subst e'
        in
        let e' = rec_subst e in
        (def.(vi) <- e'; expanded.(vi) <- true; e')
    end
  in

  let changed = ref false in
  for i = 0 to basic_block_count cfg - 1 do
    cfg.node.(i).stmts <-
      cfg.node.(i).stmts |> List.filter_map begin fun stmt ->
        let stmt' =
          match stmt with
          | S_set (v, _) when def.(int_of_var v) <> E_var v -> None
          | _ -> Some (map_stmt (fun v -> v) (subst replace) stmt)
        in
        if not !changed && Some stmt <> stmt' then changed := true;
        stmt'
      end
  done;
  !changed

let remove_dead_code_ssa cfg =
  let n = basic_block_count cfg in
  let changed = ref false in
  let use_count = count_uses_in_cfg cfg in
  for i=0 to n-1 do
    cfg.node.(i).stmts <-
      cfg.node.(i).stmts |> List.filter begin fun stmt ->
        let live =
          match stmt with
          | S_set (lhs, _) ->
            let v = int_of_var lhs in
            use_count.(v) > 0
          | S_phi (lhs, _) ->
            let v = int_of_var lhs in
            use_count.(v) > 0
          | _ -> true
        in
        if not live then changed := true;
        live
      end
  done;
  !changed

let make_arglist =
  List.map (fun r -> r, E_var (Global r))

let jumpout_io db va_opt =
  let uses, defs =
    match va_opt with
    | Some va ->
      let proc = Database.get_proc db va in
      proc.uses, proc.defs
    | None -> all_globals, all_globals
  in
  let ins = make_arglist uses in
  let outs =
    defs |> List.map (fun r -> r, Global r)
  in
  ins, outs

let debug = false

let convert_to_ssa db cfg =
  let n = basic_block_count cfg in
  (* fields of the resulting CFG *)
  let node = Array.init n (fun i -> { cfg.node.(i) with stmts = [] }) in
  let succ = Array.copy cfg.succ in
  let pred = Array.copy cfg.pred in
  (* *)
  for i=0 to n-1 do
    node.(i).stmts <-
      cfg.node.(i).stmts |> List.map begin function
        | S_jumpout (dst, is_call) ->
          if is_call then
            let arglist, retlist =
              match dst with
              | E_lit (BitvecLit, dst_bv) ->
                jumpout_io db (Some (Bitvec.to_nativeint dst_bv))
              | _ ->
                jumpout_io db None
            in
            S_call (dst, arglist, retlist)
          else
            let arglist = make_arglist all_globals in
            S_ret (dst, arglist)
        | s -> s
      end
  done;
  let cfg' = { cfg with node } in
  (* place phi functions *)
  let idom = cfg.idom in
  let children = Array.make n [] in
  idom |> Array.iteri begin fun i p ->
    if p >= 0 then children.(p) <- i :: children.(p)
  end;
  let df = Array.make n [] in
  let rec compute_df i =
    let s = ref [] in
    succ.(i) |> List.iter (fun j -> if idom.(j) <> i then s := j :: !s);
    children.(i) |> List.iter begin fun c ->
      compute_df c;
      df.(c) |> List.iter begin fun w ->
        if not (dominates cfg i w) then s := w :: !s
      end
    end;
    df.(i) <- !s
  in
  compute_df 0;
  let n_var = var_count cfg in
  let defsites = compute_defsites cfg' in
  let live_in, live_out = liveness cfg' in
  for v = 0 to n_var - 1 do
    let phi_inserted_at = Array.make n false in
    let q = Queue.create () in
    defsites.(v) |> S.iter (fun defsite -> Queue.add defsite q);
    while not (Queue.is_empty q) do
      let i = Queue.pop q in
      df.(i) |> List.iter begin fun y ->
        if not phi_inserted_at.(y) && live_in.(i).(v) then begin
          let n_pred = List.length pred.(y) in
          let lhs = var_of_int v in
          let rhs = Hashtbl.create n_pred in
          let phi = S_phi (lhs, rhs) in
          pred.(y) |> List.iter begin fun j ->
            Hashtbl.add rhs node.(j).start (E_var lhs)
          end;
          (* actually insert phi function *)
          node.(y).stmts <- phi :: node.(y).stmts;
          phi_inserted_at.(y) <- true;
          if not (S.mem y defsites.(v)) then Queue.push y q
        end
      end
    done
  done;
  (* rename variables *)
  let current_ver = Array.init n_var var_of_int in
  let next_svid = ref n_var in
  (* types of variables created during conversion to SSA *)
  let type_tab = Hashtbl.create 0 in
  let get_next_svid typ =
    let i = !next_svid in
    incr next_svid;
    Hashtbl.add type_tab i typ;
    i
  in
  let rename_lhs v =
    let i = int_of_var v in
    assert (i < n_var); (* v is not renamed yet *)
    let v' = get_next_svid (type_of_var cfg.temp_tab v) |> var_of_int in
    current_ver.(i) <- v';
    v'
  in
  let rename_rhs v =
    current_ver.(int_of_var v)
  in
  let rename_rhs_in = subst (fun v -> E_var (rename_rhs v)) in
  let rec rename_bb i =
    if debug then
      Format.printf "@[<v>entering basic block %nx@," node.(i).start;
    let saved_ver = Array.copy current_ver in
    node.(i).stmts <- begin
      node.(i).stmts |> List.map begin function
        | S_set (v, e) ->
          S_set (rename_lhs v, rename_rhs_in e)
        | S_call (dst, arglist, retlist) ->
          let dst' = rename_rhs_in dst in
          let arglist' = arglist |> List.map (fun (r,v) -> r, rename_rhs_in v) in
          let retlist' = retlist |> List.map (fun (r,v) -> r, rename_lhs v) in
          S_call (dst', arglist', retlist')
        | S_ret (dst, arglist) ->
          let dst' = rename_rhs_in dst in
          let arglist' = arglist |> List.map (fun (r,v) -> r, rename_rhs_in v) in
          S_ret (dst', arglist')
        | S_phi (lhs, rhs) ->
          (* rhs is renamed later *)
          S_phi (rename_lhs lhs, rhs)
        | S_jump (cond, dest) ->
          S_jump (Option.map rename_rhs_in cond, rename_rhs_in dest)
        | _ -> assert false
      end
    end;
    (* rename variables in RHS of phi-functions *)
    succ.(i) |> List.iter begin fun j ->
      (* i -> j *)
      let i_addr = node.(i).start in
      node.(j).stmts |> List.iter begin function
        | S_phi (_, tab) ->
          assert (Hashtbl.mem tab i_addr);
          let rhs = Hashtbl.find tab i_addr in
          Hashtbl.replace tab i_addr (rename_rhs_in rhs)
        | _ -> ()
      end
    end;
    children.(i) |> List.iter begin fun j ->
      if debug then Format.printf "  ";
      rename_bb j;
      if debug then Format.printf "@,"
    end;
    if debug then Format.printf "leaving basic block %nx" node.(i).start;
    for i=0 to number_of_globals - 1 do
      current_ver.(i) <- saved_ver.(i)
    done;
    if debug then Format.printf "@]"
  in
  if debug then Format.printf "@[<v>";
  rename_bb 0;
  if debug then Format.printf "@.";
  let temp_tab = Array.create (!next_svid - number_of_globals) T_bool in
  cfg.temp_tab |> Array.iteri (fun i typ -> temp_tab.(i) <- typ);
  type_tab |> Hashtbl.iter begin fun i typ ->
    temp_tab.(i - number_of_globals) <- typ
  end;
  { node; succ; pred; idom; edges = cfg.edges; exits = cfg.exits; temp_tab }

let convert_from_ssa cfg =
  let n = basic_block_count cfg in
  let n_var = var_count cfg in
  let new_stmts = Array.make n [] in
  let emit i s = new_stmts.(i) <- s :: new_stmts.(i) in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | S_phi _ -> ()
      | S_call (dest, arglist, retlist) ->
        let arglist' =
          arglist |> List.filter (fun (r,v) -> v <> E_var (Global r))
        in
        let retlist' =
          retlist |> List.filter (fun (r,v) -> v <> Global r)
        in
        S_call (dest, arglist', retlist') |> emit i
      | S_ret (dest, arglist) ->
        arglist |> List.iter begin fun (r,e) ->
          if e <> E_var (Global r) then
            let v = var_of_int (n_var + int_of_global r) in
            emit i (S_set (v, e))
        end;
        S_ret (dest, []) |> emit i
      | S_set _ | S_jump _ as s -> emit i s
      | S_jumpout _ -> failwith "S_jumpout"
    end
  done;
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | S_phi (lhs, rhs) ->
        cfg.pred.(i) |> List.iter begin fun j ->
          (* j -> i *)
          let src_addr = cfg.node.(j).start in
          let assign =
            S_set (lhs, Hashtbl.find rhs src_addr)
          in
          begin match new_stmts.(j) with
            | (S_jump _ as jump) :: rest ->
              new_stmts.(j) <- jump :: assign :: rest
            | rest -> new_stmts.(j) <- assign :: rest
          end
        end
      | _ -> ()
    end
  done;
  let node =
    Array.init n begin fun i ->
      { cfg.node.(i) with stmts = List.rev new_stmts.(i) }
    end
  in
  let succ = Array.copy cfg.succ in
  let pred = Array.copy cfg.pred in
  let temp_tab =
    Array.make (Array.length cfg.temp_tab + number_of_globals) T_bool
  in
  let n_temp = Array.length cfg.temp_tab in
  Array.blit cfg.temp_tab 0 temp_tab 0 n_temp;
  for i=0 to number_of_globals-1 do
    temp_tab.(n_temp+i) <- type_of_global (global_of_int i)
  done;
  { cfg with node; succ; pred; temp_tab }
