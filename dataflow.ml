open Batteries
open Cfg
open Semant

module S = Set.Int

let var_count cfg =
  Inst.number_of_registers + Array.length cfg.temp_tab

module DefUse(V : VarType) = struct

  module Sem = Semant.Make(V)
  open Sem

  let def_of_stmt = function
    | S_set (lhs, _) -> S.singleton (V.to_int lhs)
    | S_phi (lhs, _) -> S.singleton (V.to_int lhs)
    | S_jumpout_call (_, _, retlist) ->
      retlist |> List.map (fun (r,v) -> V.to_int v) |> S.of_list
    | _ -> S.empty

  let rec use_of_expr = function
    | E_lit _ -> S.empty
    | E_const _ -> S.empty
    | E_var var -> S.singleton (V.to_int var)
    | E_prim1 (_, e) -> use_of_expr e
    | E_prim2 (_, e1, e2) -> S.union (use_of_expr e1) (use_of_expr e2)
    | E_prim3 (_, e1, e2, e3) ->
      (use_of_expr e3) |> S.union (use_of_expr e2) |> S.union (use_of_expr e1)
    | E_nondet _ -> S.empty
    | E_extend (_, e, _) -> use_of_expr e
    | E_shrink (e, _) -> use_of_expr e
    | E_load (_, addr) -> (use_of_expr addr)

  and uses_expr_list es =
    es |> List.map (use_of_expr) |> List.fold_left S.union S.empty

  let use_of_stmt = function
    | S_set (_, e) -> use_of_expr e
    | S_store (_, addr, data) ->
      use_of_expr data |>
      S.union (use_of_expr addr)
    | S_jump (cond_opt, e) ->
      begin match cond_opt with
        | Some cond -> S.union (use_of_expr cond) (use_of_expr e)
        | None -> use_of_expr e
      end
    | S_jumpout (e, _) -> use_of_expr e
    | S_jumpout_call (e, l, _) ->
      l |> List.fold_left (fun acc (_, v) -> S.union acc (use_of_expr v))
        (use_of_expr e)
    | S_jumpout_ret (e, l) ->
      l |> List.fold_left (fun acc (_, v) -> S.union acc (use_of_expr v))
        (use_of_expr e)
(*     | S_jumpout_ret (e, _) -> use_of_expr e *)
    | S_phi (_, rhs) ->
      rhs |> Hashtbl.values |> List.of_enum |> uses_expr_list
    | _ -> assert false

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
          | S_set (lhs, _) ->
            let uid = V.to_int lhs in
            if live.(uid) then emit s
          | S_phi (lhs, _) ->
            let uid = V.to_int lhs in
            if live.(uid) then emit s
          | S_jumpout_call (dst, arglist, retlist) ->
            let retlist' =
              retlist |> List.filter begin fun (r,v) ->
                let uid = V.to_int v in live.(uid)
              end
            in
            S_jumpout_call (dst, arglist, retlist') |> emit
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
    let size = Array.length cfg.node in
    let n_var = var_count cfg in
    let defsites = Array.make n_var S.empty in
    for i=0 to size-1 do
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

end

module PlainDefUse = DefUse(Var)
module SSADefUse = DefUse(SSAVar)

module SSAToSSA = Transform(SSAVar)(SSAVar)
module PlainToSSA = Transform(Var)(SSAVar)
module SSAToPlain = Transform(SSAVar)(Var)

let postorder f cfg =
  let n = Array.length cfg.node in
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
  let n = Array.length cfg.node in
  let defs = Array.make n S.empty in
  let uses = Array.make n S.empty in
  for i=0 to n-1 do
    let d, u = PlainDefUse.defuse_of_bb cfg.node.(i).stmts in
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
    for rid = 0 to Inst.number_of_registers - 1 do
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
(*
  for i=0 to n-1 do
    Printf.printf "live_out[%d]:" i;
    for v=0 to n_var-1 do
      if live_out.(i).(v) then Format.printf " %a" Var.pp (Var.of_int v)
    done;
    print_endline ""
  done;
*)
  live_in, live_out

let remove_dead_code_plain cfg =
  let n = Array.length cfg.node in
  let live_in, live_out = liveness cfg in
  for i=0 to n-1 do
    PlainDefUse.remove_dead_code_bb cfg.node.(i) live_out.(i)
  done

let count_uses cfg =
  let n_var = var_count cfg in
  let use_count = Array.make n_var 0 in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin fun s ->
      s |> SSADefUse.use_of_stmt |>
      S.iter (fun v -> use_count.(v) <- use_count.(v) + 1)
    end
  done;
  use_count

let auto_subst cfg =
  let open SSA in
  let n = Array.length cfg.node in
  let n_var = var_count cfg in
  let rep = Array.make n_var None in
  let use_count = count_uses cfg in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | S_set (lhs, rhs) ->
        let v = SSAVar.to_int lhs in
        let ok =
          use_count.(v) = 1 ||
          begin match rhs with
            | E_var _ | E_lit _ -> true
            | _ -> lhs.SSAVar.orig = Var.Global R_ESP
          end
        in
        if ok then begin
          let rhs' =
            rhs |> SSAToSSA.subst begin fun sv ->
              let v' = SSAVar.to_int sv in
              rep.(v') |> Option.default (E_var sv)
            end
          in
          rep.(v) <- Some rhs'
        end
      | _ -> ()
    end;
  done;

  let f sv =
    let v = SSAVar.to_int sv in
    rep.(v) |> Option.default (E_var sv)
  in
  let changed = ref false in
  for i=0 to n-1 do
    cfg.node.(i).stmts <-
      cfg.node.(i).stmts |> List.filter_map begin fun stmt ->
        let stmt' =
          match stmt with
          | S_set (lhs, _) when rep.(SSAVar.to_int lhs) <> None -> None
          | _ -> Some (SSAToSSA.map_stmt (fun v -> v) (SSAToSSA.subst f) stmt)
        in
        if Some stmt <> stmt' then changed := true;
        stmt'
      end
  done;
  !changed

let remove_dead_code_ssa cfg =
  let open SSA in

  let n = Array.length cfg.node in
  let changed = ref false in
  let use_count = count_uses cfg in
  for i=0 to n-1 do
    cfg.node.(i).stmts <-
      cfg.node.(i).stmts |> List.filter begin fun stmt ->
        let live =
          match stmt with
          | S_set (lhs, _) ->
            let v = SSAVar.to_int lhs in
            use_count.(v) > 0
          | S_phi (lhs, _) ->
            let v = SSAVar.to_int lhs in
            use_count.(v) > 0
          | _ -> true
        in
        if not live then changed := true;
        live
      end
  done;
  !changed

let make_arglist =
  List.map (fun r -> r, Plain.E_var (Var.Global r))

let jumpout_io db va_opt =
  let uses, defs =
    match va_opt with
    | Some va ->
      let proc = Database.get_proc db va in
      proc.uses, proc.defs
    | None -> Inst.all_registers, Inst.all_registers
  in
  let ins = make_arglist uses in
  let outs =
    defs |> List.map (fun r -> r, Var.Global r)
  in
  ins, outs

let debug = false

let convert_to_ssa db cfg =
  let size = Array.length cfg.node in
  (* fields of the resulting CFG *)
  let node = cfg.node |> Array.map (fun bb -> { bb with stmts = [] }) in
  let succ = Array.copy cfg.succ in
  let pred = Array.copy cfg.pred in
  (* place phi functions *)
  let idom = cfg.idom in
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
    succ.(n) |> List.iter (fun y -> if idom.(y) <> n then s := y :: !s);
    children.(n) |> List.iter begin fun c ->
      compute_df c;
      df.(c) |> List.iter (fun w -> if not (dominates n w) then s := w :: !s)
    end;
    df.(n) <- !s
  in
  compute_df 0;
  let n_var = var_count cfg in
  let defsites = PlainDefUse.compute_defsites cfg in
  let live_in, live_out = liveness cfg in
  for v = 0 to n_var - 1 do
    let phi_inserted_at = Array.make size false in
    let q = Queue.create () in
    defsites.(v) |> S.iter (fun defsite -> Queue.add defsite q);
    while not (Queue.is_empty q) do
      let i = Queue.pop q in
      df.(i) |> List.iter begin fun y ->
        if not phi_inserted_at.(y) && live_in.(i).(v) then begin
          let n_pred = List.length pred.(y) in
          let lhs = Var.of_int v in
          let phi = Plain.(S_phi (lhs, Hashtbl.create n_pred)) in
          (* actually insert phi function *)
          cfg.node.(y).stmts <- phi :: cfg.node.(y).stmts;
          phi_inserted_at.(y) <- true;
          if not (S.mem y defsites.(v)) then Queue.push y q
        end
      end
    done
  done;
  (* rename variables *)
  let next_ver = Array.make n_var 0 in
  let current_ver = Array.make n_var 0 in
  let svid_table = Hashtbl.create 0 in
  let sv_table = Hashtbl.create 0 in
  let next_svid = ref 0 in
  let get_svid k =
    try Hashtbl.find svid_table k
    with Not_found ->
      let uid = !next_svid in
      incr next_svid;
      Hashtbl.add svid_table k uid;
      Hashtbl.add sv_table uid k;
      uid
  in
  let rename_lhs sv =
    let open SSAVar in
    let orig = sv.orig in
    let orig_uid = Var.to_int orig in
    let ver = next_ver.(orig_uid) + 1 in
    if debug then
      Format.printf "%a: %d -> %d@," Var.pp orig current_ver.(orig_uid) ver;
    next_ver.(orig_uid) <- ver;
    current_ver.(orig_uid) <- ver;
    let uid = get_svid (orig_uid, ver) in
    SSAVar.{ orig; ver; uid }
  in
  let rename_rhs sv =
    let open SSAVar in
    let orig = sv.orig in
    let orig_uid = Var.to_int orig in
    let ver = current_ver.(orig_uid) in
    let uid = get_svid (orig_uid, ver) in
    SSAVar.{ orig; ver; uid }
  in
  for i=0 to size-1 do
    let f orig = SSAVar.{ orig; ver=0; uid=0 } in
    let stmts' = ref [] in
    cfg.node.(i).stmts |> List.iter begin fun stmt ->
      let stmt' =
        match stmt with
        | Plain.S_set (name, e) ->
          let e' = PlainToSSA.rename_var f e in
          let name' = f name in
          SSA.S_set (name', e')
        | Plain.S_store (size, off, data) ->
          let off' = PlainToSSA.rename_var f off in
          let data' = PlainToSSA.rename_var f data in
          SSA.S_store (size, off', data')
        | Plain.S_jump (c, dst) ->
          let c' = Option.map (PlainToSSA.rename_var f) c in
          let dst' = PlainToSSA.rename_var f dst in
          SSA.S_jump (c', dst')
        | Plain.S_jumpout (dst, j) ->
          let dst' = PlainToSSA.rename_var f dst in
          if j then
            let arglist, retlist =
              match dst with
              | Plain.E_lit (BitvecLit, dst_bv) ->
                jumpout_io db (Some (Bitvec.to_nativeint dst_bv))
              | _ ->
                jumpout_io db None
            in
            let arglist' =
              arglist |> List.map (fun (r,v) -> r, PlainToSSA.rename_var f v)
            in
            let retlist' = retlist |> List.map (fun (r,v) -> r, f v) in
            SSA.S_jumpout_call (dst', arglist', retlist')
          else
            let arglist = make_arglist Inst.all_registers in
            let arglist' =
              arglist |> List.map (fun (r,v) -> r, PlainToSSA.rename_var f v)
            in
            SSA.S_jumpout_ret (dst', arglist')
        | Plain.S_phi (lhs, rhs) ->
          let lhs' = f lhs in
          let n = Hashtbl.length rhs in
          SSA.S_phi (lhs', Hashtbl.create n)
        | _ -> assert false
      in
      stmts' := stmt' :: !stmts'
    end;
    node.(i).stmts <- List.rev !stmts'
  done;
  let rec rename_bb i =
    if debug then
      Format.printf "@[<v>entering basic block %nx@," cfg.node.(i).start;
    let saved_ver = Array.copy current_ver in
    let open SSA in
    let sub = SSAToSSA.subst (fun sv -> E_var (rename_rhs sv)) in
    node.(i).stmts <- begin
      node.(i).stmts |> List.map begin function
        | S_set (sv, e) ->
          let e' = sub e in
          let name' = rename_lhs sv in
          S_set (name', e')
        | S_store (size, off, data) ->
          let off' = sub off in
          let data' = sub data in
          S_store (size, off', data')
        | S_jump (c, dst) ->
          let c' = Option.map sub c in
          let dst' = sub dst in
          S_jump (c', dst')
        | S_jumpout_call (dst, arglist, retlist) ->
          let dst' = sub dst in
          let arglist' = arglist |> List.map (fun (r,v) -> r, sub v) in
          let retlist' = retlist |> List.map (fun (r,v) -> r, rename_lhs v) in
          S_jumpout_call (dst', arglist', retlist')
        | S_jumpout_ret (dst, arglist) ->
          let dst' = sub dst in
          let arglist' = arglist |> List.map (fun (r,v) -> r, sub v) in
          S_jumpout_ret (dst', arglist')
        | S_phi (lhs, rhs) ->
          let lhs' = rename_lhs lhs in
          S_phi (lhs', rhs)
        | _ -> assert false
      end
    end;
    (* rename variables in RHS of phi-functions *)
    succ.(i) |> List.iter begin fun j ->
      (* i -> j *)
      let i_addr = cfg.node.(i).start in
      node.(j).stmts |> List.iter begin function
        | SSA.S_phi (lhs, rhs) ->
          let open SSAVar in
          assert (Hashtbl.mem rhs i_addr |> not);
          SSA.E_var lhs |>
          SSAToSSA.subst (fun sv -> SSA.E_var (rename_rhs sv)) |>
          Hashtbl.add rhs i_addr
        | _ -> ()
      end
    end;
    children.(i) |> List.iter begin fun j ->
      if debug then Format.printf "  ";
      rename_bb j;
      if debug then Format.printf "@,"
    end;
    if debug then Format.printf "leaving basic block %nx" cfg.node.(i).start;
    for i=0 to Inst.number_of_registers-1 do
      current_ver.(i) <- saved_ver.(i)
    done;
    if debug then Format.printf "@]"
  in
  if debug then Format.printf "@[<v>";
  rename_bb 0;
  if debug then Format.printf "@.";
  let temp_tab =
    Array.init !next_svid begin fun i ->
      let orig, ver = Hashtbl.find sv_table i in
      if orig < Inst.number_of_registers then
        type_of_reg (Inst.reg_of_int orig)
      else
        cfg.temp_tab.(orig - Inst.number_of_registers)
    end
  in
  { node; succ; pred; edges = cfg.edges; exits = cfg.exits; temp_tab }

let convert_stmt_from_ssa f s =
  let open Plain in
  match SSAToPlain.map_stmt f (SSAToPlain.rename_var f) s with
  | S_jumpout_call (dest, arglist, retlist) ->
    let arglist' =
      arglist |> List.filter (fun (r,v) -> v <> E_var (Var.Global r))
    in
    let retlist' =
      retlist |> List.filter (fun (r,v) -> v <> Var.Global r)
    in
    S_jumpout_call (dest, arglist', retlist')
  | S_jumpout_ret (dest, arglist) ->
    let arglist' =
      arglist |> List.filter (fun (r,v) -> v <> E_var (Var.Global r))
    in
    S_jumpout_ret (dest, arglist')
  | s -> s

let convert_from_ssa cfg =
  let n = Array.length cfg.node in
  let new_stmts = Array.make n [] in
  let svar_to_pvar sv =
    let open SSAVar in
    match sv with
    | { orig = (Var.Global _ as pv); ver = 0; _ } -> pv
    | { orig = (Var.Global _); _ } ->
      Var.Local (Format.asprintf "%a" SSAVar.pp sv)
    | _ ->
      Var.Local (Printf.sprintf "$%d" sv.uid)
  in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | SSA.S_phi _ -> ()
      | s ->
        let emit s = new_stmts.(i) <- s :: new_stmts.(i) in
        convert_stmt_from_ssa svar_to_pvar s |> emit
    end
  done;
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | SSA.S_phi (lhs, rhs) ->
        let open SSAVar in
        let rhs' =
          rhs |> Hashtbl.map
            (fun _ e -> (SSAToPlain.rename_var svar_to_pvar e))
        in
        cfg.pred.(i) |> List.iter begin fun j ->
          (* j -> i *)
          let src_addr = cfg.node.(j).start in
          let assign =
            Plain.S_set (svar_to_pvar lhs, Hashtbl.find rhs' src_addr)
          in
          begin match new_stmts.(j) with
            | (Plain.S_jump _ as jump) :: rest ->
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
  { cfg with node; succ; pred }
