open Batteries
open Cfg
open List
open Semant

module S = Set.Int

module DefUse(V : VarType) = struct

  module Sem = Semant.Make(V)
  open Sem

  let def_of_stmt = function
    | S_set (lhs, _) -> Some (V.to_int lhs)
    | S_phi (lhs, _) -> Some (V.to_int lhs)
    | _ -> None

  let rec use_of_expr (ep, _) =
    match ep with
    | E_lit _ -> S.empty
    | E_var var -> S.singleton (V.to_int var)
    | E_prim1 (_, e) -> use_of_expr e
    | E_prim2 (_, e1, e2) -> S.union (use_of_expr e1) (use_of_expr e2)
    | E_prim3 (_, e1, e2, e3) ->
      (use_of_expr e3) |> S.union (use_of_expr e2) |> S.union (use_of_expr e1)
    | E_primn (_, es) -> uses_expr_list es
    | E_nondet _ -> S.empty
    | E_extend (_, e, _) -> use_of_expr e
    | E_shrink (e, _) -> use_of_expr e
    | E_load (_, seg, off) -> S.union (use_of_expr seg) (use_of_expr off)

  and uses_expr_list es =
    es |> map (use_of_expr) |> fold_left S.union S.empty

  let use_of_stmt = function
    | S_set (_, e) -> use_of_expr e
    | S_store (_, seg, off, data) ->
      use_of_expr data |>
      S.union (use_of_expr off) |>
      S.union (use_of_expr seg)
    | S_jump (cond_opt, e) ->
      begin match cond_opt with
        | Some cond -> S.union (use_of_expr cond) (use_of_expr e)
        | None -> use_of_expr e
      end
    | S_jumpout (e, l) ->
      l |> List.fold_left (fun acc (_, v) -> S.union acc (use_of_expr v))
        (use_of_expr e)
    | S_phi (_, rhs) -> Array.to_list rhs |> uses_expr_list
    | _ -> assert false

  let remove_dead_code_bb bb live_out =
    let stmt_arr = Array.of_list bb.stmts in
    let n = Array.length stmt_arr in
    let keep = Array.make n true in
    begin
      let live = Array.copy live_out in
      for i=n-1 downto 0 do
        let s = stmt_arr.(i) in
        def_of_stmt s |> begin function
          | Some uid ->
            if not live.(uid) then keep.(i) <- false;
            live.(uid) <- false
          | None -> ()
        end;
        use_of_stmt s |> S.iter (fun uid -> live.(uid) <- true)
      done
    end;
    let new_stmts = ref [] in
    for i=0 to n-1 do
      if keep.(i) then new_stmts := stmt_arr.(i) :: !new_stmts
    done;
    bb.stmts <- List.rev !new_stmts

  let compute_defsites cfg =
    let size = Array.length cfg.node in
    let n_var = cfg.n_var in
    let defsites = Array.make n_var S.empty in
    for i=0 to size-1 do
      cfg.node.(i).stmts |> iter begin fun stmt ->
        def_of_stmt stmt |> begin function
          | Some uid -> defsites.(uid) <- S.add i defsites.(uid)
          | None -> ()
        end
      end
    done;
    defsites

  let defuse_of_bb stmts =
    let defs = ref S.empty in
    let uses = ref S.empty in
    stmts |> List.iter begin fun s ->
      uses := S.union !uses (S.diff (use_of_stmt s) !defs);
      def_of_stmt s |> begin function
        | Some v -> defs := S.add v !defs
        | None -> ()
      end;
    end;
    !defs, !uses

end

module PlainDefUse = DefUse(Var)
module SSADefUse = DefUse(SSAVar)

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
  let n_var = cfg.n_var in
  for i=0 to n-1 do
    live_in.(i) <- Array.make n_var false;
(*     live_out.(i) <- Array.make n_var (S.mem i cfg.exits) *)
    live_out.(i) <- Array.make n_var false;
  done;
  cfg.exits |> S.iter begin fun i ->
    live_out.(i).(Obj.magic Inst.R_EAX) <- true;
    live_out.(i).(Obj.magic Inst.R_ESP) <- true;
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
  let use_count = Array.make cfg.n_var 0 in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter begin fun s ->
      s |> SSADefUse.use_of_stmt |>
      S.iter (fun v -> use_count.(v) <- use_count.(v) + 1)
    end
  done;
  use_count

let auto_subst cfg =
  let open SSA in
  let n = Array.length cfg.node in
  let rep = Array.make cfg.n_var None in
  let use_count = count_uses cfg in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter begin function
      | S_set (lhs, rhs) ->
        let v = SSAVar.to_int lhs in
        let ok =
          use_count.(v) = 1 ||
          begin match fst rhs with
            | E_var _ | E_lit _ -> true
            | _ -> lhs.SSAVar.orig = Var.Global R_ESP
          end
        in
        if ok then begin
          let rhs' =
            rhs |> subst begin fun sv ->
              let v' = SSAVar.to_int sv in
              rep.(v') |> Option.default (E_var sv)
            end
          in
          rep.(v) <- Some (fst rhs')
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
      cfg.node.(i).stmts |> filter_map begin fun stmt ->
        let stmt' =
          match stmt with
          | S_set (lhs, rhs) when rep.(SSAVar.to_int lhs) <> None -> None
          | _ -> Some (subst_stmt f stmt)
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
      cfg.node.(i).stmts |> filter begin fun stmt ->
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

let rec rename_to_ssa f (expr, w) =
  let expr' =
    match expr with
    | Plain.E_lit bv ->
      SSA.E_lit bv
    | Plain.E_var name ->
      SSA.E_var (f name)
    | Plain.E_prim1 (p, e) ->
      SSA.E_prim1 (p, rename_to_ssa f e)
    | Plain.E_prim2 (p, e1, e2) ->
      SSA.E_prim2 (p, rename_to_ssa f e1, rename_to_ssa f e2)
    | Plain.E_prim3 (p, e1, e2, e3) ->
      SSA.E_prim3 (p, rename_to_ssa f e1, rename_to_ssa f e2, rename_to_ssa f e3)
    | Plain.E_primn (p, es) ->
      SSA.E_primn (p, List.map (rename_to_ssa f) es)
    | Plain.E_load (size, seg, addr) ->
      SSA.E_load (size, rename_to_ssa f seg, rename_to_ssa f addr)
    | Plain.E_nondet (w, id) ->
      SSA.E_nondet (w, id)
    | Plain.E_extend (sign, e, n) ->
      SSA.E_extend (sign, rename_to_ssa f e, n)
    | Plain.E_shrink (e, n) ->
      SSA.E_shrink (rename_to_ssa f e, n)
  in
  expr', w

let rec rename_from_ssa f (expr, w) =
  let expr' =
    match expr with
    | SSA.E_lit bv ->
      Plain.E_lit bv
    | SSA.E_var name ->
      Plain.E_var (f name)
    | SSA.E_prim1 (p, e) ->
      Plain.E_prim1 (p, rename_from_ssa f e)
    | SSA.E_prim2 (p, e1, e2) ->
      Plain.E_prim2 (p, rename_from_ssa f e1, rename_from_ssa f e2)
    | SSA.E_prim3 (p, e1, e2, e3) ->
      Plain.E_prim3 (p, rename_from_ssa f e1, rename_from_ssa f e2, rename_from_ssa f e3)
    | SSA.E_primn (p, es) ->
      Plain.E_primn (p, List.map (rename_from_ssa f) es)
    | SSA.E_load (size, seg, addr) ->
      Plain.E_load (size, rename_from_ssa f seg, rename_from_ssa f addr)
    | SSA.E_nondet (w, id) ->
      Plain.E_nondet (w, id)
    | SSA.E_extend (sign, e, n) ->
      Plain.E_extend (sign, rename_from_ssa f e, n)
    | SSA.E_shrink (e, n) ->
      Plain.E_shrink (rename_from_ssa f e, n)
  in
  expr', w

let plain_dummy = Plain.E_nondet (0, 0), 0
let ssa_dummy = SSA.E_nondet (0, 0), 0

let convert_to_ssa temp_tab cfg =
  let size = Array.length cfg.node in
  (* fields of the resulting CFG *)
  let node = cfg.node |> Array.map (fun bb -> { bb with stmts = [] }) in
  let succ = Array.copy cfg.succ in
  let pred = Array.copy cfg.pred in
  (* place phi functions *)
  let idom = Control_flow.compute_idom succ pred in
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
    succ.(n) |> iter (fun y -> if idom.(y) <> n then s := y :: !s);
    children.(n) |> iter begin fun c ->
      compute_df c;
      df.(c) |> iter (fun w -> if not (dominates n w) then s := w :: !s)
    end;
    df.(n) <- !s
  in
  compute_df 0;
  let n_var = cfg.n_var in
  let defsites = PlainDefUse.compute_defsites cfg in
  let live_in, live_out = liveness cfg in
  for v = 0 to n_var - 1 do
    let phi_inserted_at = Array.make size false in
    let q = Queue.create () in
    defsites.(v) |> S.iter (fun defsite -> Queue.add defsite q);
    while not (Queue.is_empty q) do
      let i = Queue.pop q in
      df.(i) |> iter begin fun y ->
        if not phi_inserted_at.(y) && live_in.(i).(v) then begin
          let n_pred = length pred.(y) in
          let lhs = Var.of_int v in
          let phi = Plain.(S_phi (lhs, Array.make n_pred plain_dummy)) in
          (* actually insert phi function *)
          cfg.node.(y).stmts <- phi :: cfg.node.(y).stmts;
          phi_inserted_at.(y) <- true;
          if not (S.mem y defsites.(v)) then Queue.push y q
        end
      end
    done
  done;
  (* rename variables *)
  let count = Array.make n_var 0 in
  let stack = Array.make n_var [0] in
  let svid_table = Hashtbl.create 0 in
  let next_svid = ref 0 in
  let get_svid k =
    try Hashtbl.find svid_table k
    with Not_found ->
      let uid = !next_svid in
      incr next_svid;
      Hashtbl.add svid_table k uid;
      uid
  in
  let rename_lhs sv =
    let open SSAVar in
    let orig = sv.orig in
    let orig_uid = Var.to_int orig in
    let ver = count.(orig_uid) + 1 in
    count.(orig_uid) <- ver;
    stack.(orig_uid) <- ver :: stack.(orig_uid);
    let uid = get_svid (orig_uid, ver) in
    SSAVar.{ orig; ver; uid }
  in
  let rename_rhs sv =
    let open SSAVar in
    let orig = sv.orig in
    let orig_uid = Var.to_int orig in
    let ver = hd stack.(orig_uid) in
    let uid = get_svid (orig_uid, ver) in
    SSAVar.{ orig; ver; uid }
  in
  for i=0 to size-1 do
    let f orig = SSAVar.{ orig; ver=0; uid=0 } in
    let stmts' = ref [] in
    cfg.node.(i).stmts |> iter begin fun stmt ->
      let stmt' =
        match stmt with
        | Plain.S_set (name, e) ->
          let e' = rename_to_ssa f e in
          let name' = f name in
          SSA.S_set (name', e')
        | Plain.S_store (size, seg, off, data) ->
          let seg' = rename_to_ssa f seg in
          let off' = rename_to_ssa f off in
          let data' = rename_to_ssa f data in
          SSA.S_store (size, seg', off', data')
        | Plain.S_jump (c, dst) ->
          let c' = Option.map (rename_to_ssa f) c in
          let dst' = rename_to_ssa f dst in
          SSA.S_jump (c', dst')
        | Plain.S_jumpout (dst, l) ->
          let dst' = rename_to_ssa f dst in
          let l' = l |> List.map (fun (r,v) -> r, rename_to_ssa f v) in
          SSA.S_jumpout (dst', l')
        | Plain.S_phi (lhs, rhs) ->
          let lhs' = f lhs in
          let n = Array.length rhs in
          SSA.S_phi (lhs', Array.make n ssa_dummy)
        | _ -> assert false
      in
      stmts' := stmt' :: !stmts'
    end;
    node.(i).stmts <- List.rev !stmts'
  done;
  let rec rename_bb i =
    let open SSA in
    let sub = subst (fun sv -> E_var (rename_rhs sv)) in
    node.(i).stmts <- begin
      node.(i).stmts |> List.map begin function
        | S_set (sv, e) ->
          let e' = sub e in
          let name' = rename_lhs sv in
          S_set (name', e')
        | S_store (size, seg, off, data) ->
          let seg' = sub seg in
          let off' = sub off in
          let data' = sub data in
          S_store (size, seg', off', data')
        | S_jump (c, dst) ->
          let c' = Option.map sub c in
          let dst' = sub dst in
          S_jump (c', dst')
        | S_jumpout (dst, l) ->
          let dst' = sub dst in
          let l' = l |> List.map (fun (r,v) -> r, sub v) in
          S_jumpout (dst', l')
        | S_phi (lhs, rhs) ->
          let lhs' = rename_lhs lhs in
          S_phi (lhs', rhs)
        | _ -> assert false
      end
    end;
    (* rename variables in RHS of phi-functions *)
    succ.(i) |> iter begin fun y ->
      (* i is the j-th predecessor of y *)
      let j = index_of i pred.(y) |> Option.get in
      node.(y).stmts |> iter begin function
        | SSA.S_phi (lhs, rhs) ->
          let open SSAVar in
          let w =
            match lhs.orig with
            | Var.Global reg -> Inst.(size_of_reg reg)
            | Var.Temp i -> temp_tab.(i)
            | _ -> failwith "???"
          in
          assert (rhs.(j) == ssa_dummy);
          rhs.(j) <-
            SSA.subst (fun sv -> SSA.E_var (rename_rhs sv))
              (SSA.E_var lhs, w)
        | _ -> ()
      end
    end;
    children.(i) |> iter rename_bb;
    cfg.node.(i).stmts |> iter begin fun stmt ->
      PlainDefUse.def_of_stmt stmt |> begin function
        | Some uid -> stack.(uid) <- tl stack.(uid)
        | None -> ()
      end
    end
  in
  rename_bb 0;
  { node; succ; pred; edges = cfg.edges; exits = cfg.exits; n_var = !next_svid }

let convert_stmt_from_ssa f s =
  let rename = rename_from_ssa f in
  match s with
  | SSA.S_set (lhs, rhs) ->
    Plain.S_set (f lhs, rename rhs)
  | SSA.S_store (size, seg, addr, data) ->
    Plain.S_store (size, rename seg, rename addr, rename data)
  | SSA.S_jump (cond_opt, dest) ->
    let cond_opt' = Option.map rename cond_opt in
    let dest' = rename dest in
    Plain.S_jump (cond_opt', dest')
  | SSA.S_jumpout (dest, l) ->
    let dest' = rename dest in
    let l' = l |> List.map (fun (r,v) -> r, rename v) in
    Plain.S_jumpout (dest', l')
  | _ -> invalid_arg "convert_stmt_from_ssa"

let convert_from_ssa cfg =
  let n = Array.length cfg.node in
  let new_stmts = Array.make n [] in
  let svar_to_pvar sv =
    let open SSAVar in
    match sv with
    | { orig = (Var.Global _ as pv); ver = 0; _ } -> pv
    | _ ->
      Var.Local (Format.asprintf "%a" SSAVar.pp sv)(*("t" ^ string_of_int v)*)
  in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | SSA.S_phi _ -> ()
      | s ->
        let emit s = new_stmts.(i) <- s :: new_stmts.(i) in
        begin
          match convert_stmt_from_ssa svar_to_pvar s with
          | S_jumpout (dst, l) ->
            l |> List.iter begin fun (r, v) ->
              if fst v <> Plain.E_var (Var.Global r) then
                emit (Plain.S_set (Var.Global r, v))
            end;
            emit (Plain.S_jump (None, dst))
          | s' -> emit s'
        end
    end
  done;
  for i=0 to n-1 do
    cfg.node.(i).stmts |> List.iter begin function
      | SSA.S_phi (lhs, rhs) ->
        let open SSAVar in
        let rhs' = rhs |> Array.map (rename_from_ssa svar_to_pvar) in
        cfg.pred.(i) |> List.iteri begin fun no j ->
          let assign = Plain.S_set (svar_to_pvar lhs, rhs'.(no)) in
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
