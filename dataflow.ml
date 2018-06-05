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
    | E_part (e, _, _) -> use_of_expr e
    | E_prim1 (_, e) -> use_of_expr e
    | E_prim2 (_, e1, e2) -> S.union (use_of_expr e1) (use_of_expr e2)
    | E_prim3 (_, e1, e2, e3) ->
      (use_of_expr e3) |> S.union (use_of_expr e2) |> S.union (use_of_expr e1)
    | E_primn (_, es) -> uses_expr_list es
    | E_nondet _ -> S.empty
    | E_extend (_, e, _) -> use_of_expr e
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
      end (* TODO: use set is incomplete *)
    | S_phi (_, rhs) -> Array.to_list rhs |> uses_expr_list
    | S_label _ -> S.empty
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

  let compute_defsites cfg n_var =
    let size = Array.length cfg.node in
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

let liveness cfg n_var =
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
  for i=0 to n-1 do
    live_in.(i) <- Array.make n_var false;
    live_out.(i) <- Array.make n_var (S.mem i cfg.exits)
  done;
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

let remove_dead_code_plain cfg n_var =
  let n = Array.length cfg.node in
  let live_in, live_out = liveness cfg n_var in
  for i=0 to n-1 do
    PlainDefUse.remove_dead_code_bb cfg.node.(i) live_out.(i)
  done

(*
let count_uses cfg =
  let use_count = Hashtbl.create 0 in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter begin fun stmt ->
      uses stmt |> S.iter begin fun svid ->
        if Hashtbl.mem use_count svid then
          Hashtbl.replace use_count svid (Hashtbl.find use_count svid + 1)
        else
          Hashtbl.add use_count svid 1
      end;
    end
  done;
  fun (var, i) ->
    let svid = Var.to_int var, i in
    if Hashtbl.mem use_count svid then Hashtbl.find use_count svid else 0
*)

let auto_subst cfg =
  let open SSA in
  let n = Array.length cfg.node in
  let t = Hashtbl.create 0 in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter begin function
      | S_set (lhs, rhs) ->
        let ok =
          begin match fst rhs with
            | E_var _ | E_lit _ -> true
            | _ -> lhs.SSAVar.orig = Var.Global "ESP"
          end
        in
        if ok then begin
          let rhs' =
            rhs |> subst begin fun sv ->
              Hashtbl.find_option t sv |> Option.default (E_var sv)
            end
          in
          Hashtbl.add t lhs (fst rhs')
        end
      | _ -> ()
    end;
  done;

  let changed = ref false in
  if not (Hashtbl.is_empty t) then begin
    let f name =
      if Hashtbl.mem t name then Hashtbl.find t name else (E_var name)
    in
    for i=0 to n-1 do
      cfg.node.(i).stmts <-
        cfg.node.(i).stmts |> filter_map begin fun stmt ->
          let stmt' =
            match stmt with
            | S_set (({ orig = Var.Temp _; _ } as lhs), rhs) when Hashtbl.mem t lhs -> None
            | _ -> Some (subst_stmt f stmt)
          in
          if Some stmt <> stmt' then changed := true;
          stmt'
        end
    done
  end;
  !changed

(*
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
            begin match def_of_stmt stmt with
              | Some (Var.Temp _, _ as sv) -> use_count sv > 0
              | _ -> true
            end
        in
        if not live then changed := true;
        live
      end
    end
  done;
  !changed
*)

exception Break

let rec rename f (expr, w) =
  let expr' =
    match expr with
    | Plain.E_lit bv ->
      SSA.E_lit bv
    | Plain.E_var name ->
      SSA.E_var (f name)
    | Plain.E_part (e, lo, hi) ->
      SSA.E_part (rename f e, lo, hi)
    | Plain.E_prim1 (p, e) ->
      SSA.E_prim1 (p, rename f e)
    | Plain.E_prim2 (p, e1, e2) ->
      SSA.E_prim2 (p, rename f e1, rename f e2)
    | Plain.E_prim3 (p, e1, e2, e3) ->
      SSA.E_prim3 (p, rename f e1, rename f e2, rename f e3)
    | Plain.E_primn (p, es) ->
      SSA.E_primn (p, List.map (rename f) es)
    | Plain.E_load (size, seg, addr) ->
      SSA.E_load (size, rename f seg, rename f addr)
    | Plain.E_nondet (w, id) ->
      SSA.E_nondet (w, id)
    | Plain.E_extend (sign, e, n) ->
      SSA.E_extend (sign, rename f e, n)
  in
  expr', w

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
  let n_var = Inst.number_of_registers + (Array.length temp_tab) in
  let defsites = PlainDefUse.compute_defsites cfg n_var in
  let live_in, live_out = liveness cfg n_var in
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
          (* RHS is never used *)
          let phi = Plain.(S_phi (lhs, Array.make n_pred (E_var lhs, 0))) in
          (* actually insert phi function *)
          begin match cfg.node.(y).stmts with
            | label :: rest -> cfg.node.(y).stmts <- label :: phi :: rest;
            | _ -> failwith "empty basic block"
          end;
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
  let rename_rhs orig =
    let orig_uid = Var.to_int orig in
    let ver = hd stack.(orig_uid) in
    let uid = get_svid (orig_uid, ver) in
    SSAVar.{ orig; ver; uid }
  in
  let rec rename_bb i =
    let rename_lhs orig =
      let orig_uid = Var.to_int orig in
      let ver = count.(orig_uid) + 1 in
      count.(orig_uid) <- ver;
      stack.(orig_uid) <- ver :: stack.(orig_uid);
      let uid = get_svid (orig_uid, ver) in
      SSAVar.{ orig; ver; uid }
    in
    let new_stmts = ref [] in
    cfg.node.(i).stmts |> iter begin fun stmt ->
      let new_stmt =
        match stmt with
        | Plain.S_set (name, e) ->
          let e' = rename rename_rhs e in
          let name' = rename_lhs name in
          SSA.S_set (name', e')
        | Plain.S_store (size, seg, off, data) ->
          let seg' = rename rename_rhs seg in
          let off' = rename rename_rhs off in
          let data' = rename rename_rhs data in
          SSA.S_store (size, seg', off', data')
        | Plain.S_jump (c, dst) ->
          let c' = Option.map (rename rename_rhs) c in
          let dst' = rename rename_rhs dst in
          SSA.S_jump (c', dst')
        | Plain.S_phi (lhs, rhs) ->
          let rhs' =
            let orig_uid = Var.to_int lhs in
            let ver = count.(orig_uid) in
            let uid = get_svid (orig_uid, ver) in
            SSAVar.{ orig = lhs; ver; uid }
          in
          let lhs' = rename_lhs lhs in
          let n = Array.length rhs in
          let w =
            match lhs with
            | Var.Global name -> Inst.(size_of_reg (lookup_reg name))
            | Var.Temp i -> temp_tab.(i)
            | _ -> failwith "???"
          in
          SSA.S_phi (lhs', Array.make n (SSA.E_var rhs', w))
        | Plain.S_label pc -> SSA.S_label pc
        | _ -> assert false
      in
      new_stmts := new_stmt :: !new_stmts
    end;
    let old_stmts = cfg.node.(i).stmts in
    node.(i).stmts <- rev !new_stmts;
    (* rename variables in RHS of phi-functions *)
    succ.(i) |> iter begin fun y ->
      (* i is the j-th predecessor of y *)
      let j = index_of i pred.(y) |> Option.get in
      node.(y).stmts |> iter begin function
        | SSA.S_phi (lhs, rhs) ->
          rhs.(j) <-
            SSA.subst (fun sv -> SSA.E_var (rename_rhs sv.SSAVar.orig)) rhs.(j)
        | _ -> ()
      end
    end;
    children.(i) |> iter rename_bb;
    old_stmts |> iter begin fun stmt ->
      PlainDefUse.def_of_stmt stmt |> begin function
        | Some uid -> stack.(uid) <- tl stack.(uid)
        | None -> ()
      end
    end
  in
  rename_bb 0;
  { node; succ; pred; edges = cfg.edges; exits = cfg.exits }
