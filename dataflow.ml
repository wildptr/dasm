open Batteries
open Cfg
open List
open Semant

module S = Set.Int

module IntPair = struct
  type t = int * int
  let compare (fst1, snd1) (fst2, snd2) =
    let c = Int.compare fst1 fst2 in
    if c <> 0 then c else Int.compare snd1 snd2
end

module SS = Set.Make(IntPair)

let number_of_registers = 56

let var_to_uid = function
  | V_global name -> Inst.lookup_reg name |> Obj.magic
  | V_temp i -> number_of_registers + i
  | _ -> failwith "var_to_uid: invalid variable"

let uid_to_var uid =
  if uid < number_of_registers then
    V_global (Inst.string_of_reg (Obj.magic uid))
  else
    V_temp (uid - number_of_registers)

let def_of_stmt = function
  | S_set (lhs, _) -> Some lhs
  | S_phi (lhs, _) -> Some lhs
  | _ -> None

let rec uses_expr = function
  | E_lit _ -> SS.empty
  | E_var (var, i) -> SS.singleton (var_to_uid var, i)
  | E_part (e, _, _) -> uses_expr e
  | E_prim1 (_, e) -> uses_expr e
  | E_prim2 (_, e1, e2) -> SS.union (uses_expr e1) (uses_expr e2)
  | E_prim3 (_, e1, e2, e3) ->
    (uses_expr e3) |> SS.union (uses_expr e2) |> SS.union (uses_expr e1)
  | E_primn (_, es) -> uses_expr_list es
  | E_nondet _ -> SS.empty
  | E_extend (_, e, _) -> uses_expr e
  | E_load (_, seg, off) -> SS.union (uses_expr seg) (uses_expr off)

and uses_expr_list es =
  es |> map uses_expr |> fold_left SS.union SS.empty

let uses = function
  | S_set (_, e) -> uses_expr e
  | S_store (_, seg, off, data) ->
    uses_expr data |>
    SS.union (uses_expr off) |>
    SS.union (uses_expr seg)
  | S_jump (cond_opt, e) ->
    begin match cond_opt with
      | Some cond -> SS.union (uses_expr cond) (uses_expr e)
      | None -> uses_expr e
    end (* TODO: use set is incomplete *)
  | S_phi (_, rhs) -> Array.to_list rhs |> uses_expr_list
  | S_label _ -> SS.empty
  | _ -> assert false

let count_uses cfg =
  let use_count = Hashtbl.create 0 in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter begin fun stmt ->
      uses stmt |> SS.iter begin fun svid ->
        if Hashtbl.mem use_count svid then
          Hashtbl.replace use_count svid (Hashtbl.find use_count svid + 1)
        else
          Hashtbl.add use_count svid 1
      end;
    end
  done;
  fun (var, i) ->
    let svid = var_to_uid var, i in
    if Hashtbl.mem use_count svid then Hashtbl.find use_count svid else 0

let auto_subst cfg =
  let n = Array.length cfg.node in
  let t = Hashtbl.create 0 in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter begin function
      | S_set (lhs, rhs) ->
        let subst =
          begin match rhs with
            | E_var _ | E_lit _ | E_part (E_var _, _, _) -> true
            | _ -> fst lhs = V_global "ESP"
          end
        in
        if subst then begin
          let rhs' =
            rhs |> subst_expr begin fun sv ->
              Hashtbl.find_option t sv |> Option.default (E_var sv)
            end
          in
          Hashtbl.add t lhs rhs'
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
            | S_set ((V_temp _, _ as lhs), rhs) ->
              if Hashtbl.mem t lhs then None else Some (subst_stmt f stmt)
            | _ -> Some (subst_stmt f stmt)
          in
          if Some stmt <> stmt' then changed := true;
          stmt'
        end
    done
  end;
  !changed

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
              | Some (V_temp _, _ as sv) -> use_count sv > 0
              | _ -> true
            end
        in
        if not live then changed := true;
        live
      end
    end
  done;
  !changed

let compute_defs (cfg : var stmt cfg) n_var =
  let size = Array.length cfg.node in
  let defs = Array.make n_var Set.Int.empty in
  for i=0 to size-1 do
    cfg.node.(i).stmts |> iter begin fun stmt ->
      def_of_stmt stmt |> begin function
        | Some var ->
          let uid = var_to_uid var in
          defs.(uid) <- Set.Int.add i defs.(uid)
        | None -> ()
      end
    end
  done;
  defs

exception Break

let convert_to_ssa (cfg, env) =
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
  let n_var = number_of_registers + (Env.temp_count env) in
  let defs = compute_defs cfg n_var in
  for uid = 0 to n_var - 1 do
    let phi_inserted_at = Array.make size false in
    let q = Queue.create () in
    defs.(uid) |> Set.Int.iter (fun defsite -> Queue.add defsite q);
    while not (Queue.is_empty q) do
      let n = Queue.pop q in
      df.(n) |> iter begin fun y ->
        if not phi_inserted_at.(y) then begin
          let n_pred = length pred.(y) in
          let lhs = uid_to_var uid in
          (* RHS is never used *)
          let phi = S_phi (lhs, Array.make n_pred (E_var lhs)) in
          (* actually insert phi function *)
          begin match cfg.node.(y).stmts with
            | label :: rest -> cfg.node.(y).stmts <- label :: phi :: rest;
            | _ -> failwith "empty basic block"
          end;
          phi_inserted_at.(y) <- true;
          if not (Set.Int.mem y defs.(uid)) then Queue.push y q
        end
      end
    done
  done;
  (* rename variables *)
  let count = Array.make n_var 0 in
  let stack = Array.make n_var [0] in
  let rename_rhs var =
    let uid = var_to_uid var in
    let i = hd stack.(uid) in
    var, i
  in
  let rec rename n =
    let rename_lhs var =
      let uid = var_to_uid var in
      let i = count.(uid) + 1 in
      count.(uid) <- i;
      stack.(uid) <- i :: stack.(uid);
      var, i
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
        | S_phi (lhs, rhs) ->
          let rhs' =
            let uid = var_to_uid lhs in
            let i = count.(uid) in
            (lhs, i)
          in
          let lhs' = rename_lhs lhs in
          let n = Array.length rhs in
          S_phi (lhs', Array.make n (E_var rhs'))
        | S_label _ as s -> s
        | _ -> assert false
      in
      new_stmts := new_stmt :: !new_stmts
    end;
    let old_stmts = cfg.node.(n).stmts in
    node.(n).stmts <- rev !new_stmts;
    (* rename variables in RHS of phi-functions *)
    succ.(n) |> iter begin fun y ->
      (* n is the j-th predecessor of y *)
      let j = index_of n pred.(y) |> Option.get in
      node.(y).stmts |> iter begin function
        | S_phi (lhs, rhs) ->
          rhs.(j) <- rename_variables rename_rhs (E_var (fst lhs))
        | _ -> ()
      end
    end;
    children.(n) |> iter rename;
    old_stmts |> iter begin fun stmt ->
      def_of_stmt stmt |> begin function
        | Some var ->
          let uid = var_to_uid var in
          stack.(uid) <- tl stack.(uid)
        | None -> ()
      end
    end
  in
  rename 0;
  { node; succ; pred; edges = cfg.edges }
