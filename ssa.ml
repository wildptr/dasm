open Cfg
open List
open Semant

module S = BatSet.String

let get_rmid name =
  if name = "M" then
    Inst.number_of_registers
  else
    Inst.index_of_reg (Inst.lookup_reg name)

let get_rm_name rmid =
  if rmid = Inst.number_of_registers then "M" else Inst.reg_name_table.(rmid)

(* adapted from Modern Compiler Implementation in C, pp. 448-449 *)
let compute_idom cfg =
  let size = Array.length cfg.node in
  let bucket = Array.make size [] in
  let dfnum = Array.make size 0 in
  let semi = Array.make size (-1) in
  let ancestor = Array.make size (-1) in
  let idom = Array.make size (-1) in
  let samedom = Array.make size (-1) in
  let vertex = Array.make size 0 in
  let parent = Array.make size (-1) in
  let best = Array.make size 0 in
  let rec ancestor_with_lowest_semi v =
    let a = ancestor.(v) in
    if ancestor.(a) >= 0 then begin
      let b = ancestor_with_lowest_semi a in
      ancestor.(v) <- ancestor.(a);
      if dfnum.(semi.(b)) < dfnum.(semi.(best.(v))) then best.(v) <- b;
    end;
    best.(v)
  in
  let link p n =
    ancestor.(n) <- p;
    best.(n) <- n
  in
  let next_dfnum = ref 0 in
  let rec dfs p n =
    if dfnum.(n) = 0 then begin
      dfnum.(n) <- !next_dfnum;
      vertex.(!next_dfnum) <- n;
      parent.(n) <- p;
      incr next_dfnum;
      iter (fun w -> dfs n w) cfg.succ.(n)
    end
  in
  dfs (-1) 0;
  for i = size-1 downto 1 do
    let n = vertex.(i) in
    let p = parent.(n) in
    (* semi-dominator of n *)
    let s =
      cfg.pred.(n) |> map (fun v ->
          if dfnum.(v) <= dfnum.(n) then v
          else semi.(ancestor_with_lowest_semi v)) |>
      fold_left min p
    in
    semi.(n) <- s;
    bucket.(s) <- n :: bucket.(s);
    link p n;
    bucket.(p) |> iter (fun v ->
        let y = ancestor_with_lowest_semi v in
        if semi.(y) = semi.(v) then idom.(v) <- p else samedom.(v) <- y);
    bucket.(p) <- []
  done;
  for i = 1 to size-1 do
    let n = vertex.(i) in
    if samedom.(n) >= 0 then idom.(n) <- idom.(samedom.(n))
  done;
  (*let open Format in
  for i=1 to size-1 do
    fprintf err_formatter "%d -> %d@." idom.(i) i
  done;*)
  idom

let compute_defs cfg =
  let size = Array.length cfg.node in
  let defs = Array.make (Inst.number_of_registers+1) BatSet.Int.empty in
  for i=0 to size-1 do
    cfg.node.(i).stmts |> iter (fun stmt ->
        Dataflow.defs' stmt |> S.iter (fun name ->
          begin match name.[0] with
            | 'A'..'Z' ->
              let rmid = get_rmid name in
              defs.(rmid) <- BatSet.Int.add i defs.(rmid)
            | _ -> ()
          end))
  done;
  defs

exception Break

let convert_to_ssa cfg =
  (* place phi functions *)
  let size = Array.length cfg.node in
  let idom = compute_idom cfg in
  let children = Array.make size [] in
  let df = Array.make size [] in
  let rec dominates x y =
    if x = y then true
    else
      let dy = idom.(y) in
      if dy < 0 then false
      else dominates x dy
  in
  idom |> Array.iteri (fun n p ->
      if p >= 0 then children.(p) <- n :: children.(p));
  let rec compute_df n =
    let s = ref [] in
    cfg.succ.(n) |> iter (fun y -> if idom.(y) <> n then s := y :: !s);
    children.(n) |> iter (fun c ->
        compute_df c;
        df.(c) |> iter (fun w ->
            if not (dominates n w) then s := w :: !s));
    df.(n) <- !s
  in
  compute_df 0;
  let defs = compute_defs cfg in
  for rmid = 0 to Inst.number_of_registers do
    let phi_inserted_at = Array.make size false in
    let worklist = Queue.create () in
    defs.(rmid) |> BatSet.Int.iter (fun defsite -> Queue.add defsite worklist);
    while not (Queue.is_empty worklist) do
      let n = Queue.pop worklist in
      df.(n) |> iter (fun y ->
          if not phi_inserted_at.(y) then begin
            let n_pred = length cfg.pred.(y) in
            let phi =
              S_phi (get_rm_name rmid, Array.make n_pred (E_var (get_rm_name rmid)))
            in
            cfg.node.(y).stmts <- phi :: cfg.node.(y).stmts;
            phi_inserted_at.(y) <- true;
            if not (BatSet.Int.mem y defs.(rmid)) then Queue.push y worklist
          end)
    done
  done;
  (* rename variables *)
  let count = Array.make (Inst.number_of_registers+1) 0 in
  let stack = Array.make (Inst.number_of_registers+1) [0] in
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
    cfg.node.(n).stmts |> iter (fun stmt ->
        let new_stmt =
          match stmt with
          | S_set (name, e) ->
            let e' = rename_variables rename_rhs e in
            let name' = rename_lhs name in
            S_set (name', e')
          | S_store (size, addr, data, m1, m0) ->
            let addr' = rename_variables rename_rhs addr in
            let data' = rename_variables rename_rhs data in
            let m0' = rename_variables rename_rhs m0 in
            let m1' = rename_lhs m1 in
            S_store (size, addr', data', m1', m0')
          | S_jump (c, dst, d, u) ->
            let c' = BatOption.map (rename_variables rename_rhs) c in
            let dst' = rename_variables rename_rhs dst in
            let u' = map (rename_variables rename_rhs) u in
            let d' = map rename_lhs d in
            S_jump (c', dst', d', u')
          | S_phi (lhs, rhs) -> S_phi (rename_lhs lhs, rhs)
          | _ -> assert false
        in
        (*Format.(fprintf err_formatter "%a -> %a@." pp_stmt stmt pp_stmt new_stmt);*)
        new_stmts := new_stmt :: !new_stmts);
    let old_stmts = cfg.node.(n).stmts in
    cfg.node.(n).stmts <- rev !new_stmts;
    (* rename variables in RHS of phi-functions *)
    cfg.succ.(n) |> iter (fun y ->
        (* n is the j-th predecessor of y *)
        let j =
          match BatList.index_of n cfg.pred.(y) with
          | Some i -> i
          | None -> assert false
        in
        begin
          try
            cfg.node.(y).stmts |> iter (function
                | S_phi (_, rhs) -> rhs.(j) <- rename_variables rename_rhs rhs.(j)
                | _ -> raise Break);
          with Break -> ()
        end);
    children.(n) |> iter rename;
    old_stmts |> iter (fun stmt ->
        Dataflow.defs' stmt |> S.iter (fun name ->
          begin match name.[0] with
            | 'A'..'Z' ->
              let rmid = get_rmid name in
              stack.(rmid) <- List.tl stack.(rmid)
            | _ -> ()
          end))
  in
  rename 0
