open Cfg
open List
open Semant
open Util

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
  idom

let all_registers = range 0 (Inst.number_of_registers-1)

let register_modified_by_stmt = function
  | S_set (name, _) ->
    begin match name.[0] with
      | 'A'..'Z' -> [Inst.index_of_reg (Inst.lookup_reg name)]
      | _ -> []
    end
  | S_jump (_, true) -> all_registers
  | _ -> []

let rec registers_used_by_expr = function
  | E_literal _ -> []
  | E_var name ->
    begin match name.[0] with
      | 'A'..'Z' -> [Inst.index_of_reg (Inst.lookup_reg name)]
      | _ -> []
    end
  | E_part (e, _, _) -> registers_used_by_expr e
  | E_prim p ->
    begin match p with
      | P_not e -> registers_used_by_expr e
      | P_concat es -> union_set (map registers_used_by_expr es)
      | P_add es -> union_set (map registers_used_by_expr es)
      | P_sub (e1, e2) ->
        union (registers_used_by_expr e1) (registers_used_by_expr e2)
      | P_eq (e1, e2) ->
        union (registers_used_by_expr e1) (registers_used_by_expr e2)
      | P_and es -> union_set (map registers_used_by_expr es)
      | P_xor es -> union_set (map registers_used_by_expr es)
      | P_or es -> union_set (map registers_used_by_expr es)
      | P_shiftleft (e1, e2) ->
        union (registers_used_by_expr e1) (registers_used_by_expr e2)
      | P_logshiftright (e1, e2) ->
        union (registers_used_by_expr e1) (registers_used_by_expr e2)
      | P_arishiftright (e1, e2) ->
        union (registers_used_by_expr e1) (registers_used_by_expr e2)
      | P_undef _ -> []
      | P_repeat (e, _) -> registers_used_by_expr e
      | P_addwithcarry (e1, e2, e3) ->
        union_set (map registers_used_by_expr [e1;e2;e3])
      | P_reduce_and e -> registers_used_by_expr e
      | P_reduce_xor e -> registers_used_by_expr e
      | P_reduce_or e -> registers_used_by_expr e
      | P_signextend (e, _) -> registers_used_by_expr e
      | P_zeroextend (e, _) -> registers_used_by_expr e
    end
  | E_load (_, e) -> registers_used_by_expr e

(* return type is int list *)
let registers_used_by_stmt = function
  | S_set (_, e) -> registers_used_by_expr e
  | S_store (_, addr, data) ->
    union (registers_used_by_expr addr) (registers_used_by_expr data)
  | S_jump (e, u) ->
    if u then all_registers else registers_used_by_expr e
  | S_br (cond, e, u) ->
    if u then all_registers
    else union (registers_used_by_expr cond) (registers_used_by_expr e)
  | _ -> assert false

let compute_defs cfg =
  let size = Array.length cfg.node in
  let defs = Array.make Inst.number_of_registers [] in
  for i=0 to size-1 do
    cfg.node.(i).stmts |> iter (fun stmt ->
        register_modified_by_stmt stmt |> iter (fun regid ->
            defs.(regid) <- union defs.(regid) [i]));
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
  for regid = 0 to Inst.number_of_registers-1 do
    let phi_inserted_at = Array.make size false in
    let worklist = Queue.create () in
    defs.(regid) |> iter (fun defsite -> Queue.add defsite worklist);
    while not (Queue.is_empty worklist) do
      let n = Queue.pop worklist in
      df.(n) |> iter (fun y ->
          if not phi_inserted_at.(y) then begin
            let n_pred = length cfg.pred.(y) in
            let phi = S_phi (Inst.reg_name_table.(regid), Array.make n_pred Inst.reg_name_table.(regid)) in
            cfg.node.(y).stmts <- phi :: cfg.node.(y).stmts;
            phi_inserted_at.(y) <- true;
            if not (mem y defs.(regid)) then Queue.push y worklist
          end)
    done
  done;
  (* rename variables *)
  let count = Array.make Inst.number_of_registers 0 in
  let stack = Array.make Inst.number_of_registers [0] in
  let rename_variable name =
    match name.[0] with
    | 'A'..'Z' ->
      let regid = Inst.index_of_reg (Inst.lookup_reg name) in
      let i = hd stack.(regid) in
      name ^ "_" ^ string_of_int i
    | _ -> name
  in
  let rec rename n =
    let n_def = Array.copy count in
    cfg.node.(n).stmts <-
      cfg.node.(n).stmts |> map (function
          | S_set (name, e) ->
            let e' = rename_variables rename_variable e in
            let name' =
              match name.[0] with
              | 'A'..'Z' ->
                let regid = Inst.index_of_reg (Inst.lookup_reg name) in
                let i = count.(regid) + 1 in
                count.(regid) <- i;
                stack.(regid) <- i :: stack.(regid);
                n_def.(regid) <- n_def.(regid) + 1;
                name ^ "_" ^ string_of_int i
              | _ -> name
            in
            S_set (name', e')
          | S_store (size, addr, data) ->
            let addr' = rename_variables rename_variable addr in
            let data' = rename_variables rename_variable data in
            S_store (size, addr', data')
          | S_jump (dst, u) -> S_jump (rename_variables rename_variable dst, u)
          | S_br (cond, dst, u) ->
            let cond' = rename_variables rename_variable cond in
            let dst' = rename_variables rename_variable dst in
            S_br (cond', dst', u)
          | S_phi (lhs, rhs) ->
            let lhs' =
              match lhs.[0] with
              | 'A'..'Z' ->
                let regid = Inst.index_of_reg (Inst.lookup_reg lhs) in
                let i = count.(regid) + 1 in
                count.(regid) <- i;
                stack.(regid) <- i :: stack.(regid);
                (*n_def.(regid) <- n_def.(regid) + 1;*)
                lhs ^ "_" ^ string_of_int i
              | _ -> lhs
            in
            S_phi (lhs', rhs)
          | _ -> assert false);
    for i=0 to Inst.number_of_registers-1 do
      n_def.(i) <- count.(i) - n_def.(i)
    done;
    (* rename variables in RHS of phi-functions *)
    cfg.succ.(n) |> iter (fun y ->
        (* n is the j-th predecessor of y *)
        let j = index n cfg.pred.(y) in
        begin
          try
            cfg.node.(y).stmts |> iter (function
                | S_phi (lhs, rhs) -> rhs.(j) <- rename_variable rhs.(j)
                | _ -> raise Break);
          with Break -> ()
        end);
    children.(n) |> iter rename;
    for i=0 to Inst.number_of_registers-1 do
      stack.(i) <- drop stack.(i) n_def.(i)
    done
  in
  rename 0
