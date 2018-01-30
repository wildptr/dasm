open Cfg
open List
open Semant

module S = BatSet.String
module M = BatMap.String

let all_register_names = S.of_array Inst.reg_name_table

let defs = function
  | S_set (lhs, _) -> Some lhs
  | S_phi (lhs, _) -> Some lhs
  | S_store (_, _, _, m1, _) -> Some m1
  | _ -> None

let defs' = function
  | S_set (lhs, _) -> S.singleton lhs
  | S_phi (lhs, _) -> S.singleton lhs
  | S_store (_, _, _, m1, _) -> S.singleton m1
  | S_jump (_, _, d, _) -> S.of_list d
  | _ -> S.empty

let rec uses_expr = function
  | E_literal _ -> S.empty
  | E_var name -> S.singleton name
  | E_part (e, _, _) -> uses_expr e
  | E_prim1 (_, e) -> uses_expr e
  | E_prim2 (_, e1, e2) -> S.union (uses_expr e1) (uses_expr e2)
  | E_prim3 (_, e1, e2, e3) ->
    (uses_expr e3) |> S.union (uses_expr e2) |> S.union (uses_expr e1)
  | E_primn (_, es) -> uses_expr_list es
  | E_nondet _ -> S.empty
  | E_repeat (e, _) -> uses_expr e
  | E_extend (_, e, _) -> uses_expr e
  | E_load (_, e, m) -> S.union (uses_expr e) (uses_expr m)

and uses_expr_list es =
  es |> map uses_expr |> fold_left S.union S.empty

let uses = function
  | S_set (_, e) -> uses_expr e
  | S_store (_, addr, data, m1, m0) ->
    S.add m1 @@ (uses_expr m0) |> S.union (uses_expr data) |> S.union (uses_expr addr)
  | S_jump (cond_opt, e, _, u) ->
    begin match cond_opt with
      | Some cond -> S.union (uses_expr cond) (uses_expr e)
      | None -> uses_expr e
    end |> S.union (uses_expr_list u)
  | S_phi (_, rhs) -> Array.to_list rhs |> uses_expr_list
  | _ -> assert false

let count_uses cfg =
  let use_count = Hashtbl.create 0 in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter (fun stmt ->
        uses stmt |> S.iter (fun name ->
            if Hashtbl.mem use_count name then
              Hashtbl.replace use_count name (Hashtbl.find use_count name + 1)
            else
              Hashtbl.add use_count name 1))
  done;
  fun name ->
    if Hashtbl.mem use_count name then Hashtbl.find use_count name else 0

let auto_subst cfg =
  let changed = ref false in
  let t = Hashtbl.create 0 in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    cfg.node.(i).stmts |> iter (function
        | S_set (lhs, rhs) ->
          let is_candidate =
            begin match rhs with
              | E_var _ | E_literal _ -> true
              | _ -> false
            end
          in
          if is_candidate then begin
            changed := true;
            Hashtbl.add t lhs rhs
          end
        | _ -> ())
  done;
  let f name =
    if Hashtbl.mem t name then Hashtbl.find t name else (E_var name)
  in
  for i=0 to n-1 do
    cfg.node.(i).stmts <- map (subst_stmt f) cfg.node.(i).stmts
  done;
  !changed

let remove_dead_code cfg =
  let n = Array.length cfg.node in
  let changed = ref false in
  let use_count = count_uses cfg in
  for i=0 to n-1 do
    cfg.node.(i).stmts <- cfg.node.(i).stmts |> filter (fun stmt ->
        let live =
          match defs stmt with
          | Some name -> use_count name > 0
          | None -> true
        in
        if not live then changed := true;
        live)
  done;
  !changed
