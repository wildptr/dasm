open Core_kernel.Std
open Semant

let rec map_expr tab = function
  | E_literal _ as e -> e
  | E_local i -> E_local (Int.Table.find_exn tab i)
  | E_global _ as e -> e
  | E_part (e, range) -> E_part (map_expr tab e, range)
  | E_prim p ->
      let p' =
        match p with
        | P_not e -> P_not (map_expr tab e)
        | P_concat es -> P_concat (List.map es ~f:(map_expr tab))
        | P_add es -> P_add (List.map es ~f:(map_expr tab))
        | P_sub (e1, e2) -> P_sub (map_expr tab e1, map_expr tab e2)
        | P_eq (e1, e2) -> P_eq (map_expr tab e1, map_expr tab e2)
        | P_and es -> P_and (List.map es ~f:(map_expr tab))
        | P_xor es -> P_xor (List.map es ~f:(map_expr tab))
        | P_or es -> P_or (List.map es ~f:(map_expr tab))
        | P_shiftleft (e1, e2) -> P_shiftleft (map_expr tab e1, map_expr tab e2)
        | P_undef _ as p -> p
        | P_repeat (e, n) -> P_repeat (map_expr tab e, n)
        | P_add_ex (e1, e2, e3) ->
            P_add_ex (map_expr tab e1, map_expr tab e2, map_expr tab e3)
      in
      E_prim p'

let map_id width_tab tab env id =
  match Int.Table.find tab id with
  | None ->
      (* get width of local #id in env *)
      let w = Int.Table.find_exn width_tab id in
      let id' = new_temp env w in
      Int.Table.add_exn tab ~key:id ~data:id';
      id'
  | Some id' -> id'

let rec expand_stmt width_tab tab env retval stmt =
  Format.printf "Expanding: %a@." pp_stmt stmt;
  match stmt with
  (* translate locals *)
  (*let local_map = Int.Table.create 0 ~len:(Int.Table.length env.local_tab) in*)
  | S_setlocal (id, e) ->
      let e' = map_expr tab e in
      let id' = map_id width_tab tab env id in
      append_stmt env (S_setlocal (id', e'))
  | S_setglobal (r, e) ->
      append_stmt env (S_setglobal (r, map_expr tab e))
  | S_setglobal_part (r, range, e) ->
      append_stmt env (S_setglobal_part (r, range, map_expr tab e))
  | S_load (size, addr, dest) ->
      append_stmt env (S_load (size, map_expr tab addr, map_id width_tab tab env dest))
  | S_store (size, addr, data) ->
      append_stmt env (S_store (size, map_expr tab addr, map_expr tab data))
  | S_label _ as s ->
      append_stmt env s
  | S_jump _ as s ->
      append_stmt env s
  | S_jump_var e ->
      append_stmt env (S_jump_var (map_expr tab e))
  | S_br (e, label) ->
      append_stmt env (S_br (map_expr tab e, label))
  | S_br_var (e1, e2) ->
      append_stmt env (S_br_var (map_expr tab e1, map_expr tab e2))
  | S_call (proc, args, retval) ->
      let tab' = Int.Table.create () in
      List.iteri (List.zip_exn args proc.p_param_widths)
        ~f:begin fun i (arg, param_width) ->
          let arg_id = new_temp env param_width in
          Int.Table.add_exn tab' ~key:i ~data:arg_id;
          append_stmt env (S_setlocal (arg_id, arg))
        end;
      let retval' =
        match retval with
        | None -> None
        | Some id -> Some (map_id width_tab tab env id)
      in
      let width_tab = Int.Table.create () in
      Array.iteri proc.p_local_widths ~f:begin fun i w ->
        Int.Table.add_exn width_tab ~key:i ~data:w
      end;
      List.iter proc.p_body ~f:(expand_stmt width_tab tab' env retval')
  | S_return e ->
      begin match retval with
      | None -> assert false
      | Some id ->
          append_stmt env (S_setlocal (id, map_expr tab e))
      end

let expand env =
  let stmts = get_stmt_list env in
  let env' = new_env () in
  let tab = Int.Table.create () in
  List.iter stmts ~f:(expand_stmt env.local_tab tab env' None);
  env'
