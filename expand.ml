open Core_kernel.Std
open Semant

let rec map_expr f = function
  | E_literal _ as e -> e
  | E_var name -> E_var (f name)
  | E_part (e, range) -> E_part (map_expr f e, range)
  | E_prim p ->
      let p' =
        match p with
        | P_not e -> P_not (map_expr f e)
        | P_concat es -> P_concat (List.map es ~f:(map_expr f))
        | P_add es -> P_add (List.map es ~f:(map_expr f))
        | P_sub (e1, e2) -> P_sub (map_expr f e1, map_expr f e2)
        | P_eq (e1, e2) -> P_eq (map_expr f e1, map_expr f e2)
        | P_and es -> P_and (List.map es ~f:(map_expr f))
        | P_xor es -> P_xor (List.map es ~f:(map_expr f))
        | P_or es -> P_or (List.map es ~f:(map_expr f))
        | P_shiftleft (e1, e2) -> P_shiftleft (map_expr f e1, map_expr f e2)
        | P_undef _ as p -> p
        | P_repeat (e, n) -> P_repeat (map_expr f e, n)
        | P_add_ex (e1, e2, e3) ->
            P_add_ex (map_expr f e1, map_expr f e2, map_expr f e3)
      in
      E_prim p'

let rec expand_stmt env call_id f retval stmt =
  Format.printf "Expanding: %a@." pp_stmt stmt;
  match stmt with
  | S_set (id, e) ->
      let e' = map_expr f e in
      let id' = f id in
      append_stmt env (S_set (id', e'))
  | S_set_part (name, range, e) ->
      append_stmt env (S_set_part (f name, range, map_expr f e))
  | S_load (size, addr, dest) ->
      append_stmt env (S_load (size, map_expr f addr, f dest))
  | S_store (size, addr, data) ->
      append_stmt env (S_store (size, map_expr f addr, map_expr f data))
  | S_label _ as s ->
      append_stmt env s
  | S_jump _ as s ->
      append_stmt env s
  | S_jump_var e ->
      append_stmt env (S_jump_var (map_expr f e))
  | S_br (e, label) ->
      append_stmt env (S_br (map_expr f e, label))
  | S_br_var (e1, e2) ->
      append_stmt env (S_br_var (map_expr f e1, map_expr f e2))
  | S_call (proc, args, rv) ->
      let call_id_ = !call_id in
      let f' name =
        let name' = f name in
        if Char.is_uppercase name.[0] then name'
        else Printf.sprintf "%s.%d" name' call_id_
      in
      call_id := !call_id+1;
      (* variable table *)
      String.Table.iteri proc.p_var_tab ~f:(fun ~key ~data ->
        String.Table.add_exn env.var_tab ~key:(f' key) ~data);
      (* pass arguments *)
      List.iter (List.zip_exn args proc.p_param_names)
        ~f:(fun (arg, param_name) ->
          append_stmt env (S_set (f' param_name, arg)));
      let rv' =
        match rv with
        | None -> None
        | Some id -> Some (f id)
      in
      List.iter proc.p_body ~f:(expand_stmt env (ref 0) f' rv')
  | S_return e ->
      begin match retval with
      | None -> assert false
      | Some name ->
          append_stmt env (S_set (name, map_expr f e))
      end

let expand env =
  let stmts = get_stmt_list env in
  let env' = new_env () in
  List.iter stmts ~f:(expand_stmt env' (ref 0) (fun name -> name) None);
  env'
