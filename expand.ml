open Semant
open Util

let rec map_expr f = function
  | E_literal _ as e -> e
  | E_var name -> E_var (f name)
  | E_part (e, lo, hi) -> E_part (map_expr f e, lo, hi)
  | E_prim p ->
    let p' =
      match p with
      | P_not e -> P_not (map_expr f e)
      | P_concat es -> P_concat (List.map (map_expr f) es)
      | P_add es -> P_add (List.map (map_expr f) es)
      | P_sub (e1, e2) -> P_sub (map_expr f e1, map_expr f e2)
      | P_eq (e1, e2) -> P_eq (map_expr f e1, map_expr f e2)
      | P_and es -> P_and (List.map (map_expr f) es)
      | P_xor es -> P_xor (List.map (map_expr f) es)
      | P_or es -> P_or (List.map (map_expr f) es)
      | P_shiftleft (e1, e2) -> P_shiftleft (map_expr f e1, map_expr f e2)
      | P_logshiftright (e1, e2) -> P_logshiftright (map_expr f e1, map_expr f e2)
      | P_arishiftright (e1, e2) -> P_arishiftright (map_expr f e1, map_expr f e2)
      | P_undef _ as p -> p
      | P_repeat (e, n) -> P_repeat (map_expr f e, n)
      | P_addwithcarry (e1, e2, e3) ->
        P_addwithcarry (map_expr f e1, map_expr f e2, map_expr f e3)
      | P_reduce_and e -> P_reduce_and (map_expr f e)
      | P_reduce_xor e -> P_reduce_xor (map_expr f e)
      | P_reduce_or e -> P_reduce_or (map_expr f e)
      | P_zeroextend (e, size) -> P_zeroextend (map_expr f e, size)
      | P_signextend (e, size) -> P_signextend (map_expr f e, size)
    in
    E_prim p'
  | E_load (size, addr) -> E_load (size, map_expr f addr)

let rec expand_stmt env call_id f retval stmt =
  (*Format.printf "Expanding: %a@." pp_stmt stmt;*)
  match stmt with
  | S_set (loc, e) ->
    let e' = map_expr f e in
    let loc' =
      (*match loc with
      | L_var id -> L_var (f id)
      | L_part (id, lo, hi) -> L_part (f id, lo, hi)*)
      loc
    in
    append_stmt env (S_set (loc', e'))
  | S_store (size, addr, data) ->
    append_stmt env (S_store (size, map_expr f addr, map_expr f data))
  | S_jump e ->
    append_stmt env (S_jump (map_expr f e))
  | S_br (e1, e2) ->
    append_stmt env (S_br (map_expr f e1, map_expr f e2))
  | S_call (proc, args, rv) ->
    let call_id_ = !call_id in
    let f' name =
      let name' = f name in
      match name.[0] with
      | 'A'..'Z' -> name'
      | _ -> Printf.sprintf "%s_%d" name' call_id_
    in
    call_id := !call_id+1;
    (* variable table *)
    proc.p_var_tab |> Hashtbl.iter (fun k v ->
        Hashtbl.add env.var_tab (f' k) v);
    (* pass arguments *)
    (* TODO: check arity & widths *)
    zip args proc.p_param_names |> List.iter
      (fun (arg, param_name) ->
         append_stmt env (S_set (f' param_name, arg)));
    let rv' =
      match rv with
      | None -> None
      | Some loc ->
        let loc' =
          (*match loc with
          | L_var id -> L_var (f id)
          | L_part (id, lo, hi) -> L_part (f id, lo, hi)*)
          loc
        in
        Some loc'
    in
    List.iter (expand_stmt env (ref 0) f' rv') proc.p_body
  | S_output e ->
    begin match retval with
      | None -> ()
      | Some name ->
        append_stmt env (S_set (name, map_expr f e))
    end

let expand env =
  let stmts = get_stmts env in
  let env' = new_env () in
  List.iter (expand_stmt env' (ref 0) (fun name -> name) None) stmts;
  env'
