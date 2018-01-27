open Semant
open Util

(* TODO: expand assignments to overlapping registers *)

let rec expand_stmt env retval stmt =
  let rename_var name =
    match name.[0] with
    | 'A'..'Z' | '$' -> name
    | _ -> Hashtbl.find env.rename_table name
  in
  let rename e =
    rename_variables rename_var e
  in
  match stmt with
  | S_set (loc, e) ->
    let e' = rename e in
    let loc' =
      (*match loc with
      | L_var id -> L_var (f id)
      | L_part (id, lo, hi) -> L_part (f id, lo, hi)*)
      rename_var loc
    in
    append_stmt env (S_set (loc', e'))
  | S_store (size, addr, data) ->
    append_stmt env (S_store (size, rename addr, rename data))
  | S_jump (e, u) ->
    append_stmt env (S_jump (rename e, u))
  | S_br (e1, e2, u) ->
    append_stmt env (S_br (rename e1, rename e2, u))
  | S_call (proc, args, rv) ->
    (* variable table *)
    proc.p_var_tab |> Hashtbl.iter (fun name width ->
        let name' = new_temp env width in
        Hashtbl.add env.rename_table name name');
    (* pass arguments *)
    (* TODO: check arity & widths *)
    List.combine args proc.p_param_names |> List.iter
      (fun (arg, param_name) ->
         append_stmt env (S_set (rename_var param_name, arg)));
    let rv' =
      match rv with
      | None -> None
      | Some loc ->
        let loc' =
          (*match loc with
          | L_var id -> L_var (f id)
          | L_part (id, lo, hi) -> L_part (f id, lo, hi)*)
          rename_var loc
        in
        Some loc'
    in
    List.iter (expand_stmt env rv') proc.p_body;
    proc.p_var_tab |> Hashtbl.iter (fun name _ ->
        Hashtbl.remove env.rename_table name)
  | S_output e ->
    begin match retval with
      | None -> ()
      | Some name ->
        append_stmt env (S_set (name, rename e))
    end
  | S_phi _ -> assert false

let expand env =
  let stmts = get_stmts env in
  env.stmts_rev <- [];
  List.iter (expand_stmt env None) stmts
