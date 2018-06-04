open Batteries
open Env
open Semant

let rec expand_stmt env retval stmt =
  let pc = ref 0n in (* initial value should never be used... *)
  let rename_var = function
    | V_local name ->
      begin
        try Hashtbl.find env.rename_table name
        with Not_found -> failwith ("unbound local variable: "^name)
      end
    | V_pc -> E_lit (Bitvec.of_nativeint 32 !pc)
    | v -> E_var v
  in
  let rename e = subst_expr rename_var e in
  match stmt with
  | S_set (var, e) ->
    let var' =
      match rename_var var with
      | E_lit _ -> failwith "assignment to parameter (via ordinary assignment)"
      | E_var var' -> var'
      | _ -> assert false
    in
    let e' = rename e in
    emit env (S_set (var', e'))
  | S_store (size, seg, addr, data) ->
    emit env (S_store (size, seg, rename addr, rename data))
  | S_jump (c, e) ->
    emit env (S_jump (Option.map rename c, rename e))
  | S_call (proc, args, rv) ->
    (* try not to create temporary variables for constants, as they confuse the
       recursive procedure scanner *)
    let arg_arr = Array.of_list args in
    let n_arg = Array.length arg_arr in
    let arg_is_const =
      arg_arr |> Array.map (function E_lit _ -> true | _ -> false)
    in
    let n_param = List.length proc.p_param_names in
    (* TODO: check widths *)
    if n_param <> n_arg then begin
      let open Format in
      printf "procedure: %s@." proc.p_name;
      printf "arguments:@.";
      args |> List.iter (printf "%a@." pp_expr);
      failwith "wrong arity"
    end;
    let param_arr = proc.p_param_names |> Array.of_list in
    let param_index_map =
      proc.p_param_names |> List.mapi (fun i name -> name, i) |>
      List.fold_left (fun m (k, v) -> Map.String.add k v m) Map.String.empty
    in
    proc.p_var_tab |> Hashtbl.iter begin fun name width ->
      let arg_temp =
        match Map.String.Exceptionless.find name param_index_map with
        | Some i when arg_is_const.(i) -> arg_arr.(i)
        | _ -> E_var (new_temp env width)
      in
      Hashtbl.add env.rename_table name arg_temp
    end;
    (* pass arguments *)
    for i=0 to n_arg-1 do
      if not arg_is_const.(i) then
        let arg = arg_arr.(i) in
        let param_name = param_arr.(i) in
        let param_var =
          match Hashtbl.find env.rename_table param_name with
          | E_var v -> v
          | _ -> assert false
        in
        emit env (S_set (param_var, rename arg))
    done;
    let rv' =
      rv |> Option.map begin fun rv ->
        match rename_var rv with
        | E_var v -> v
        | E_lit _ -> failwith "assignment to parameter (via call)"
        | _ -> assert false
      end
    in
    List.iter (expand_stmt env rv') proc.p_body;
    proc.p_var_tab |> Hashtbl.iter begin fun name _ ->
      Hashtbl.remove env.rename_table name
    end
  | S_return e ->
    begin match retval with
      | None -> ()
      | Some name ->
        emit env (S_set (name, rename e))
    end
  | S_label va as s ->
    pc := va;
    emit env s
  | _ -> assert false

let expand env =
  let stmts = get_stmts env in
  env.stmts_rev <- [];
  List.iter (expand_stmt env None) stmts
