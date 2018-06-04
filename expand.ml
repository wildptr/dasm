open Env
open Semant

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
(*
    begin match loc.[0] with
      | 'A'..'Z' ->
        let r = Inst.lookup_reg loc in
        let module L = struct
          type reg_type = Other | OL | OH | OX | EOX | OO | EOO
        end in
        let open L in
        let reg_type =
          match r with
          | R_AL | R_CL | R_DL | R_BL -> OL
          | R_AH | R_CH | R_DH | R_BH -> OH
          | R_AX | R_CX | R_DX | R_BX -> OX
          | R_EAX | R_ECX | R_EDX | R_EBX -> EOX
          | R_SP | R_BP | R_SI | R_DI -> OO
          | R_ESP | R_EBP | R_ESI | R_EDI -> EOO
          | _ -> Other
        in
        if reg_type = Other then
          emit env (S_set (Inst.name_of_reg r, e'))
        else begin
          let ol, oh, ox, eox =
            match r with
            | R_AL | R_AH | R_AX | R_EAX -> "AL", "AH", "AX", "EAX"
            | R_CL | R_CH | R_CX | R_ECX -> "CL", "CH", "CX", "ECX"
            | R_DL | R_DH | R_DX | R_EDX -> "DL", "DH", "DX", "EDX"
            | R_BL | R_BH | R_BX | R_EBX -> "BL", "BH", "BX", "EBX"
            | R_SP | R_ESP -> "", "", "SP", "ESP"
            | R_BP | R_EBP -> "", "", "BP", "EBP"
            | R_SI | R_ESI -> "", "", "SI", "ESI"
            | R_DI | R_EDI -> "", "", "DI", "EDI"
            | _ -> assert false
          in
          let bits16_32 = E_part (E_var eox, 16, 32) in
          match reg_type with
          | EOX ->
            emit env (S_set (eox, e'));
            emit env (S_set (ox, E_part (E_var eox, 0, 16)));
            emit env (S_set (oh, E_part (E_var eox, 8, 16)));
            emit env (S_set (ol, E_part (E_var eox, 0, 8)));
          | OX ->
            emit env (S_set (ox, e'));
            emit env (S_set (eox, E_primn (Pn_concat, [bits16_32; E_var ox])));
            emit env (S_set (oh, E_part (E_var ox, 8, 16)));
            emit env (S_set (ol, E_part (E_var ox, 0, 8)));
          | OH ->
            emit env (S_set (oh, e'));
            emit env (S_set (ox, E_primn (Pn_concat, [E_var oh; E_var ol])));
            emit env (S_set (eox, E_primn (Pn_concat, [bits16_32; E_var ox])));
          | OL ->
            emit env (S_set (ol, e'));
            emit env (S_set (ox, E_primn (Pn_concat, [E_var oh; E_var ol])));
            emit env (S_set (eox, E_primn (Pn_concat, [bits16_32; E_var ox])));
          | EOO ->
            emit env (S_set (eox, e'));
            emit env (S_set (ox, E_part (E_var eox, 0, 16)))
          | OO ->
            emit env (S_set (ox, e'));
            emit env (S_set (eox, E_primn (Pn_concat, [bits16_32; E_var ox])))
          | _ -> assert false
        end
      | _ -> emit env (S_set (rename_var loc, e'))
    end
*)
    emit env (S_set (rename_var loc, e'))
  | S_store (size, seg, addr, data) ->
    emit env (S_store (size, seg, rename addr, rename data))
  | S_jump (c, e) ->
    emit env (S_jump (BatOption.map rename c, rename e))
  | S_call (proc, args, rv) ->
    (* variable table *)
    proc.p_var_tab |> Hashtbl.iter (fun name width ->
        let name' = new_temp env width in
        Hashtbl.add env.rename_table name name');
    (* pass arguments *)
    (* TODO: check arity & widths *)
    begin
      try
        List.combine args proc.p_param_names |> List.iter
          (fun (arg, param_name) ->
             emit env (S_set (rename_var param_name, arg)));
      with e ->
        let open Format in
        printf "procedure: %s@." proc.p_name;
        printf "arguments:@.";
        args |> List.iter (printf "%a@." pp_expr);
        raise e
    end;
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
  | S_return e ->
    begin match retval with
      | None -> ()
      | Some name ->
        emit env (S_set (name, rename e))
    end
  | _ -> assert false

let expand env =
  let stmts = get_stmts env in
  env.stmts_rev <- [];
  List.iter (expand_stmt env None) stmts
