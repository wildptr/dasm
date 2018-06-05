open Batteries
open Env
open Inst
open Semant
open Plain

let eCF = E_var (Var.Global "CF"), 1
let ePF = E_var (Var.Global "PF"), 1
let eAF = E_var (Var.Global "AF"), 1
let eZF = E_var (Var.Global "ZF"), 1
let eSF = E_var (Var.Global "SF"), 1
let eDF = E_var (Var.Global "DF"), 1
let eOF = E_var (Var.Global "OF"), 1

let predef_table : (string, proc) Hashtbl.t = Hashtbl.create 0

let lookup_predef name =
  try Hashtbl.find predef_table name
  with Not_found ->
    failwith ("predefined semantic procedure not found: " ^ name)

let cond_expr1 = function
  | 0 -> eOF
  | 1 -> eCF
  | 2 -> eZF
  | 3 -> E_primn (Pn_or, [eCF; eZF]), 1 (* CF|ZF *)
  | 4 -> eSF
  | 5 -> ePF
  | 6 -> E_primn (Pn_xor, [eSF; eOF]), 1 (* SF^OF *)
  | 7 -> E_primn (Pn_or, [eZF; E_primn (Pn_xor, [eSF; eOF]), 1]), 1 (* ZF|(SF^OF) *)
  | _ -> assert false

let cond_expr code =
  let e = cond_expr1 (code lsr 1) in
  if (code land 1) = 0 then e else not_expr e

let elaborate_reg r =
  match r with
  | R_AL -> E_part ((E_var (Var.Global "EAX"), 32), 0, 8), 8
  | R_CL -> E_part ((E_var (Var.Global "ECX"), 32), 0, 8), 8
  | R_DL -> E_part ((E_var (Var.Global "EDX"), 32), 0, 8), 8
  | R_BL -> E_part ((E_var (Var.Global "EBX"), 32), 0, 8), 8
  | R_AH -> E_part ((E_var (Var.Global "EAX"), 32), 8, 16), 8
  | R_CH -> E_part ((E_var (Var.Global "ECX"), 32), 8, 16), 8
  | R_DH -> E_part ((E_var (Var.Global "EDX"), 32), 8, 16), 8
  | R_BH -> E_part ((E_var (Var.Global "EBX"), 32), 8, 16), 8
  | R_AX -> E_part ((E_var (Var.Global "EAX"), 32), 0, 16), 16
  | R_CX -> E_part ((E_var (Var.Global "ECX"), 32), 0, 16), 16
  | R_DX -> E_part ((E_var (Var.Global "EDX"), 32), 0, 16), 16
  | R_BX -> E_part ((E_var (Var.Global "EBX"), 32), 0, 16), 16
  | R_SP -> E_part ((E_var (Var.Global "ESP"), 32), 0, 16), 16
  | R_BP -> E_part ((E_var (Var.Global "EBP"), 32), 0, 16), 16
  | R_SI -> E_part ((E_var (Var.Global "ESI"), 32), 0, 16), 16
  | R_DI -> E_part ((E_var (Var.Global "EDI"), 32), 0, 16), 16
  | _ -> E_var (Var.Global (string_of_reg r)), size_of_reg r

(* TODO: don't hard code address size *)

let elaborate_mem_index (reg, scale) =
  let e_reg = elaborate_reg reg in
  if scale = 0 then e_reg
  else
    let e_scale = make_lit 2 (Nativeint.of_int scale) in
    E_prim2 (P2_shiftleft, e_reg, e_scale), 32

let make_address addr = make_lit 32 addr

let elaborate_mem_addr m =
  let seg = elaborate_reg m.seg in
  let off =
    match m.base, m.index with
    | Some base, Some index ->
      let e_base = elaborate_reg base in
      let e_index = elaborate_mem_index index in
      let to_be_added =
        if m.disp = 0n then [e_base; e_index]
        else
          let e_disp = make_address m.disp in
          [e_base; e_index; e_disp]
      in
      E_primn (Pn_add, to_be_added), 32
    | Some base, None ->
      let e_base = elaborate_reg base in
      if m.disp = 0n then e_base
      else
        let e_disp = make_address m.disp in
        E_primn (Pn_add, [e_base; e_disp]), 32
    | None, Some index ->
      let e_index = elaborate_mem_index index in
      if m.disp = 0n then e_index
      else
        let e_disp = make_address m.disp in
        E_primn (Pn_add, [e_index; e_disp]), 32
    | None, None ->
      make_address m.disp
  in
  seg, off

let elaborate_operand pc' = function
  | O_reg reg -> elaborate_reg reg
  | O_mem (mem, size) ->
    if size <= 0 then failwith "size of operand invalid";
    let seg, off = elaborate_mem_addr mem in
    E_load (size, seg, off), size*8
  | O_imm (imm, size) ->
    if size <= 0 then failwith "size of operand invalid";
    make_lit (size*8) imm
  | O_offset ofs -> make_address (Nativeint.(pc' + ofs))
  | _ -> failwith "invalid operand type"

let elaborate_writeback emit o_dst e_data =
  match o_dst with
  | O_reg r -> emit (S_set (Var.Global (string_of_reg r), e_data))
  | O_mem (m, size) ->
    assert (size > 0);
    let seg, off = elaborate_mem_addr m in
    emit (S_store (size, seg, off, e_data))
  | _ -> failwith "elaborate_writeback: invalid operand type"

let fnname_of_op = function
  | I_ADC -> "adc"
  | I_ADD -> "add"
  | I_AND -> "and"
  | I_CALL -> "call"
  | I_CMP -> "sub"
  | I_DEC -> "dec"
  | I_INC -> "inc"
  | I_LEAVE -> "leave"
  | I_NEG -> "neg"
  | I_NOT -> "not"
  | I_OR -> "or"
  | I_POP -> "pop"
  | I_PUSH -> "push"
  | I_RET -> "ret"
  | I_RETN -> "retn"
  | I_SAR -> "sar"
  | I_SBB -> "sbb"
  | I_SHL -> "shl"
  | I_SHR -> "shr"
  | I_SUB -> "sub"
  | I_TEST -> "and"
  | I_XOR -> "xor"
  | _ -> failwith "fnname_of_op: not implemented"

let rec expand_stmt env pc retval stmt =
  let rename_var = function
    | Var.Local name ->
      begin
        try Hashtbl.find env.rename_table name
        with Not_found -> failwith ("unbound local variable: "^name)
      end
    | Var.PC -> E_lit (Bitvec.of_nativeint 32 pc)
    | v -> E_var v
  in
  let rename e = subst rename_var e in
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
      arg_arr |> Array.map begin fun (argp, _) ->
        argp |> function E_lit _ -> true | _ -> false
      end
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
    let temps = ref [] in
    proc.p_var_tab |> Hashtbl.iter begin fun name width ->
      let arg =
        match Map.String.Exceptionless.find name param_index_map with
        | Some i when arg_is_const.(i) -> fst arg_arr.(i)
        | _ ->
          let temp = acquire_temp env width in
          temps := temp :: !temps;
          E_var temp
      in
      Hashtbl.add env.rename_table name arg
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
    List.iter (expand_stmt env pc rv') proc.p_body;
    proc.p_var_tab |> Hashtbl.iter begin fun name _ ->
      Hashtbl.remove env.rename_table name
    end;
    !temps |> List.iter (release_temp env)
  | S_return e ->
    begin match retval with
      | None -> ()
      | Some name ->
        emit env (S_set (name, rename e))
    end
  | _ -> assert false

let elaborate_inst env pc inst =
  let op = operation_of inst in
  let lsize = inst.variant land 15 in (* log size in bytes *)
  let size = 8 lsl lsize in
  let operands = operands_of inst in
  let fn inst =
    let fnname_base = fnname_of_op op in
    let fnname = Printf.sprintf "%s%d" fnname_base size in
    lookup_predef fnname
  in
  emit env (S_label pc);
  let inst_stmts = ref [] in
  let emit' s =
    inst_stmts := s :: !inst_stmts
  in
  let pc' = Nativeint.(pc + of_int (length_of inst)) in
  begin
    match op with
    | I_ADD | I_OR | I_ADC | I_SBB | I_AND | I_SUB | I_XOR
    | I_SHL | I_SHR | I_SAR | I_INC | I_DEC | I_NEG | I_NOT ->
      let temp = acquire_temp env size in
      let args = operands |> List.map (elaborate_operand pc') in
      emit' (S_call (fn inst, args, Some temp));
      elaborate_writeback emit' (List.hd operands) (E_var temp, size);
      release_temp env temp
    | I_CMP | I_PUSH | I_TEST | I_CALL | I_RET | I_RETN | I_LEAVE ->
      let args = operands |> List.map (elaborate_operand pc') in
      emit' (S_call (fn inst, args, None))
    | I_POP ->
      let temp = acquire_temp env size in
      emit' (S_call (fn inst, [], Some temp));
      elaborate_writeback emit' (List.hd operands) (E_var temp, size);
      release_temp env temp
    | I_MOV ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      elaborate_writeback emit' dst (elaborate_operand pc' src)
    | I_MOVZX | I_MOVSX ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      (*let lsize_src = inst.variant lsr 4 in*)
      (*let src_size = 8 lsl lsize_src in*)
      let src' = elaborate_operand pc' src in
      elaborate_writeback emit' dst (E_extend (op = I_MOVSX, src', size), size)
    | I_LEA ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      let _, addr =
        match src with
        | O_mem (m, _size) -> elaborate_mem_addr m
        | _ -> assert false
      in
      elaborate_writeback emit' dst addr
    | I_JMP | I_CJMP ->
      let cond_opt =
        if op = I_CJMP then
          Some (cond_expr (inst.variant lsr 4))
        else
          None
      in
      emit' (S_jump (cond_opt, elaborate_operand pc' (List.hd operands)))
    | I_SET ->
      let dst =
        match operands with
        | [dst] -> dst
        | _ -> assert false
      in
      let cond = cond_expr (inst.variant lsr 4) in
      let data = E_extend (false, cond, 8), 8 in
      elaborate_writeback emit' dst data
    | I_XCHG ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      let dst' = elaborate_operand pc' dst in
      let src' = elaborate_operand pc' src in
      elaborate_writeback emit' dst src';
      elaborate_writeback emit' src dst'
    | _ ->
      Format.printf "elaborate_inst: not implemented: %a@." Inst.pp inst
  end;
  List.rev !inst_stmts |> List.iter (expand_stmt env pc' None)

let elaborate_basic_block env bb =
  let open Cfg in
  let pc = ref bb.start in
  bb.stmts |> List.iter begin fun inst ->
    elaborate_inst env !pc inst;
    pc := Nativeint.(!pc + of_int (length_of inst))
  end;
  let stmts = get_stmts env in
  env.stmts_rev <- [];
  { bb with stmts }

let elaborate_cfg db cfg =
  let open Cfg in
  let env = Env.create db in
  let node = cfg.node |> Array.map (elaborate_basic_block env) in
  let succ = Array.copy cfg.succ in
  let pred = Array.copy cfg.pred in
  { node; succ; pred; edges = cfg.edges }, env

let fail_with_parsing_error filename lexbuf msg =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.fprintf stderr "%s:%d:%d: %s\n" filename line col msg;
  failwith "invalid spec"

let load_spec filepath =
  let in_chan = open_in filepath in
  let lexbuf = Lexing.from_channel in_chan in
  let spec_ast =
    try
      Spec_parser.top Spec_lexer.read lexbuf
    with
    | Spec_parser.Error ->
      fail_with_parsing_error filepath lexbuf "syntax error"
    | Spec_lexer.Error msg ->
      fail_with_parsing_error filepath lexbuf msg
  in
  close_in in_chan;
  let symtab =
    try Translate.translate_ast spec_ast with
    | Translate.Index_out_of_bounds ((e,w),b) ->
      let open Format in
      fprintf err_formatter
        "width of expression %a is %d, %d is out of bounds@."
        Spec_ast.pp_astexpr e w b;
      exit 1
  in
  symtab |> Map.String.iter begin fun key data ->
    match data with
    | Translate.Proc proc -> Hashtbl.add predef_table key proc
    | _ -> ()
  end
