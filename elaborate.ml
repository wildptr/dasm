open Batteries
open Env
open Inst
open Semant

let eCF = E_var "CF"
let ePF = E_var "PF"
let eAF = E_var "AF"
let eZF = E_var "ZF"
let eSF = E_var "SF"
let eDF = E_var "DF"
let eOF = E_var "OF"

let predef_table : (string, proc) Hashtbl.t = Hashtbl.create 0

let lookup_predef name =
  try Hashtbl.find predef_table name
  with Not_found ->
    failwith ("predefined semantic procedure not found: " ^ name)

let cond_expr1 = function
  | 0 -> eOF
  | 1 -> eCF
  | 2 -> eZF
  | 3 -> E_primn (Pn_or, [eCF; eZF]) (* CF|ZF *)
  | 4 -> eSF
  | 5 -> ePF
  | 6 -> E_primn (Pn_xor, [eSF; eOF]) (* SF^OF *)
  | 7 -> E_primn (Pn_or, [eZF; E_primn (Pn_xor, [eSF; eOF])]) (* ZF|(SF^OF) *)
  | _ -> assert false

let cond_expr code =
  let e = cond_expr1 (code lsr 1) in
  if (code land 1) = 0 then e else E_prim1 (P1_not, e)

let elaborate_reg r =
  match r with
  | R_AL -> E_part (E_var "EAX", 0, 8)
  | R_CL -> E_part (E_var "ECX", 0, 8)
  | R_DL -> E_part (E_var "EDX", 0, 8)
  | R_BL -> E_part (E_var "EBX", 0, 8)
  | R_AH -> E_part (E_var "EAX", 8, 16)
  | R_CH -> E_part (E_var "ECX", 8, 16)
  | R_DH -> E_part (E_var "EDX", 8, 16)
  | R_BH -> E_part (E_var "EBX", 8, 16)
  | R_AX -> E_part (E_var "EAX", 0, 16)
  | R_CX -> E_part (E_var "ECX", 0, 16)
  | R_DX -> E_part (E_var "EDX", 0, 16)
  | R_BX -> E_part (E_var "EBX", 0, 16)
  | R_SP -> E_part (E_var "ESP", 0, 16)
  | R_BP -> E_part (E_var "EBP", 0, 16)
  | R_SI -> E_part (E_var "ESI", 0, 16)
  | R_DI -> E_part (E_var "EDI", 0, 16)
  | _ -> E_var (string_of_reg r)

let elaborate_mem_index (reg, scale) =
  let e_reg = elaborate_reg reg in
  if scale = 0 then e_reg
  else
    let e_scale = E_lit (Bitvec.of_int 2 scale) in
    E_prim2 (P2_shiftleft, e_reg, e_scale)

let make_address addr = E_lit (Bitvec.of_nativeint 32 addr)

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
      E_primn (Pn_add, to_be_added)
    | Some base, None ->
      let e_base = elaborate_reg base in
      if m.disp = 0n then e_base
      else
        let e_disp = make_address m.disp in
        E_primn (Pn_add, [e_base; e_disp])
    | None, Some index ->
      let e_index = elaborate_mem_index index in
      if m.disp = 0n then e_index
      else
        let e_disp = make_address m.disp in
        E_primn (Pn_add, [e_index; e_disp])
    | None, None ->
      make_address m.disp
  in
  seg, off

let elaborate_operand pc' = function
  | O_reg reg -> elaborate_reg reg
  | O_mem (mem, size) ->
    if size <= 0 then failwith "size of operand invalid";
    let seg, off = elaborate_mem_addr mem in
    E_load (size, seg, off)
  | O_imm (imm, size) ->
    if size <= 0 then failwith "size of operand invalid";
    E_lit (Bitvec.of_nativeint (size*8) imm)
  | O_offset ofs -> make_address (Nativeint.(pc' + ofs))
  | _ -> failwith "invalid operand type"

let elaborate_writeback env o_dst e_data =
  match o_dst with
  | O_reg r -> emit env (S_set (string_of_reg r, e_data))
  | O_mem (m, size) ->
    assert (size > 0);
    let seg, off = elaborate_mem_addr m in
    emit env (S_store (size, seg, off, e_data))
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

let elaborate_inst env pc inst =
  let op = operation_of inst in
  let lsize = inst.variant land 15 in (* log size in bytes *)
  let operands = operands_of inst in
  let fn inst =
    let fnname_base =
      try fnname_of_op op
      with Failure msg ->
        Format.printf "%s: %a@." msg Inst.pp inst;
        exit 1
    in
    let fnname = Printf.sprintf "%s%d" fnname_base (1 lsl (lsize+3)) in
    lookup_predef fnname
  in
  let pc' = Nativeint.(pc + of_int (length_of inst)) in
  try
    match op with
    | I_ADD | I_OR | I_ADC | I_SBB | I_AND | I_SUB | I_XOR
    | I_SHL | I_SHR | I_SAR | I_INC | I_DEC | I_NEG | I_NOT ->
      let temp = new_temp env (8 lsl lsize) in
      let args = operands |> List.map (elaborate_operand pc') in
      emit env (S_call (fn inst, args, Some temp));
      elaborate_writeback env (List.hd operands) (E_var temp)
    | I_CMP | I_PUSH | I_TEST | I_RET | I_RETN | I_LEAVE ->
      let args = operands |> List.map (elaborate_operand pc') in
      emit env (S_call (fn inst, args, None))
    | I_POP ->
      let temp = new_temp env (8 lsl lsize) in
      emit env (S_call (fn inst, [], Some temp));
      elaborate_writeback env (List.hd operands) (E_var temp)
    | I_CALL ->
      let args = operands |> List.map (elaborate_operand pc') in
      let arg_pc = E_lit (Bitvec.of_nativeint (8 lsl lsize) pc') in
      emit env (S_call (fn inst, arg_pc :: args, None))
    | I_MOV ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      elaborate_writeback env dst (elaborate_operand pc' src)
    | I_MOVZX | I_MOVSX ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      (*let lsize_src = inst.variant lsr 4 in*)
      let dst_size = 8 lsl lsize in
      (*let src_size = 8 lsl lsize_src in*)
      let src' = elaborate_operand pc' src in
      elaborate_writeback env dst (E_extend (op = I_MOVSX, src', dst_size))
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
      elaborate_writeback env dst addr
    | I_JMP | I_CJMP ->
      let cond_opt =
        if op = I_CJMP then
          Some (cond_expr (inst.variant lsr 4))
        else
          None
      in
      emit env
        (S_jump (cond_opt, elaborate_operand pc' (List.hd operands)))
    | I_SET ->
      let dst =
        match operands with
        | [dst] -> dst
        | _ -> assert false
      in
      let cond = cond_expr (inst.variant lsr 4) in
      let data = E_extend (false, cond, 8) in
      elaborate_writeback env dst data
    | I_XCHG ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      let dst' = elaborate_operand pc' dst in
      let src' = elaborate_operand pc' src in
      elaborate_writeback env dst src';
      elaborate_writeback env src dst'
    | _ ->
      Format.printf "elaborate_inst: not implemented: %a@." Inst.pp inst
  with Failure msg ->
    (* internal error *)
    Format.printf "%s: %a@." msg Inst.pp inst;
    exit 1

let elaborate_basic_block expand env bb =
  let open Cfg in
  let pc = ref bb.start in
  bb.stmts |> List.iter begin fun inst ->
    elaborate_inst env !pc inst;
    pc := Nativeint.(!pc + of_int (length_of inst))
  end;
  if expand then Expand.expand env;
  let stmts = get_stmts env in
  env.stmts_rev <- [];
  { bb with stmts }

let elaborate_cfg db expand cfg =
  let env = Env.create db in
  let node' = cfg.Cfg.node |> Array.map (elaborate_basic_block expand env) in
  { cfg with Cfg.node = node' }, env

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
