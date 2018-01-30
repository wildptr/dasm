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

let elaborate_reg r = E_var (name_of_reg r)

let elaborate_mem_index (reg, scale) =
  let e_reg = elaborate_reg reg in
  if scale = 0 then e_reg
  else
    let e_scale = E_literal (Bitvec.of_int 2 scale) in
    E_prim2 (P2_shiftleft, e_reg, e_scale)

let make_address addr = E_literal (Bitvec.of_int 32 addr)

let elaborate_mem_addr m =
  match m.base, m.index with
  | Some base, Some index ->
    let e_base = elaborate_reg base in
    let e_index = elaborate_mem_index index in
    let to_be_added =
      if m.disp = 0 then [e_base; e_index]
      else
        let e_disp = make_address m.disp in
        [e_base; e_index; e_disp]
    in
    E_primn (Pn_add, to_be_added)
  | Some base, None ->
    let e_base = elaborate_reg base in
    if m.disp = 0 then e_base
    else
      let e_disp = make_address m.disp in
      E_primn (Pn_add, [e_base; e_disp])
  | None, Some index ->
    let e_index = elaborate_mem_index index in
    if m.disp = 0 then e_index
    else
      let e_disp = make_address m.disp in
      E_primn (Pn_add, [e_index; e_disp])
  | None, None ->
    make_address m.disp

let elaborate_operand pc' = function
  | O_reg reg -> elaborate_reg reg
  | O_mem (mem, size) ->
    if size <= 0 then failwith "size of operand invalid";
    let e_addr = elaborate_mem_addr mem in
    E_load (size, e_addr, E_var "M")
  | O_imm (imm, size) ->
    if size <= 0 then failwith "size of operand invalid";
    E_literal (Bitvec.of_int (size*8) imm)
  | O_offset ofs -> make_address (pc'+ofs)
  | _ -> failwith "invalid operand type"

let elaborate_writeback env o_dst e_data =
  match o_dst with
  | O_reg r -> append_stmt env (S_set (name_of_reg r, e_data))
  | O_mem (m, size) ->
    assert (size > 0);
    let e_addr = elaborate_mem_addr m in
    append_stmt env (S_store (size, e_addr, e_data, "M", E_var "M"))
  | _ -> failwith "elaborate_writeback: invalid operand type"

let fnname_of_op = function
  | I_adc -> "adc"
  | I_add -> "add"
  | I_and -> "and"
  | I_call -> "push"
  | I_cmp -> "sub"
  | I_or -> "or"
  | I_pop -> "pop"
  | I_push -> "push"
  | I_ret -> "pop"
  | I_retn -> "pop"
  | I_sar -> "sar"
  | I_sbb -> "sbb"
  | I_shl -> "shl"
  | I_shr -> "shr"
  | I_sub -> "sub"
  | I_test -> "and"
  | I_xor -> "xor"
  | _ -> failwith "fnname_of_op: not implemented"

let xxx env pc =
  let jump = Hashtbl.find env.jump_info pc in
  let d, u =
    match jump with
    | J_unknown -> [], (Array.to_list reg_name_table) |> List.map (fun name -> E_var name)
    | J_resolved -> [], []
    | J_call ->
      ["M"; "EAX"; "AX"; "AH"; "AL"; "ECX"; "CX"; "CH"; "CL"; "EDX"; "DX"; "DH"; "DL"; "ESP"; "SP"],
      ["M"; "ECX"; "CX"; "CH"; "CL"; "EDX"; "DX"; "DH"; "DL"; "ESP"; "SP"] |> List.map (fun name -> E_var name)
    | J_ret ->
      [], ["M"; "EAX"; "EBX"; "ESP"; "EBP"; "ESI"; "EDI"] |> List.map (fun name -> E_var name)
  in
  d, u

let elaborate_inst env pc inst =
  let op = operation_of inst in
  let lsize = inst.variant land 3 in (* log size in bytes *)
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
  let pc' = pc + length_of inst in
  try
    match op with
    | I_add | I_or | I_adc | I_sbb | I_and | I_sub | I_xor | I_shl | I_shr | I_sar ->
      let temp = new_temp env (8 lsl lsize) in
      let args = operands |> List.map (elaborate_operand pc') in
      append_stmt env (S_call (fn inst, args, Some temp));
      elaborate_writeback env (List.hd operands) (E_var temp)
    | I_cmp | I_push | I_test ->
      let args = operands |> List.map (elaborate_operand pc') in
      append_stmt env (S_call (fn inst, args, None))
    | I_pop ->
      let temp = new_temp env (8 lsl lsize) in
      append_stmt env (S_call (fn inst, [], Some temp));
      elaborate_writeback env (List.hd operands) (E_var temp)
    | I_mov ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      elaborate_writeback env dst (elaborate_operand pc' src)
    | I_lea ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      let addr =
        match src with
        | O_mem (m, _size) -> elaborate_mem_addr m
        | _ -> assert false
      in
      elaborate_writeback env dst addr
    | I_jmp | I_cjmp ->
      let cond_opt =
        if op = I_cjmp then
          Some (cond_expr (inst.variant lsr 2))
        else
          None
      in
      let d, u = xxx env pc in
      append_stmt env (S_jump (cond_opt, elaborate_operand pc' (List.hd operands), d, u))
    | I_movzx | I_movsx ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      (*let lsize_src = inst.variant lsr 2 in*)
      let dst_size = 8 lsl lsize in
      (*let src_size = 8 lsl lsize_src in*)
      let src' = elaborate_operand pc' src in
      elaborate_writeback env dst (E_extend (op = I_movsx, src', dst_size))
    | I_xchg ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      let dst' = elaborate_operand pc' dst in
      let src' = elaborate_operand pc' src in
      elaborate_writeback env dst src';
      elaborate_writeback env src dst'
    | I_call ->
      let dst' = elaborate_operand pc' (List.hd operands) in
      (* push pc *)
      append_stmt env (S_call (fn inst, [make_address pc'], None));
      (* jump dst *)
      let d, u = xxx env pc in
      append_stmt env (S_jump (None, dst', d, u))
    | I_ret ->
      (* pop addr *)
      let addr = new_temp env (8 lsl lsize) in
      append_stmt env (S_call (fn inst, [], Some addr));
      (* jump addr *)
      let d, u = xxx env pc in
      append_stmt env (S_jump (None, E_var addr, d, u))
    | I_retn ->
      let inc = elaborate_operand pc' (List.hd operands) in
      (* pop addr *)
      let addr = new_temp env (8 lsl lsize) in
      append_stmt env (S_call (fn inst, [], Some addr));
      (* increment SP *)
      let sp_name =
        match lsize with
        | 1 -> "SP"
        | 2 -> "ESP"
        | _ -> assert false
      in
      append_stmt env (S_set (sp_name, E_primn (Pn_add, [E_var sp_name; inc])));
      (* jump addr *)
      let d, u = xxx env pc in
      append_stmt env (S_jump (None, E_var addr, d, u))
    | _ ->
      Format.printf "elaborate_inst: not implemented: %a@." Inst.pp inst;
      exit 1
  with Failure msg ->
    (* internal error *)
    Format.printf "%s: %a@." msg Inst.pp inst;
    exit 1

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
  symtab |> BatMap.String.iter begin fun key data ->
    match data with
    | Translate.Proc proc -> Hashtbl.add predef_table key proc
    | _ -> ()
  end
