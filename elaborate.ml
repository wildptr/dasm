open Inst
open Semant
open Util

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

let to_label addr = Printf.sprintf "L%x" addr

let cond_expr1 = function
  | 0x0 -> eOF
  | 0x1 -> eCF
  | 0x2 -> eZF
  | 0x3 -> E_prim (P_or [eCF; eZF]) (* CF|XF *)
  | 0x4 -> eSF
  | 0x5 -> ePF
  | 0x6 -> E_prim (P_xor [eSF; eOF]) (* SF^OF *)
  | 0x7 -> E_prim (P_or [eZF; E_prim (P_xor [eSF; eOF])]) (* ZF|(SF^OF) *)
  | _ -> assert false

let cond_expr code =
  let e = cond_expr1 (code lsr 1) in
  if (code land 1) = 0 then e else E_prim (P_not e)

let name_of_reg r = String.uppercase_ascii (string_of_reg r)

let elaborate_reg r = E_var (name_of_reg r)

let elaborate_mem_index (reg, scale) =
  let e_reg = elaborate_reg reg in
  if scale = 0 then e_reg
  else
    let e_scale = E_literal (Bitvec.of_int 2 scale) in
    E_prim (P_shiftleft (e_reg, e_scale))

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
    E_prim (P_add to_be_added)
  | Some base, None ->
    let e_base = elaborate_reg base in
    if m.disp = 0 then e_base
    else
      let e_disp = make_address m.disp in
      E_prim (P_add [e_base; e_disp])
  | None, Some index ->
    let e_index = elaborate_mem_index index in
    if m.disp = 0 then e_index
    else
      let e_disp = make_address m.disp in
      E_prim (P_add [e_index; e_disp])
  | None, None ->
    make_address m.disp

let elaborate_operand pc' = function
  | O_reg reg -> elaborate_reg reg
  | O_mem (mem, size) ->
    if size <= 0 then failwith "size of operand invalid";
    let e_addr = elaborate_mem_addr mem in
    E_load (size, e_addr)
  | O_imm (imm, size) ->
    if size <= 0 then failwith "size of operand invalid";
    E_literal (Bitvec.of_int (size*8) imm)
  | O_offset ofs -> make_address (pc'+ofs)
  | _ -> failwith "invalid operand type"

let elaborate_writeback env o_dst e_data =
  match o_dst with
  | O_reg r ->
    let module L = struct
      type reg_type = Other | OL | OH | OX | EOX
    end in
    let open L in
    let reg_type =
      match r with
      | R_AL | R_CL | R_DL | R_BL -> OL
      | R_AH | R_CH | R_DH | R_BH -> OH
      | R_AX | R_CX | R_DX | R_BX -> OX
      | R_EAX | R_ECX | R_EDX | R_EBX -> EOX
      | _ -> Other
    in
    if reg_type = Other then
      append_stmt env (S_set (name_of_reg r, e_data))
    else begin
      let temp = new_temp env (size_of_reg r) in
      let e_temp = E_var temp in
      append_stmt env (S_set (temp, e_data));
      let ol, oh, ox, eox =
        match r with
        | R_AL | R_AH | R_AX | R_EAX -> "AL", "AH", "AX", "EAX"
        | R_CL | R_CH | R_CX | R_ECX -> "CL", "CH", "CX", "ECX"
        | R_DL | R_DH | R_DX | R_EDX -> "DL", "DH", "DX", "EDX"
        | R_BL | R_BH | R_BX | R_EBX -> "BL", "BH", "BX", "EBX"
        | _ -> assert false
      in
      match reg_type with
      | EOX ->
        append_stmt env (S_set (eox, e_temp));
        append_stmt env (S_set (ox, E_part (e_temp, 0, 16)));
        append_stmt env (S_set (oh, E_part (e_temp, 8, 16)));
        append_stmt env (S_set (ol, E_part (e_temp, 0, 8)));
      | OX ->
        let bits16_32 = E_part (E_var eox, 16, 32) in
        append_stmt env (S_set (eox, E_prim (P_concat [bits16_32; e_temp])));
        append_stmt env (S_set (ox, e_temp));
        append_stmt env (S_set (oh, E_part (e_temp, 8, 16)));
        append_stmt env (S_set (ol, E_part (e_temp, 0, 8)));
      | OH ->
        let bits16_32 = E_part (E_var eox, 16, 32) in
        append_stmt env (S_set (eox, E_prim (P_concat [bits16_32; e_temp; E_var ol])));
        append_stmt env (S_set (ox, E_prim (P_concat [e_temp; E_var ol])));
        append_stmt env (S_set (oh, e_temp));
      | OL ->
        let bits8_32 = E_part (E_var eox, 8, 32) in
        append_stmt env (S_set (eox, E_prim (P_concat [bits8_32; e_temp])));
        append_stmt env (S_set (ox, E_prim (P_concat [E_var oh; e_temp])));
        append_stmt env (S_set (ol, e_temp));
      | _ -> assert false
    end
  | O_mem (m, size) ->
    assert (size > 0);
    let e_addr = elaborate_mem_addr m in
    append_stmt env (S_store (size, e_addr, e_data))
  | _ -> failwith "elaborate_writeback: invalid operand type"

let fnname_of_op = function
  | I_adc -> "adc"
  | I_add -> "add"
  | I_and -> "and"
  | I_call -> "call"
  | I_cmp -> "sub"
  | I_or -> "or"
  | I_pop -> "pop"
  | I_push -> "push"
  | I_ret -> "ret"
  | I_retn -> "retn"
  | I_sar -> "sar"
  | I_sbb -> "sbb"
  | I_shl -> "shl"
  | I_shr -> "shr"
  | I_sub -> "sub"
  | I_test -> "and"
  | I_xor -> "xor"
  | _ -> failwith "fnname_of_op: not implemented"

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
    | I_cmp | I_push | I_ret | I_retn | I_test ->
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
    | I_jmp ->
      append_stmt env (S_jump (elaborate_operand pc' (List.hd operands)))
    | I_cjmp ->
      let cond = cond_expr (inst.variant lsr 2) in
      append_stmt env (S_br (cond, elaborate_operand pc' (List.hd operands)))
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
      let result =
        if op = I_movzx then
          E_prim (P_zeroextend (src', dst_size))
        else
          E_prim (P_signextend (src', dst_size))
      in
      elaborate_writeback env dst result
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
      append_stmt env (S_call (fn inst, [make_address pc'; dst'], None))
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
  symtab |> StringMap.iter begin fun key data ->
    match data with
    | Translate.Proc proc -> Hashtbl.add predef_table key proc
    | _ -> ()
  end
