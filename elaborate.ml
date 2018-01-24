open Inst
open Semant
open Util

let eR0 = E_var "AX"
let eR1 = E_var "CX"
let eR2 = E_var "DX"
let eR3 = E_var "BX"
let eR4 = E_var "SP"
let eR5 = E_var "BP"
let eR6 = E_var "SI"
let eR7 = E_var "DI"
let eCF = E_var "CF"
let ePF = E_var "PF"
let eAF = E_var "AF"
let eZF = E_var "ZF"
let eSF = E_var "SF"
let eDF = E_var "DF"
let eOF = E_var "OF"
let eES = E_var "ES"
let eCS = E_var "CS"
let eSS = E_var "SS"
let eDS = E_var "DS"
let eFS = E_var "FS"
let eGS = E_var "GS"

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

let elaborate_reg = function
  | R_AL -> E_part (eR0, (0, 8))
  | R_CL -> E_part (eR1, (0, 8))
  | R_DL -> E_part (eR2, (0, 8))
  | R_BL -> E_part (eR3, (0, 8))
  | R_AH -> E_part (eR0, (8, 16))
  | R_CH -> E_part (eR1, (8, 16))
  | R_DH -> E_part (eR2, (8, 16))
  | R_BH -> E_part (eR3, (8, 16))
  | R_AX -> E_part (eR0, (0, 16))
  | R_CX -> E_part (eR1, (0, 16))
  | R_DX -> E_part (eR2, (0, 16))
  | R_BX -> E_part (eR3, (0, 16))
  | R_SP -> E_part (eR4, (0, 16))
  | R_BP -> E_part (eR5, (0, 16))
  | R_SI -> E_part (eR6, (0, 16))
  | R_DI -> E_part (eR7, (0, 16))
  | R_EAX -> eR0
  | R_ECX -> eR1
  | R_EDX -> eR2
  | R_EBX -> eR3
  | R_ESP -> eR4
  | R_EBP -> eR5
  | R_ESI -> eR6
  | R_EDI -> eR7
  | R_ES -> eES
  | R_CS -> eCS
  | R_SS -> eSS
  | R_DS -> eDS
  | R_FS -> eFS
  | R_GS -> eGS
  | _ -> failwith "elaborate_reg: not implemented"

let elaborate_mem_index (reg, scale) =
  let e_reg = elaborate_reg reg in
  if scale = 0 then e_reg
  else
    let e_scale = E_literal (Bitvec.of_int 2 scale) in
    E_prim (P_shiftleft (e_reg, e_scale))

let elaborate_disp disp = E_literal (Bitvec.of_int 32 disp)

let elaborate_mem_addr m =
  match m.base, m.index with
  | Some base, Some index ->
    let e_base = elaborate_reg base in
    let e_index = elaborate_mem_index index in
    let to_be_added =
      if m.disp = 0 then [e_base; e_index]
      else
        let e_disp = elaborate_disp m.disp in
        [e_base; e_index; e_disp]
    in
    E_prim (P_add to_be_added)
  | Some base, None ->
    let e_base = elaborate_reg base in
    if m.disp = 0 then e_base
    else
      let e_disp = elaborate_disp m.disp in
      E_prim (P_add [e_base; e_disp])
  | None, Some index ->
    let e_index = elaborate_mem_index index in
    if m.disp = 0 then e_index
    else
      let e_disp = elaborate_disp m.disp in
      E_prim (P_add [e_index; e_disp])
  | None, None ->
    elaborate_disp m.disp

let elaborate_operand pc' env = function
  | O_reg reg -> elaborate_reg reg
  | O_mem (mem, size) ->
    if size <= 0 then failwith "size of operand invalid";
    let e_addr = elaborate_mem_addr mem in
    E_load (size, e_addr)
  | O_imm (imm, size) ->
    if size <= 0 then failwith "size of operand invalid";
    E_literal (Bitvec.of_int (size*8) imm)
  | O_offset ofs -> E_literal (Bitvec.of_int 32 (pc' + ofs))
  | _ -> failwith "invalid operand type"

let elaborate_writeback env o_dst e_data =
  match o_dst with
  | O_reg r ->
    begin match elaborate_reg r with
      | E_var regname ->
        append_stmt env (S_set (L_var regname, e_data))
      | E_part (E_var regname, (lo, hi)) ->
        append_stmt env (S_set (L_part (regname, lo, hi), e_data))
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
      let args = operands |> List.map (elaborate_operand pc' env) in
      append_stmt env (S_call (fn inst, args, Some (L_var temp)));
      elaborate_writeback env (List.hd operands) (E_var temp)
    | I_cmp | I_push | I_call | I_ret | I_retn | I_test ->
      let args = operands |> List.map (elaborate_operand pc' env) in
      append_stmt env (S_call (fn inst, args, None))
    | I_pop ->
      let temp = new_temp env (8 lsl lsize) in
      append_stmt env (S_call (fn inst, [], Some (L_var temp)));
      elaborate_writeback env (List.hd operands) (E_var temp)
    | I_mov ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      elaborate_writeback env dst (elaborate_operand pc' env src)
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
      append_stmt env (S_jump_var (elaborate_operand pc' inst (List.hd operands)))
    | I_cjmp ->
      let cond = cond_expr (inst.variant lsr 2) in
      append_stmt env (S_br_var (cond, elaborate_operand pc' inst (List.hd operands)))
    | I_movzx | I_movsx ->
      let dst, src =
        match operands with
        | [d; s] -> d, s
        | _ -> assert false
      in
      (*let lsize_src = inst.variant lsr 2 in*)
      let dst_size = 8 lsl lsize in
      (*let src_size = 8 lsl lsize_src in*)
      let src' = elaborate_operand pc' env src in
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
      let dst' = elaborate_operand pc' inst dst in
      let src' = elaborate_operand pc' inst src in
      elaborate_writeback env dst src';
      elaborate_writeback env src dst'
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
