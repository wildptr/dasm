open Batteries
open Elab_env
open Inst
open Semant
open Normal

let mk_global g = E_var (Global g)
let memory = mk_global Memory

let elaborate_reg r =
  let rid = Inst.int_of_reg r in
  if rid < 16 then
    let a, g = alias_table.(rid) in
    E_prim1 (P1_part a, mk_global g)
  else
    E_var (Global (global_of_reg r))

let eCF = mk_global CF
let ePF = mk_global PF
let eZF = mk_global ZF
let eSF = mk_global SF
let eOF = mk_global OF

let proc_table : (string, proc) Hashtbl.t = Hashtbl.create 0

let lookup_proc name =
  try Hashtbl.find proc_table name
  with Not_found ->
    failwith ("predefined semantic procedure not found: " ^ name)

let cond_expr1 = function
  | 0 -> eOF
  | 1 -> eCF
  | 2 -> eZF
  | 3 -> E_prim2 (P2_or, eCF, eZF) (* CF|ZF *)
  | 4 -> eSF
  | 5 -> ePF
  | 6 -> E_prim2 (P2_xor, eSF, eOF) (* SF^OF *)
  | 7 -> E_prim2 (P2_or, eZF, (E_prim2 (P2_xor, eSF, eOF))) (* ZF|(SF^OF) *)
  | _ -> assert false

let cond_expr code =
  let e = cond_expr1 (code lsr 1) in
  if (code land 1) = 0 then e else not_expr e

(* TODO: don't hard code address size *)

let elaborate_mem_index (reg, scale) =
  let g = global_of_reg reg in
  let e_reg = mk_global g in
  if scale = 0 then e_reg
  else
    let e_scale = make_lit (size_of_global g) (Nativeint.of_int scale) in
    E_prim2 (P2_shl, e_reg, e_scale)

let make_address addr = make_lit 32 addr

let elaborate_mem_addr m =
  let addr =
    match m.base, m.index with
    | Some base, Some index ->
      let e_base = elaborate_reg base in
      let e_index = elaborate_mem_index index in
      if m.disp = 0n then
        make_prim2 P2_add e_base e_index
      else
        let e_disp = make_address m.disp in
        make_prim2 P2_add (make_prim2 P2_add e_base e_index) e_disp
    | Some base, None ->
      let e_base = elaborate_reg base in
      if m.disp = 0n then e_base
      else
        let e_disp = make_address m.disp in
        E_prim2 (P2_add, e_base, e_disp)
    | None, Some index ->
      let e_index = elaborate_mem_index index in
      if m.disp = 0n then e_index
      else
        let e_disp = make_address m.disp in
        E_prim2 (P2_add, e_index, e_disp)
    | None, None ->
      make_address m.disp
  in
  match m.seg with
  | R_ES | R_CS | R_SS | R_DS -> addr
  | R_FS -> E_prim2 (P2_add, E_const ("FS_BASE", T_bitvec 32), addr)
  | R_GS -> E_prim2 (P2_add, E_const ("GS_BASE", T_bitvec 32), addr)
  | _ -> failwith "elaborate_mem_addr: invalid segment register"

let elaborate_operand pc' = function
  | O_reg reg -> elaborate_reg reg
  | O_mem (mem, nbyte) ->
    if nbyte <= 0 then failwith "size of operand invalid";
    let off = elaborate_mem_addr mem in
    E_prim2 (P2_load nbyte, memory, off)
  | O_imm (imm, size) ->
    if size <= 0 then failwith "size of operand invalid";
    make_lit (size*8) imm
  | O_offset ofs -> make_address (Nativeint.(pc' + ofs))
  | _ -> failwith "invalid operand type"

let elaborate_writeback emit o_dst e_data =
  match o_dst with
  | O_reg r ->
    let rid = Inst.int_of_reg r in
    if rid < 16 then
      let a, fullreg = alias_table.(rid) in
      emit (S_set (Global fullreg,
                   make_prim2 (P2_updatepart a) (mk_global fullreg) e_data))
    else
      emit (S_set (Global (global_of_reg r), e_data))
  | O_mem (m, nbyte) ->
    assert (nbyte > 0);
    let off = elaborate_mem_addr m in
    emit (S_set (Global Memory, E_prim3 (P3_store nbyte, memory, off, e_data)))
  | _ -> failwith "elaborate_writeback: invalid operand type"

let proc_name_of_op = function
  | I_ADC -> "adc"
  | I_ADD -> "add"
  | I_AND -> "and"
  | I_CALL -> "call"
  | I_CMP -> "sub"
  | I_DEC -> "dec"
  | I_IMUL -> "imul_"
  | I_IMUL2 | I_IMUL3 -> "imul2_"
  | I_INC -> "inc"
  | I_LEAVE -> "leave"
  | I_MUL -> "mul_"
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
  | _ -> failwith "proc_name_of_op: not implemented"

(*
let default_arglist = all_globals |> List.map (fun g -> g, mk_global g)
let default_retlist = all_globals |> List.map (fun g -> g, Global g)
*)

let emit_proc env pc proc args rets =
  let module T = Transform(TemplVar)(Var) in
  let arg_tab = Array.of_list args in
  let ret_tab = Array.of_list rets in
  let local_tab =
    proc.local_types |> List.map (acquire_temp env) |> Array.of_list
  in
  assert (Array.length arg_tab = List.length proc.arg_types);
  assert (Array.length ret_tab = List.length proc.ret_types);
  assert (Array.length local_tab = List.length proc.local_types);
  let map_lvar = function
    | TV_Global g -> Global g
    | TV_Local i -> local_tab.(i)
    | TV_Output i -> ret_tab.(i)
    | _ -> failwith "invalid assignment"
  in
  let map_rvar = function
    | TV_Global g -> mk_global g
    | TV_Local i -> E_var local_tab.(i)
    | TV_Input i -> arg_tab.(i)
    | TV_Output i -> E_var ret_tab.(i)
    | TV_PC -> E_lit (BitvecLit, Bitvec.of_nativeint 32 pc)
    | TV_Nondet t -> fresh_nondet t env
  in
  begin
    try
      proc.body |> List.iter begin fun s ->
        s |> T.map_stmt map_lvar (T.subst map_rvar) |> emit env
      end;
    with e ->
      let open Format in
      printf "local_tab:\n";
      local_tab |> Array.iteri begin fun i v ->
        printf "[%d]=%a\n" i pp_var v
      end;
      proc.body |> List.iter (printf "%a@." Template.pp_stmt);
      raise e
  end;
  local_tab |> Array.iter (release_temp env)

let zero8 = E_lit (BitvecLit, Bitvec.of_nativeint 8 0n)
and one8  = E_lit (BitvecLit, Bitvec.of_nativeint 8 1n)

let elaborate_inst env inst =
  let op = inst.operation in
  let lsize = inst.variant land 15 in (* log size in bytes *)
  let size = 8 lsl lsize in
  let size_typ = T_bitvec size in
  let operands = inst.operands in
  let get_proc inst =
    let proc_name_base = proc_name_of_op op in
    let proc_name = Printf.sprintf "%s%d" proc_name_base size in
    lookup_proc proc_name
  in
  let pc = env.pc in
  let pc' = Nativeint.(pc + of_int (inst_length inst)) in
  match op with
  | I_ADD | I_OR | I_ADC | I_SBB | I_AND | I_SUB | I_XOR
  | I_SHL | I_SHR | I_SAR | I_INC | I_DEC | I_NEG | I_NOT
  | I_IMUL2 ->
    let temp = acquire_temp env size_typ in
    let args = operands |> List.map (elaborate_operand pc') in
    emit_proc env pc' (get_proc inst) args [temp];
    elaborate_writeback (emit env) (List.hd operands) (E_var temp);
    release_temp env temp
  | I_CMP | I_PUSH | I_TEST | I_CALL | I_RET | I_RETN | I_LEAVE
  | I_MUL | I_IMUL ->
    let proc = get_proc inst in
    let temps =
      proc.ret_types |> List.map (acquire_temp env)
    in
    let args = operands |> List.map (elaborate_operand pc') in
    emit_proc env pc' proc args temps;
    (* no writeback *)
    temps |> List.iter (release_temp env)
  | I_IMUL3 ->
    let temp = acquire_temp env size_typ in
    let args = List.tl operands |> List.map (elaborate_operand pc') in
    emit_proc env pc' (get_proc inst) args [temp];
    elaborate_writeback (emit env) (List.hd operands) (E_var temp);
    release_temp env temp
  | I_POP ->
    let temp = acquire_temp env size_typ in
    emit_proc env pc' (get_proc inst) [] [temp];
    elaborate_writeback (emit env) (List.hd operands) (E_var temp);
    release_temp env temp
  | I_MOV ->
    let dst, src =
      match operands with
      | [d; s] -> d, s
      | _ -> assert false
    in
    elaborate_writeback (emit env) dst (elaborate_operand pc' src)
  | I_MOVZX | I_MOVSX ->
    let dst, src =
      match operands with
      | [d; s] -> d, s
      | _ -> assert false
    in
    (*let lsize_src = inst.variant lsr 4 in*)
    (*let src_size = 8 lsl lsize_src in*)
    let src' = elaborate_operand pc' src in
    elaborate_writeback (emit env) dst
      (E_prim1 (P1_extend (op = I_MOVSX, size), src'))
  | I_LEA ->
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
    elaborate_writeback (emit env) dst addr
  | I_JMP | I_CJMP ->
    let cond_opt =
      if op = I_CJMP then
        Some (cond_expr (inst.variant lsr 4))
      else
        None
    in
    emit env (S_jump (cond_opt, elaborate_operand pc' (List.hd operands)))
  | I_SET ->
    let dst =
      match operands with
      | [dst] -> dst
      | _ -> assert false
    in
    let cond = cond_expr (inst.variant lsr 4) in
    let data = E_prim3 (P3_ite, cond, one8, zero8) in
    elaborate_writeback (emit env) dst data
  | I_XCHG ->
    let dst, src =
      match operands with
      | [d; s] -> d, s
      | _ -> assert false
    in
    let dst' = elaborate_operand pc' dst in
    let src' = elaborate_operand pc' src in
    elaborate_writeback (emit env) dst src';
    elaborate_writeback (emit env) src dst'
  | _ ->
    Format.printf "elaborate_inst: not implemented: %a@." Inst.pp_inst inst

let elaborate_basic_block env bb =
  let open CFG in
  env.pc <- bb.start;
  bb.stmts |> List.iter begin fun inst ->
    elaborate_inst env inst;
    env.pc <- Nativeint.(env.pc + of_int (inst_length inst))
  end;
  let stmts = get_stmts env in
  env.stmts_rev <- [];
  (* no temps should be in use *)
  for i=0 to env.n_temp-1 do
    assert env.temp_avail_tab.(i)
  done;
  { bb with stmts }

let elaborate_cfg db_opt cfg =
  let open CFG in
  let env = Elab_env.create db_opt in
  let node = cfg.node |> Array.map (elaborate_basic_block env) in
  let succ = Array.copy cfg.succ in
  let pred = Array.copy cfg.pred in
  { cfg with node; succ; pred; temp_tab = env.temp_type_tab }

let syntax_error filename lexbuf msg =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.eprintf "%s:%d:%d: %s\n" filename line col msg;
  failwith "invalid spec"

let load_spec filepath =
  let in_chan = open_in filepath in
  let lexbuf = Lexing.from_channel in_chan in
  let spec_ast =
    try
      Spec_parser.top Spec_lexer.read lexbuf
    with
    | Spec_parser.Error ->
      syntax_error filepath lexbuf "syntax error"
    | Spec_lexer.Error msg ->
      syntax_error filepath lexbuf msg
  in
  close_in in_chan;
  let symtab =
    try Translate.translate_ast spec_ast with
    | Translate.Error msg ->
      Printf.eprintf "%s\n" msg;
      failwith "invalid spec"
  in
  symtab |> Map.String.iter begin fun key data ->
    match data with
    | Trans_env.Proc proc -> Hashtbl.add proc_table key proc
    | _ -> ()
  end
