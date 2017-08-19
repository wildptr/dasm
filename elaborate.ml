open Core
open Inst
open Semant

let eAX = E_global R_AX
let eCX = E_global R_CX
let eDX = E_global R_DX
let eBX = E_global R_BX
let eSP = E_global R_SP
let eBP = E_global R_BP
let eSI = E_global R_SI
let eDI = E_global R_DI

let e8legacy = [|
  E_part (eAX, (0,  8)); (* AL *)
  E_part (eCX, (0,  8)); (* CL *)
  E_part (eDX, (0,  8)); (* DL *)
  E_part (eBX, (0,  8)); (* BL *)
  E_part (eAX, (8, 16)); (* AH *)
  E_part (eCX, (8, 16)); (* CH *)
  E_part (eDX, (8, 16)); (* DH *)
  E_part (eBX, (8, 16)); (* BH *)
|]

let e_arr = [| eAX; eCX; eDX; eBX; eSP; eBP; eSI; eDI |]

(* size in bytes *)
let gpr_set_size = function
  | Reg8bitLegacy | Reg8bitUniform -> 1
  | Reg16bit -> 2
  | Reg32bit -> 4
  | Reg64bit -> 8

let elaborate_mem_addr m =
  let e_base =
    match m.base with
    | None -> E_literal (Bitvec.zero 32)
    | Some r -> e_arr.(r)
  in
  let e_index =
    match m.index with
    | None -> E_literal (Bitvec.zero 32)
    | Some (r, scale) ->
        let log_scale =
          match scale with
          | 1 -> 0
          | 2 -> 1
          | 4 -> 2
          | 8 -> 3
          | _ -> assert false
        in
        E_prim (P_shiftleft (e_arr.(r), E_literal (Bitvec.of_int 2 log_scale)))
  in
  let e_disp = E_literal (Bitvec.of_int 32 m.disp) in
  E_prim (P_add [e_base; e_index; e_disp])

let elaborate_reg_operand reg_set r =
  match reg_set with
  | Reg8bitLegacy -> e8legacy.(r)
  | Reg8bitUniform
  | Reg16bit
  | Reg32bit
  | Reg64bit ->
      let size = 8 * gpr_set_size reg_set in
      E_part (e_arr.(r), (0, size))

let elaborate_g_operand env reg_set = function
  | G_reg r -> elaborate_reg_operand reg_set r
  | G_mem m ->
      let size = gpr_set_size reg_set in
      let e_addr = elaborate_mem_addr m in
      let temp = new_temp env (size*8) in
      append_stmt env (S_load (size, e_addr, temp));
      E_local temp

let elaborate_writeback env reg_set g e_data =
  match g with
  | G_reg r ->
      begin match elaborate_reg_operand reg_set r with
      | E_global reg ->
          append_stmt env (S_setglobal (reg, e_data))
      | E_part (E_global reg, range) ->
          append_stmt env (S_setglobal_part (reg, range, e_data))
      | _ -> assert false
      end
  | G_mem m ->
      let size = gpr_set_size reg_set in
      let e_addr = elaborate_mem_addr m in
      append_stmt env (S_store (size, e_addr, e_data))

let predef_table = String.Table.create ()

let predef = String.Table.find_exn predef_table

let elaborate_inst env (inst : inst) : unit =
  let extopcode = extopcode_of_inst inst in
  let opcode, r, prefix, mode = decode_extopcode extopcode in
  let alt_data = prefix land (prefix_mask Prefix_66) <> 0 in
  let word_size =
    match mode with
    | Mode16bit -> if alt_data then 4 else 2
    | _ -> if alt_data then 2 else 4
  in
  let operand = operand_of_inst inst in
  let do_binary f size st ld1 ld2 =
    let src1 = ld1 size in
    let src2 = ld2 size in
    let dst_temp = new_temp env (size*8) in
    f size (src1, src2, dst_temp);
    st size (E_local dst_temp)
  in
  let ld_g size =
    let reg_set = gpr_set_of_reg_operand mode size in
    match operand with
    | Op_M g -> elaborate_g_operand env reg_set g
    | _ -> assert false
  in
  let ld_r r size =
    let reg_set = gpr_set_of_reg_operand mode size in
    elaborate_reg_operand reg_set r
  in
  let ld_i size =
    match operand with
    | Op_I imm -> E_literal (Bitvec.of_int (size*8) imm)
    | _ -> assert false
  in
  let st_g size data =
    let reg_set = gpr_set_of_reg_operand mode size in
    match operand with
    | Op_M g -> elaborate_writeback env reg_set g data
    | _ -> assert false
  in
  let st_r r size data =
    let reg_set = gpr_set_of_reg_operand mode size in
    elaborate_writeback env reg_set (G_reg r) data
  in
  let st_nop _ _ = () in
  let f_add size (src1, src2, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "adc%d" (size*8)),
        [src1; src2; E_literal (Bitvec.zero 1)],
        Some dst_temp
      end
    end
  in
  let f_or size (src1, src2, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "or%d" (size*8)),
        [src1; src2],
        Some dst_temp
      end
    end
  in
  let f_and size (src1, src2, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "and%d" (size*8)),
        [src1; src2],
        Some dst_temp
      end
    end
  in
  let f_xor size (src1, src2, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "xor%d" (size*8)),
        [src1; src2],
        Some dst_temp
      end
    end
  in
  let f_adc size (src1, src2, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "adc%d" (size*8)),
        [src1; src2; E_global Flag_C],
        Some dst_temp
      end
    end
  in
  let f_sbb size (src1, src2, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "sbb%d" (size*8)),
        [src1; src2; E_global Flag_C],
        Some dst_temp
      end
    end
  in
  let f_sub size (src1, src2, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "sbb%d" (size*8)),
        [src1; src2; E_literal (Bitvec.zero 1)],
        Some dst_temp
      end
    end
  in
  if opcode < 0x100
  then
    match opcode with
    | 0x00 -> (* add g1,r1 *)
        do_binary f_add 1 st_g ld_g (ld_r r)
    | 0x01 -> (* add gw,rw *)
        do_binary f_add word_size st_g ld_g (ld_r r)
    | 0x02 -> (* add r1,g1 *)
        do_binary f_add 1 (st_r r) (ld_r r) ld_g
    | 0x03 -> (* add rw,gw *)
        do_binary f_add word_size (st_r r) (ld_r r) ld_g
    | 0x04 -> (* add a1,i *)
        do_binary f_add 1 (st_r 0) (ld_r 0) ld_i
    | 0x05 -> (* add aw,i *)
        do_binary f_add word_size (st_r 0) (ld_r 0) ld_i
    | 0x06 -> (* push es *)
        append_stmt env (S_call (predef "push32_segr", [E_global R_ES], None))
    | 0x07 -> (* pop es *)
        let temp = new_temp env 32 in
        append_stmt env (S_call (predef "pop32", [], Some temp));
        append_stmt env (S_setglobal (R_ES, E_part (E_local temp, (0, 16))))
    | 0x08 -> (* or g1,r1 *)
        do_binary f_or 1 st_g ld_g (ld_r r)
    | 0x09 -> (* or gw,rw *)
        do_binary f_or word_size st_g ld_g (ld_r r)
    | 0x0a -> (* or r1,g1 *)
        do_binary f_or 1 (st_r r) (ld_r r) ld_g
    | 0x0b -> (* or rw,gw *)
        do_binary f_or word_size (st_r r) (ld_r r) ld_g
    | 0x0c -> (* or a1,i *)
        do_binary f_or 1 (st_r 0) (ld_r 0) ld_i
    | 0x0d -> (* or aw,i *)
        do_binary f_or word_size (st_r 0) (ld_r 0) ld_i

    | 0x10 -> (* adc g1,r1 *)
        do_binary f_adc 1 st_g ld_g (ld_r r)
    | 0x11 -> (* adc gw,rw *)
        do_binary f_adc word_size st_g ld_g (ld_r r)
    | 0x12 -> (* adc r1,g1 *)
        do_binary f_adc 1 (st_r r) (ld_r r) ld_g
    | 0x13 -> (* adc rw,gw *)
        do_binary f_adc word_size (st_r r) (ld_r r) ld_g
    | 0x14 -> (* adc a1,i *)
        do_binary f_adc 1 (st_r 0) (ld_r 0) ld_i
    | 0x15 -> (* adc aw,i *)
        do_binary f_adc word_size (st_r 0) (ld_r 0) ld_i

    | 0x18 -> (* sbb g1,r1 *)
        do_binary f_sbb 1 st_g ld_g (ld_r r)
    | 0x19 -> (* sbb gw,rw *)
        do_binary f_sbb word_size st_g ld_g (ld_r r)
    | 0x1a -> (* sbb r1,g1 *)
        do_binary f_sbb 1 (st_r r) (ld_r r) ld_g
    | 0x1b -> (* sbb rw,gw *)
        do_binary f_sbb word_size (st_r r) (ld_r r) ld_g
    | 0x1c -> (* sbb a1,i *)
        do_binary f_sbb 1 (st_r 0) (ld_r 0) ld_i
    | 0x1d -> (* sbb aw,i *)
        do_binary f_sbb word_size (st_r 0) (ld_r 0) ld_i

    | 0x20 -> (* and g1,r1 *)
        do_binary f_and 1 st_g ld_g (ld_r r)
    | 0x21 -> (* and gw,rw *)
        do_binary f_and word_size st_g ld_g (ld_r r)
    | 0x22 -> (* and r1,g1 *)
        do_binary f_and 1 (st_r r) (ld_r r) ld_g
    | 0x23 -> (* and rw,gw *)
        do_binary f_and word_size (st_r r) (ld_r r) ld_g
    | 0x24 -> (* and a1,i *)
        do_binary f_and 1 (st_r 0) (ld_r 0) ld_i
    | 0x25 -> (* and aw,i *)
        do_binary f_and word_size (st_r 0) (ld_r 0) ld_i

    | 0x28 -> (* sub g1,r1 *)
        do_binary f_sub 1 st_g ld_g (ld_r r)
    | 0x29 -> (* sub gw,rw *)
        do_binary f_sub word_size st_g ld_g (ld_r r)
    | 0x2a -> (* sub r1,g1 *)
        do_binary f_sub 1 (st_r r) (ld_r r) ld_g
    | 0x2b -> (* sub rw,gw *)
        do_binary f_sub word_size (st_r r) (ld_r r) ld_g
    | 0x2c -> (* sub a1,i *)
        do_binary f_sub 1 (st_r 0) (ld_r 0) ld_i
    | 0x2d -> (* sub aw,i *)
        do_binary f_sub word_size (st_r 0) (ld_r 0) ld_i

    | 0x30 -> (* xor g1,r1 *)
        do_binary f_xor 1 st_g ld_g (ld_r r)
    | 0x31 -> (* xor gw,rw *)
        do_binary f_xor word_size st_g ld_g (ld_r r)
    | 0x32 -> (* xor r1,g1 *)
        do_binary f_xor 1 (st_r r) (ld_r r) ld_g
    | 0x33 -> (* xor rw,gw *)
        do_binary f_xor word_size (st_r r) (ld_r r) ld_g
    | 0x34 -> (* xor a1,i *)
        do_binary f_xor 1 (st_r 0) (ld_r 0) ld_i
    | 0x35 -> (* xor aw,i *)
        do_binary f_xor word_size (st_r 0) (ld_r 0) ld_i

    | 0x38 -> (* cmp g1,r1 *)
        do_binary f_sub 1 st_nop ld_g (ld_r r)
    | 0x39 -> (* cmp gw,rw *)
        do_binary f_sub word_size st_nop ld_g (ld_r r)
    | 0x3a -> (* cmp r1,g1 *)
        do_binary f_sub 1 st_nop (ld_r r) ld_g
    | 0x3b -> (* cmp rw,gw *)
        do_binary f_sub word_size st_nop (ld_r r) ld_g
    | 0x3c -> (* cmp a1,i *)
        do_binary f_sub 1 st_nop (ld_r 0) ld_i
    | 0x3d -> (* cmp aw,i *)
        do_binary f_sub word_size st_nop (ld_r 0) ld_i

    | _ ->
        failwithf "not implemented: opcode=%x" opcode ()
  else
    failwithf "not implemented: opcode=%x" opcode ()

let fail_with_parsing_error filename lexbuf msg =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.fprintf stderr "%s:%d:%d: %s\n" filename line col msg;
  failwith "invalid spec"

let load_spec filepath =
  let in_chan = In_channel.create filepath in
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
  In_channel.close in_chan;
  let symtab =
    try Translate.translate_ast spec_ast with
    | Translate.Index_out_of_bounds ((e,w),b) ->
        fprintf stderr "width of expression %s is %d, %d is out of bounds\n"
          (Spec_ast.string_of_astexpr e) w b;
        exit 1
  in
  String.Map.iteri symtab ~f:(fun ~key ~data ->
    match data with
    | Proc proc -> Hashtbl.set predef_table ~key ~data:proc
    | _ -> ())
