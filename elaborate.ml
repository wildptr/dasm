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

let to_label addr = sprintf "L%x" addr

let cond_expr1 = function
  | 0x0 -> E_global Flag_O
  | 0x1 -> E_global Flag_C
  | 0x2 -> E_global Flag_Z
  | 0x3 -> E_prim (P_or [E_global Flag_C; E_global Flag_Z]) (* CF|XF *)
  | 0x4 -> E_global Flag_S
  | 0x5 -> E_global Flag_P
  | 0x6 -> E_prim (P_xor [E_global Flag_S; E_global Flag_O]) (* SF^OF *)
  | 0x7 -> E_prim (P_or [E_global Flag_Z; E_prim (P_xor [E_global Flag_S; E_global Flag_O])]) (* ZF|(SF^OF) *)
  | _ -> assert false

let cond_expr code =
  let e = cond_expr1 (code lsr 1) in
  if (code land 1) = 0 then e else E_prim (P_not e)

let elaborate_inst env inst pc =
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
  let do_unary f size st ld =
    let src = ld size in
    let dst_temp = new_temp env (size*8) in
    f size (src, dst_temp);
    st size (E_local dst_temp)
  in
  let do_mov size st ld =
    st size (ld size)
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
  let f_inc size (src, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "inc%d" (size*8)),
        [src],
        Some dst_temp
      end
    end
  in
  let f_dec size (src, dst_temp) =
    append_stmt env begin
      S_call begin
        predef (sprintf "dec%d" (size*8)),
        [src],
        Some dst_temp
      end
    end
  in
  let do_push size ld =
    let data = ld size in
    append_stmt env (S_call (predef (sprintf "push%d" (size*8)), [data], None))
  in
  let do_pop size r =
    let w = size*8 in
    let temp = new_temp env w in
    append_stmt env (S_call (predef (sprintf "pop%d" w), [], Some temp));
    match r with
    | E_global reg ->
        append_stmt env (S_setglobal (reg, E_local temp))
    | E_part (E_global reg, range) ->
        append_stmt env (S_setglobal_part (reg, range, E_local temp))
    | _ -> assert false
  in
  let do_push_segr segr =
    append_stmt env (S_call (predef "push32_segr", [E_global segr], None))
  in
  let do_pop_segr segr =
    let temp = new_temp env 32 in
    append_stmt env (S_call (predef "pop32", [], Some temp));
    append_stmt env (S_setglobal (segr, E_part (E_local temp, (0, 16))))
  in
  let not_impl s = failwithf "not implemented: %2x %s" opcode s () in
  let f_add_group = [|f_add;f_or;f_adc;f_sbb;f_and;f_sub;f_xor;f_sub|] in
  let do_xchg size st1 st2 ld1 ld2 =
    let src1 = ld1 size in
    let src2 = ld2 size in
    let temp = new_temp env (size*8) in
    append_stmt env (S_setlocal (temp, src1));
    st1 size src2;
    st2 size (E_local temp)
  in
  let ld_abs size =
    match operand with
    | Op_I i ->
        let w = size*8 in
        let temp = new_temp env w in
        append_stmt env (S_load (size, E_literal (Bitvec.of_int w i), temp));
        E_local temp
    | _ -> assert false
  in
  let st_abs size data =
    match operand with
    | Op_I i ->
        let w = size*8 in
        append_stmt env (S_store (size, E_literal (Bitvec.of_int w i), data))
    | _ -> assert false
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
        do_push_segr R_ES
    | 0x07 -> (* pop es *)
        do_pop_segr R_ES
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
    | 0x0e -> (* push cs *)
        do_push_segr R_CS
    | 0x0f ->
        assert false
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
    | 0x16 ->
        do_push_segr R_SS
    | 0x17 ->
        do_pop_segr R_SS
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
    | 0x1e -> (* push ds *)
        do_push_segr R_DS
    | 0x1f -> (* pop ds *)
        do_pop_segr R_DS
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
    | 0x26 -> (* prefix *)
        assert false
    | 0x27 -> (* daa *)
        do_pop_segr R_FS
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
    | 0x2e -> (* prefix *)
        assert false
    | 0x2f -> (* das *)
        not_impl "das"
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
    | 0x36 -> (* prefix *)
        assert false
    | 0x37 -> (* aaa *)
        not_impl "aaa"
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
    | 0x3e -> (* prefix *)
        assert false
    | 0x3f -> (* aas *)
        not_impl "aas"
    | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 | 0x47 -> (* inc qw *)
        let q = opcode land 7 in
        do_unary f_inc word_size (st_r q) (ld_r q)
    | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f -> (* dec qw *)
        let q = opcode land 7 in
        do_unary f_dec word_size (st_r q) (ld_r q)
    | 0x50 | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57 -> (* push qw *)
        let q = opcode land 7 in
        do_push word_size (ld_r q)
    | 0x58 | 0x59 | 0x5a | 0x5b | 0x5c | 0x5d | 0x5e | 0x5f -> (* pop qw *)
        let q = opcode land 7 in
        do_pop word_size (ld_r q word_size)
    | 0x60 ->
        not_impl "pusha/pushad"
    | 0x61 ->
        not_impl "popa/popad"
    | 0x62 ->
        not_impl "bound"
    | 0x63 ->
        not_impl "arpl"
    | 0x64 | 0x65 | 0x66 | 0x67 ->
        assert false
    | 0x68 -> (* push i *)
        do_push word_size ld_i
    | 0x69 -> (* imul rw,gw,i *)
        not_impl "imul"
    | 0x6a -> (* push i *)
        do_push word_size ld_i
    | 0x6b -> (* imul rw,gw,i *)
        not_impl "imul"
    | 0x6c ->
        not_impl "insb"
    | 0x6d ->
        not_impl "insw/insd"
    | 0x6e ->
        not_impl "outsb"
    | 0x6f ->
        not_impl "outsw/outsd"
    | 0x70 | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 | 0x77
    | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f ->
        let offset =
          match operand with
          | Op_I i -> i
          | _ -> assert false
        in
        let s = S_br (cond_expr (opcode-0x70), to_label (pc+offset)) in
        append_stmt env s
    | 0x80 | 0x81 | 0x82 | 0x83 ->
        let st = if r = 7 then st_nop else st_g in
        let size = if opcode land 1 = 0 then 1 else word_size in
        do_binary f_add_group.(r) size st ld_g ld_i
    | 0x84 | 0x85 -> (* test g?,r? *)
        let size = if opcode land 1 = 0 then 1 else word_size in
        do_binary f_and size st_nop ld_g (ld_r r)
    | 0x86 | 0x87 -> (* xchg g?,r? *)
        let size = if opcode land 1 = 0 then 1 else word_size in
        do_xchg size st_g (st_r r) ld_g (ld_r r)
    | 0x88 | 0x89 -> (* mov g?,r? *)
        let size = if opcode land 1 = 0 then 1 else word_size in
        do_mov size st_g (ld_r r)
    | 0x8a | 0x8b -> (* mov r?,g? *)
        let size = if opcode land 1 = 0 then 1 else word_size in
        do_mov size (st_r r) ld_g
    | 0x8c ->
        not_impl "mov"
    | 0x8d -> (* lea *)
        let m =
          match operand with
          | Op_M (G_mem m) -> m
          | Op_M _ -> failwith "invalid instruction"
          | _ -> assert false
        in
        (* FIXME: size *)
        st_r r 4 (elaborate_mem_addr m)
    | 0x8e ->
        not_impl "mov"
    | 0x8f ->
        not_impl "pop"
    | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 ->
        let q = opcode land 7 in
        do_xchg word_size (st_r 0) (st_r q) (ld_r 0) (ld_r q)
    | 0x98 ->
        not_impl "cbw"
    | 0x99 ->
        not_impl "cwd/cdq"
    | 0x9a ->
        not_impl "call far"
    | 0x9b ->
        not_impl "wait"
    | 0x9c ->
        not_impl "pushf"
    | 0x9d ->
        not_impl "popf"
    | 0x9e ->
        not_impl "sahf"
    | 0x9f ->
        not_impl "lahf"
    | 0xa0 ->
        do_mov 1 (st_r 0) ld_abs
    | 0xa1 ->
        do_mov word_size (st_r 0) ld_abs
    | 0xa2 ->
        do_mov 1 st_abs (ld_r 0)
    | 0xa3 ->
        do_mov word_size st_abs (ld_r 0)
    | 0xa4 ->
        not_impl "movsb"
    | 0xa5 ->
        not_impl "movsw/movsd"
    | 0xa6 ->
        not_impl "cmpsb"
    | 0xa7 ->
        not_impl "cmpsw/cmpsd"
    | 0xa8 -> (* test a1,i *)
        do_binary f_and 1 st_nop (ld_r 0) ld_i
    | 0xa9 -> (* test aw,i *)
        do_binary f_and word_size st_nop (ld_r 0) ld_i
    | 0xaa ->
        not_impl "stosb"
    | 0xab ->
        not_impl "stosw/stosd"
    | 0xac ->
        not_impl "lodsb"
    | 0xad ->
        not_impl "lodsw/lodsd"
    | 0xae ->
        not_impl "scasb"
    | 0xaf ->
        not_impl "scasw/scasd"
    | 0xb0 | 0xb1 | 0xb2 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7
    | 0xb8 | 0xb9 | 0xba | 0xbb | 0xbc | 0xbd | 0xbe | 0xbf ->
        let size = if opcode land 8 = 0 then 1 else word_size in
        let q = opcode land 7 in
        do_mov size (st_r q) ld_i
    | 0xc0 ->
        not_impl "[rol]"
    | 0xc1 ->
        not_impl "[rol]"
    | 0xc2 ->
        not_impl "ret"
    | 0xc3 ->
        append_stmt env (S_call (predef "ret32", [], None))
    | 0xc4 ->
        not_impl "les"
    | 0xc5 ->
        not_impl "lds"
    | 0xc6 | 0xc7 ->
        let size = if opcode land 1 = 0 then 1 else word_size in
        if r = 0
        then do_mov size st_g ld_i
        else failwith "invalid instruction"
    | 0xc8 ->
        not_impl "enter"
    | 0xc9 ->
        not_impl "leave"
    | 0xca ->
        not_impl "ret far"
    | 0xcb ->
        not_impl "ret far"
    | 0xcc ->
        not_impl "int3"
    | 0xcd ->
        not_impl "int"
    | 0xce ->
        not_impl "into"
    | 0xcf ->
        not_impl "iret"
    | 0xd0 | 0xd1 | 0xd2 | 0xd3 ->
        not_impl "[rol]"
    | 0xd4 ->
        not_impl "aam"
    | 0xd5 ->
        not_impl "aad"
    | 0xd6 ->
        not_impl "<unknown instruction>"
    | 0xd7 ->
        not_impl "xlat"
    | 0xd8 | 0xd9 | 0xda | 0xdb | 0xdc | 0xdd | 0xde | 0xdf ->
        not_impl "<FPU instruction>"
    | 0xe0 ->
        not_impl "loopnz"
    | 0xe1 ->
        not_impl "loopz"
    | 0xe2 ->
        not_impl "loop"
    | 0xe3 ->
        not_impl "jcxz"
    | 0xe4 | 0xe5 ->
        not_impl "in"
    | 0xe6 | 0xe7 ->
        not_impl "out"
    | 0xe8 -> (* call o *)
        let offset =
          match operand with
          | Op_I i -> i
          | _ -> assert false
        in
        let args = [
          E_literal (Bitvec.of_int 32 pc);
          E_literal (Bitvec.of_int 32 offset);
        ] in
        append_stmt env (S_call (predef "call32", args, None))
    | 0xe9 | 0xeb -> (* jmp o *)
        let offset =
          match operand with
          | Op_I i -> i
          | _ -> assert false
        in
        let s = S_jump (to_label (pc+offset)) in
        append_stmt env s
    | 0xea ->
        not_impl "jmp far"
    | 0xec | 0xed ->
        not_impl "in"
    | 0xee | 0xef ->
        not_impl "out"
    | 0xf0 ->
        assert false
    | 0xf1 ->
        not_impl "int1"
    | 0xf2 | 0xf3 ->
        assert false
    | 0xf4 ->
        not_impl "hlt"
    | 0xf5 ->
        not_impl "cmc"
    | 0xf6 | 0xf7 ->
        not_impl "[test]"
    | 0xf8 ->
        not_impl "clc"
    | 0xf9 ->
        not_impl "stc"
    | 0xfa ->
        not_impl "cli"
    | 0xfb ->
        not_impl "sti"
    | 0xfc ->
        not_impl "cld"
    | 0xfd ->
        not_impl "std"
    | 0xfe | 0xff ->
        not_impl "[inc]"
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
  String.Map.iteri symtab ~f:begin fun ~key ~data ->
    match data with
    | Translate.Proc proc -> Hashtbl.set predef_table ~key ~data:proc
    | _ -> ()
  end
