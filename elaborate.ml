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
  | Reg32bit -> 3
  | Reg64bit -> 4

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
        E_prim (P_shiftleft (e_arr.(r), E_literal (Bitvec.of_int 2 scale)))
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

let elaborate_g_operand reg_set = function
  | G_reg r -> elaborate_reg_operand reg_set r
  | G_mem m ->
      let size = gpr_set_size reg_set in
      let e_addr = elaborate_mem_addr m in
      E_prim (P_load (size, e_addr))

let elaborate_writeback reg_set g e =
  match g with
  | G_reg r ->
      begin match elaborate_reg_operand reg_set r with
      | E_global reg -> E_set (reg, e)
      | E_part (E_global reg, range) -> E_setpart (reg, range, e)
      | _ -> assert false
      end
  | G_mem m ->
      let size = gpr_set_size reg_set in
      let e_addr = elaborate_mem_addr m in
      E_prim (P_store (size, e_addr, e))

let elaborate_inst (inst : inst) : expr =
  let extopcode = extopcode_of_inst inst in
  let inst_len = length_of_inst inst in
  let opcode, r, prefix, mode = decode_extopcode extopcode in
  if opcode < 0x100
  then
    match opcode with
    | 0x00 -> (* add g1,r1 *)
        let reg_set = gpr_set_of_reg_operand mode 1 in
        begin match operand_of_inst inst with
        | Op_M g ->
            let e_g = elaborate_g_operand reg_set g in
            let e_r = elaborate_reg_operand reg_set r in
            let e_result = E_let (e_g, E_let (e_r, e_adc8)) in
            elaborate_writeback reg_set g e_result
        | _ -> assert false
        end
    | _ -> assert false
  else
    failwith "not implemented"

let fail_with_parsing_error filename lexbuf msg =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.fprintf stderr "%s:%d:%d: %s\n" filename line col msg;
  failwith "invalid spec"

let load_spec () =
  let spec_path = "spec" in
  let in_chan = In_channel.create spec_path in
  let lexbuf = Lexing.from_channel in_chan in
  let spec_ast =
    try
      Spec_parser.top Spec_lexer.read lexbuf
    with
    | Spec_parser.Error ->
        fail_with_parsing_error spec_path lexbuf "syntax error"
    | Spec_lexer.Error msg ->
        fail_with_parsing_error filepath lexbuf msg
  in
  ()