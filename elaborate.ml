open Core
open Inst
open Semant

type elab_env = {
  local_tab : int Int.Table.t;
  mutable stmts_rev : stmt list;
}

let new_env () =
  { local_tab = Int.Table.create ();
    stmts_rev = [] }

let new_temp env width =
  let id = Int.Table.length env.local_tab in
  Int.Table.add_exn env.local_tab ~key:id ~data:width;
  id

let append_stmt env stmt =
  env.stmts_rev <- stmt :: env.stmts_rev

let get_stmt_list env =
  List.rev env.stmts_rev

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
      append_stmt env (S_load (e_addr, size, temp));
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
      append_stmt env (S_store (e_addr, size, e_data))

let predef_table = String.Table.create ()

let elaborate_inst env (inst : inst) : unit =
  let extopcode = extopcode_of_inst inst in
  let opcode, r, prefix, mode = decode_extopcode extopcode in
  if opcode < 0x100
  then
    match opcode with
    | 0x00 -> (* add g1,r1 *)
        let reg_set = gpr_set_of_reg_operand mode 1 in
        begin match operand_of_inst inst with
        | Op_M g ->
            let e_g = elaborate_g_operand env reg_set g in
            let e_r = elaborate_reg_operand reg_set r in
            let result_temp = new_temp env 8 in
            let e_result = E_local result_temp in
            append_stmt env (S_call ("adc8", [e_g; e_r; E_literal (Bitvec.zero 1)], Some result_temp));
            elaborate_writeback env reg_set g e_result
        | _ ->
            failwith "not implemented"
        end
    | _ ->
        failwith "not implemented"
  else
    failwith "not implemented"

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
  let static_env =
    try Translate.translate_ast spec_ast with
    | Translate.Index_out_of_bounds ((e,w),b) ->
        fprintf stderr "width of expression %s is %d, %d is out of bounds\n"
          (Spec_ast.string_of_astexpr e) w b;
        exit 1
  in
  String.Map.iteri (Translate.env_proc_map static_env) ~f:(fun ~key ~data ->
    Hashtbl.set predef_table ~key ~data)
