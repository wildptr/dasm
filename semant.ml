open Core_kernel.Std
open Format

type reg =
  | R_AX
  | R_CX
  | R_DX
  | R_BX
  | R_SP
  | R_BP
  | R_SI
  | R_DI
  | Flag_C (*  0 *)
  | Flag_P (*  2 *)
  | Flag_A (*  4 *)
  | Flag_Z (*  6 *)
  | Flag_S (*  7 *)
  | Flag_D (* 10 *)
  | Flag_O (* 11 *)
  | Flag_0f
  | R_ES
  | R_CS
  | R_SS
  | R_DS
  | R_FS
  | R_GS

let string_of_reg = function
  | R_AX -> "AX"
  | R_CX -> "CX"
  | R_DX -> "DX"
  | R_BX -> "BX"
  | R_SP -> "SP"
  | R_BP -> "BP"
  | R_SI -> "SI"
  | R_DI -> "DI"
  | Flag_C -> "CF"
  | Flag_P -> "PF"
  | Flag_A -> "AF"
  | Flag_Z -> "ZF"
  | Flag_S -> "SF"
  | Flag_D -> "DF"
  | Flag_O -> "OF"
  | R_ES -> "ES"
  | R_CS -> "CS"
  | R_SS -> "SS"
  | R_DS -> "DS"
  | R_FS -> "FS"
  | R_GS -> "GS"
  | _ -> "??"

exception Unindexed_register of reg

let index_of_reg = function
  | R_AX -> 0
  | R_CX -> 1
  | R_DX -> 2
  | R_BX -> 3
  | R_SP -> 4
  | R_BP -> 5
  | R_SI -> 6
  | R_DI -> 7
  | R_ES -> 0
  | R_CS -> 1
  | R_SS -> 2
  | R_DS -> 3
  | R_FS -> 4
  | R_GS -> 5
  | _ as r -> raise (Unindexed_register r)

type prim =
  | P_not of expr
  | P_concat of expr list
  | P_add of expr list
  | P_sub of expr * expr
  | P_eq of expr * expr
  | P_and of expr list
  | P_xor of expr list
  | P_or of expr list
  | P_shiftleft of expr * expr
  | P_undef of int
  | P_repeat of expr * int
  | P_add_ex of expr * expr * expr (* add with carry *)

and expr =
  | E_literal of Bitvec.t
  | E_var of string
  | E_part of expr * (int * int)
  | E_prim of prim

(* elaborated form of instructions *)
type stmt =
  | S_set of string * expr
  | S_set_part of string * (int * int) * expr
  | S_load of int * expr * string
  | S_store of int * expr * expr
  | S_label of string
  | S_jump of string
  | S_jump_var of expr
  | S_br of expr * string
  | S_br_var of expr * expr
  (* the following do not occur after elaboration *)
  | S_call of proc * expr list * string option
  | S_return of expr

and proc = {
  (* for pretty printing *)
  p_name : string;
  p_body : stmt list;
  p_param_names : string list;
  p_result_width : int;
  p_var_tab : int String.Table.t;
}

let rec pp_prim f p =
  let pp_prim_es f op_char es =
    fprintf f "@[(";
    let n = List.length es in
    List.iteri es ~f:(fun i e ->
      pp_expr f e;
      if i < n-1 then fprintf f " %c@ " op_char);
    fprintf f ")@]"
  in
  match p with
  | P_not e -> pp_expr f e
  | P_concat es -> pp_prim_es f '.' es
  | P_add es -> pp_prim_es f '+' es
  | P_sub (e1, e2) ->
      fprintf f "@[(%a -@ %a)@]" pp_expr e1 pp_expr e2
  | P_eq (e1, e2) ->
      fprintf f "@[(%a ==@ %a)@]" pp_expr e1 pp_expr e2
  | P_and es -> pp_prim_es f '&' es
  | P_xor es -> pp_prim_es f '^' es
  | P_or es -> pp_prim_es f '|' es
  | P_shiftleft (e1, e2) ->
      fprintf f "@[(%a <<@ %a)@]" pp_expr e1 pp_expr e2
  | P_undef width ->
      fprintf f "undefined(%d)" width
  | P_repeat (data, n) ->
      fprintf f "repeat(@[%a,@ %d@])" pp_expr data n
  | P_add_ex (e_a, e_b, e_c) ->
      fprintf f "add_ex(@[%a,@ %a,@ %a@])" pp_expr e_a pp_expr e_b pp_expr e_c

and pp_expr f = function
  | E_literal bv -> (*fprintf f "'%a'" Bitvec.pp bv*)
      fprintf f "%d:%d" (Bitvec.to_int bv) (Bitvec.length bv)
  | E_var s -> fprintf f "%s" s
  | E_part (e, (lo, hi)) -> fprintf f "@[%a[%d:%d]@]" pp_expr e lo hi
  | E_prim p -> pp_prim f p
  (*| E_let (e_bind, e_body) ->
      fprintf f "@[let %a@ in@ %a@]" pp_expr e_bind pp_expr e_body
  | E_set (reg, e_value) ->
      fprintf f "@[%s =@ %a@]" (string_of_reg reg) pp_expr e_value
  | E_seq (e1, e2) ->
      fprintf f "@[<v>%a;@,%a@]" pp_expr e1 pp_expr e2
  | E_setpart (reg, (lo, hi), e_value) ->
      fprintf f "@[%s[%d:%d] =@ %a@]" (string_of_reg reg) lo hi pp_expr e_value*)

let pp_stmt f = function
  | S_set (name, e) ->
      fprintf f "%s @[=@ %a@]" name pp_expr e
  | S_set_part (name, (lo, hi), e) ->
      fprintf f "%s[%d:%d] @[=@ %a@]" name lo hi pp_expr e
  | S_load (size, e_addr, dst) ->
      fprintf f "%s @[=@ load %d,@ %a@]" dst size pp_expr e_addr
  | S_store (size, e_addr, e_data) ->
      fprintf f "store @[%d,@ %a,@ %a@]" size pp_expr e_addr pp_expr e_data
  | S_label l ->
      fprintf f "%s:" l
  | S_jump l ->
      fprintf f "jump %s" l
  | S_jump_var e ->
      fprintf f "jump_var @[%a@]" pp_expr e
  | S_br (e, l) ->
      fprintf f "br @[%a,@ %s@]" pp_expr e l
  | S_br_var (e, e') ->
      fprintf f "br_var @[%a,@ %a@]" pp_expr e pp_expr e'
  | S_call (proc, args, result_opt) ->
      begin match result_opt with
      | None -> ()
      | Some name -> fprintf f "%s @[=@ " name
      end;
      fprintf f "%s(" proc.p_name;
      let n = List.length args in
      List.iteri args ~f:(fun i arg ->
        pp_expr f arg;
        if i < n-1 then fprintf f ",@ ");
      fprintf f ")@]";
  | S_return e ->
      fprintf f "return @[%a@]" pp_expr e

let pp_proc f proc =
  let n_param = List.length proc.p_param_names in
  fprintf f "@[<v>";
  (* print header *)
  fprintf f "@[(";
  List.iteri proc.p_param_names ~f: (fun i name ->
    fprintf f "%s" name;
    if i < n_param-1 then fprintf f ",@ ");
  fprintf f "):%d@]@ " proc.p_result_width;
  (* print env *)
  (*fprintf f "%a@ " pp_env proc.p_env;*)
  (* print body*)
  fprintf f "{@ ";
  fprintf f "  @[<v>";
  let n_stmt = List.length proc.p_body in
  List.iteri proc.p_body ~f:(fun i stmt ->
    fprintf f "%a" pp_stmt stmt;
    if i < n_stmt-1 then fprintf f "@ ");
  fprintf f "@]@ ";
  fprintf f "}@]";

type env = {
  var_tab : int String.Table.t;
  mutable stmts_rev : stmt list;
}

let new_env () =
  { var_tab = String.Table.create ();
    stmts_rev = [] }

let new_temp env width =
  let n = String.Table.length env.var_tab in
  let id = sprintf "$%d" n in
  String.Table.add_exn env.var_tab ~key:id ~data:width;
  id

let append_stmt env stmt =
  env.stmts_rev <- stmt :: env.stmts_rev

let get_stmt_list env =
  List.rev env.stmts_rev
