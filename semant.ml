open Format

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
  | P_logshiftright of expr * expr
  | P_arishiftright of expr * expr
  | P_undef of int
  | P_repeat of expr * int
  | P_addwithcarry of expr * expr * expr
  | P_reduce_and of expr
  | P_reduce_xor of expr
  | P_reduce_or of expr
  | P_signextend of expr * int
  | P_zeroextend of expr * int

and expr =
  | E_literal of Bitvec.t
  | E_var of string
  | E_part of expr * int * int
  | E_prim of prim
  | E_load of int * expr

type loc = string

(* elaborated form of instructions *)
type stmt =
  | S_set of loc * expr
  | S_store of int * expr * expr
  | S_jump of expr
  | S_br of expr * expr
  (* the following do not occur after elaboration *)
  | S_call of proc * expr list * loc option
  | S_output of expr

and proc = {
  (* for pretty printing *)
  p_name : string;
  p_body : stmt list;
  p_param_names : string list;
  p_result_width : int;
  p_var_tab : (string, int) Hashtbl.t;
}

let rec pp_prim f p =
  let pp_prim_es f op_char es =
    fprintf f "(";
    let n = List.length es in
    es |> List.iteri (fun i e ->
        pp_expr f e;
        if i < n-1 then fprintf f " %c " op_char);
    fprintf f ")"
  in
  match p with
  | P_not e -> pp_expr f e
  | P_concat es -> pp_prim_es f '.' es
  | P_add es -> pp_prim_es f '+' es
  | P_sub (e1, e2) ->
    fprintf f "(%a - %a)" pp_expr e1 pp_expr e2
  | P_eq (e1, e2) ->
    fprintf f "(%a == %a)" pp_expr e1 pp_expr e2
  | P_and es -> pp_prim_es f '&' es
  | P_xor es -> pp_prim_es f '^' es
  | P_or es -> pp_prim_es f '|' es
  | P_shiftleft (e1, e2) ->
    fprintf f "shift_left(%a, %a)" pp_expr e1 pp_expr e2
  | P_logshiftright (e1, e2) ->
    fprintf f "log_shift_right(%a, %a)" pp_expr e1 pp_expr e2
  | P_arishiftright (e1, e2) ->
    fprintf f "ari_shift_right(%a, %a)" pp_expr e1 pp_expr e2
  | P_undef width ->
    fprintf f "undefined(%d)" width
  | P_repeat (data, n) ->
    fprintf f "repeat(%a, %d)" pp_expr data n
  | P_addwithcarry (e_a, e_b, e_c) ->
    fprintf f "add_with_carry(%a, %a, %a)" pp_expr e_a pp_expr e_b pp_expr e_c
  | P_reduce_and e ->
    fprintf f "&(%a)" pp_expr e
  | P_reduce_xor e ->
    fprintf f "^(%a)" pp_expr e
  | P_reduce_or e ->
    fprintf f "|(%a)" pp_expr e
  | P_zeroextend (e, n) ->
    fprintf f "zero_extend(%a, %d)" pp_expr e n
  | P_signextend (e, n) ->
    fprintf f "sign_extend(%a, %d)" pp_expr e n

and pp_expr f = function
  | E_literal bv -> (*fprintf f "'%a'" Bitvec.pp bv*)
    (*fprintf f "%d:%d" (Bitvec.to_int bv) (Bitvec.length bv)*)
    pp_print_int f (Bitvec.to_int bv)
  | E_var s -> fprintf f "%s" s
  | E_part (e, lo, hi) -> fprintf f "%a[%d:%d]" pp_expr e lo hi
  | E_prim p -> pp_prim f p
  | E_load (size, addr) -> fprintf f "%d[%a]" size pp_expr addr

(*let pp_loc f = function
  | L_var name -> pp_print_string f name
  | L_part (name, lo, hi) -> fprintf f "%s[%d:%d]" name lo hi*)

let pp_loc = pp_print_string

let pp_stmt f = function
  | S_set (loc, e) ->
    fprintf f "%a = %a" pp_loc loc pp_expr e
  | S_store (size, e_addr, e_data) ->
    fprintf f "%d[%a] = %a" size pp_expr e_addr pp_expr e_data
  | S_jump e ->
    fprintf f "jump %a" pp_expr e
  | S_br (e, e') ->
    fprintf f "br %a, %a" pp_expr e pp_expr e'
  | S_call (proc, args, result_opt) ->
    begin match result_opt with
      | None -> ()
      | Some loc -> fprintf f "%a = " pp_loc loc
    end;
    fprintf f "%s(" proc.p_name;
    let n = List.length args in
    args |> List.iteri (fun i arg ->
        pp_expr f arg;
        if i < n-1 then fprintf f ", ");
    fprintf f ")";
  | S_output e ->
    fprintf f "output %a" pp_expr e

let pp_proc f proc =
  let n_param = List.length proc.p_param_names in
  fprintf f "@[<v>";
  (* print header *)
  fprintf f "@[(";
  proc.p_param_names |> List.iteri (fun i name ->
      fprintf f "%s" name;
      if i < n_param-1 then fprintf f ",@ ");
  fprintf f "):%d@]@ " proc.p_result_width;
  (* print env *)
  (*fprintf f "%a@ " pp_env proc.p_env;*)
  (* print body*)
  fprintf f "{@ ";
  fprintf f "  @[<v>";
  let n_stmt = List.length proc.p_body in
  proc.p_body |> List.iteri (fun i stmt ->
      fprintf f "%a" pp_stmt stmt;
      if i < n_stmt-1 then fprintf f "@ ");
  fprintf f "@]@ ";
  fprintf f "}@]";

type env = {
  var_tab : (string, int) Hashtbl.t;
  mutable stmts_rev : stmt list;
}

let new_env () =
  { var_tab = Hashtbl.create 0;
    stmts_rev = [] }

let new_temp env width =
  let n = Hashtbl.length env.var_tab in
  let id = sprintf "$%d" n in
  Hashtbl.add env.var_tab id width;
  id

let append_stmt env stmt =
  env.stmts_rev <- stmt :: env.stmts_rev

let get_stmts env =
  List.rev env.stmts_rev
