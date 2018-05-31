open Batteries
open Format

type prim1 =
  | P1_not
  | P1_foldand
  | P1_foldxor
  | P1_foldor

type prim2 =
  | P2_sub
  | P2_eq
  | P2_shiftleft
  | P2_logshiftright
  | P2_arishiftright
  | P2_less
  | P2_below

type prim3 =
  | P3_addwithcarry

type primn =
  | Pn_concat
  | Pn_add
  | Pn_and
  | Pn_xor
  | Pn_or

type expr =
  | E_lit of Bitvec.t
  | E_var of string
  | E_part of expr * int * int
  | E_prim1 of prim1 * expr
  | E_prim2 of prim2 * expr * expr
  | E_prim3 of prim3 * expr * expr * expr
  | E_primn of primn * expr list
  | E_load of int * expr * expr
  | E_nondet of int * int
  | E_extend of bool * expr * int

type loc = string

type jump =
  | J_unknown
  | J_resolved
  | J_call
  | J_ret

(* elaborated form of instructions *)
type stmt =
  | S_set of loc * expr
  | S_store of int * expr * expr * expr
  | S_jump of expr option * expr * string list * expr list
  | S_phi of string * expr array
  (* the following do not occur after elaboration *)
  | S_call of proc * expr list * loc option
  | S_return of expr
  | S_if of expr * stmt list
  | S_if_else of expr * stmt list * stmt list
  | S_do_while of stmt list * expr

and proc = {
  (* for pretty printing *)
  p_name : string;
  p_body : stmt list;
  p_param_names : string list;
  p_result_width : int;
  p_var_tab : (string, int) Hashtbl.t;
}

let pp_sep_list sep pp f = function
  | [] -> ()
  | hd :: tl ->
    fprintf f "%a" pp hd;
    List.iter (fprintf f "%s%a" sep pp) tl

let rec pp_expr f = function
  | E_lit bv -> (*fprintf f "'%a'" Bitvec.pp bv*)
    (*fprintf f "%d:%d" (Bitvec.to_int bv) (Bitvec.length bv)*)
    fprintf f "%nu" (Bitvec.to_nativeint bv)
  | E_var s -> pp_print_string f s
  | E_part (e, lo, hi) -> fprintf f "%a[%d:%d]" pp_expr e lo hi
  | E_prim1 (p, e) ->
    let op_s =
      match p with
      | P1_not -> "~"
      | P1_foldand -> "&"
      | P1_foldxor -> "^"
      | P1_foldor -> "|"
    in
    fprintf f "(%s%a)" op_s pp_expr e
  | E_prim2 (p, e1, e2) ->
    begin match p with
      | P2_sub -> fprintf f "(%a - %a)" pp_expr e1 pp_expr e2
      | P2_eq ->  fprintf f "(%a == %a)" pp_expr e1 pp_expr e2
      | P2_shiftleft -> fprintf f "shift_left(%a, %a)" pp_expr e1 pp_expr e2
      | P2_logshiftright -> fprintf f "log_shift_right(%a, %a)" pp_expr e1 pp_expr e2
      | P2_arishiftright -> fprintf f "ari_shift_right(%a, %a)" pp_expr e1 pp_expr e2
      | P2_less -> fprintf f "(%a <s %a)" pp_expr e1 pp_expr e2
      | P2_below -> fprintf f "(%a <u %a)" pp_expr e1 pp_expr e2
    end
  | E_prim3 (p, e1, e2, e3) ->
    begin match p with
      | P3_addwithcarry ->
        fprintf f "add_with_carry(%a, %a, %a)" pp_expr e1 pp_expr e2 pp_expr e3
    end
  | E_primn (p, es) ->
    let op_s =
      match p with
      | Pn_concat -> "."
      | Pn_add -> "+"
      | Pn_and -> "&"
      | Pn_xor -> "^"
      | Pn_or -> "|"
    in
    fprintf f "(%a)" (pp_sep_list (" "^op_s^" ") pp_expr) es
  | E_load (size, seg, addr) ->
    fprintf f "%a:[%a]@%d" pp_expr seg pp_expr addr size
  | E_nondet (n, id) -> fprintf f "nondet(%d)#%d" n id
  | E_extend (sign, e, n) ->
    let op_s = if sign then "sign_extend" else "zero_extend" in
    fprintf f "%s(%a, %d)" op_s pp_expr e n

(*let pp_loc f = function
  | L_var name -> pp_print_string f name
  | L_part (name, lo, hi) -> fprintf f "%s[%d:%d]" name lo hi*)

let pp_loc = pp_print_string

let pp_stmt f = function
  | S_set (loc, e) ->
    fprintf f "%a = %a" pp_loc loc pp_expr e
  | S_store (size, seg, e_addr, e_data) ->
    fprintf f "%a:[%a]@%d = %a" pp_expr seg pp_expr e_addr size pp_expr e_data
  | S_jump (cond_opt, e, _, _) ->
    (*let j_s =
      match j with
      | J_unknown -> "(?)"
      | J_resolved -> ""
      | J_call -> "(call)"
      | J_ret -> "(ret)"
    in
    fprintf f "jump%s %a" j_s pp_expr e;*)
    begin match cond_opt with
      | Some cond -> fprintf f "if (%a) " pp_expr cond
      | None -> ()
    end;
    fprintf f "goto %a" pp_expr e
  | S_phi (lhs, rhs) ->
    fprintf f "%s = phi(%a)" lhs (pp_sep_list ", " pp_expr) (Array.to_list rhs)
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
  | S_return e ->
    fprintf f "return %a" pp_expr e
  | S_if (e, _) -> fprintf f "if (%a) ..." pp_expr e
  | S_if_else (e, _, _) -> fprintf f "if (%a) ... else ..." pp_expr e
  | S_do_while (_, e) -> fprintf f "do ... while (%a)" pp_expr e

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
  fprintf f "}@]"

let rec subst_expr f = function
  | E_lit _ as e -> e
  | E_var name -> f name
  | E_part (e, lo, hi) -> E_part (subst_expr f e, lo, hi)
  | E_prim1 (p, e) -> E_prim1 (p, subst_expr f e)
  | E_prim2 (p, e1, e2) ->
    E_prim2 (p, subst_expr f e1, subst_expr f e2)
  | E_prim3 (p, e1, e2, e3) ->
    E_prim3 (p, subst_expr f e1, subst_expr f e2, subst_expr f e3)
  | E_primn (p, es) ->
    E_primn (p, List.map (subst_expr f) es)
  | E_load (size, seg, addr) -> E_load (size, seg, subst_expr f addr)
  | E_nondet _ as e -> e
  | E_extend (sign, e, n) -> E_extend (sign, subst_expr f e, n)

let map_stmt f = function
  | S_set (lhs, rhs) -> S_set (lhs, f rhs)
  | S_store (size, seg, addr, data) ->
    S_store (size, seg, f addr, f data)
  | S_jump (cond_opt, dest, d, u) ->
    let cond_opt' = Option.map f cond_opt in
    let dest' = f dest in
    let u' = List.map f u in
    S_jump (cond_opt', dest', d, u')
  | S_phi (lhs, rhs) -> S_phi (lhs, Array.map f rhs)
  | _ -> failwith "not implemented"

let subst_stmt f stmt = map_stmt (subst_expr f) stmt

let rec rename_variables f expr = subst_expr (fun name -> E_var (f name)) expr
