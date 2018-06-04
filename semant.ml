open Batteries
open Format

type prim1 =
  | P1_not
  | P1_neg
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
  | P3_carry

type primn =
  | Pn_concat
  | Pn_add
  | Pn_and
  | Pn_xor
  | Pn_or

type var =
  | V_global of string
  | V_temp of int
  | V_local of string
  | V_pc

type ssa_var = var * int
(*
  | SV_global of string * int
  | SV_temp of int
*)

type 'a expr =
  | E_lit of Bitvec.t
  | E_var of 'a
  | E_part of 'a expr * int * int
  | E_prim1 of prim1 * 'a expr
  | E_prim2 of prim2 * 'a expr * 'a expr
  | E_prim3 of prim3 * 'a expr * 'a expr * 'a expr
  | E_primn of primn * 'a expr list
  | E_load of int * 'a expr * 'a expr
  | E_nondet of int * int
  | E_extend of bool * 'a expr * int

(* elaborated form of instructions *)
type 'a stmt =
  | S_set of 'a * 'a expr
  | S_store of int * 'a expr * 'a expr * 'a expr
  | S_jump of 'a expr option * 'a expr
  | S_phi of 'a * 'a expr array
  | S_label of nativeint (* program counter *)
  (* the following do not occur after elaboration *)
  | S_call of proc * 'a expr list * 'a option
  | S_return of 'a expr
  | S_if of 'a expr * 'a stmt list
  | S_if_else of 'a expr * 'a stmt list * 'a stmt list
  | S_do_while of 'a stmt list * 'a expr

and proc = {
  (* for pretty printing *)
  p_name : string;
  p_body : var stmt list;
  p_param_names : string list;
  p_result_width : int;
  p_var_tab : (string, int) Hashtbl.t;
}

let pp_sep_list sep pp f = function
  | [] -> ()
  | hd :: tl ->
    fprintf f "%a" pp hd;
    List.iter (fprintf f "%s%a" sep pp) tl

let pp_var f = function
  | V_global s -> pp_print_string f s
  | V_temp i -> fprintf f "$%d" i
  | V_local s -> pp_print_string f s
  | V_pc -> pp_print_string f "PC"

let pp_ssa_var f (var, i) =
  fprintf f "%a#%d" pp_var var i
(*
  | SV_global (s, i) -> fprintf f "%s#%d" s i
  | SV_temp i -> fprintf f "$%d" i
*)

let rec pp_expr' pp_v f = function
  | E_lit bv -> fprintf f "%nd" (Bitvec.to_nativeint bv) (* width is lost *)
  | E_var var -> pp_v f var
  | E_part (e, lo, hi) -> fprintf f "%a[%d:%d]" (pp_expr' pp_v) e lo hi
  | E_prim1 (p, e) ->
    let op_s =
      match p with
      | P1_not -> "~"
      | P1_neg -> "-"
      | P1_foldand -> "&"
      | P1_foldxor -> "^"
      | P1_foldor -> "|"
    in
    fprintf f "(%s%a)" op_s (pp_expr' pp_v) e
  | E_prim2 (p, e1, e2) ->
    begin match p with
      | P2_sub -> fprintf f "(%a - %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2
      | P2_eq ->  fprintf f "(%a == %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2
      | P2_shiftleft -> fprintf f "shift_left(%a, %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2
      | P2_logshiftright -> fprintf f "log_shift_right(%a, %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2
      | P2_arishiftright -> fprintf f "ari_shift_right(%a, %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2
      | P2_less -> fprintf f "(%a <s %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2
      | P2_below -> fprintf f "(%a <u %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2
    end
  | E_prim3 (p, e1, e2, e3) ->
    begin match p with
      | P3_carry ->
        fprintf f "carry(%a, %a, %a)" (pp_expr' pp_v) e1 (pp_expr' pp_v) e2 (pp_expr' pp_v) e3
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
    fprintf f "(%a)" (pp_sep_list (" "^op_s^" ") (pp_expr' pp_v)) es
  | E_load (size, seg, addr) ->
    fprintf f "%a:[%a]@%d" (pp_expr' pp_v) seg (pp_expr' pp_v) addr size
  | E_nondet (n, id) -> fprintf f "nondet(%d)#%d" n id
  | E_extend (sign, e, n) ->
    let op_s = if sign then "sign_extend" else "zero_extend" in
    fprintf f "%s(%a, %d)" op_s (pp_expr' pp_v) e n

let pp_stmt' pp_v f = function
  | S_set (var, e) ->
    fprintf f "%a = %a" pp_v var (pp_expr' pp_v) e
  | S_store (size, seg, e_addr, e_data) ->
    fprintf f "%a:[%a]@%d = %a" (pp_expr' pp_v) seg (pp_expr' pp_v) e_addr size (pp_expr' pp_v) e_data
  | S_jump (cond_opt, e) ->
    begin match cond_opt with
      | Some cond -> fprintf f "if (%a) " (pp_expr' pp_v) cond
      | None -> ()
    end;
    fprintf f "goto %a" (pp_expr' pp_v) e
  | S_phi (lhs, rhs) ->
    fprintf f "%a = phi(%a)" pp_v lhs (pp_sep_list ", " (pp_expr' pp_v)) (Array.to_list rhs)
  | S_label pc -> fprintf f "%nd:" pc
  | S_call (proc, args, result_opt) ->
    begin match result_opt with
      | None -> ()
      | Some var -> fprintf f "%a = " pp_v var
    end;
    fprintf f "%s(" proc.p_name;
    let n = List.length args in
    args |> List.iteri (fun i arg ->
        (pp_expr' pp_v) f arg;
        if i < n-1 then fprintf f ", ");
    fprintf f ")";
  | S_return e ->
    fprintf f "return %a" (pp_expr' pp_v) e
  | S_if (e, _) -> fprintf f "if (%a) ..." (pp_expr' pp_v) e
  | S_if_else (e, _, _) -> fprintf f "if (%a) ... else ..." (pp_expr' pp_v) e
  | S_do_while (_, e) -> fprintf f "do ... while (%a)" (pp_expr' pp_v) e

let pp_proc f proc =
  let n_param = List.length proc.p_param_names in
  fprintf f "@[<v>";
  (* print header *)
  fprintf f "@[(";
  proc.p_param_names |> List.iteri (fun i name ->
      fprintf f "%s" name;
      if i < n_param-1 then fprintf f ",@ ");
  fprintf f "):%d@]@ " proc.p_result_width;
  (* print body *)
  fprintf f "{@ ";
  fprintf f "  @[<v>";
  let n_stmt = List.length proc.p_body in
  proc.p_body |> List.iteri (fun i stmt ->
      fprintf f "%a" (pp_stmt' pp_var) stmt;
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
  | E_load (size, seg, addr) -> E_load (size, subst_expr f seg, subst_expr f addr)
  | E_nondet _ as e -> e
  | E_extend (sign, e, n) -> E_extend (sign, subst_expr f e, n)

let map_stmt f = function
  | S_set (lhs, rhs) -> S_set (lhs, f rhs)
  | S_store (size, seg, addr, data) ->
    S_store (size, seg, f addr, f data)
  | S_jump (cond_opt, dest) ->
    let cond_opt' = Option.map f cond_opt in
    let dest' = f dest in
    S_jump (cond_opt', dest')
  | S_phi (lhs, rhs) -> S_phi (lhs, Array.map f rhs)
  | S_label _ as s -> s
  | _ -> failwith "map_stmt: not implemented"

let subst_stmt f stmt = map_stmt (subst_expr f) stmt

let rec rename_variables f expr = subst_expr (fun name -> E_var (f name)) expr
