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

module type VarType = sig
  type t
  val pp : Format.formatter -> t -> unit
  val to_int : t -> int
end

module Var = struct

  type t =
    | Global of string
    | Temp of int
    | Local of string
    | PC
    | Nondet of int

  let pp f = function
    | Global s -> pp_print_string f s
    | Temp i -> fprintf f "$%d" i
    | Local s -> pp_print_string f s
    | PC -> pp_print_string f "PC"
    | Nondet w -> fprintf f "?%d" w

  let to_int = function
    | Global name -> Inst.lookup_reg name |> Obj.magic
    | Temp i -> Inst.number_of_registers + i
    | _ -> failwith "Var.to_int: invalid variable"

  let of_int uid =
    if uid < Inst.number_of_registers then
      Global (Inst.string_of_reg (Obj.magic uid))
    else
      Temp (uid - Inst.number_of_registers)

end

module SSAVar = struct
  type t = { orig : Var.t; ver : int; uid : int }
  let pp f { orig; ver; uid } = fprintf f "%a#%d" Var.pp orig ver
  let to_int sv = sv.uid
end
(*
  | SV_global of string * int
  | SV_temp of int
*)

let pp_sep_list sep pp f = function
  | [] -> ()
  | hd :: tl ->
    fprintf f "%a" pp hd;
    List.iter (fprintf f "%s%a" sep pp) tl

module Make(V : VarType) = struct

  type var = V.t

  type expr_proper =
    | E_lit of Bitvec.t
    | E_var of var
    | E_part of expr * int * int
    | E_prim1 of prim1 * expr
    | E_prim2 of prim2 * expr * expr
    | E_prim3 of prim3 * expr * expr * expr
    | E_primn of primn * expr list
    | E_load of int * expr * expr
    | E_nondet of int * int
    | E_extend of bool * expr * int

  and expr = expr_proper * int (* width *)

  let make_lit width value = E_lit (Bitvec.of_nativeint width value), width
  let expr_of_bitvec bv = E_lit bv, Bitvec.length bv
  let not_expr (_, w as e) = E_prim1 (P1_not, e), w

  (* elaborated form of instructions *)
  type stmt =
    | S_set of var * expr
    | S_store of int * expr * expr * expr
    | S_jump of expr option * expr
    | S_phi of var * expr array
    (* the following do not occur after elaboration *)
    | S_call of proc * expr list * var option
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

  let rec pp_expr f (expr, _) =
    match expr with
    | E_lit bv -> fprintf f "%nd" (Bitvec.to_nativeint bv) (* width is lost *)
    | E_var var -> V.pp f var
    | E_part (e, lo, hi) -> fprintf f "%a[%d:%d]" pp_expr e lo hi
    | E_prim1 (p, e) ->
      let op_s =
        match p with
        | P1_not -> "~"
        | P1_neg -> "-"
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
        | P3_carry ->
          fprintf f "carry(%a, %a, %a)" pp_expr e1 pp_expr e2 pp_expr e3
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

  let pp_stmt f = function
    | S_set (var, e) ->
      fprintf f "%a = %a" V.pp var pp_expr e
    | S_store (size, seg, e_addr, e_data) ->
      fprintf f "%a:[%a]@%d = %a" pp_expr seg pp_expr e_addr size pp_expr e_data
    | S_jump (cond_opt, e) ->
      begin match cond_opt with
        | Some cond -> fprintf f "if (%a) " pp_expr cond
        | None -> ()
      end;
      fprintf f "goto %a" pp_expr e
    | S_phi (lhs, rhs) ->
      fprintf f "%a = phi(%a)" V.pp lhs (pp_sep_list ", " pp_expr) (Array.to_list rhs)
    | S_call (proc, args, result_opt) ->
      begin match result_opt with
        | None -> ()
        | Some var -> fprintf f "%a = " V.pp var
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
    (* print body *)
    fprintf f "{@ ";
    fprintf f "  @[<v>";
    let n_stmt = List.length proc.p_body in
    proc.p_body |> List.iteri (fun i stmt ->
        fprintf f "%a" pp_stmt stmt;
        if i < n_stmt-1 then fprintf f "@ ");
    fprintf f "@]@ ";
    fprintf f "}@]"

  let rec subst f (expr, w) =
    let expr' =
      match expr with
      | E_lit _ as e -> e
      | E_var v -> f v
      | E_part (e, lo, hi) -> E_part (subst f e, lo, hi)
      | E_prim1 (p, e) -> E_prim1 (p, subst f e)
      | E_prim2 (p, e1, e2) ->
        E_prim2 (p, subst f e1, subst f e2)
      | E_prim3 (p, e1, e2, e3) ->
        E_prim3 (p, subst f e1, subst f e2, subst f e3)
      | E_primn (p, es) ->
        E_primn (p, List.map (subst f) es)
      | E_load (size, seg, addr) -> E_load (size, subst f seg, subst f addr)
      | E_nondet _ as e -> e
      | E_extend (sign, e, n) -> E_extend (sign, subst f e, n)
    in
    expr', w

  let map_stmt f = function
    | S_set (lhs, rhs) -> S_set (lhs, f rhs)
    | S_store (size, seg, addr, data) ->
      S_store (size, f seg, f addr, f data)
    | S_jump (cond_opt, dest) ->
      let cond_opt' = Option.map f cond_opt in
      let dest' = f dest in
      S_jump (cond_opt', dest')
    | S_phi (lhs, rhs) -> S_phi (lhs, Array.map f rhs)
    | _ -> failwith "map_stmt: not implemented"

  let subst_stmt f stmt = map_stmt (subst f) stmt

end

module Plain = Make(Var)
module SSA = Make(SSAVar)

(*
  | SV_global (s, i) -> fprintf f "%s#%d" s i
  | SV_temp i -> fprintf f "$%d" i
*)
