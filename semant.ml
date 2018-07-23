open Batteries
open Format

type reg_part = LoByte | HiByte | LoWord

let string_of_reg_part = function
  | LoByte -> "LoByte"
  | HiByte -> "HiByte"
  | LoWord -> "LoWord"

type prim1 =
  | P1_not
  | P1_neg
  | P1_foldand
  | P1_foldxor
  | P1_foldor
  | P1_part of reg_part

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
    | Global of Inst.reg
    | Temp of int
    | Local of string
    | PC
    | Nondet of int

  let pp f = function
    | Global r -> pp_print_string f (Inst.string_of_reg r)
    | Temp i -> fprintf f "$%d" i
    | Local s -> pp_print_string f s
    | PC -> pp_print_string f "PC"
    | Nondet w -> fprintf f "?%d" w

  let to_int = function
    | Global r -> Inst.int_of_reg r
    | Temp i -> Inst.number_of_registers + i
    | Local name -> failwith ("Var.to_int: Local " ^ name)
    | PC -> failwith "Var.to_int: PC"
    | Nondet _ -> failwith "Var.to_int: Nondet"

  let of_int uid =
    if uid < Inst.number_of_registers then
      Global (Inst.reg_of_int uid)
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
    | E_const of string
    | E_var of var
    | E_prim1 of prim1 * expr
    | E_prim2 of prim2 * expr * expr
    | E_prim3 of prim3 * expr * expr * expr
    | E_primn of primn * expr list
    | E_load of int * expr
    | E_nondet of int * int
    | E_extend of bool * expr * int
    | E_shrink of expr * int

  and expr = expr_proper * int (* width *)

  let make_lit width value = E_lit (Bitvec.of_nativeint width value), width
  let expr_of_bitvec bv = E_lit bv, Bitvec.length bv
  let not_expr (_, w as e) = E_prim1 (P1_not, e), w
  let make_prim2 p e1 e2 =
    let size =
      match p with
      | P2_sub ->
        if snd e1 <> snd e2 then failwith "make_prim2: width mismatch";
        snd e1
      | P2_eq | P2_below | P2_less ->
        if snd e1 <> snd e2 then failwith "make_prim2: width mismatch";
        1
      | P2_shiftleft | P2_logshiftright | P2_arishiftright ->
        snd e1
    in
    E_prim2 (p, e1, e2), size
  let make_primn p es =
    let size =
      match es with
      | [] -> failwith "make_primn: empty expression list"
      | e::es' ->
        begin match p with
          | Pn_concat ->
            es' |> List.fold_left (fun acc e' -> acc + snd e') (snd e)
          | Pn_add | Pn_and | Pn_or | Pn_xor ->
            es' |> List.iter begin fun (_, size) ->
              if snd e <> size then failwith "make_primn: width mismatch"
            end;
            snd e
        end
    in
    E_primn (p, es), size
  let extend_expr sign e n =
    E_extend (sign, e, n), n

  (* elaborated form of instructions *)
  type stmt =
    | S_set of var * expr
    | S_setpart of var * reg_part * expr
    | S_store of int * expr * expr
    | S_jump of expr option * expr
    | S_jumpout of expr * bool
    | S_jumpout_call of expr * (Inst.reg * expr) list * (Inst.reg * var) list
    | S_jumpout_ret of expr * (Inst.reg * expr) list
    | S_phi of var * expr array
    (* the following do not occur after elaboration *)
    | S_call of proc * expr list * var list
    | S_if of expr * stmt list
    | S_if_else of expr * stmt list * stmt list
    | S_do_while of stmt list * expr

  and proc = {
    (* for pretty printing *)
    p_name : string;
    p_body : stmt list;
    p_param_names : string list;
    p_results : (string * int) list;
    p_var_tab : (string, int) Hashtbl.t;
  }

  let pp_var_part f (var, part) =
    fprintf f "%s(%a)" (string_of_reg_part part) V.pp var

  let rec pp_expr f (expr, _) =
    match expr with
    | E_lit bv -> fprintf f "%nd" (Bitvec.to_nativeint bv) (* width is lost *)
    | E_const name -> pp_print_string f name
    | E_var var -> V.pp f var
    | E_prim1 (p, e) ->
      let sym_pp op_s = fprintf f "(%s%a)" op_s pp_expr e in
      let ident_pp op_s = fprintf f "%s(%a)" op_s pp_expr e in
      begin match p with
        | P1_not -> sym_pp "~"
        | P1_neg -> sym_pp "-"
        | P1_foldand -> sym_pp "&"
        | P1_foldxor -> sym_pp "^"
        | P1_foldor -> sym_pp "|"
        | P1_part p ->
          ident_pp
            (match p with
             | LoByte -> "LoByte"
             | HiByte -> "HiByte"
             | LoWord -> "LoWord")
      end
    | E_prim2 (p, e1, e2) ->
      begin match p with
        | P2_sub -> fprintf f "(%a - %a)" pp_expr e1 pp_expr e2
        | P2_eq ->  fprintf f "(%a == %a)" pp_expr e1 pp_expr e2
        | P2_shiftleft -> fprintf f "(%a << %a)" pp_expr e1 pp_expr e2
        | P2_logshiftright -> fprintf f "(%a >> %a)" pp_expr e1 pp_expr e2
        | P2_arishiftright -> fprintf f "(%a ±>> %a)" pp_expr e1 pp_expr e2
        | P2_less -> fprintf f "(%a ±< %a)" pp_expr e1 pp_expr e2
        | P2_below -> fprintf f "(%a < %a)" pp_expr e1 pp_expr e2
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
    | E_load (size, addr) ->
      fprintf f "[%a]" pp_expr addr
    | E_nondet (n, id) -> fprintf f "nondet(%d)#%d" n id
    | E_extend (sign, e, n) ->
      let op_s = if sign then "sign_extend" else "zero_extend" in
      fprintf f "%s(%a, %d)" op_s pp_expr e n
    | E_shrink (e, n) ->
      fprintf f "shrink(%a, %d)" pp_expr e n

  let pp_stmt f = function
    | S_set (var, e) ->
      fprintf f "%a = %a" V.pp var pp_expr e
    | S_setpart (var, part, e) ->
      fprintf f "%a = %a" pp_var_part (var, part) pp_expr e
    | S_store (size, e_addr, e_data) ->
      fprintf f "[%a]@%d = %a" pp_expr e_addr size pp_expr e_data
    | S_jump (cond_opt, e) ->
      begin match cond_opt with
        | Some cond -> fprintf f "if (%a) " pp_expr cond
        | None -> ()
      end;
      fprintf f "goto %a" pp_expr e
    | S_jumpout (e, _) ->
      fprintf f "jumpout %a" pp_expr e
    | S_jumpout_call (dst, arglist, retlist) ->
      retlist |> List.iter begin fun (r,v) ->
        fprintf f "%a=%s " V.pp v (Inst.string_of_reg r)
      end;
      fprintf f "call %a" pp_expr dst;
      let pp_pair f (r, v) =
        fprintf f "%s=%a" (Inst.string_of_reg r) pp_expr v
      in
      begin match arglist with
        | [] -> ()
        | hd::tl ->
          fprintf f " [%a" pp_pair hd;
          tl |> List.iter (fprintf f " %a" pp_pair);
          fprintf f "]"
      end
    | S_jumpout_ret (dst, arglist) ->
      fprintf f "return_to %a" pp_expr dst;
      let pp_pair f (r, v) =
        fprintf f "%s=%a" (Inst.string_of_reg r) pp_expr v
      in
      begin match arglist with
        | [] -> ()
        | hd::tl ->
          fprintf f " [%a" pp_pair hd;
          tl |> List.iter (fprintf f " %a" pp_pair);
          fprintf f "]"
      end
    | S_phi (lhs, rhs) ->
      fprintf f "%a = phi(%a)" V.pp lhs (pp_sep_list ", " pp_expr) (Array.to_list rhs)
    | S_call (proc, args, results) ->
      begin match results with
        | [] -> ()
        | hd::tl ->
          V.pp f hd;
          tl |> List.iter (fprintf f ", %a" V.pp);
          pp_print_string f " = "
      end;
      fprintf f "%s(" proc.p_name;
      let n = List.length args in
      args |> List.iteri (fun i arg ->
          pp_expr f arg;
          if i < n-1 then fprintf f ", ");
      fprintf f ")";
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
    fprintf f ") -> ...@ "; (* TODO *)
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
      | E_const _ as e -> e
      | E_var v -> f v
      | E_prim1 (p, e) -> E_prim1 (p, subst f e)
      | E_prim2 (p, e1, e2) ->
        E_prim2 (p, subst f e1, subst f e2)
      | E_prim3 (p, e1, e2, e3) ->
        E_prim3 (p, subst f e1, subst f e2, subst f e3)
      | E_primn (p, es) ->
        E_primn (p, List.map (subst f) es)
      | E_load (size, addr) -> E_load (size, subst f addr)
      | E_nondet _ as e -> e
      | E_extend (sign, e, n) -> E_extend (sign, subst f e, n)
      | E_shrink (e, n) -> E_shrink (subst f e, n)
    in
    expr', w

  let map_stmt f = function
    | S_set (lhs, rhs) -> S_set (lhs, f rhs)
    | S_setpart (lhs, p, rhs) -> S_setpart (lhs, p, f rhs)
    | S_store (size, addr, data) ->
      S_store (size, f addr, f data)
    | S_jump (cond_opt, dest) ->
      let cond_opt' = Option.map f cond_opt in
      let dest' = f dest in
      S_jump (cond_opt', dest')
    | S_jumpout (dest, j) ->
      S_jumpout (f dest, j)
    | S_jumpout_call (dest, arglist, retlist) ->
      let dest' = f dest in
      let arglist' = arglist |> List.map (fun (r,v) -> r, f v) in
      S_jumpout_call (dest', arglist', retlist)
    | S_jumpout_ret (dest, arglist) ->
      let dest' = f dest in
      let arglist' = arglist |> List.map (fun (r,v) -> r, f v) in
      S_jumpout_ret (dest', arglist')
    | S_phi (lhs, rhs) -> S_phi (lhs, Array.map f rhs)
    | _ -> invalid_arg "map_stmt"

  let subst_stmt f stmt = map_stmt (subst f) stmt

end

module Plain = Make(Var)
module SSA = Make(SSAVar)

(*
  | SV_global (s, i) -> fprintf f "%s#%d" s i
  | SV_temp i -> fprintf f "$%d" i
*)
