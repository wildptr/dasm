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
  | R_PC

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
  | R_PC -> "PC"

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
  | P_load of int * expr (* size, address *)
  | P_store of int * expr * expr (* size, address, value *)
  | P_shiftleft of expr * expr
  | P_add_ex of expr * expr * expr (* add with carry *)

and expr =
  | E_literal of Bitvec.t
  | E_local of int
  | E_global of reg
  | E_part of expr * (int * int)
  | E_prim of prim
  | E_let of expr * expr
  | E_set of reg * expr (* set global *)
  | E_seq of expr * expr
  | E_setpart of reg * (int * int) * expr

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
  | P_load (size, e_addr) ->
      fprintf f "@[LOAD %d,@ %a@]" size pp_expr e_addr
  | P_store (size, e_addr, e_value) ->
      fprintf f "@[STORE %d,@ %a,@ %a@]" size pp_expr e_addr pp_expr e_value
  | P_shiftleft (e1, e2) ->
      fprintf f "@[(%a <<@ %a)@]" pp_expr e1 pp_expr e2
  | P_add_ex (e_a, e_b, e_c) ->
      fprintf f "@[add_ex(%a,@ %a,@ %a)@]" pp_expr e_a pp_expr e_b pp_expr e_c

and pp_expr f = function
  | E_literal bv -> Bitvec.pp f bv
  | E_local i -> fprintf f "$%d" i
  | E_global r -> fprintf f "%s" (string_of_reg r)
  | E_part (e, (lo, hi)) -> fprintf f "@[%a[%d:%d]@]" pp_expr e lo hi
  | E_prim p -> pp_prim f p
  | E_let (e_bind, e_body) ->
      fprintf f "@[let %a@ in@ %a@]" pp_expr e_bind pp_expr e_body
  | E_set (reg, e_value) ->
      fprintf f "@[%s =@ %a@]" (string_of_reg reg) pp_expr e_value
  | E_seq (e1, e2) ->
      fprintf f "@[<v>%a;@,%a@]" pp_expr e1 pp_expr e2
  | E_setpart (reg, (lo, hi), e_value) ->
      fprintf f "@[%s[%d:%d] =@ %a@]" (string_of_reg reg) lo hi pp_expr e_value
