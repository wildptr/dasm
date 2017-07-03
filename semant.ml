open Core_kernel.Std
open Printf

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
[@@deriving show]

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

[@@deriving show]

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
[@@deriving show]
