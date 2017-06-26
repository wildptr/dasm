type reg =
  | R_AX
  | R_CX
  | R_DX
  | R_BX
  | R_SP
  | R_BP
  | R_SI
  | R_DI

type prim =
  | P_not
  | P_concat
  | P_add
  | P_sub
  | P_eq
  | P_and
  | P_xor
  | P_or

type expr =
  | E_literal of Bitvec.t
  | E_local of int
  | E_global of reg
  | E_part of expr * (int * int)
  | E_prim of prim * expr list
  | E_let of expr * expr

type cmd =
  | C_set_global of reg * expr
  | C_let of expr * cmd
