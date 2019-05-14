open Semant
open Normal

module B = Z3.Boolean
module BV = Z3.BitVector
module E = Z3.Expr

type ctx = {
  z3 : Z3.context;
  bool_sort : Z3.Sort.sort;
  int_sort : Z3.Sort.sort;
  bv8_sort : Z3.Sort.sort;
  bv16_sort : Z3.Sort.sort;
  bv32_sort : Z3.Sort.sort;
  mem_sort : Z3.Sort.sort
}

let width_of_type = function
  | T_bitvec n -> n
  | _ -> failwith "width_of_type: not a bit-vector type"

let ctx =
  let z3 = Z3.mk_context [] in
  let bool_sort = B.mk_sort z3
  and int_sort = Z3.Arithmetic.Integer.mk_sort z3
  and bv8_sort = BV.mk_sort z3 8
  and bv16_sort = BV.mk_sort z3 8
  and bv32_sort = BV.mk_sort z3 32 in
  let mem_sort = Z3.Z3Array.mk_sort z3 bv32_sort bv8_sort in
  { z3; bool_sort; int_sort; bv8_sort; bv16_sort; bv32_sort; mem_sort }

let to_sort = function
  | T_bool -> ctx.bool_sort
  | T_bitvec n -> BV.mk_sort ctx.z3 n
  | T_mem -> ctx.mem_sort

let mk_and2 z3 e1 e2 =
  B.mk_and z3 [e1;e2]

let mk_or2 z3 e1 e2 =
  B.mk_or z3 [e1;e2]

let mk_neq z3 e1 e2 =
  B.mk_not z3 (B.mk_eq z3 e1 e2)

let rec to_z3expr tab e =
  let typ = type_of_expr tab e in
  match e with
  | E_lit (BitvecLit, bv) ->
    let s = Bitvec.to_string bv in
    BV.mk_numeral ctx.z3 s (width_of_type typ)
  | E_lit (BoolLit, b) ->
    B.(if b then mk_true else mk_false) ctx.z3
  | E_const (s, typ) -> E.mk_const_s ctx.z3 s (to_sort typ)
  | E_var v ->
    E.mk_const_s ctx.z3 (Printf.sprintf "v%d" (int_of_var v)) (to_sort typ)
  | E_prim1 (p, e) ->
    let mk =
      match p with
      | P1_not -> B.mk_not
      | P1_lognot -> BV.mk_not
      | P1_neg -> BV.mk_neg
      | P1_foldand -> BV.mk_redand
      | P1_foldor -> BV.mk_redor
      | P1_part p ->
        let lo, hi =
          match p with
          | LoByte -> 0, 7
          | HiByte -> 8, 15
          | LoWord -> 0, 15
        in
        fun z3 -> BV.mk_extract z3 hi lo
      | P1_extract (lo, hi) -> fun z3 -> BV.mk_extract z3 (hi-1) lo
      | P1_extend (sign, size) -> fun z3 ->
        let size_inc = size - width_of_type (type_of_expr tab e) in
        (if sign then BV.mk_sign_ext else BV.mk_zero_ext) z3 size_inc
    in
    mk ctx.z3 (to_z3expr tab e)
  | E_prim2 (p, e1, e2) ->
    let mk =
      match p with
      | P2_mul -> BV.mk_mul
      | P2_add -> BV.mk_add
      | P2_and -> mk_and2
      | P2_xor -> B.mk_xor
      | P2_or -> mk_or2
      | P2_logand -> BV.mk_and
      | P2_logxor -> BV.mk_xor
      | P2_logor -> BV.mk_or
      | P2_concat -> BV.mk_concat
      | P2_sub -> BV.mk_sub
      | P2_eq -> B.mk_eq
      | P2_neq -> mk_neq
      | P2_shl -> BV.mk_shl
      | P2_lshr -> BV.mk_lshr
      | P2_ashr -> BV.mk_ashr
      | P2_less -> BV.mk_slt
      | P2_greater_eq -> BV.mk_sge
      | P2_less_eq -> BV.mk_sle
      | P2_greater -> BV.mk_sgt
      | P2_below -> BV.mk_ult
      | P2_above_eq -> BV.mk_uge
      | P2_below_eq -> BV.mk_ule
      | P2_above -> BV.mk_ugt
      | P2_updatepart p ->
        let size = width_of_type typ in
        begin match p with
          | LoByte ->
            fun z3 e1 e2 ->
              BV.mk_concat z3 (BV.mk_extract z3 (size-1) 8 e1) e2
          | LoWord ->
            fun z3 e1 e2 ->
              BV.mk_concat z3 (BV.mk_extract z3 (size-1) 16 e1) e2
          | HiByte ->
            fun z3 e1 e2 ->
              BV.mk_concat z3 (BV.mk_extract z3 (size-1) 16 e1)
                (BV.mk_concat z3 e2 (BV.mk_extract z3 7 0 e1))
        end
      | P2_load nbyte -> fun z3 e1 e2 ->
        begin match nbyte with
          | 1 -> Z3.Z3Array.mk_select z3 e1 e2
          | 2 ->
            let f =
              Z3.FuncDecl.mk_func_decl_s z3 "select2"
                [ctx.mem_sort; ctx.bv32_sort] ctx.bv16_sort
            in
            E.mk_app z3 f [e1; e2]
(*
            let e2_1 = mk_add z3 e2 (mk_numeral z3 "1" 32) in
            Z3Array.mk_select z3 e1 e2 |>
            mk_concat z3 (Z3Array.mk_select z3 e1 e2_1)
*)
          | 4 ->
            let f =
              Z3.FuncDecl.mk_func_decl_s z3 "select4"
                [ctx.mem_sort; ctx.bv32_sort] ctx.bv32_sort in
            E.mk_app z3 f [e1; e2]
(*
            let e2_1 = mk_add z3 e2 (mk_numeral z3 "1" 32) in
            let e2_2 = mk_add z3 e2 (mk_numeral z3 "2" 32) in
            let e2_3 = mk_add z3 e2 (mk_numeral z3 "3" 32) in
            Z3Array.mk_select z3 e1 e2 |>
            mk_concat z3 (Z3Array.mk_select z3 e1 e2_1) |>
            mk_concat z3 (Z3Array.mk_select z3 e1 e2_2) |>
            mk_concat z3 (Z3Array.mk_select z3 e1 e2_3)
*)
          | _ -> failwith "unsupported load size"
        end
    in
    mk ctx.z3 (to_z3expr tab e1) (to_z3expr tab e2)
  | E_prim3 (p, e1, e2, e3) ->
    begin match p with
      | P3_carry ->
        let size = type_of_expr tab e1 |> width_of_type in
        let sortn = BV.mk_sort ctx.z3 size in
        let carry_func =
          Z3.FuncDecl.mk_func_decl_s ctx.z3 (Printf.sprintf "carry%d" size)
            [sortn; sortn; ctx.bool_sort] ctx.bool_sort
        in
        E.mk_app ctx.z3 carry_func
          [to_z3expr tab e1; to_z3expr tab e2; to_z3expr tab e3]
      | P3_ite ->
        B.mk_ite ctx.z3 (to_z3expr tab e1)
          (to_z3expr tab e2) (to_z3expr tab e3)
      | P3_store nbyte ->
        let e1 = to_z3expr tab e1
        and e2 = to_z3expr tab e2
        and e3 = to_z3expr tab e3 in
        begin match nbyte with
          | 1 -> Z3.Z3Array.mk_store ctx.z3 e1 e2 e3
          | 2 ->
            let f =
              Z3.FuncDecl.mk_func_decl_s ctx.z3 "store2"
                [ctx.mem_sort; ctx.bv32_sort; ctx.bv16_sort] ctx.mem_sort
            in
            E.mk_app ctx.z3 f [e1; e2; e3]
(*
            let e2_1 = mk_add z3 e2 (mk_numeral z3 "1" 32) in
            e1 |> fun a ->
            Z3Array.mk_store z3 a e2   (mk_extract z3  7 0 e3) |> fun a ->
            Z3Array.mk_store z3 a e2_1 (mk_extract z3 15 8 e3)
*)
          | 4 ->
            let f =
              Z3.FuncDecl.mk_func_decl_s ctx.z3 "store4"
                [ctx.mem_sort; ctx.bv32_sort; ctx.bv32_sort] ctx.mem_sort
            in
            E.mk_app ctx.z3 f [e1; e2; e3]
(*
            let e2_1 = mk_add z3 e2 (mk_numeral z3 "1" 32) in
            let e2_2 = mk_add z3 e2 (mk_numeral z3 "2" 32) in
            let e2_3 = mk_add z3 e2 (mk_numeral z3 "3" 32) in
            e1 |> fun a ->
            Z3Array.mk_store z3 a e2   (mk_extract z3  7  0 e3) |> fun a ->
            Z3Array.mk_store z3 a e2_1 (mk_extract z3 15  8 e3) |> fun a ->
            Z3Array.mk_store z3 a e2_2 (mk_extract z3 23 16 e3) |> fun a ->
            Z3Array.mk_store z3 a e2_3 (mk_extract z3 31 24 e3)
*)
          | _ -> failwith "unsupported store size"
        end
    end
  | E_nondet (typ, id) ->
    let nondet_func =
      Z3.FuncDecl.mk_func_decl_s ctx.z3 (Format.asprintf "nondet%a" pp_typ typ)
        [ctx.int_sort] (to_sort typ)
    in
    E.mk_app ctx.z3 nondet_func [E.mk_numeral_int ctx.z3 id ctx.int_sort]

let parse_symbol s =
  Scanf.sscanf s "v%d" (fun id -> E_var (var_of_int id))

let rec mk_prim2 prim = function
  | [] -> failwith "mk_prim2"
  | [e] -> e
  | e1::e2::es ->
    mk_prim2 prim (E_prim2 (prim, e1, e2) :: es)
