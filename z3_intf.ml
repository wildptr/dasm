open Batteries
open Semant
open Normal

let mk_andb2 z3 e1 e2 =
  Z3.Boolean.mk_and z3 [e1;e2]

let mk_orb2 z3 e1 e2 =
  Z3.Boolean.mk_or z3 [e1;e2]

let rec to_z3expr z3 tab e =
  let open Z3 in
  let open Expr in
  let open BitVector in
  let poly tab e mk_bool mk_bv =
    let typ = type_of_expr tab e in
    match typ with
    | T_bool -> mk_bool
    | T_bitvec _ -> mk_bv
    | T_mem -> failwith "poly: type error"
  in
  let typ = type_of_expr tab e in
  let extract_width = function
    | T_bitvec n -> n
    | _ -> failwith "extract_width: type error"
  in
  let to_sort z3 = function
    | T_bool -> Boolean.mk_sort z3
    | T_bitvec n -> mk_sort z3 n
    | T_mem ->
      let addr_sort = mk_sort z3 32 in
      let byte_sort = mk_sort z3 8 in
      Z3Array.mk_sort z3 addr_sort byte_sort
  in
  match e with
  | E_lit (BitvecLit, bv) ->
    let i = Bitvec.to_nativeint bv in
    let s = Nativeint.to_string i in
    mk_numeral z3 s (extract_width typ)
  | E_lit (BoolLit, b) -> (if b then Boolean.mk_true else Boolean.mk_false) z3
  | E_const (s, typ) -> Expr.mk_const_s z3 s (to_sort z3 typ)
  | E_var v ->
    Expr.mk_const_s z3 (Printf.sprintf "v%d" (int_of_var v)) (to_sort z3 typ)
  | E_prim1 (p, e) ->
    let mk =
      match p with
      | P1_not -> poly tab e Boolean.mk_not BitVector.mk_not
      | P1_neg -> mk_neg
      | P1_foldand -> mk_redand
      | P1_foldxor -> failwith "to_z3expr: P1_foldxor"
      | P1_foldor -> mk_redor
      | P1_part p ->
        let lo, hi =
          match p with
          | LoByte -> 0, 7
          | HiByte -> 8, 15
          | LoWord -> 0, 15
        in
        fun z3 -> mk_extract z3 hi lo
      | P1_extract (lo, hi) -> fun z3 -> mk_extract z3 (hi-1) lo
      | P1_extend (sign, size) -> fun z3 ->
        let size_inc = size - extract_width (type_of_expr tab e) in
        (if sign then mk_sign_ext else mk_zero_ext) z3 size_inc
    in
    mk z3 (to_z3expr z3 tab e)
  | E_prim2 (p, e1, e2) ->
    let mk =
      match p with
      | P2_mul -> mk_mul
      | P2_add -> mk_add
      | P2_and -> poly tab e1 mk_andb2 BitVector.mk_and
      | P2_xor -> poly tab e1 Boolean.mk_xor BitVector.mk_xor
      | P2_or -> poly tab e1 mk_orb2 BitVector.mk_or
      | P2_concat -> mk_concat
      | P2_sub -> mk_sub
      | P2_eq -> Boolean.mk_eq
      | P2_shiftleft -> mk_shl
      | P2_logshiftright -> mk_lshr
      | P2_arishiftright -> mk_ashr
      | P2_less -> mk_slt
      | P2_less_eq -> mk_sle
      | P2_below -> mk_ult
      | P2_below_eq -> mk_ule
      | P2_updatepart p ->
        let size = extract_width typ in
        begin match p with
          | LoByte ->
            fun z3 e1 e2 -> mk_concat z3 (mk_extract z3 (size-1) 8 e1) e2
          | LoWord ->
            fun z3 e1 e2 -> mk_concat z3 (mk_extract z3 (size-1) 16 e1) e2
          | HiByte ->
            fun z3 e1 e2 ->
              mk_concat z3 (mk_extract z3 (size-1) 16 e1)
                (mk_concat z3 e2 (mk_extract z3 7 0 e1))
        end
      | P2_load nbyte -> fun z3 e1 e2 ->
        begin match nbyte with
          | 1 -> Z3Array.mk_select z3 e1 e2
          | 2 ->
            let mem = to_sort z3 T_mem in
            let bv16 = mk_sort z3 16 in
            let bv32 = mk_sort z3 32 in
            let f = FuncDecl.mk_func_decl_s z3 "select2" [mem; bv32] bv16 in
            mk_app z3 f [e1; e2]
(*
            let e2_1 = mk_add z3 e2 (mk_numeral z3 "1" 32) in
            Z3Array.mk_select z3 e1 e2 |>
            mk_concat z3 (Z3Array.mk_select z3 e1 e2_1)
*)
          | 4 ->
            let mem = to_sort z3 T_mem in
            let bv32 = mk_sort z3 32 in
            let f = FuncDecl.mk_func_decl_s z3 "select4" [mem; bv32] bv32 in
            mk_app z3 f [e1; e2]
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
    mk z3 (to_z3expr z3 tab e1) (to_z3expr z3 tab e2)
  | E_prim3 (p, e1, e2, e3) ->
    begin match p with
      | P3_carry ->
        let size = type_of_expr tab e1 |> extract_width in
        let sortn = mk_sort z3 size in
        let bool_sort = Boolean.mk_sort z3 in
        let carry_func =
          FuncDecl.mk_func_decl_s z3 (Printf.sprintf "carry%d" size)
            [sortn; sortn; bool_sort] bool_sort
        in
        mk_app z3 carry_func
          [to_z3expr z3 tab e1; to_z3expr z3 tab e2; to_z3expr z3 tab e3]
      | P3_ite ->
        Boolean.mk_ite z3 (to_z3expr z3 tab e1)
          (to_z3expr z3 tab e2) (to_z3expr z3 tab e3)
      | P3_store nbyte ->
        let e1 = to_z3expr z3 tab e1 in
        let e2 = to_z3expr z3 tab e2 in
        let e3 = to_z3expr z3 tab e3 in
        begin match nbyte with
          | 1 -> Z3Array.mk_store z3 e1 e2 e3
          | 2 ->
            let mem = to_sort z3 T_mem in
            let bv16 = mk_sort z3 16 in
            let bv32 = mk_sort z3 32 in
            let f = FuncDecl.mk_func_decl_s z3 "store2" [mem; bv32; bv16] mem in
            mk_app z3 f [e1; e2; e3]
(*
            let e2_1 = mk_add z3 e2 (mk_numeral z3 "1" 32) in
            e1 |> fun a ->
            Z3Array.mk_store z3 a e2   (mk_extract z3  7 0 e3) |> fun a ->
            Z3Array.mk_store z3 a e2_1 (mk_extract z3 15 8 e3)
*)
          | 4 ->
            let mem = to_sort z3 T_mem in
            let bv32 = mk_sort z3 32 in
            let f = FuncDecl.mk_func_decl_s z3 "store4" [mem; bv32; bv32] mem in
            mk_app z3 f [e1; e2; e3]
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
    let int_sort = Arithmetic.Integer.mk_sort z3 in
    let nondet_func =
      FuncDecl.mk_func_decl_s z3 (Format.asprintf "nondet%a" pp_typ typ)
        [int_sort] (to_sort z3 typ)
    in
    mk_app z3 nondet_func [mk_numeral_int z3 id int_sort]

let rec make_prim2_from_list p = function
  | [] -> failwith "make_prim2_from_list: empty list"
  | [a] -> a
  | a::b::l -> make_prim2_from_list p (E_prim2 (p, a, b) :: l)

let func_sym_table = [
  "bvmul", (make_prim2_from_list P2_mul);
  "bvadd", (make_prim2_from_list P2_add);
  "bvsub", (make_prim2_from_list P2_sub);
  "bvand", (make_prim2_from_list P2_and);
  "and", (make_prim2_from_list P2_and);
  "bvxor", (make_prim2_from_list P2_xor);
  "bvor", (make_prim2_from_list P2_or);
  "or", (make_prim2_from_list P2_or);
  "bvslt", (fun [a;b] -> E_prim2 (P2_less, a, b));
  "bvsle", (fun [a;b] -> E_prim2 (P2_less_eq, a, b));
  "bvult", (fun [a;b] -> E_prim2 (P2_below, a, b));
  "bvule", (fun [a;b] -> E_prim2 (P2_below_eq, a, b));
  "bvnot", (fun [a] -> E_prim1 (P1_not, a));
  "not", (fun [a] -> E_prim1 (P1_not, a));
  "=", (fun [a;b] -> E_prim2 (P2_eq, a, b));
  "concat", (make_prim2_from_list P2_concat);
  "ite", (fun [a;b;c] -> E_prim3 (P3_ite, a, b, c));
  "bvshl",  (fun [a;b] -> E_prim2 (P2_shiftleft, a, b));
  "bvlshr", (fun [a;b] -> E_prim2 (P2_logshiftright, a, b));
  "bvashr", (fun [a;b] -> E_prim2 (P2_arishiftright, a, b));
] [@warning "-8"] |> List.enum |> Map.String.of_enum

let rec of_sexp lb sexp =
  let open Sexplib0.Sexp in
  match sexp with
  | Atom s ->
    if s.[0] = '#' then
      E_lit (
        BitvecLit,
        match s.[1] with
        | 'b' ->
          "0b" ^ String.tail s 2 |> Nativeint.of_string |>
          Bitvec.of_nativeint (String.length s - 2)
        | 'x' ->
          "0x" ^ String.tail s 2 |> Nativeint.of_string |>
          Bitvec.of_nativeint ((String.length s - 2) * 4)
        | _ -> invalid_arg ("of_sexp: " ^ s)
      )
    else
    if s = "true" then E_lit (BoolLit, true)
    else if s = "false" then E_lit (BoolLit, false)
    else if String.left s 1 = "v" then
      let v = String.tail s 1 |> int_of_string |> var_of_int in E_var v
    else lb s
  | List l ->
    begin match l with
      | [Atom "let"; List bindings; body] ->
        let m =
          bindings |> List.map begin fun (List [Atom name; val_sexp]) ->
            name, of_sexp lb val_sexp
          end [@warning "-8"] |> List.enum |> Map.String.of_enum
        in
        let lb' name =
          match Map.String.Exceptionless.find name m with
            Some e -> e | None -> lb name
        in
        of_sexp lb' body
      | [Atom "select"; a; b] ->
        E_prim2 (P2_load 1, of_sexp lb a, of_sexp lb b)
      | [Atom "select2"; a; b] ->
        E_prim2 (P2_load 2, of_sexp lb a, of_sexp lb b)
      | [Atom "select4"; a; b] ->
        E_prim2 (P2_load 4, of_sexp lb a, of_sexp lb b)
      | [Atom "store"; a; b; c] ->
        E_prim3 (P3_store 1, of_sexp lb a, of_sexp lb b, of_sexp lb c)
      | [Atom "store2"; a; b; c] ->
        E_prim3 (P3_store 2, of_sexp lb a, of_sexp lb b, of_sexp lb c)
      | [Atom "store4"; a; b; c] ->
        E_prim3 (P3_store 4, of_sexp lb a, of_sexp lb b, of_sexp lb c)
      | Atom s :: tl ->
        if String.left s 6 = "nondet" then
          let typ =
            if s.[6] = 'b' then T_bool
            else let size = String.tail s 6 |> int_of_string in T_bitvec size
          in
          let id =
            match tl with
            | [Atom s] -> int_of_string s
            | _ -> invalid_arg "of_sexp(nondet)"
          in
          E_nondet (typ, id)
        else if String.left s 5 = "carry" then
          (*             let size = String.tail s 5 |> int_of_string in *)
          let e1, e2, e3 =
            match tl with
            | [a;b;c] -> of_sexp lb a, of_sexp lb b, of_sexp lb c
            | _ -> invalid_arg "of_sexp(carry)"
          in
          E_prim3 (P3_carry, e1, e2, e3)
        else
          let f =
            try Map.String.find s func_sym_table
            with Not_found ->
              invalid_arg ("of_sexp: unknown function symbol " ^ s)
          in
          tl |> List.map (of_sexp lb) |> f
      | [List [Atom "_"; Atom "extract"; Atom hi; Atom lo]; a] ->
        E_prim1
          (P1_extract (int_of_string lo, int_of_string hi + 1), of_sexp lb a)
      | _ -> invalid_arg "of_sexp"
    end

let from_z3expr z3e =
  try
    z3e |> Z3.Expr.to_string |> Parsexp.Single.parse_string_exn |>
    of_sexp (fun name -> failwith ("unbound variable: " ^ name))
  with e ->
    Format.printf "%s@." (z3e |> Z3.Expr.to_string);
    raise e
