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
  | P1_extract of int * int

type prim2 =
  | P2_concat
  | P2_mul
  | P2_add
  | P2_sub
  | P2_shiftleft
  | P2_logshiftright
  | P2_arishiftright
  | P2_less
  | P2_less_eq
  | P2_below
  | P2_below_eq
  | P2_eq
  | P2_and
  | P2_xor
  | P2_or
  | P2_updatepart of reg_part

type prim3 =
  | P3_carry
  | P3_ite

type typ =
  | T_bool
  | T_bitvec of int

let pp_typ f = function
  | T_bool -> pp_print_string f "bool"
  | T_bitvec size -> pp_print_int f size

let type_of_reg r =
  let open Inst in
  match r with
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH -> T_bitvec 8
  | R_AX | R_CX | R_DX | R_BX | R_SI | R_DI | R_SP | R_BP -> T_bitvec 16
  | R_EAX | R_ECX | R_EDX | R_EBX | R_ESI | R_EDI | R_ESP | R_EBP -> T_bitvec 32
  | R_ES | R_CS | R_SS | R_DS | R_FS | R_GS | R_S6 | R_S7 -> T_bitvec 16
  | R_CF | R_PF | R_AF | R_ZF | R_SF | R_IF | R_DF | R_OF -> T_bool
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 -> T_bitvec 80
  | R_XMM0 | R_XMM1 | R_XMM2 | R_XMM3 | R_XMM4 | R_XMM5 | R_XMM6 | R_XMM7 -> T_bitvec 128

module type VarType = sig
  type t
  val pp : Format.formatter -> t -> unit
  val to_int : t -> int
  val to_string : t -> string
  val of_string : string -> t
  val typ : typ array -> t -> typ
end

module Var = struct

  type t =
    | Global of Inst.reg
    | Temp of int
    | Local of string
    | PC
    | Nondet of typ

  let pp f = function
    | Global r -> pp_print_string f (Inst.string_of_reg r)
    | Temp i -> fprintf f "$%d" i
    | Local s -> pp_print_string f s
    | PC -> pp_print_string f "PC"
    | Nondet t -> fprintf f "?%a" pp_typ t

  let to_string =
    Printf.(function
        | Global r -> sprintf "R:%s" (Inst.string_of_reg r)
        | Temp i -> sprintf "T:%d" i
        | Local s -> sprintf "L:%s" s
        | PC -> "PC"
        | Nondet t -> Format.asprintf "N:%a" pp_typ t
      )

  let of_string s =
    let tl = String.tail s 2 in
    match String.left s 2 with
    | "R:" -> Global (Inst.lookup_reg tl)
    | "T:" -> Temp (int_of_string tl)
    | "L:" -> Local tl
    | "PC" -> PC
    | "N:" ->
      let typ =
        if tl.[0] = 'b' then T_bool else T_bitvec (int_of_string tl)
      in
      Nondet typ
    | _ -> invalid_arg ("Var.of_string: " ^ s)

  let typ tab = function
    | Global r -> type_of_reg r
    | Temp i -> tab.(i)
    | _ -> invalid_arg "Var.typ"

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
  let to_string { orig; ver; uid } =
    Printf.sprintf "%s,%d,%d" (Var.to_string orig) ver uid
  let of_string s =
    let fields = String.split_on_char ',' s in
    match fields with
    | [orig_s;ver_s;uid_s] ->
      let orig = Var.of_string orig_s in
      let ver = int_of_string ver_s in
      let uid = int_of_string uid_s in
      { orig; ver; uid }
    | _ -> invalid_arg ("SSAVar.of_string: " ^ s)
  let typ tab { uid; _ } = tab.(uid)
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

let mk_andb2 z3 e1 e2 =
  Z3.Boolean.mk_and z3 [e1;e2]

let mk_orb2 z3 e1 e2 =
  Z3.Boolean.mk_or z3 [e1;e2]

type 'a lit =
  | BitvecLit : Bitvec.t lit
  | BoolLit : bool lit

module Make(V : VarType) = struct

  type var = V.t

  type expr =
    | E_lit : 'a lit * 'a -> expr
    | E_const : string * typ -> expr
    | E_var : var -> expr
    | E_prim1 : prim1 * expr -> expr
    | E_prim2 : prim2 * expr * expr -> expr
    | E_prim3 : prim3 * expr * expr * expr -> expr
    | E_load : int * expr -> expr
    | E_nondet : typ * int -> expr
    | E_extend : bool * expr * int -> expr
    | E_shrink : expr * int -> expr

  let make_lit width value = E_lit (BitvecLit, Bitvec.of_nativeint width value)
  let expr_of_bitvec bv = E_lit (BitvecLit, bv)
  let not_expr e = E_prim1 (P1_not, e)
  let make_prim2 p e1 e2 =
    (* let size =
       match p with
       | P2_concat -> snd e1 + snd e2
       | P2_add | P2_sub | P2_and | P2_xor | P2_or ->
        if snd e1 <> snd e2 then failwith "make_prim2: width mismatch";
        snd e1
       | P2_eq | P2_below | P2_less ->
        if snd e1 <> snd e2 then failwith "make_prim2: width mismatch";
        1
       | P2_shiftleft | P2_logshiftright | P2_arishiftright ->
        snd e1
       | P2_updatepart _ -> snd e1
       in *)
    E_prim2 (p, e1, e2)
  (* let make_primn p es =
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
     E_primn (p, es), size *)
  let extend_expr sign e n =
    E_extend (sign, e, n)

  (* elaborated form of instructions *)
  type stmt =
    | S_set of var * expr
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
    p_results : (string * typ) list;
    p_var_tab : (string, typ) Hashtbl.t;
  }

  let pp_var_part f (var, part) =
    fprintf f "%s(%a)" (string_of_reg_part part) V.pp var

  let rec pp_expr f = function
    | E_lit (BitvecLit, bv) -> fprintf f "%nd" (Bitvec.to_nativeint bv)
    | E_lit (BoolLit, b) -> pp_print_bool f b
    | E_const (name, _) -> pp_print_string f name
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
        | P1_part p -> ident_pp (string_of_reg_part p)
        | P1_extract (lo, hi) -> fprintf f "extract(%d, %d, %a)" lo hi pp_expr e
      end
    | E_prim2 (p, e1, e2) ->
      begin match p with
        | P2_concat -> fprintf f "(%a.%a)" pp_expr e1 pp_expr e2
        | P2_mul -> fprintf f "(%a * %a)" pp_expr e1 pp_expr e2
        | P2_add -> fprintf f "(%a + %a)" pp_expr e1 pp_expr e2
        | P2_sub -> fprintf f "(%a - %a)" pp_expr e1 pp_expr e2
        | P2_shiftleft -> fprintf f "(%a << %a)" pp_expr e1 pp_expr e2
        | P2_logshiftright -> fprintf f "(%a >> %a)" pp_expr e1 pp_expr e2
        | P2_arishiftright -> fprintf f "(%a ±>> %a)" pp_expr e1 pp_expr e2
        | P2_less -> fprintf f "(%a ±< %a)" pp_expr e1 pp_expr e2
        | P2_less_eq -> fprintf f "(%a ±<= %a)" pp_expr e1 pp_expr e2
        | P2_below -> fprintf f "(%a < %a)" pp_expr e1 pp_expr e2
        | P2_below_eq -> fprintf f "(%a <= %a)" pp_expr e1 pp_expr e2
        | P2_eq ->  fprintf f "(%a == %a)" pp_expr e1 pp_expr e2
        | P2_and -> fprintf f "(%a & %a)" pp_expr e1 pp_expr e2
        | P2_xor -> fprintf f "(%a ^ %a)" pp_expr e1 pp_expr e2
        | P2_or -> fprintf f "(%a | %a)" pp_expr e1 pp_expr e2
        | P2_updatepart p ->
          fprintf f "Update%s(%a, %a)" (string_of_reg_part p)
            pp_expr e1 pp_expr e2
      end
    | E_prim3 (p, e1, e2, e3) ->
      begin match p with
        | P3_carry ->
          fprintf f "carry(%a, %a, %a)" pp_expr e1 pp_expr e2 pp_expr e3
        | P3_ite ->
          fprintf f "(if %a then %a else %a)" pp_expr e1 pp_expr e2 pp_expr e3
      end
    (* | E_primn (p, es) ->
       let op_s =
        match p with
        | Pn_concat -> "."
        | Pn_add -> "+"
        | Pn_and -> "&"
        | Pn_xor -> "^"
        | Pn_or -> "|"
       in
       fprintf f "(%a)" (pp_sep_list (" "^op_s^" ") pp_expr) es *)
    | E_load (size, addr) ->
      fprintf f "[%a]" pp_expr addr
    | E_nondet (typ, id) -> fprintf f "nondet(%a)#%d" pp_typ typ id
    | E_extend (sign, e, n) ->
      let op_s = if sign then "sign_extend" else "zero_extend" in
      fprintf f "%s(%a, %d)" op_s pp_expr e n
    | E_shrink (e, n) ->
      fprintf f "shrink(%a, %d)" pp_expr e n

  let pp_stmt f = function
    | S_set (var, e) ->
      fprintf f "%a = %a" V.pp var pp_expr e
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

  let rec type_of_expr tab = function
    | E_lit (BitvecLit, bv) -> T_bitvec (Bitvec.length bv)
    | E_lit (BoolLit, _) -> T_bool
    | E_const (_, typ) -> typ
    | E_var v -> V.typ tab v
    | E_prim1 (p, e) ->
      begin match p with
        | P1_not | P1_neg -> type_of_expr tab e
        | P1_foldand | P1_foldxor | P1_foldor -> T_bitvec 1
        | P1_part LoByte | P1_part HiByte -> T_bitvec 8
        | P1_part LoWord -> T_bitvec 16
        | P1_extract (lo, hi) -> T_bitvec (hi-lo)
      end
    | E_prim2 (p, e1, e2) ->
      begin match p with
        | P2_concat -> begin
            let T_bitvec w1 = type_of_expr tab e1 in
            let T_bitvec w2 = type_of_expr tab e2 in
            T_bitvec (w1 + w2)
          end [@warning "-8"]
        | P2_mul | P2_add | P2_sub
        | P2_shiftleft | P2_logshiftright | P2_arishiftright
        | P2_and | P2_xor | P2_or | P2_updatepart _ ->
          type_of_expr tab e1
        | P2_eq | P2_less | P2_less_eq | P2_below | P2_below_eq -> T_bool
      end
    | E_prim3 (p, e1, e2, e3) ->
      begin match p with
        | P3_carry -> T_bool
        | P3_ite -> type_of_expr tab e2
      end
    | E_load (nbyte, _) -> T_bitvec (nbyte * 8)
    | E_nondet (typ, _) -> typ
    | E_extend (_, _, size) -> T_bitvec size
    | E_shrink (_, size) -> T_bitvec size

  let poly tab e mk_bool mk_bv =
    let typ = type_of_expr tab e in
    match typ with
    | T_bool -> mk_bool
    | T_bitvec _ -> mk_bv

  let rec to_z3expr z3 tab e =
    let open Z3 in
    let open Expr in
    let open BitVector in
    let typ = type_of_expr tab e in
    let extract_width = function
      | T_bool -> failwith "type error"
      | T_bitvec n -> n
    in
    let to_sort z3 = function
      | T_bool -> Boolean.mk_sort z3
      | T_bitvec n -> mk_sort z3 n
    in
    match e with
    | E_lit (BitvecLit, bv) ->
      let i = Bitvec.to_nativeint bv in
      let s = Nativeint.to_string i in
      mk_numeral z3 s (extract_width typ)
    | E_lit (BoolLit, b) -> (if b then Boolean.mk_true else Boolean.mk_false) z3
    | E_const (s, typ) -> Expr.mk_const_s z3 s (to_sort z3 typ)
    | E_var v -> Expr.mk_const_s z3 (V.to_string v) (to_sort z3 typ)
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
              fun z3 e1 e2 -> mk_concat z3 e2 (mk_extract z3 (size-1) 8 e1)
            | LoWord ->
              fun z3 e1 e2 -> mk_concat z3 e2 (mk_extract z3 (size-1) 16 e1)
            | HiByte ->
              fun z3 e1 e2 ->
                mk_concat z3 (mk_extract z3 7 0 e1)
                  (mk_concat z3 e2 (mk_extract z3 (size-1) 16 e1))
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
      end
    | E_load (nbyte, e) ->
      let mem_func =
        FuncDecl.mk_func_decl_s z3 (Printf.sprintf "mem%d" (nbyte*8))
          [mk_sort z3 32] (mk_sort z3 (nbyte*8))
      in
      mk_app z3 mem_func [to_z3expr z3 tab e]
    | E_nondet (typ, id) ->
      let int_sort = Arithmetic.Integer.mk_sort z3 in
      let nondet_func =
        FuncDecl.mk_func_decl_s z3 (Format.asprintf "nondet%a" pp_typ typ)
          [int_sort] (to_sort z3 typ)
      in
      mk_app z3 nondet_func [mk_numeral_int z3 id int_sort]
    | E_extend (sign, e, size) ->
      let size_inc = size - extract_width (type_of_expr tab e) in
      (if sign then mk_sign_ext else mk_zero_ext) z3 size_inc (to_z3expr z3 tab e)
    | E_shrink (e, size) ->
      mk_extract z3 (size-1) 0 (to_z3expr z3 tab e)

  let rec make_prim2_from_list p = function
    | [] -> failwith "make_prim2_from_list: empty list"
    | [a] -> a
    | a::b::l -> make_prim2_from_list p (E_prim2 (p, a, b) :: l)

  let func_sym_table = [
    "bvmul", (make_prim2_from_list P2_mul);
    "bvadd", (make_prim2_from_list P2_add);
    "bvsub", (make_prim2_from_list P2_sub);
    "bvand", (make_prim2_from_list P2_and);
    "bvxor", (make_prim2_from_list P2_xor);
    "bvor", (make_prim2_from_list P2_or);
    "bvslt", (fun [a;b] -> E_prim2 (P2_less, a, b));
    "bvsle", (fun [a;b] -> E_prim2 (P2_less_eq, a, b));
    "bvult", (fun [a;b] -> E_prim2 (P2_below, a, b));
    "bvule", (fun [a;b] -> E_prim2 (P2_below_eq, a, b));
    "bvnot", (fun [a] -> E_prim1 (P1_not, a));
    "not", (fun [a] -> E_prim1 (P1_not, a));
    "=", (fun [a;b] -> E_prim2 (P2_eq, a, b));
    "concat", (make_prim2_from_list P2_concat);
    "ite", (fun [a;b;c] -> E_prim3 (P3_ite, a, b, c));
  ] [@warning "-8"] |> List.enum |> Map.String.of_enum

  let rec of_sexp sexp =
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
      else
        let len = String.length s in
        E_var begin
          (if String.left s 1 = "|" && String.right s 1 = "|" then
             String.sub s 1 (len-2)
           else s) |> V.of_string
        end
    | List l ->
      begin match l with
        | Atom s :: tl ->
          if String.left s 3 = "mem" then
            let nbyte = (String.tail s 3 |> int_of_string)/8 in
            let e =
              match tl with
              | [sexp] -> of_sexp sexp
              | _ -> invalid_arg "of_sexp(mem)"
            in
            E_load (nbyte, e)
          else if String.left s 6 = "nondet" then
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
              | [a;b;c] -> of_sexp a, of_sexp b, of_sexp c
              | _ -> invalid_arg "of_sexp(carry)"
            in
            E_prim3 (P3_carry, e1, e2, e3)
          else
            let f =
              try Map.String.find s func_sym_table
              with Not_found ->
                invalid_arg ("of_sexp: unknown function symbol " ^ s)
            in
            tl |> List.map of_sexp |> f
        | [List [Atom "_"; Atom "extract"; Atom hi; Atom lo]; a] ->
          E_prim1
            (P1_extract (int_of_string lo, int_of_string hi + 1), of_sexp a)
        | _ -> invalid_arg "of_sexp"
      end

  let from_z3expr z3e =
    try
      z3e |> Z3.Expr.to_string |> Parsexp.Single.parse_string_exn |> of_sexp
    with e ->
      Format.printf "%s@." (z3e |> Z3.Expr.to_string);
      raise e

end

module Plain = Make(Var)
module SSA = Make(SSAVar)

module Transform (V : VarType) (V' : VarType) = struct

  module S = Make(V)
  module S' = Make(V')

  let rec subst f = function
    | S.E_lit (t, v) -> S'.E_lit (t, v)
    | S.E_const (name, typ) -> S'.E_const (name, typ)
    | S.E_var v -> f v
    | S.E_prim1 (p, e) -> S'.E_prim1 (p, subst f e)
    | S.E_prim2 (p, e1, e2) ->
      S'.E_prim2 (p, subst f e1, subst f e2)
    | S.E_prim3 (p, e1, e2, e3) ->
      S'.E_prim3 (p, subst f e1, subst f e2, subst f e3)
    | S.E_load (size, addr) -> S'.E_load (size, subst f addr)
    | S.E_nondet (typ, id) -> S'.E_nondet (typ, id)
    | S.E_extend (sign, e, n) -> S'.E_extend (sign, subst f e, n)
    | S.E_shrink (e, n) -> S'.E_shrink (subst f e, n)

  let rename_var f = subst (fun v -> S'.E_var (f v))

  let map_stmt fv fe = function
    | S.S_set (lhs, rhs) -> S'.S_set (fv lhs, fe rhs)
    | S.S_store (size, addr, data) ->
      S'.S_store (size, fe addr, fe data)
    | S.S_jump (cond_opt, dest) ->
      let cond_opt' = Option.map fe cond_opt in
      let dest' = fe dest in
      S'.S_jump (cond_opt', dest')
    | S.S_jumpout (dest, j) ->
      S'.S_jumpout (fe dest, j)
    | S.S_jumpout_call (dest, arglist, retlist) ->
      let dest' = fe dest in
      let arglist' = arglist |> List.map (fun (r,v) -> r, fe v) in
      let retlist' = retlist |> List.map (fun (r,v) -> r, fv v) in
      S'.S_jumpout_call (dest', arglist', retlist')
    | S.S_jumpout_ret (dest, arglist) ->
      let dest' = fe dest in
      let arglist' = arglist |> List.map (fun (r,v) -> r, fe v) in
      S'.S_jumpout_ret (dest', arglist')
    | S.S_phi (lhs, rhs) -> S'.S_phi (fv lhs, Array.map fe rhs)
    | _ -> invalid_arg "map_stmt"

end

(*
  | SV_global (s, i) -> fprintf f "%s#%d" s i
  | SV_temp i -> fprintf f "$%d" i
*)
