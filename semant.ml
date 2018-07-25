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
  | P2_concat
  | P2_add
  | P2_sub
  | P2_shiftleft
  | P2_logshiftright
  | P2_arishiftright
  | P2_less
  | P2_below
  | P2_eq
  | P2_and
  | P2_xor
  | P2_or
  | P2_updatepart of reg_part

type prim3 =
  | P3_carry

module type VarType = sig
  type t
  val pp : Format.formatter -> t -> unit
  val to_int : t -> int
  val to_string : t -> string
  val of_string : string -> t
  val size_in_cfg : 'a Cfg.cfg -> t -> int
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

  let to_string =
    Printf.(function
        | Global r -> sprintf "R:%s" (Inst.string_of_reg r)
        | Temp i -> sprintf "T:%d" i
        | Local s -> sprintf "L:%s" s
        | PC -> "PC"
        | Nondet w -> sprintf "N:%d" w
      )

  let of_string s =
    let tl = String.tail s 2 in
    match String.left s 2 with
    | "R:" -> Global (Inst.lookup_reg tl)
    | "T:" -> Temp (int_of_string tl)
    | "L:" -> Local tl
    | "PC" -> PC
    | "N:" -> Nondet (int_of_string tl)
    | _ -> invalid_arg ("Var.of_string: " ^ s)

  let size_in_cfg cfg = function
    | Global r -> Inst.size_of_reg r
    | Temp i -> cfg.Cfg.temp_tab.(i)
    | _ -> invalid_arg "Var.size_in_cfg"

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
  let size_in_cfg cfg { uid; _ } = cfg.Cfg.temp_tab.(uid)
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

  type expr =
    | E_lit of Bitvec.t
    | E_const of string * int
    | E_var of var
    | E_prim1 of prim1 * expr
    | E_prim2 of prim2 * expr * expr
    | E_prim3 of prim3 * expr * expr * expr
    | E_load of int * expr
    | E_nondet of int * int
    | E_extend of bool * expr * int
    | E_shrink of expr * int

  let make_lit width value = E_lit (Bitvec.of_nativeint width value)
  let expr_of_bitvec bv = E_lit bv
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
    p_results : (string * int) list;
    p_var_tab : (string, int) Hashtbl.t;
  }

  let pp_var_part f (var, part) =
    fprintf f "%s(%a)" (string_of_reg_part part) V.pp var

  let rec pp_expr f = function
    | E_lit bv -> fprintf f "%nd" (Bitvec.to_nativeint bv) (* width is lost *)
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
      end
    | E_prim2 (p, e1, e2) ->
      begin match p with
        | P2_concat -> fprintf f "(%a.%a)" pp_expr e1 pp_expr e2
        | P2_add -> fprintf f "(%a + %a)" pp_expr e1 pp_expr e2
        | P2_sub -> fprintf f "(%a - %a)" pp_expr e1 pp_expr e2
        | P2_shiftleft -> fprintf f "(%a << %a)" pp_expr e1 pp_expr e2
        | P2_logshiftright -> fprintf f "(%a >> %a)" pp_expr e1 pp_expr e2
        | P2_arishiftright -> fprintf f "(%a ±>> %a)" pp_expr e1 pp_expr e2
        | P2_less -> fprintf f "(%a ±< %a)" pp_expr e1 pp_expr e2
        | P2_below -> fprintf f "(%a < %a)" pp_expr e1 pp_expr e2
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
    | E_nondet (n, id) -> fprintf f "nondet(%d)#%d" n id
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

  let rec subst f = function
    | E_lit _ as e -> e
    | E_const _ as e -> e
    | E_var v -> f v
    | E_prim1 (p, e) -> E_prim1 (p, subst f e)
    | E_prim2 (p, e1, e2) ->
      E_prim2 (p, subst f e1, subst f e2)
    | E_prim3 (p, e1, e2, e3) ->
      E_prim3 (p, subst f e1, subst f e2, subst f e3)
    | E_load (size, addr) -> E_load (size, subst f addr)
    | E_nondet _ as e -> e
    | E_extend (sign, e, n) -> E_extend (sign, subst f e, n)
    | E_shrink (e, n) -> E_shrink (subst f e, n)

  let map_stmt f = function
    | S_set (lhs, rhs) -> S_set (lhs, f rhs)
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

  let rec size_of_expr cfg = function
    | E_lit bv -> Bitvec.length bv
    | E_const (_, size) -> size
    | E_var v -> V.size_in_cfg cfg v
    | E_prim1 (p, e) ->
      begin match p with
        | P1_not | P1_neg -> size_of_expr cfg e
        | P1_foldand | P1_foldxor | P1_foldor -> 1
        | P1_part LoByte | P1_part HiByte -> 8
        | P1_part LoWord -> 16
      end
    | E_prim2 (p, e1, e2) ->
      begin match p with
        | P2_concat -> size_of_expr cfg e1 + size_of_expr cfg e2
        | P2_add | P2_sub
        | P2_shiftleft | P2_logshiftright | P2_arishiftright
        | P2_and | P2_xor | P2_or | P2_updatepart _ ->
          size_of_expr cfg e1
        | P2_eq | P2_less | P2_below -> 1
      end
    | E_prim3 (p, e1, e2, e3) ->
      begin match p with
        | P3_carry -> 1
      end
    | E_load (nbyte, _) -> nbyte * 8
    | E_nondet (size, _) -> size
    | E_extend (_, _, size) -> size
    | E_shrink (_, size) -> size

  let rec to_z3expr z3 cfg e =
    let open Z3 in
    let open Expr in
    let open BitVector in
    let size = size_of_expr cfg e in
    match e with
    | E_lit bv ->
      let i = Bitvec.to_nativeint bv in
      let s = Nativeint.to_string i in
      mk_numeral z3 s size
    | E_const (s, _) -> mk_const_s z3 s size
    | E_var v ->
      mk_const_s z3 (V.to_string v) size
    | E_prim1 (p, e) ->
      let mk =
        match p with
        | P1_not -> mk_not
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
          fun z3 -> mk_extract z3 lo hi
      in
      mk z3 (to_z3expr z3 cfg e)
    | E_prim2 (p, e1, e2) ->
      let mk =
        match p with
        | P2_add -> mk_add
        | P2_and -> mk_and
        | P2_xor -> mk_xor
        | P2_or -> mk_or
        | P2_concat -> mk_concat
        | P2_sub -> mk_sub
        | P2_eq -> Boolean.mk_eq
        | P2_shiftleft -> mk_shl
        | P2_logshiftright -> mk_lshr
        | P2_arishiftright -> mk_ashr
        | P2_less -> mk_slt
        | P2_below -> mk_ult
        | P2_updatepart p ->
          begin match p with
            | LoByte ->
              fun z3 e1 e2 -> mk_concat z3 e2 (mk_extract z3 8 (size-1) e1)
            | LoWord ->
              fun z3 e1 e2 -> mk_concat z3 e2 (mk_extract z3 16 (size-1) e1)
            | HiByte ->
              fun z3 e1 e2 ->
                mk_concat z3 (mk_extract z3 0 7 e1)
                  (mk_concat z3 e2 (mk_extract z3 16 (size-1) e1))
          end
      in
      mk z3 (to_z3expr z3 cfg e1) (to_z3expr z3 cfg e2)
    | E_prim3 (p, e1, e2, e3) ->
      begin match p with
        | P3_carry ->
          let size = size_of_expr cfg e1 in
          let sortn = mk_sort z3 size in
          let sort1 = mk_sort z3 1 in
          let carry_func =
            FuncDecl.mk_func_decl_s z3 (Printf.sprintf "carry%d" size)
              [sortn; sortn; sort1] sort1
          in
          mk_app z3 carry_func
            [to_z3expr z3 cfg e1; to_z3expr z3 cfg e2; to_z3expr z3 cfg e3]
      end
    | E_load (nbyte, e) ->
      let mem_func =
        FuncDecl.mk_func_decl_s z3 (Printf.sprintf "mem%d" (nbyte*8))
          [mk_sort z3 32] (mk_sort z3 (nbyte*8))
      in
      mk_app z3 mem_func [to_z3expr z3 cfg e]
    | E_nondet (size, id) ->
      let int_sort = Arithmetic.Integer.mk_sort z3 in
      let nondet_func =
        FuncDecl.mk_func_decl_s z3 (Printf.sprintf "nondet%d" id)
          [int_sort] (mk_sort z3 size)
      in
      mk_app z3 nondet_func [mk_numeral_int z3 id int_sort]
    | E_extend (sign, e, size)->
      (if sign then mk_sign_ext else mk_zero_ext) z3 size (to_z3expr z3 cfg e)
    | E_shrink (e, size)->
      mk_extract z3 0 (size-1) (to_z3expr z3 cfg e)

  let func_sym_table = [
    "bvadd", (fun [a;b] -> E_prim2 (P2_add, a, b));
    "bvsub", (fun [a;b] -> E_prim2 (P2_sub, a, b));
    "bvand", (fun [a;b] -> E_prim2 (P2_and, a, b));
    "bvxor", (fun [a;b] -> E_prim2 (P2_xor, a, b));
    "bvsle", (fun [a;b] -> E_prim2 (P2_less, a, b));
    "bvule", (fun [a;b] -> E_prim2 (P2_below, a, b));
    "bvor", (fun [a;b] -> E_prim2 (P2_or, a, b));
    "bvnot", (fun [a] -> E_prim1 (P1_not, a));
    "not", (fun [a] -> E_prim1 (P1_not, a));
    "=", (fun [a;b] -> E_prim2 (P2_eq, a, b));
  ] |> List.enum |> Map.String.of_enum

  let rec of_sexp = function
    | Sexplib0.Sexp.Atom s ->
      if s.[0] = '#' then
        E_lit begin
          match s.[1] with
          | 'x' ->
            "0x" ^ String.tail s 2 |> Nativeint.of_string |>
            Bitvec.of_nativeint ((String.length s - 2) * 4)
          | _ -> invalid_arg ("of_sexp: " ^ s)
        end
      else
        let len = String.length s in
        E_var begin
          (if String.left s 1 = "|" && String.right s 1 = "|" then
             String.sub s 1 (len-2)
           else s) |> V.of_string
        end
    | Sexplib0.Sexp.List l ->
      begin match l with
        | Sexplib0.Sexp.Atom s :: tl ->
          if String.left s 3 = "mem" then
            let nbyte = (String.tail s 3 |> int_of_string)/8 in
            let e =
              match tl with
              | [sexp] -> of_sexp sexp
              | _ -> invalid_arg "of_sexp(mem)"
            in
            E_load (nbyte, e)
          else if String.left s 6 = "nondet" then
            let size = String.tail s 6 |> int_of_string in
            let id =
              match tl with
              | [Sexplib0.Sexp.Atom s] -> int_of_string s
              | _ -> invalid_arg "of_sexp(nondet)"
            in
            E_nondet (size, id)
          (* else if String.left s 5 = "carry" then
            let size = String.tail s 5 |> int_of_string in
            let e1, e2, e3 =
              match
                E_
            E_carry () *)
          else
            let f =
              try Map.String.find s func_sym_table
              with Not_found ->
                invalid_arg ("of_sexp: unknown function symbol " ^ s)
            in
            tl |> List.map of_sexp |> f
        | _ -> invalid_arg "of_sexp"
      end

  let from_z3expr z3e =
    z3e |> Z3.Expr.to_string |> Parsexp.Single.parse_string_exn |> of_sexp

end

module Plain = Make(Var)
module SSA = Make(SSAVar)

(*
  | SV_global (s, i) -> fprintf f "%s#%d" s i
  | SV_temp i -> fprintf f "$%d" i
*)
