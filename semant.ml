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

let size_of_reg r =
  match type_of_reg r with
  | T_bitvec n -> n
  | _ -> failwith "size_of_reg"

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
    | S_phi of var * (nativeint, expr) Hashtbl.t
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

  let pp_expr f e =
    let low = 15 in
    let wrap c p pp =
      if c < p then
        (pp_print_char f '('; pp f; pp_print_char f ')')
      else
        pp f
    in
    let rec pp c f = function
      | E_lit (BitvecLit, bv) -> fprintf f "%nd" (Bitvec.to_nativeint bv)
      | E_lit (BoolLit, b) -> pp_print_bool f b
      | E_const (name, _) -> pp_print_string f name
      | E_var var -> V.pp f var
      | E_prim1 (p, e) ->
        let sym_pp op_s = wrap c 1 (fun f -> fprintf f "(%s%a)" op_s (pp 1) e) in
        let ident_pp op_s = fprintf f "%s(%a)" op_s (pp low) e in
        begin match p with
          | P1_not -> sym_pp "~"
          | P1_neg -> sym_pp "-"
          | P1_foldand -> sym_pp "&"
          | P1_foldxor -> sym_pp "^"
          | P1_foldor -> sym_pp "|"
          | P1_part p -> ident_pp (string_of_reg_part p)
          | P1_extract (lo, hi) ->
            fprintf f "extract(%d, %d, %a)" lo hi (pp low) e
        end
      | E_prim2 (p, e1, e2) ->
        begin match p with
          | P2_concat -> wrap c 2 (fun f -> fprintf f "%a.%a" (pp 2) e1 (pp 1) e2)
          | P2_mul -> wrap c 3 (fun f -> fprintf f "%a * %a" (pp 3) e1 (pp 2) e2)
          | P2_add -> wrap c 4 (fun f -> fprintf f "%a + %a" (pp 4) e1 (pp 3) e2)
          | P2_sub -> wrap c 4 (fun f -> fprintf f "%a - %a" (pp 4) e1 (pp 3) e2)
          | P2_shiftleft -> wrap c 5 (fun f -> fprintf f "%a << %a" (pp 5) e1 (pp 4) e2)
          | P2_logshiftright -> wrap c 5 (fun f -> fprintf f "%a >> %a" (pp 5) e1 (pp 4) e2)
          | P2_arishiftright -> wrap c 5 (fun f -> fprintf f "%a ±>> %a" (pp 5) e1 (pp 4) e2)
          | P2_less -> wrap c 6 (fun f -> fprintf f "%a ±< %a" (pp 6) e1 (pp 5) e2)
          | P2_less_eq -> wrap c 6 (fun f -> fprintf f "%a ±<= %a" (pp 6) e1 (pp 5) e2)
          | P2_below -> wrap c 6 (fun f -> fprintf f "%a < %a" (pp 6) e1 (pp 5) e2)
          | P2_below_eq -> wrap c 6 (fun f -> fprintf f "%a <= %a" (pp 6) e1 (pp 5) e2)
          | P2_eq ->  wrap c 7 (fun f -> fprintf f "%a == %a" (pp 7) e1 (pp 6) e2)
          | P2_and -> wrap c 8 (fun f -> fprintf f "%a & %a" (pp 8) e1 (pp 7) e2)
          | P2_xor -> wrap c 9 (fun f -> fprintf f "%a ^ %a" (pp 9) e1 (pp 8) e2)
          | P2_or -> wrap c 10 (fun f -> fprintf f "%a | %a" (pp 10) e1 (pp 9) e2)
          | P2_updatepart p ->
            fprintf f "Update%s(%a, %a)" (string_of_reg_part p)
              (pp low) e1 (pp low) e2
        end
      | E_prim3 (p, e1, e2, e3) ->
        begin match p with
          | P3_carry ->
            fprintf f "carry(%a, %a, %a)" (pp low) e1 (pp low) e2 (pp low) e3
          | P3_ite ->
            wrap c 11 begin fun f ->
              fprintf f "if %a then %a else %a" (pp low) e1
                (pp low) e2 (pp 11) e3
            end
        end
      | E_load (size, addr) ->
        fprintf f "[%a]" (pp low) addr
      | E_nondet (typ, id) -> fprintf f "nondet(%a)#%d" pp_typ typ id
      | E_extend (sign, e, n) ->
        let op_s = if sign then "sign_extend" else "zero_extend" in
        fprintf f "%s(%a, %d)" op_s (pp low) e n
      | E_shrink (e, n) ->
        fprintf f "shrink(%a, %d)" (pp low) e n
    in
    pp low f e

  let pp_expr_dest f = function
    | E_lit (BitvecLit, bv) -> fprintf f "%nx" (Bitvec.to_nativeint bv)
    | e -> pp_expr f e

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
      fprintf f "goto %a" pp_expr_dest e
    | S_jumpout (e, _) ->
      fprintf f "jumpout %a" pp_expr_dest e
    | S_jumpout_call (dst, arglist, retlist) ->
      retlist |> List.iter begin fun (r,v) ->
        fprintf f "%a=%s " V.pp v (Inst.string_of_reg r)
      end;
      fprintf f "call %a" pp_expr_dest dst;
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
      fprintf f "return_to %a" pp_expr_dest dst;
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
      let pp_pair f (a, e) =
        fprintf f "%nx: %a" a pp_expr e
      in
      let pp_rhs f rhs =
        rhs |> Hashtbl.enum |> List.of_enum |> pp_sep_list ", " pp_pair f
      in
      fprintf f "%a = phi(%a)" V.pp lhs pp_rhs rhs
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

end

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
    | S.S_phi (lhs, rhs) ->
      S'.S_phi (fv lhs, Hashtbl.map (fun _ e -> fe e) rhs)
    | _ -> invalid_arg "map_stmt"

end

module Plain = Make(Var)
module SSA = Make(SSAVar)
