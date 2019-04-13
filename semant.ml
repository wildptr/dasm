open Batteries
open Format
open Pp_util

type reg_part = LoByte | HiByte | LoWord

let string_of_reg_part = function
  | LoByte -> "LoByte"
  | HiByte -> "HiByte"
  | LoWord -> "LoWord"

let size_of_reg_part = function
  | LoByte | HiByte -> 8
  | LoWord -> 16

type prim1 =
  | P1_not
  | P1_lognot
  | P1_neg
  | P1_foldand
  | P1_foldor
  | P1_part of reg_part
  | P1_extract of int * int
  | P1_extend of bool * int

type prim2 =
  | P2_concat
  | P2_mul
  | P2_add
  | P2_sub
  | P2_shl
  | P2_lshr
  | P2_ashr
  | P2_less
  | P2_greater_eq
  | P2_less_eq
  | P2_greater
  | P2_below
  | P2_above_eq
  | P2_below_eq
  | P2_above
  | P2_eq
  | P2_neq
  | P2_and
  | P2_xor
  | P2_or
  | P2_logand
  | P2_logxor
  | P2_logor
  | P2_updatepart of reg_part
  | P2_load of int

type prim3 =
  | P3_carry
  | P3_ite
  | P3_store of int

type typ =
  | T_bool
  | T_bitvec of int
  | T_mem

let string_of_typ = function
  | T_bool -> "bool"
  | T_bitvec size -> string_of_int size
  | T_mem -> "mem"

let pp_typ f t = pp_print_string f (string_of_typ t)

type global =
  | EAX | ECX | EDX | EBX | ESP | EBP | ESI | EDI
  | ES | CS | SS | DS | FS | GS | S6 | S7
  | CF | PF | AF | ZF | SF | IF | DF | OF
  | ST0 | ST1 | ST2 | ST3 | ST4 | ST5 | ST6 | ST7
  | XMM0 | XMM1 | XMM2 | XMM3 | XMM4 | XMM5 | XMM6 | XMM7
  | Memory

let string_of_global = function
  | EAX -> "EAX"
  | ECX -> "ECX"
  | EDX -> "EDX"
  | EBX -> "EBX"
  | ESP -> "ESP"
  | EBP -> "EBP"
  | ESI -> "ESI"
  | EDI -> "EDI"
  | CF -> "CF"
  | PF -> "PF"
  | AF -> "AF"
  | ZF -> "ZF"
  | SF -> "SF"
  | IF -> "IF"
  | DF -> "DF"
  | OF -> "OF"
  | ES -> "ES"
  | CS -> "CS"
  | SS -> "SS"
  | DS -> "DS"
  | FS -> "FS"
  | GS -> "GS"
  | S6 -> "S6"
  | S7 -> "S7"
  | ST0 -> "ST0"
  | ST1 -> "ST1"
  | ST2 -> "ST2"
  | ST3 -> "ST3"
  | ST4 -> "ST4"
  | ST5 -> "ST5"
  | ST6 -> "ST6"
  | ST7 -> "ST7"
  | XMM0 -> "XMM0"
  | XMM1 -> "XMM1"
  | XMM2 -> "XMM2"
  | XMM3 -> "XMM3"
  | XMM4 -> "XMM4"
  | XMM5 -> "XMM5"
  | XMM6 -> "XMM6"
  | XMM7 -> "XMM7"
  | Memory -> "M"

let number_of_globals = Obj.magic Memory + 1

let int_of_global : global -> int = Obj.magic
let global_of_int : int -> global = Obj.magic

let all_globals =
  List.range 0 `To (number_of_globals - 1) |> List.map global_of_int

let type_of_global = function
  | EAX | ECX | EDX | EBX | ESI | EDI | ESP | EBP -> T_bitvec 32
  | ES | CS | SS | DS | FS | GS | S6 | S7 -> T_bitvec 16
  | CF | PF | AF | ZF | SF | IF | DF | OF -> T_bool
  | ST0 | ST1 | ST2 | ST3 | ST4 | ST5 | ST6 | ST7 -> T_bitvec 80
  | XMM0 | XMM1 | XMM2 | XMM3 | XMM4 | XMM5 | XMM6 | XMM7 -> T_bitvec 128
  | Memory -> T_mem

let size_of_global g =
  match type_of_global g with
  | T_bitvec n -> n
  | _ -> failwith "size_of_global"

let global_of_reg r =
  let open Inst in
  match r with
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH
  | R_AX | R_CX | R_DX | R_BX | R_SP | R_BP | R_SI | R_DI ->
    failwith "global_of_reg: partial register"
  | R_EAX -> EAX
  | R_ECX -> ECX
  | R_EDX -> EDX
  | R_EBX -> EBX
  | R_ESP -> ESP
  | R_EBP -> EBP
  | R_ESI -> ESI
  | R_EDI -> EDI
  | R_CF -> CF
  | R_PF -> PF
  | R_AF -> AF
  | R_ZF -> ZF
  | R_SF -> SF
  | R_IF -> IF
  | R_DF -> DF
  | R_OF -> OF
  | R_ES -> ES
  | R_CS -> CS
  | R_SS -> SS
  | R_DS -> DS
  | R_FS -> FS
  | R_GS -> GS
  | R_S6 -> S6
  | R_S7 -> S7
  | R_ST0 -> ST0
  | R_ST1 -> ST1
  | R_ST2 -> ST2
  | R_ST3 -> ST3
  | R_ST4 -> ST4
  | R_ST5 -> ST5
  | R_ST6 -> ST6
  | R_ST7 -> ST7
  | R_XMM0 -> XMM0
  | R_XMM1 -> XMM1
  | R_XMM2 -> XMM2
  | R_XMM3 -> XMM3
  | R_XMM4 -> XMM4
  | R_XMM5 -> XMM5
  | R_XMM6 -> XMM6
  | R_XMM7 -> XMM7

let alias_table = [|
  LoByte, EAX;
  LoByte, ECX;
  LoByte, EDX;
  LoByte, EBX;
  HiByte, EAX;
  HiByte, ECX;
  HiByte, EDX;
  HiByte, EBX;
  LoWord, EAX;
  LoWord, ECX;
  LoWord, EDX;
  LoWord, EBX;
  LoWord, ESP;
  LoWord, EBP;
  LoWord, ESI;
  LoWord, EDI;
|]

let global_of_reg' r =
  let open Inst in
  match r with
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH
  | R_AX | R_CX | R_DX | R_BX | R_SP | R_BP | R_SI | R_DI ->
    let part, g = alias_table.(int_of_reg r) in
    g, Some part
  | _ ->
    global_of_reg r, None

module type VarType = sig
  type t
  val pp : Format.formatter -> t -> unit
end

type var =
  | Global of global
  | Temp of int

let string_of_var = function
  | Global g -> string_of_global g
  | Temp i -> Printf.sprintf "$%d" i

let pp_var f v = pp_print_string f (string_of_var v)

type templ_var =
  | TV_Global of global
  | TV_Local of int
  | TV_Input of int
  | TV_Output of int
  | TV_PC
  | TV_Nondet of typ

let string_of_templ_var = function
  | TV_Global g -> string_of_global g
  | TV_Local i -> Printf.sprintf "$%d" i
  | TV_Input i -> Printf.sprintf "$input:%d" i
  | TV_Output i -> Printf.sprintf "$output:%d" i
  | TV_PC -> Printf.sprintf "PC"
  | TV_Nondet t -> "?" ^ string_of_typ t

let pp_templ_var f v = pp_print_string f (string_of_templ_var v)

module Var = struct
  type t = var
  let pp = pp_var
end

module TemplVar = struct
  type t = templ_var
  let pp = pp_templ_var
end

let type_of_var tab = function
  | Global g -> type_of_global g
  | Temp i -> tab.(i)

let int_of_var = function
  | Global g -> int_of_global g
  | Temp i -> number_of_globals + i

let var_of_int i =
  if i < number_of_globals then
    Global (global_of_int i)
  else
    Temp (i - number_of_globals)

type _ lit =
  | BitvecLit : Bitvec.t lit
  | BoolLit : bool lit

module Make(V : VarType) = struct

  type var = V.t

  type expr =
    | E_lit : 'a lit * 'a -> expr
    | E_const : string * typ -> expr
    | E_var : var -> expr
    | E_nondet : typ * int -> expr
    | E_prim1 : prim1 * expr -> expr
    | E_prim2 : prim2 * expr * expr -> expr
    | E_prim3 : prim3 * expr * expr * expr -> expr

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

  (* elaborated form of instructions *)
  type stmt =
    | S_set of var * expr
    | S_jump of expr option * expr
    | S_jumpout of expr * bool
    | S_call of expr * (global * expr) list * (global * var) list
    | S_ret of expr * (global * expr) list
    | S_phi of var * (nativeint, expr) Hashtbl.t

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
      | E_lit (BitvecLit, bv) -> Bitvec.pp f bv
      | E_lit (BoolLit, b) -> pp_print_bool f b
      | E_const (name, _) -> pp_print_string f name
      | E_var var -> V.pp f var
      | E_nondet (typ, id) -> fprintf f "nondet(%a)#%d" pp_typ typ id
      | E_prim1 (p, e) ->
        let sym_pp op_s = wrap c 1 (fun f -> fprintf f "%s%a" op_s (pp 1) e) in
        let ident_pp op_s = fprintf f "%s(%a)" op_s (pp low) e in
        begin match p with
          | P1_not | P1_lognot -> sym_pp "~"
          | P1_neg -> sym_pp "-"
          | P1_foldand -> sym_pp "&"
          | P1_foldor -> sym_pp "|"
          | P1_part p -> ident_pp (string_of_reg_part p)
          | P1_extract (lo, hi) ->
            fprintf f "extract(%a, %d, %d)" (pp low) e lo hi
          | P1_extend (sign, size) ->
            fprintf f "%s_extend(%a, %d)" (if sign then "sign" else "zero")
              (pp low) e size
        end
      | E_prim2 (p, e1, e2) ->
        let pp_binary prec sym =
          wrap c prec
            (fun f -> fprintf f "%a %s %a" (pp prec) e1 sym (pp (prec-1)) e2)
        in
        begin match p with
          | P2_concat -> pp_binary 2 "."
          | P2_mul -> pp_binary 3 "*"
          | P2_add -> pp_binary 4 "+"
          | P2_sub -> pp_binary 4 "-"
          | P2_shl -> pp_binary 5 "<<"
          | P2_lshr -> pp_binary 5 ">>u"
          | P2_ashr -> pp_binary 5 ">>s"
          | P2_less -> pp_binary 6 "<s"
          | P2_greater_eq -> pp_binary 6 ">=s"
          | P2_less_eq -> pp_binary 6 "<=s"
          | P2_greater -> pp_binary 6 ">s"
          | P2_below -> pp_binary 6 "<u"
          | P2_above_eq -> pp_binary 6 ">=u"
          | P2_below_eq -> pp_binary 6 "<=u"
          | P2_above -> pp_binary 6 ">u"
          | P2_eq -> pp_binary 7 "=="
          | P2_neq -> pp_binary 7 "!="
          | P2_and | P2_logand -> pp_binary 8 "&"
          | P2_xor | P2_logxor -> pp_binary 9 "^"
          | P2_or  | P2_logor  -> pp_binary 10 "|"
          | P2_updatepart p ->
            fprintf f "Update%s(%a, %a)" (string_of_reg_part p)
              (pp low) e1 (pp low) e2
          | P2_load nbyte -> fprintf f "%a[%a]" (pp 0) e1 (pp low) e2
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
          | P3_store nbyte ->
            fprintf f "%a[%a → %a]" (pp 0) e1 (pp low) e2 (pp low) e3
        end
    in
    pp low f e

  let pp_expr_dest f = function
    | E_lit (BitvecLit, bv) -> fprintf f "%nx" (Bitvec.to_nativeint bv)
    | e -> pp_expr f e

  let pp_stmt f = function
    | S_set (var, e) ->
      fprintf f "%a = %a" V.pp var pp_expr e
    | S_jump (cond_opt, e) ->
      begin match cond_opt with
        | Some cond -> fprintf f "if (%a) " pp_expr cond
        | None -> ()
      end;
      fprintf f "goto %a" pp_expr_dest e
    | S_jumpout (e, _) ->
      fprintf f "jumpout %a" pp_expr_dest e
    | S_call (dst, arglist, retlist) ->
      retlist |> List.iter begin fun (r,v) ->
        fprintf f "%a=%s " V.pp v (string_of_global r)
      end;
      fprintf f "call %a" pp_expr_dest dst;
      let pp_pair f (r, v) =
        fprintf f "%s=%a" (string_of_global r) pp_expr v
      in
      begin match arglist with
        | [] -> ()
        | hd::tl ->
          fprintf f " [%a" pp_pair hd;
          tl |> List.iter (fprintf f " %a" pp_pair);
          fprintf f "]"
      end
    | S_ret (dst, arglist) ->
      fprintf f "return_to %a" pp_expr_dest dst;
      let pp_pair f (r, v) =
        fprintf f "%s=%a" (string_of_global r) pp_expr v
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

  (* let pp_proc f proc =
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
    fprintf f "}@]" *)

end

module Normal = Make(Var)
module Template = Make(TemplVar)

open Normal

let rec type_of_expr tab = function
  | E_lit (BitvecLit, bv) -> T_bitvec (Bitvec.length bv)
  | E_lit (BoolLit, _) -> T_bool
  | E_const (_, typ) -> typ
  | E_var v -> type_of_var tab v
  | E_nondet (typ, _) -> typ
  | E_prim1 (p, e) ->
    begin match p with
      | P1_not | P1_lognot | P1_neg -> type_of_expr tab e
      | P1_foldand | P1_foldor -> T_bitvec 1
      | P1_part LoByte | P1_part HiByte -> T_bitvec 8
      | P1_part LoWord -> T_bitvec 16
      | P1_extract (lo, hi) -> T_bitvec (hi-lo)
      | P1_extend (_, size) -> T_bitvec size
    end
  | E_prim2 (p, e1, e2) ->
    begin match p with
      | P2_concat -> begin
          let T_bitvec w1 = type_of_expr tab e1 in
          let T_bitvec w2 = type_of_expr tab e2 in
          T_bitvec (w1 + w2)
        end [@warning "-8"]
      | P2_mul | P2_add | P2_sub
      | P2_shl | P2_lshr | P2_ashr
      | P2_and | P2_xor | P2_or
      | P2_logand | P2_logxor | P2_logor | P2_updatepart _ ->
        type_of_expr tab e1
      | P2_eq | P2_neq
      | P2_less | P2_greater_eq | P2_less_eq | P2_greater
      | P2_below | P2_above_eq | P2_below_eq | P2_above -> T_bool
      | P2_load nbyte -> T_bitvec (nbyte*8)
    end
  | E_prim3 (p, e1, e2, e3) ->
    begin match p with
      | P3_carry -> T_bool
      | P3_ite -> type_of_expr tab e2
      | P3_store _ -> T_mem
    end

module Transform (V : VarType) (V' : VarType) = struct

  module S = Make(V)
  module S' = Make(V')

  let rec subst f = function
    | S.E_lit (t, v) ->
      S'.E_lit (t, v)
    | S.E_const (name, typ) ->
      S'.E_const (name, typ)
    | S.E_var v -> f v
    | S.E_nondet (typ, id) ->
      S'.E_nondet (typ, id)
    | S.E_prim1 (p, e) ->
      S'.E_prim1 (p, subst f e)
    | S.E_prim2 (p, e1, e2) ->
      S'.E_prim2 (p, subst f e1, subst f e2)
    | S.E_prim3 (p, e1, e2, e3) ->
      S'.E_prim3 (p, subst f e1, subst f e2, subst f e3)

  let rename_var f = subst (fun v -> S'.E_var (f v))

  let map_stmt fv fe = function
    | S.S_set (lhs, rhs) -> S'.S_set (fv lhs, fe rhs)
    | S.S_jump (cond_opt, dest) ->
      let cond_opt' = Option.map fe cond_opt
      and dest' = fe dest in
      S'.S_jump (cond_opt', dest')
    | S.S_jumpout (dest, j) ->
      S'.S_jumpout (fe dest, j)
    | S.S_call (dest, arglist, retlist) ->
      let dest' = fe dest
      and arglist' = arglist |> List.map (fun (r,v) -> r, fe v)
      and retlist' = retlist |> List.map (fun (r,v) -> r, fv v) in
      S'.S_call (dest', arglist', retlist')
    | S.S_ret (dest, arglist) ->
      let dest' = fe dest
      and arglist' = arglist |> List.map (fun (r,v) -> r, fe v) in
      S'.S_ret (dest', arglist')
    | S.S_phi (lhs, rhs) ->
      S'.S_phi (fv lhs, Hashtbl.map (fun _ e -> fe e) rhs)

end

type proc = {
  name : string; (* for pretty printing *)
  body : Template.stmt list;
  arg_types : typ list;
  ret_types : typ list;
  local_types : typ list;
}
