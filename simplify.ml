open Batteries
open Semant

module Make(V : VarType) = struct

  module Sem = Make(V)
  open Sem

  let rec simplify = function
    | E_lit _ as e -> e
    | E_const _ as e -> e
    | E_var _ as e -> e
    | E_prim1 (p, e) ->
      let (ep', _ as e') = simplify' e in
      begin match ep' with
        | E_lit b ->
          begin match p with
            | P1_not -> E_lit (Bitvec.notv b)
            | _ -> E_prim1 (p, e') (* TODO *)
          end
        | E_prim1 (p1, (ep1,_)) ->
          if p = P1_not && p1 = P1_not then ep1 else E_prim1 (p, e')
        | _ -> E_prim1 (p, e')
      end
    | E_prim2 (p, e1, e2) ->
      let (ep1', _ as e1') = simplify' e1 in
      let (ep2', _ as e2') = simplify' e2 in
      begin match ep1', ep2' with
        | E_lit b1, E_lit b2 ->
          begin match p with
            | P2_sub -> E_lit (Bitvec.sub b1 b2)
            | P2_eq -> E_lit (Bitvec.of_bool (Bitvec.equal b1 b2))
            | _ -> E_prim2 (p, e1', e2') (* TODO *)
          end
        | _, E_lit b ->
          if p = P2_sub then
            E_primn (Pn_add, [e1'; expr_of_bitvec (Bitvec.neg b)]) |> simplify
          else E_prim2 (p, e1', e2')
        | _ -> E_prim2 (p, e1', e2')
      end
    | E_prim3 (p, e1, e2, e3) ->
      let e1' = simplify' e1 in
      let e2' = simplify' e2 in
      let e3' = simplify' e3 in
      E_prim3 (p, e1', e2', e3')
    | E_primn (p, es) ->
      let rec flatten es =
        es |> List.map begin fun (ep, _ as e) ->
          match ep with
          | E_primn (p1, es1) when p1 = p -> flatten es1
          | _ -> [e]
        end |> List.concat
      in
      let fold_const es =
        match p with
        | Pn_add | Pn_and | Pn_xor | Pn_or ->
          let consts =
            es |> List.filter_map (function (E_lit b, _) -> Some b | _ -> None)
          in
          begin match consts with
            | [] -> es
            | hd::tl ->
              let const =
                let op =
                  match p with
                  | Pn_add -> Bitvec.add
                  | Pn_and -> Bitvec.andv
                  | Pn_xor -> Bitvec.xorv
                  | Pn_or  -> Bitvec.orv
                  | _ -> assert false
                in
                List.reduce op consts
              in
              let nonconsts =
                es |> List.filter (function (E_lit _, _) -> false | _ -> true)
              in
              if Bitvec.to_nativeint const = 0n then
                match p with
                | Pn_add | Pn_xor | Pn_or -> nonconsts
                | Pn_and -> [expr_of_bitvec const]
                | _ -> assert false
              else nonconsts @ [expr_of_bitvec const]
          end
        | _ -> es
      in
      let rec simpl es =
        match es with
        | e1 :: e2 :: rest when e1 = e2 && (p = Pn_and || p = Pn_or) ->
          e2 :: simpl rest
        | e1 :: e2 :: rest when e1 = e2 && p = Pn_xor ->
          expr_of_bitvec (Bitvec.zero (snd e1)) :: simpl rest
        | e :: rest -> e :: simpl rest
        | [] -> []
      in
      let es' = es |> List.map simplify' |> flatten |> fold_const |> simpl in
      begin match es' with
        | [e] -> fst e
        | _ -> E_primn (p, es')
      end
    | E_load (size, off) ->
      let off' = simplify' off in
      E_load (size, off')
    | E_nondet _ as e -> e
    | E_extend (sign, e, n) ->
      let e' = simplify' e in
      begin match fst e' with
        | E_lit bv ->
          E_lit ((if sign then Bitvec.sign_extend else Bitvec.zero_extend) n bv)
        | _ -> E_extend (sign, e', n)
      end
    | E_shrink (e, n) ->
      let e' = simplify' e in
      begin match fst e' with
        | E_lit bv ->
          E_lit (Bitvec.truncate n bv)
        | _ -> E_shrink (e', n)
      end

  and simplify' (ep, w) = simplify ep, w

  let simplify_cfg cfg =
    let n = Array.length cfg.Cfg.node in
    let changed = ref false in
    for i=0 to n-1 do
      cfg.Cfg.node.(i).Cfg.stmts <-
        cfg.Cfg.node.(i).Cfg.stmts |> List.map begin fun stmt ->
          let stmt' = map_stmt simplify' stmt in
          if stmt' <> stmt then changed := true;
          stmt'
        end
    done;
    !changed

end

module Plain = Make(Var)
module SSA = Make(SSAVar)
