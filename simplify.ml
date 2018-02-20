open Batteries
open Env
open Semant

let rec simplify env = function
  | E_lit _ as e -> e
  | E_var _ as e -> e
  | E_part (e, lo, hi) ->
    let e' = simplify env e in
    begin match e' with
      | E_lit b -> E_lit (Bitvec.part (lo, hi) b)
      | E_part (e1, lo1, hi1) -> E_part (e1, lo1+lo, lo1+hi)
      | _ -> E_part (e', lo, hi)
    end
  | E_prim1 (p, e) ->
    let e' = simplify env e in
    begin match e' with
      | E_lit b ->
        begin match p with
          | P1_not -> E_lit (Bitvec.notv b)
          | _ -> E_prim1 (p, e') (* TODO *)
        end
      | E_prim1 (p1, e1) ->
        if p = P1_not && p1 = P1_not then e1 else E_prim1 (p, e')
      | _ -> E_prim1 (p, e')
    end
  | E_prim2 (p, e1, e2) ->
    let e1' = simplify env e1 in
    let e2' = simplify env e2 in
    begin match e1', e2' with
      | E_lit b1, E_lit b2 ->
        begin match p with
          | P2_sub -> E_lit (Bitvec.sub b1 b2)
          | P2_eq -> E_lit (Bitvec.of_bool (Bitvec.equal b1 b2))
          | _ -> E_prim2 (p, e1', e2') (* TODO *)
        end
      | _, E_lit b ->
        if p = P2_sub then
          E_primn (Pn_add, [e1'; E_lit (Bitvec.neg b)]) |> simplify env
        else E_prim2 (p, e1', e2')
      | _ -> E_prim2 (p, e1', e2')
    end
  | E_prim3 (p, e1, e2, e3) ->
    let e1' = simplify env e1 in
    let e2' = simplify env e2 in
    let e3' = simplify env e3 in
    E_prim3 (p, e1', e2', e3')
  | E_primn (p, es) ->
    let es' = List.map (simplify env) es in
    let rec flatten es =
      es |> List.map begin fun e ->
        match e with
        | E_primn (p1, es1) -> if p1 = p then flatten es1 else [e]
        | _ -> [e]
      end |> List.concat
    in
    let es'flat = flatten es' in
    let es'const =
      begin match p with
        | Pn_add | Pn_and | Pn_xor | Pn_or ->
          let consts =
            es'flat |> List.filter_map (function E_lit b -> Some b | _ -> None)
          in
          let nonconsts =
            es'flat |> List.filter (function E_lit _ -> false | _ -> true)
          in
          begin match consts with
            | [] -> es'flat
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
              if Bitvec.to_int const = 0 then
                match p with
                | Pn_add | Pn_xor | Pn_or -> nonconsts
                | Pn_and -> [E_lit const]
                | _ -> assert false
              else nonconsts @ [E_lit const]
          end
        | _ -> es'flat
      end
    in
    let rec simpl es =
      match es with
      | e1 :: e2 :: rest when e1 = e2 && (p = Pn_and || p = Pn_or) ->
        e2 :: simpl rest
      | e1 :: e2 :: rest when e1 = e2 && p = Pn_xor ->
        E_lit (Bitvec.zero (size_of_expr env e1)) :: simpl rest
      | e :: rest -> e :: simpl rest
      | [] -> []
    in
    let es'simpl = simpl es'const in
    begin match es'simpl with
      | [e] -> e
      | _ -> E_primn (p, es'simpl)
    end
  | E_load (size, addr) ->
    let addr' = simplify env addr in
    E_load (size, addr')
  | E_nondet _ as e -> e
  | E_repeat (e, n) ->
    let e' = simplify env e in
    E_repeat (e', n)
  | E_extend (sign, e, n) ->
    let e' = simplify env e in
    E_extend (sign, e', n)

let simplify_cfg env cfg =
  let n = Array.length cfg.Cfg.node in
  let changed = ref false in
  for i=0 to n-1 do
    cfg.node.(i).stmts <-
      cfg.node.(i).stmts |> List.map begin fun stmt ->
        let stmt' = map_stmt (simplify env) stmt in
        if stmt' <> stmt then changed := true;
        stmt'
      end
  done;
  !changed
