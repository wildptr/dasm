open Core
open Semant

(* dynamic environment *)
type env = {
  env_globals : Bitvec.t array;
  env_locals : Bitvec.t list;
  env_mload : int (* size *) -> int (* address *) -> string (* byte string *);
  env_mstore : int -> int -> unit;
}

let init_env =
  (* TODO: replace this with a reasonable memory model *)
  let env_mload = fun _ _ -> "" in
  let env_mstore = fun _ _ -> () in
  { env_globals = Array.create ~len:8 (Bitvec.zero 32);
    env_locals = [];
    env_mload;
    env_mstore }

let get_local env i =
  List.nth_exn env.env_locals i

let get_global env r =
  env.env_globals.(index_of_reg r)

let set_global env r value =
  env.env_globals.(index_of_reg r) <- value

let extend_env value env =
  { env with env_locals = value :: env.env_locals }

let rec eval env = function
  | E_literal bv -> bv
  | E_local i -> get_local env i
  | E_global r -> get_global env r
  | E_part (e, range) ->
      Bitvec.part range (eval env e)
  | E_prim p -> eval_prim env p
  | E_let (value, body) ->
      eval (extend_env (eval env value) env) body
  | E_set (reg, value) ->
      set_global env reg (eval env value);
      Bitvec.zero 0
  | E_seq (e1, e2) ->
      assert (eval env e1 = Bitvec.zero 0);
      eval env e2

and eval_prim env prim =
  let ev = eval env in
  let reduce f es =
    match es with
    | e :: es' -> List.fold ~init:(ev e) ~f:(fun acc e' -> f acc (ev e')) es'
    | _ -> assert false
  in
  match prim with
  | P_not e -> Bitvec.notv (ev e)
  | P_concat es -> Bitvec.concat (List.map ~f:(ev) es)
  | P_add es -> reduce Bitvec.add es
  | P_sub (e1, e2) -> Bitvec.sub (ev e1) (ev e2)
  | P_eq (e1, e2) -> Bitvec.of_bool ((ev e1) = (ev e2))
  | P_and es -> reduce Bitvec.andv es
  | P_xor es -> reduce Bitvec.xorv es
  | P_or  es -> reduce Bitvec.orv  es
  | P_load (size, e_addr) ->
      Bitvec.of_bytestring (env.env_mload size (Bitvec.to_int (ev e_addr)))
  | P_store (size, e_addr) ->
      env.env_mstore size (Bitvec.to_int (ev e_addr));
      Bitvec.zero 0
  | P_shiftleft (e1, e2) ->
      let e1_val = eval env e1 in
      let e2_val = eval env e2 in
      Bitvec.concat [e1_val; Bitvec.zero (Bitvec.to_int e2_val)]
  | P_add_ex (e1, e2, e_carry) ->
      let e1_val = eval env e1 in
      let e2_val = eval env e2 in
      let e_carry_val = eval env e_carry in
      Bitvec.add_c e1_val e2_val (Bitvec.to_bool e_carry_val)
