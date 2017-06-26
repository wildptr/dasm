open Core
open Semant

(* dynamic environment *)
type env = {
  env_globals : Bitvec.t array;
  env_locals : Bitvec.t list;
}

let init_env =
  { env_globals = Array.create ~len:8 (Bitvec.zero 32);
    env_locals = [] }

let get_local env i =
  List.nth_exn env.env_locals i

let index_of_reg =
  function
  | R_AX -> 0
  | R_CX -> 1
  | R_DX -> 2
  | R_BX -> 3
  | R_SP -> 4
  | R_BP -> 5
  | R_SI -> 6
  | R_DI -> 7

let get_global env r =
  env.env_globals.(index_of_reg r)

let extend_env value env =
  { env with env_locals = value :: env.env_locals }

let eval_prim prim args =
  match prim with
  | P_not ->
      begin match args with
      | arg :: [] -> Bitvec.notv arg
      | _ -> assert false
      end
  | P_concat -> Bitvec.concat args
  | P_add ->
      begin match args with
      | arg :: args' ->
          List.fold ~init:arg ~f:(fun acc arg -> Bitvec.add acc arg) args'
      | _ -> assert false
      end
  | P_sub ->
      begin match args with
      | a1 :: a2 :: [] -> Bitvec.sub a1 a2
      | _ -> assert false
      end
  | P_eq ->
      begin match args with
      | a1 :: a2 :: [] -> Bitvec.of_bool (a1 = a2)
      | _ -> assert false
      end
  | P_and ->
      begin match args with
      | arg :: args' ->
          List.fold ~init:arg ~f:(fun acc arg -> Bitvec.andv acc arg) args'
      | _ -> assert false
      end
  | P_xor ->
      begin match args with
      | arg :: args' ->
          List.fold ~init:arg ~f:(fun acc arg -> Bitvec.xorv acc arg) args'
      | _ -> assert false
      end
  | P_or ->
      begin match args with
      | arg :: args' ->
          List.fold ~init:arg ~f:(fun acc arg -> Bitvec.orv acc arg) args'
      | _ -> assert false
      end

let rec eval env = function
  | E_literal bv -> bv
  | E_local i -> get_local env i
  | E_global r -> get_global env r
  | E_part (e, range) ->
      Bitvec.part range (eval env e)
  | E_prim (p, args) ->
      let args' = List.map ~f:(eval env) args in
      eval_prim p args'
  | E_let (value, body) ->
      eval (extend_env (eval env value) env) body
