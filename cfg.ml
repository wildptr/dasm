open Batteries

type conclusion = NoJump | Jump | Branch

type 'a basic_block = {
  start : nativeint;
  stop : nativeint;
  mutable stmts : 'a list;
  conclusion : conclusion;
}

type edge_attr = Edge_neutral | Edge_true | Edge_false
type edge = int * int * edge_attr

type 'a cfg = {
  node : 'a basic_block array;
  succ : int list array;
  pred : int list array;
  edges : edge list;
  exits : Set.Int.t;
  n_var : int;
}

let print_cfg pp_stmt cfg =
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    let open Format in
    printf "%d -> [" i;
    cfg.succ.(i) |> List.iter (printf " %d");
    printf " ]\n";
    cfg.node.(i).stmts |> List.iter (printf "%a@." pp_stmt)
  done

type 'a ctlstruct =
  | Virtual
  | BB of 'a basic_block * int
  | Seq of 'a ctlstruct * 'a ctlstruct
  | Generic of int list * 'a ctlstruct array * edge list
  | If of 'a ctlstruct * bool * 'a ctlstruct * bool
  | If_else of 'a ctlstruct * bool * 'a ctlstruct * 'a ctlstruct
  | Fork1 of 'a ctlstruct * bool * 'a ctlstruct * bool
  | Fork2 of 'a ctlstruct * bool * 'a ctlstruct * bool * 'a ctlstruct * bool
  | Do_while of 'a ctlstruct * bool
  | While_true of 'a ctlstruct

let rec map_ctlstruct f = function
  | Virtual -> Virtual
  | BB (b, nexit) -> BB (f b, nexit)
  | Seq (v1, v2) -> Seq (map_ctlstruct f v1, map_ctlstruct f v2)
  | Generic (exits, node, edges) ->
    Generic (exits, Array.map (map_ctlstruct f) node, edges)
  | If (v1, t, v2, has_exit) ->
    If (map_ctlstruct f v1, t, map_ctlstruct f v2, has_exit)
  | If_else (v1, t, v2, v3) ->
    If_else (map_ctlstruct f v1, t, map_ctlstruct f v2, map_ctlstruct f v3)
  | Do_while (v, t) -> Do_while (map_ctlstruct f v, t)
  | _ -> failwith "not implemented"

let rec start_of_ctlstruct = function
  | Virtual -> failwith "start_of_ctlstruct: virtual node"
  | BB (b, _) -> b.start
  | Seq (v1, _) -> start_of_ctlstruct v1
  | Generic (_, node, _) -> start_of_ctlstruct node.(0)
  | If (v1, _, _, _) -> start_of_ctlstruct v1
  | If_else (v1, _, _, _) -> start_of_ctlstruct v1
  | Do_while (v, _) -> start_of_ctlstruct v
  | While_true v -> start_of_ctlstruct v
  | Fork1 _ -> failwith "start_of_ctlstruct: Fork1 not implemented"
  | Fork2 _ -> failwith "start_of_ctlstruct: Fork2 not implemented"

let rec remove_final_jump = function
  | Virtual -> ()
  | BB (b, _) ->
    if b.conclusion = Jump then
      b.stmts <- b.stmts |> List.rev |> List.tl |> List.rev
  | Seq (_, v2) -> remove_final_jump v2
  | Generic _ -> () (* TODO *)
  | If (_, _, v2, has_exit) ->
    if has_exit then remove_final_jump v2
  | If_else (_, _, v2, v3) ->
    remove_final_jump v2;
    remove_final_jump v3;
  | Do_while _ -> ()
  | _ -> ()
