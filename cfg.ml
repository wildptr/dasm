type 'a basic_block = {
  start : int;
  stop : int;
  mutable stmts : 'a list;
}

type edge_attr = Edge_neutral | Edge_true | Edge_false
type edge = int * int * edge_attr

type 'a cfg = {
  node : 'a basic_block array;
  succ : int list array;
  pred : int list array;
  edges : edge list;
}

type 'a stmt =
  | Virtual
  | BB of 'a basic_block * int
  | Seq of 'a stmt * 'a stmt
  | Generic of int list * 'a stmt array * edge list
  | If of 'a stmt * bool * 'a stmt * bool
  | If_else of 'a stmt * bool * 'a stmt * 'a stmt
  | Fork1 of 'a stmt * bool * 'a stmt * bool
  | Fork2 of 'a stmt * bool * 'a stmt * bool * 'a stmt * bool
  | Do_while of 'a stmt * bool
  | While_true of 'a stmt

let rec map_stmt f = function
  | Virtual -> Virtual
  | BB (b, nexit) -> BB (f b, nexit)
  | Seq (v1, v2) -> Seq (map_stmt f v1, map_stmt f v2)
  | Generic (exits, node, edges) ->
    Generic (exits, Array.map (map_stmt f) node, edges)
  | If (v1, t, v2, has_exit) ->
    If (map_stmt f v1, t, map_stmt f v2, has_exit)
  | If_else (v1, t, v2, v3) ->
    If_else (map_stmt f v1, t, map_stmt f v2, map_stmt f v3)
  | Do_while (v, t) -> Do_while (map_stmt f v, t)
  | _ -> failwith "not implemented"
