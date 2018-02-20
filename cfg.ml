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

type 'a node =
  | Virtual
  | BB of 'a basic_block * int
  | Seq of 'a node * 'a node
  | Generic of int list * 'a node array * edge list
  | If of 'a node * bool * 'a node * bool
  | If_else of 'a node * bool * 'a node * 'a node
  | Fork1 of 'a node * bool * 'a node * bool
  | Fork2 of 'a node * bool * 'a node * bool * 'a node * bool
  | Do_while of 'a node * bool
  | While_true of 'a node
