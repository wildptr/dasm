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
