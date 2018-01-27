type basic_block = {
  start : int;
  stop : int;
  mutable stmts : Semant.stmt list;
}

type cfg = {
  node : basic_block array;
  succ : int list array;
  pred : int list array;
}
