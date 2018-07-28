open Batteries

type 'a basic_block = {
  start : nativeint;
  stop : nativeint;
  mutable stmts : 'a list;
  has_final_jump : bool;
}

type edge_attr = Edge_neutral | Edge_true | Edge_false
type edge = int * int * edge_attr

type 'a cfg = {
  node : 'a basic_block array;
  succ : int list array;
  pred : int list array;
  idom : int array;
  edges : edge list;
  exits : Set.Int.t;
  temp_tab : Semant.typ array;
}

let basic_block_count cfg = Array.length cfg.node

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
  | BB of 'a basic_block * nativeint option
  | Seq of 'a ctlstruct * 'a ctlstruct
  | If of 'a ctlstruct * bool * 'a ctlstruct * nativeint
  | IfElse of 'a ctlstruct * bool * 'a ctlstruct * 'a ctlstruct * nativeint
  | DoWhile of 'a ctlstruct * bool * nativeint
  | Generic of 'a ctlstruct array

let rec start_of_ctlstruct = function
  | BB (bb, _) -> bb.start
  | Seq (a, _) -> start_of_ctlstruct a
  | If (a, _, _, _) -> start_of_ctlstruct a
  | IfElse (a, _, _, _, _) -> start_of_ctlstruct a
  | DoWhile (a, _, _) -> start_of_ctlstruct a
  | Generic l -> start_of_ctlstruct l.(0)

let rec dominates cfg i j =
  if i=j then true
  else if j=0 then false
  else dominates cfg i cfg.idom.(j)

let iter_stmt f cfg =
  for i = 0 to basic_block_count cfg - 1 do
    List.iter f cfg.node.(i).stmts
  done

let var_count cfg =
  Semant.number_of_globals + Array.length cfg.temp_tab
