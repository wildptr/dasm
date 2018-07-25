open Batteries
open Cfg

let write_dot fmtr cfg =
  let idom = Control_flow.domtree_of_cfg cfg in
  let rec dominates i j =
    if i=j then true
    else if j=0 then false
    else dominates i idom.(j)
  in
  let strictly_dominates i j = i <> j && dominates i j in
  let open Format in
  pp_print_string fmtr "digraph {\n";
  pp_print_string fmtr "  node [shape=box];\n";
  let n = basic_block_count cfg in
  let bb_name bb = Printf.sprintf "\"%nx\"" bb.start in
  let node_name i = bb_name cfg.node.(i) in
  for i=0 to n-1 do
    if cfg.succ.(i) = [] then
      fprintf fmtr "  %s [style=filled; fillcolor=gray];\n" (node_name i);
    cfg.succ.(i) |> List.iter begin fun j ->
      if strictly_dominates j i then
        fprintf fmtr "  %s -> %s [dir=back penwidth=2.0];\n"
          (node_name j) (node_name i)
      else
        fprintf fmtr "  %s -> %s;\n" (node_name i) (node_name j)
    end;
    let p = idom.(i) in
    if p>=0 then
      fprintf fmtr "  %s -> %s [style=dotted];\n" (node_name p) (node_name i)
  done;
  let cs = Fold_cfg.fold_cfg cfg in
  let inc_ind ind = ind ^ "  " in
  let fresh_cluster_name =
    let next = ref 0 in
    begin fun () ->
      let name = Printf.sprintf "cluster%d" !next in
      incr next;
      name
    end
  in
  let print_subgraph_attr f ind =
    fprintf f "%scolor = gray; fontcolor = gray;\n" ind
  in
  let rec group seq ind = function
    | BB (bb, _) -> fprintf fmtr "%s%s;\n" ind (bb_name bb)
    | Seq (a, b) ->
      if seq then begin
        group true ind a; group true ind b
      end else begin
        let ind' = inc_ind ind in
        fprintf fmtr "%ssubgraph %s {\n" ind (fresh_cluster_name ());
        print_subgraph_attr fmtr ind';
        fprintf fmtr "%slabel = \"seq\";\n" ind';
        group true ind' a; group true ind' b;
        fprintf fmtr "%s}\n" ind
      end
    | If (a, _, b, _) ->
      let ind' = inc_ind ind in
      fprintf fmtr "%ssubgraph %s {\n" ind (fresh_cluster_name ());
      print_subgraph_attr fmtr ind';
      fprintf fmtr "%slabel = \"if\";\n" ind';
      group false ind' a; group false ind' b;
      fprintf fmtr "%s}\n" ind
    | IfElse (a, _, b, c, _) ->
      let ind' = inc_ind ind in
      fprintf fmtr "%ssubgraph %s {\n" ind (fresh_cluster_name ());
      print_subgraph_attr fmtr ind';
      fprintf fmtr "%slabel = \"if-else\";\n" ind';
      group false ind' a; group false ind' b; group false ind' c;
      fprintf fmtr "%s}\n" ind
    | DoWhile (a, _, _) ->
      let ind' = inc_ind ind in
      fprintf fmtr "%ssubgraph %s {\n" ind (fresh_cluster_name ());
      print_subgraph_attr fmtr ind';
      fprintf fmtr "%slabel = \"do-while\";\n" ind';
      group false ind' a;
      fprintf fmtr "%s}\n" ind
    | Generic cs ->
      let ind' = inc_ind ind in
      fprintf fmtr "%ssubgraph %s {\n" ind (fresh_cluster_name ());
      print_subgraph_attr fmtr ind';
      fprintf fmtr "%slabel = \"generic\";\n" ind';
      cs |> Array.iter (group false ind');
      fprintf fmtr "%s}\n" ind
  in
  group false "  " cs;
  fprintf fmtr "}@."
