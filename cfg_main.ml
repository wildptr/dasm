open Control_flow
open Inst

let write_cfg cfg =
  let open Format in
  print_string "digraph {\n";
  print_string "  node [shape=box fontname=Monospace]\n";
  (*let insts = ref [] in
  let insts = List.rev !insts in*)
  cfg.node |> Array.iteri (fun i bb ->
      printf "  loc_%x [label=\"" bb.start;
      printf "[%d] %x \\l" i bb.start;
      List.iter (fun stmt -> printf "%a\\l" Semant.pp_stmt stmt) bb.stmts;
      print_string "\"];\n";
      cfg.succ.(i) |> List.iter (fun succ ->
          printf "  loc_%x -> loc_%x;\n" bb.start cfg.node.(succ).start));
  print_string "}\n"

let () =
  Printexc.record_backtrace true;
  let init_pc = int_of_string Sys.argv.(1) in
  let in_path = Sys.argv.(2) in
  let init_offset = int_of_string Sys.argv.(3) in
  Elaborate.load_spec "spec";
  let in_chan = open_in in_path in
  let in_chan_len = in_channel_length in_chan in
  let code = really_input_string in_chan in_chan_len in
  close_in in_chan;
  let cfg = build_cfg code init_pc init_offset in
  Ssa.convert_to_ssa cfg;
  let rec loop () =
    let c1 = Dataflow.auto_subst cfg in
    let c2 = Dataflow.remove_dead_code cfg in
    if c1 || c2 then loop ()
  in
  loop ();
  write_cfg cfg
