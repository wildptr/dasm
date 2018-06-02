open Batteries

let rec command_loop () =
  print_string "> ";
  flush stdout;
  let cmd =
    try input_line stdin
    with End_of_file -> exit 0
  in
  Printf.printf "command: %s\n" cmd;
  command_loop ()

let () =
  Printexc.record_backtrace true;
  if Array.length Sys.argv <= 1 then begin
    Printf.eprintf "incorrect usage\n";
    exit 1
  end;
  let in_path = Sys.argv.(1) in

  Elaborate.load_spec "spec";
  let pe = Pe.load in_path in
  let code = pe.Pe.code in
  let entry_point = pe.Pe.entry_point in
  let init_pc = Nativeint.(entry_point + 0x400000n) (* FIXME *) in
  let db = Database.create code in

  Analyze.scan db init_pc;

  command_loop ()
