open Batteries

exception SyntaxError

let parse_cmd s =
  let n = String.length s in
  let p = ref 0 in
  let words = ref [] in
  let isws = function
    | ' ' | '\t' -> true
    | _ -> false
  in
  let rec skipws () =
    if !p < n then
      let c = s.[!p] in
      if isws c then (incr p; skipws ())
  in
  let read_word () =
    let start = !p in
    let rec loop () =
      if !p < n then
        let c = s.[!p] in
        if not (isws c) then (incr p; loop ())
    in
    loop ();
    words := (String.sub s start (!p-start)) :: !words
  in
  let rec loop () =
    skipws ();
    if !p < n then read_word ();
    if !p < n then loop ()
  in
  loop ();
  List.rev !words

let parse_hex s =
  Nativeint.of_string ("0x"^s)

let db = Database.create ()

let cmd_analyze args =
  let va = List.hd args |> parse_hex in
  let proc = Build_cfg.build_cfg db va in
  Database.set_proc db va proc

let cmd_scan args =
  let va = List.hd args |> parse_hex in
  Analyze.scan db va

let cmd_pcode args =
  let va = List.hd args |> parse_hex in
  let proc = Database.get_proc db va in
  let stmts = proc.Database.il in
  print_string Semant.Plain.(string_of_pcode stmts)

let cmd_ssa args =
  let va = List.hd args |> parse_hex in
  let proc = Database.get_proc db va in
  let cfg = proc.Database.stmt_cfg in
  let temp_tab = proc.Database.temp_tab in
  let cfg' = Dataflow.convert_to_ssa temp_tab cfg in
  let changed = ref false in
  let rec loop () =
    if Dataflow.auto_subst cfg' then changed := true;
    if Simplify.SSA.simplify_cfg cfg' then changed := true;
    if Dataflow.remove_dead_code_ssa cfg' then changed := true;
    if !changed then begin
      changed := false;
      loop ()
    end
  in
  loop ();
  let cs = Fold_cfg.fold_cfg ~debug:false cfg' in
  let il = Pseudocode.SSA.(convert cs |> remove_unused_labels) in
  print_string Semant.SSA.(string_of_pcode il);
  print_endline (String.make 80 '=');
  let final_cfg = Dataflow.convert_from_ssa cfg' in
  let final_cs = Fold_cfg.fold_cfg ~debug:false final_cfg in
  let final_il = Pseudocode.Plain.(convert final_cs |> remove_unused_labels) in
  print_string Semant.Plain.(string_of_pcode final_il)

let cmd_inst args =
  let va = List.hd args |> parse_hex in
  let inst = Database.get_inst db va in
  let bytes = inst.Inst.bytes in
  let n = String.length bytes in
  for i=0 to n-1 do
    Printf.printf "%02x" (int_of_char bytes.[i])
  done;
  print_string "  ";
  Inst.to_string inst |> print_endline

let cmd_load args =
  let path = List.hd args in
  Database.load_image db path

let unknown_cmd _ =
  print_endline "unknown command"

let cmd_table = [
  "analyze", cmd_analyze;
  "inst", cmd_inst;
  "load", cmd_load;
  "pcode", cmd_pcode;
  "ssa", cmd_ssa;
  "scan", cmd_scan;
] |> List.fold_left (fun m (k, v) -> Map.String.add k v m) Map.String.empty

let () =
  Printexc.record_backtrace true;
  Elaborate.load_spec "spec";
  let interactive = Unix.(isatty stdout) in
  let rec loop () =
    if interactive then begin
      print_string "> ";
      flush stdout;
    end;
    let cmd =
      try input_line stdin
      with End_of_file ->
        if interactive then print_endline "exit";
        exit 0
    in
    begin
      try
        let words = parse_cmd cmd in
        match words with
        | [] -> ()
        | cmd::args ->
          let handler =
            try Map.String.find cmd cmd_table
            with Not_found -> unknown_cmd
          in
          begin
            try handler args
            with e ->
              Printf.printf "internal error: %s\n" (Printexc.to_string e);
              Printexc.print_backtrace stdout
          end
      with SyntaxError -> print_endline "syntax error"
    end;
    loop ()
  in
  loop ()
