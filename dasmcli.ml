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

let unknown_cmd _ =
  print_endline "unknown command"

let cmd_table = [
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
