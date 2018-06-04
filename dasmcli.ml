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
  let buf = Buffer.create 0 in
  let open Format in
  let fmtr = formatter_of_buffer buf in
  let open Semant in
  let rec print_stmt indent stmt =
    match stmt with
    | S_if (cond, body) ->
      fprintf fmtr "%sif (%a) {@." indent pp_expr cond;
      body |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s}@." indent
    | S_if_else (cond, body_t, body_f) ->
      fprintf fmtr "%sif (%a) {@." indent pp_expr cond;
      body_t |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s} else {@." indent;
      body_f |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s}@." indent
    | S_do_while (body, cond) ->
      fprintf fmtr "%sdo {@." indent;
      body |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s} while (%a)@." indent pp_expr cond
    | _ -> fprintf fmtr "%s%a@." indent pp_stmt stmt
  in
  stmts |> List.iter (print_stmt "");
  let text = Buffer.contents buf in
  print_string text

let cmd_load args =
  let path = List.hd args in
  Database.load_image db path

let unknown_cmd _ =
  print_endline "unknown command"

module StringMap = Map.Make(String)

let cmd_table = [
  "analyze", cmd_analyze;
  "load", cmd_load;
  "pcode", cmd_pcode;
  "scan", cmd_scan;
] |> List.fold_left (fun m (k, v) -> StringMap.add k v m) StringMap.empty

let () =
  Printexc.record_backtrace true;
  Elaborate.load_spec "spec";
  let rec loop () =
    print_string "> ";
    flush stdout;
    let cmd =
      try input_line stdin
      with End_of_file -> exit 0
    in
    begin
      try
        let words = parse_cmd cmd in
        match words with
        | [] -> ()
        | cmd::args ->
          let handler =
            try StringMap.find cmd cmd_table
            with Not_found -> unknown_cmd
          in
          begin
            try handler args
            with e -> Printexc.to_string e |> print_endline
          end
      with SyntaxError -> print_endline "syntax error"
    end;
    loop ()
  in
  loop ()
