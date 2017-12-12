let fail_with_parsing_error filename lexbuf msg =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.fprintf stderr "%s:%d:%d: %s\n" filename line col msg;
  exit 1

let main () =
  let filepath = "<stdin>" in
  let lexbuf = Lexing.from_channel stdin in
  let ast =
    try
      Spec_parser.top Spec_lexer.read lexbuf
    with Spec_parser.Error ->
      fail_with_parsing_error filepath lexbuf "syntax error"
      | Spec_lexer.Error msg ->
          fail_with_parsing_error filepath lexbuf msg
  in
  let ast_s = Spec_ast.string_of_ast ast in
  print_endline ast_s;
  let lexbuf' = Lexing.from_string ast_s in
  let ast' = Spec_parser.top Spec_lexer.read lexbuf' in
  if ast = ast'
  then begin
    print_endline "PASS";
    let symtab = Translate.translate_ast ast in
    Format.printf "%a@." Translate.pp_symtab symtab
  end else begin
    print_endline "FAIL";
    let ast_s' = Spec_ast.string_of_ast ast' in
    print_endline ast_s;
    print_endline ast_s'
  end

let () = main ()
