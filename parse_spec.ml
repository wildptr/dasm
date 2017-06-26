let main () =
  let lexbuf = Lexing.from_channel stdin in
  let top = Spec_parser.top Spec_lexer.read lexbuf in
  ()

let () = main ()
