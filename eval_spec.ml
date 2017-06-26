open Core
open Eval

let report_error filename lexbuf msg =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let col = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.fprintf stderr "%s:%d:%d: %s\n" filename line col msg

let main () =
  let filepath = "<stdin>" in
  let lexbuf = Lexing.from_channel In_channel.stdin in
  try
    let expr = Spec_parser.expr_top Spec_lexer.read lexbuf in
    let bv = eval init_env (Translate.translate_expr Translate.init_env expr) in
    print_endline (Bitvec.to_string bv)
  with
  | Spec_parser.Error ->
      report_error filepath lexbuf "syntax error";
      exit 1
  | Spec_lexer.Error msg ->
      report_error filepath lexbuf msg;
      exit 1

let () = main ()
