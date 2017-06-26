{
open Lexing
open Spec_parser
open Batteries

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = lexbuf.lex_curr_pos;
      pos_lnum = pos.pos_lnum + 1 }

module String_Map = Map.Make (String)

let keyword_map : token String_Map.t =
  [
    "let", K_let;
    "proc", K_proc;
    "return", K_return;
  ]
  |> List.fold (fun acc (k, v) -> String_Map.add k v acc) String_Map.empty

let make_bitvec : string -> bool list =
  String.map (fun c -> c = '1')

}

let int = ('0' | ['1'-'9'] ['0'-'9']*)
let white = [' ' '\t']+
let newline = '\n'
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
let comment = "//" [^'\n']* '\n'
let bitvec = '\'' ['0' '1']* '\''

rule read = parse
  | white { read lexbuf }
  | comment { next_line lexbuf; read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | int { Int (int_of_string (Lexing.lexeme lexbuf)) }
  | bitvec { Bitvec (make_bitvec (Lexing.lexeme lexbuf)) }
  | id
    { let s = Lexing.lexeme lexbuf in
      try String_Map.find keyword_map s
      with Not_found -> Ident s }
  | "==" { EqEq }
  | '(' { LParen }
  | ')' { RParen }
  | ',' { Comma }
  | ':' { Colon }
  | ';' { Semi }
  | '=' { Eq }
  | '[' { LBrack }
  | ']' { RBrack }
  | '{' { LBrace }
  | '}' { RBrace }
  | eof { EOF }
  | _ { raise (SyntaxError ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }
