{
open Core
open Lexing
open Spec_parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = lexbuf.lex_curr_pos;
      pos_lnum = pos.pos_lnum + 1 }

let keyword_map : token String.Map.t =
  [
    "func", K_func;
    "in", K_in;
    "let", K_let;
    "proc", K_proc;
    "return", K_return;
  ]
  |> String.Map.of_alist_exn

}

let int = ('0' | ['1'-'9'] ['0'-'9']*)
let white = [' ' '\t']+
let newline = '\n'
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
let comment = "//" [^'\n']* '\n'

rule read = parse
  | white { read lexbuf }
  | comment { next_line lexbuf; read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | int { Int (int_of_string (Lexing.lexeme lexbuf)) }
  | '\'' (['0' '1']* as s) '\'' { Bitvec (Bitvec.of_string s) }
  | id
    { let s = Lexing.lexeme lexbuf in
      match String.Map.find keyword_map s with
      | Some k -> k
      | None -> Ident s }
  | "==" { EqEq }
  | '&' { Amp }
  | '(' { LParen }
  | ')' { RParen }
  | '+' { Plus }
  | ',' { Comma }
  | '-' { Minus }
  | '.' { Dot }
  | ':' { Colon }
  | ';' { Semi }
  | '=' { Eq }
  | '[' { LBrack }
  | ']' { RBrack }
  | '^' { Caret }
  | '{' { LBrace }
  | '|' { Bar }
  | '}' { RBrace }
  | '~' { Tilde }
  | eof { EOF }
  | _ { raise (SyntaxError ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }
