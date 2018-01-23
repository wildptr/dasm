{
open Lexing
open Spec_parser

exception Error of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = lexbuf.lex_curr_pos;
      pos_lnum = pos.pos_lnum + 1 }

module StringMap = Map.Make(String)

let keyword_map : token StringMap.t =
  [
    "call", K_call;
    "if", K_if;
    "jump", K_jump;
    "load", K_load;
    "proc", K_proc;
    "repeat", K_repeat;
    "return", K_return;
    "store", K_store;
    "template", K_template;
    "undefined", K_undefined;
  ] |> List.fold_left (fun map (k, v) -> StringMap.add k v map) StringMap.empty

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
      match StringMap.find_opt s keyword_map with
      | Some k -> k
      | None -> Ident s }
  | "==" { EqEq }
  | '$' { Dollar }
  | '&' { Amp }
  | '(' { LParen }
  | ')' { RParen }
  | '*' { Star }
  | '+' { Plus }
  | ',' { Comma }
  | '-' { Minus }
  | '.' { Dot }
  | '/' { Slash }
  | ':' { Colon }
  | ';' { Semi }
  | '<' { LAngle }
  | '=' { Eq }
  | '>' { RAngle }
  | '[' { LBrack }
  | ']' { RBrack }
  | '^' { Caret }
  | '{' { LBrace }
  | '|' { Bar }
  | '}' { RBrace }
  | '~' { Tilde }
  | eof { EOF }
  | _ { raise (Error ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }
