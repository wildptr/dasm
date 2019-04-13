{
open Batteries
open Lexing
open Spec_parser

exception Error of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = pos.pos_cnum;
      pos_lnum = pos.pos_lnum + 1 }

let keyword_map : token Map.String.t =
  [
    "bool", BOOL;
    "extract", EXTRACT;
    "false", FALSE;
    "jump", JUMP;
    "pc", PC;
    "proc", PROC;
    "sign_extend", SIGN_EXTEND;
    "template", TEMPLATE;
    "true", TRUE;
    "undefined", UNDEFINED;
    "var", VAR;
  ] |> List.fold_left (fun m (k, v) -> Map.String.add k v m) Map.String.empty

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
  | '\'' (['0' '1']* as s) '\'' { Bitvec (Bitvec.of_string_base 2 s) }
  | id
    { let s = Lexing.lexeme lexbuf in
      try Map.String.find s keyword_map with Not_found -> Ident s }
  | "->" { Arrow }
  | "==" { EqEq }
  | "!=" { BangEq }
  (*| '$' { Dollar }*)
  | '#' { Hash }
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
  (*| '@' { At }*)
  | '[' { LBrack }
  | ']' { RBrack }
  | '^' { Caret }
  | '{' { LBrace }
  | '|' { Bar }
  | '}' { RBrace }
  | '~' { Tilde }
  | eof { EOF }
  | _ { raise (Error ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }
