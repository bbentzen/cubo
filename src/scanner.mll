{
(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Performs the lexical analysis 
 **)

open Syntax
}

let identifier =
  ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '0'-'9' '_' ''']* as str

let number =
  ['0'-'9']* as str

let whitespace =
  [' ' '\t']+

let end_of_line =
    '\r'
  | '\n'
  | "\r\n"

rule token = parse
  | "/*"               { comment lexbuf } (* Comments *)
  | "i0"               { I0 }
  | "i1"               { I1 }
  | "I"                { INTERVAL }
  | "𝕀"                { INTERVAL }
  | "λ"                { ABS }
  | "app"              { APP }
  | "->"               { RARROW }
  | "→"                { RARROW }
  | "↔"                { LRARROW }
  | "Π"                { PI }
  | "∏"                { PI }
  | "("                { LPAREN }
  | ","                { COMMA }
  | ")"                { RPAREN }
  | "fst"              { FST }
  | "snd"              { SND }
  | "×"                { PROD }
  | "⨉"                { PROD }
  | "Σ"                { SIGMA }
  | "inl"              { INL }
  | "inr"              { INR }
  | "case"             { CASE }
  | "+"                { SUM }  
  | "0"                { ZERO }
  | "succ"             { SUCC }
  | "natrec"           { NATREC }
  | "nat"              { NAT }
  | "ℕ"                { NAT }
  | "true"             { TRUE }
  | "false"            { FALSE }
  | "if"               { IF }
  | "bool"             { BOOL }
  | "()"               { STAR }
  | "let"              { LET }
  | "unit"             { UNIT }
  | "abort"            { ABORT }
  | "empty"            { VOID }
  | "void"             { VOID }
  | "¬"                { NEG }
  | "<"                { LANGLE }
  | ">"                { RANGLE }
  | "@"                { AT }
  | "refl"             { REFL }
  | "path"             { PATH }
  | "pathd"            { PATHD }
  | "_"                { WILDCARD }
  | "??"               { PLACEHOLDER }
  | ":="               { COLONEQ }
  | "type"             { TYPE }
  | ":"                { COLON }
  | "|-"               { VDASH }
  | "⊢"                { VDASH }
  | "{"                { LBRACE }
  | "}"                { RBRACE }
  | "definition"       { DEF }
  | "def"              { DEF }
  | "lemma"            { DEF }
  | "theorem"          { DEF }
  | "thm"              { DEF }
  | "print"            { PRINT }
  | "infer"            { INFER }
  | whitespace         { token lexbuf }
  | end_of_line        { Lexing.new_line lexbuf; token lexbuf } (* needs fix later *)
  | identifier         { ID(str) }
  | number             { NUMBER(str) }
  | _ as chr           { failwith ("Lex error: "^(Char.escaped chr))}
  | eof                { EOF }

and comment = parse
  | "*/"               { token lexbuf }
  | _                  { comment lexbuf }

(*
(* | "--"               { comment_line lexbuf } *)
and comment_line = parse
  | end_of_line        { token lexbuf }
  | _                  { comment_line lexbuf } *)