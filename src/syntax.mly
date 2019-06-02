%{
(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The parser of the program
 **)

open Ast
%}

%token <string> ID
%token <string> NUMBER
%token DEF PRINT LBRACE RBRACE
%token TYPE COLON VDASH
%token I0 I1 INTERVAL
%token ABS APP RARROW LRARROW PI
%token LPAREN RPAREN COMMA FST SND PROD SIGMA
%token INL INR CASE SUM
%token ZERO SUCC NATREC NAT
%token TRUE FALSE IF BOOL
%token STAR LET UNIT
%token ABORT VOID NEG
%token LANGLE RANGLE AT REFL PATHD PATH
%token WILDCARD PLACEHOLDER COLONEQ
%token EOF
%right LRARROW
%right PI
%right RARROW
%right SUM PROD SIGMA
%nonassoc NEG
%nonassoc FST SND INL INR SUCC 
%nonassoc CASE ABORT
%left APP AT

%start command
%type <Ast.command> command
%type <Ast.proof> decl
%type <((string list * Ast.expr) * bool) list> ctx
%type <Ast.expr> expr
%type <string list>ids 

%%

command:
  | decl command                                            {Thm($2, $1)}
  | PRINT ID command                                        {Print($3, $2)}
  | EOF                                                     {Eof()}

decl:
  | DEF ID ctx expr COLONEQ expr                            {Prf($2, $3, $4, $6)}

ctx: 
  | LPAREN ids expr RPAREN ctx                              {(($2, $3), true) :: $5}
  | LBRACE ids expr RBRACE ctx                              {(($2, $3), false) :: $5}
  | VDASH                                                   {([])}

ids:
  | ID ids                                                  {$1 :: $2}
  | COLON                                                   {([])}

expr: 
  | ID                                                      { Id($1) }
  | LPAREN expr RPAREN                                      { $2 }
  | I0                                                      { I0() }
  | I1                                                      { I1() }
  | INTERVAL                                                { Int() }  
  | ABS ID COMMA expr %prec PI                              { Abs($2,$4) }
  | ABS WILDCARD COMMA expr %prec PI                        { Abs("v?",$4) }
  | ABS LPAREN ID COLON expr RPAREN COMMA expr %prec PI     { Abs($3,$8) } 
  | APP expr expr                                           { App($2,$3) }
  | expr RARROW expr                                        { Pi("v?",$1,$3) }
  | PI ID COLON expr expr %prec CASE                        { Pi($2,$4,$5) } 
  | PI LPAREN ID COLON expr RPAREN expr %prec PI            { Pi($3,$5,$7) }
  | expr LRARROW expr                                       { Sigma("v?",Pi("v?",$1,$3),Pi("v?",$3,$1))}
  | LPAREN expr COMMA expr RPAREN                           { Pair($2,$4) }
  | FST expr                                                { Fst($2) }
  | SND expr                                                { Snd($2) }
  | expr PROD expr                                          { Sigma("v?",$1,$3) }
  | SIGMA ID COLON expr expr %prec SIGMA                    { Sigma($2,$4,$5) }
  | SIGMA LPAREN ID COLON expr RPAREN expr %prec SIGMA      { Sigma($3,$5,$7) } 
  | INL expr                                                { Inl($2) }
  | INR expr                                                { Inr($2) }
  | CASE expr expr expr %prec CASE                          { Case($2,$3,$4) }
  | expr SUM expr                                           { Sum($1,$3) }
  | TRUE                                                    { True() }
  | FALSE                                                   { False() }
  | IF expr expr expr %prec CASE                            { If($2,$3,$4) }
  | BOOL                                                    { Bool() }
  | ZERO                                                    { Zero() }
  | SUCC expr                                               { Succ($2) }
  | NATREC expr expr expr %prec ABORT                       { Natrec($2,$3,$4) }
  | NAT                                                     { Nat() }
  | STAR                                                    { Star() }
  | LET expr expr %prec ABORT                               { Let($2,$3) }
  | UNIT                                                    { Unit() }
  | ABORT expr %prec ABORT                                  { Abort($2) }
  | VOID                                                    { Void() }
  | NEG expr                                                { Pi("v?",$2,Void()) }
  | LANGLE ID RANGLE expr %prec CASE                        { Pabs($2,$4) }
  | LANGLE WILDCARD RANGLE expr %prec CASE                  { Pabs("v?",$4) }
  | expr AT expr                                            { At($1,$3) }
  | REFL                                                    { Pabs("v?", Wild()) }
  | PATHD expr expr expr %prec ABORT                        { Pathd($2,$3,$4) }
  | PATH expr expr expr %prec ABORT                         { Pathd(Abs("v?",$2),$3,$4) }
  | TYPE ZERO                                               { Type(0) }
  | TYPE NUMBER                                             { Type(int_of_string $2) }
  | PLACEHOLDER NUMBER                                      { Hole($2, []) }
  | WILDCARD                                                { Wild() }