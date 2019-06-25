%{
(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The parser of the program
 **)

open Ast

let rec abs_of_list e = function
  | [] -> e
  | id :: l ->
    Ast.Abs(id, abs_of_list e l)

let rec pi_of_list e = function
  | [] -> e
  | (id, ty) :: l ->
    Ast.Pi (id, ty, pi_of_list e l)

let rec sigma_of_list e = function
  | [] -> e
  | (id, ty) :: l ->
    Ast.Sigma (id, ty, sigma_of_list e l)

let fill_def i j ty e e1 e2 =
  let v1 = Substitution.fresh_var (App(e1, e2)) e 2 in
  Hfill(Abs(v1, Coe (i, j, ty, App(e, Id v1))), 
  Abs(v1, Coe (Id v1, j, ty, App(e1, Id v1))),
  Abs(v1, Coe (Id v1, j, ty, App(e2, Id v1))))

%}

%token <string> ID
%token <string> FILENAME
%token <string> NUMBER
%token IMPORT UNIVERSE DEF PRINT INFER LBRACE RBRACE
%token TYPE MAX NEXT COLON VDASH
%token I0 I1 INTERVAL COE HCOM HFILL FILL COM BAR
%token ABS APP RARROW LRARROW PI
%token LPAREN RPAREN COMMA FST SND PROD SIGMA
%token INL INR CASE SUM
%token ZERO SUCC NATREC NAT
%token TRUE FALSE IF BOOL
%token STAR LET UNIT
%token ABORT VOID NEG
%token LANGLE RANGLE AT REFL SYMM TRANS PATHD PATH
%token WILDCARD PLACEHOLDER COLONEQ
%token EOF
%right LRARROW
%right PI
%right RARROW
%left AT
%right SUM PROD
%right TRANS
%nonassoc NEG
%nonassoc FST SND INL INR SUCC 
%nonassoc CASE ABORT
%left APP
%nonassoc SYMM

%start command
%type <Ast.command> command
%type <Ast.proof> decl
%type <((string list * Ast.expr) * bool) list> ctx
%type <Ast.level> level
%type <Ast.expr> expr
%type <string list> ids 
%type <((string * expr) list) * expr> blocks

%%

command:  
  | decl command                                            {Thm($2, $1)}
  | IMPORT FILENAME command                                 {Import($3, $2)}
  | UNIVERSE ids command                                    {Level($3, $2)}
  | PRINT ID command                                        {Print($3, $2)}
  | INFER expr command                                      {Infer($3, $2)}
  | EOF                                                     {Eof()}

decl:
  | DEF ID ctx expr COLONEQ expr                            {Prf($2, $3, $4, $6)}

ctx: 
  | LPAREN ids COLON expr RPAREN ctx                        {(($2, $4), true) :: $6}
  | LBRACE ids COLON expr RBRACE ctx                        {(($2, $4), false) :: $6}
  | VDASH                                                   {([])}

ids:
  | ID                                                      { [$1] }
  | ID ids                                                  { $1 :: $2 }

vars:
  | ID                                                      { [$1] }
  | WILDCARD                                                { ["v?"] }
  | ID vars                                                 { $1 :: $2 }
  | WILDCARD vars                                           { "v?" :: $2 }

blocks:
  | expr                                                   { ([], $1) }
  | LPAREN ID COLON expr RPAREN blocks                     { (($2, $4) :: fst $6, snd $6) }

level:
  | ID                                                     { Var ($1) }
  | NUMBER                                                 { Num (int_of_string ($1)) }
  | NEXT level                                             { Suc ($2) }
  | MAX level level                                        { Max ($2, $3) }
  | LPAREN level RPAREN                                    { $2 }

expr: 
  | ID                                                      { Id($1) }
  | LPAREN expr RPAREN                                      { $2 }
  | I0                                                      { I0() }
  | I1                                                      { I1() }
  | INTERVAL                                                { Int() }
  | COE expr expr expr expr %prec CASE                      { Coe($2,$3,$4,$5) }
  | COM expr expr expr expr  
    BAR I0 RARROW expr 
    BAR I1 RARROW expr                                      { App (fill_def ($2) ($3) ($4) ($5) ($9) ($13), I1()) }
  | FILL expr expr expr expr  
    BAR I0 RARROW expr 
    BAR I1 RARROW expr                                      { fill_def ($2) ($3) ($4) ($5) ($9) ($13) }
  | HCOM expr  
    BAR I0 RARROW expr 
    BAR I1 RARROW expr %prec CASE                           { App(Hfill($2,$6,$10),I1()) }
  | HFILL expr  
    BAR I0 RARROW expr 
    BAR I1 RARROW expr %prec CASE                           { Hfill($2,$6,$10) }
  | ABS vars COMMA expr %prec PI                            { abs_of_list ($4) ($2) }
  | ABS LPAREN ID COLON expr RPAREN COMMA expr %prec PI     { Abs($3,$8) } 
  | APP expr expr                                           { App($2,$3) }
  | expr RARROW expr                                        { Pi("v?",$1,$3) }
  | PI blocks                                               { pi_of_list (snd $2) (fst $2) }
  | expr LRARROW expr                                       { Sigma("v?", Pi("v?",$1,$3), Pi("v?",$3,$1)) }
  | LPAREN expr COMMA expr RPAREN                           { Pair($2,$4) }
  | FST expr                                                { Fst($2) }
  | SND expr                                                { Snd($2) }
  | expr PROD expr                                          { Sigma("v?",$1,$3) }
  | SIGMA blocks                                            { sigma_of_list (snd $2) (fst $2) }
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
  | LANGLE ID RANGLE expr %prec PI                          { Pabs($2,$4) }
  | LANGLE WILDCARD RANGLE expr %prec PI                    { Pabs("v?",$4) }
  | expr AT expr                                            { At($1,$3) }
  | REFL                                                    { Pabs("v?", Wild 0) }
  | expr SYMM                                               { App(Id "path_symm", $1) }
  | expr TRANS expr                                         { App(App(Id "path_trans", $1), $3) }
  | PATHD expr expr expr %prec ABORT                        { Pathd($2,$3,$4) }
  | PATH expr expr expr %prec ABORT                         { Pathd(Abs("v?",$2),$3,$4) }
  | TYPE ZERO                                               { Type(Num 0) }
  | TYPE level                                              { Type ($2) }
  | PLACEHOLDER NUMBER                                      { Hole($2, []) }
  | WILDCARD                                                { Wild 0 }
