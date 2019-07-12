(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The pretty printer indents hfill terms, 
         distinguishes between dependent and non-dependent functions, products, and paths,
          prints nested lambdas, pis, sigmas, and uses parentheses when necessary
 **)

open Ast

(* A simple pretty printer *)

let rec print = function
  
  | Coe (i, j, e1, e2) -> 
    String.concat "" ["coe "; par i; par j; par e1; par e2]
  
  | Hfill (e, e1, e2) -> 
    String.concat "" ["\n  hfill "; par e; 
    "\n    | i0 → "; print e1; 
    "\n    | i1 → "; print e2]
    
  | Abs (y, e) ->  
    let rec iter = function
      | Abs (y', e') ->
        " " ^ y' ^ iter e'
      | e' ->
        ", " ^ print e'
    in
    "λ " ^ y ^ iter e

  | Pi (x, e1, e2) ->

    if Substitution.has_var x e2 then
      begin
      let rec diter = function
        | Pi (x', e1', e2') ->
          if Substitution.has_var x' e2' then
            String.concat "" ["("; x'; " : "; print e1'; ") "; diter e2']
          else
            String.concat "" [tpar e1'; "→ "; print e2']
        | e' ->
          print e'
      in
      "Π (" ^ x ^ " : " ^ print e1 ^ ") " ^ diter e2
      end

    else
      begin
        match e2 with
        | Void() -> 
          "¬" ^ tpar e1
        | _ ->
          let rec iter = function
            | Pi (x', e1', e2') ->
              if Substitution.has_var x' e2' then
                String.concat "" ["Π ("; x'; " : "; print e1'; ") "; print e2']
              else
                String.concat "" [tpar e1'; "→ "; iter e2']
            | e' ->
              print e'
          in
          tpar e1 ^ "→ " ^ iter e2
      end

  | Sigma (x, e1, e2) ->
    
    if Substitution.has_var x e2 then
      begin
      let rec diter = function
        | Sigma (x', e1', e2') ->
          if Substitution.has_var x' e2' then
            String.concat "" ["("; x'; " : "; print e1'; ") "; diter e2']
          else
            String.concat "" [tpar e1'; "× "; print e2']
        | e' ->
          print e'
      in
      "Σ (" ^ x ^ " : " ^ print e1 ^ ") " ^ diter e2
      end

    else
      let rec iter = function
        | Sigma (x', e1', e2') ->
          if Substitution.has_var x' e2' then
            String.concat "" ["Σ ("; x'; " : "; print e1'; ") "; print e2']
          else
            String.concat "" [tpar e1'; "× "; iter e2']
        | e' ->
          print e'
      in
      tpar e1 ^ "× " ^ iter e2

  | Pathd (e, e1, e2) ->
    begin
      match e with
      | Abs (i, ty) ->
        if Substitution.has_var i ty then
          "pathd (" ^ print (Abs (i, ty)) ^ ") " ^ par e1 ^ par e2
        else
          "path " ^ par ty ^ par e1 ^ par e2
      | _ ->
        "path " ^ par e ^ par e1 ^ par e2
    end

  | App (e1, e2) ->
      let rec iter = function
      | App (e3, e4) -> iter e3 ^ par e4
      | e -> par e
    in
    iter e1 ^ par e2    

  | Type l -> 
    "type " ^ print_level l ^ " "

  | Pair (e1, e2) -> "(" ^ par e1 ^ ", " ^ par e2 ^ ") "
  | Fst e -> "fst " ^ par e
  | Snd e -> "snd " ^ par e
  | Case (e, e1, e2) -> String.concat "" ["case "; par e; par e1; par e2]
  | Sum (e1, e2) -> String.concat "" ["( "; par e1; "+ "; par e2; ") "]
  | Succ e -> String.concat "" ["succ "; par e]
  | Natrec (e, e1, e2) -> String.concat "" ["natrec "; par e; par e1; par e2]
  | If (e, e1, e2) -> String.concat "" ["if "; par e; par e1; par e2]
  | Let (e1, e2) -> String.concat "" ["let "; par e1; par e2]
  | Abort e -> String.concat "" ["abort "; par e]
  | Pabs (y, e) -> String.concat "" ["<"; y; "> "; print e]
  | At (e1, e2) -> String.concat "" [par e1; "@ "; par e2]
  | Hole (n, _) -> "?" ^ n ^ "? "
  | Id y -> y ^ " "
  | I0() -> "i0 "
  | I1() -> "i1 "
  | Int() -> "I " 
  | Zero() -> "0 "
  | Nat() -> "nat "
  | True() -> "true "
  | False() -> "false "
  | Bool() -> "bool "
  | Star() -> "() "
  | Unit() -> "unit "
  | Void() -> "void "
  | Inl e -> "inl " ^ par e
  | Inr e -> "inr " ^ par e
  | Wild n -> "?0" ^ string_of_int n ^ "? "

and par e = 
  let helper = function
    | Abs _ | Ast.Pabs _ | Pi _ | Sigma _ | Fst _ | Snd _ 
    | Inl _ | Inr _ | Succ _ | Abort _ | App _ | Pair _ 
    | Sum _ | Let _ | At _ | Case _ | Natrec _ | If _ 
    | Pathd _ | Coe _ -> 
      true
    | _ -> false
  in
  if helper e then
    "(" ^ print e ^ ") "
  else
    print e

and tpar e = 
let helper = function
  | Pi _ | Sigma _ | Sum _  | Pathd _ | Hfill _ | Coe _ -> 
    true
  | _ -> false
in
if helper e then
  "(" ^ print e ^ ") "
else
  print e

and print_level = function
  | Num n -> string_of_int n
  | Suc n -> print_level n ^ "+ 1"
  | Var l -> l
  | Max (n, Num m) | Max (Num m, n) -> print_level n ^ " + " ^ string_of_int m
  | Max (n, m) -> "max(" ^ print_level n ^ "," ^ print_level m ^ ")"