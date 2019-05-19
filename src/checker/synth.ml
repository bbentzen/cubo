(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Performs synthesization of terms
 **)

open Basis
open Ast
open Substitution

(* Returns the type of a term variable when it has been declared *)

let rec synth_placeholder x ctxtrm =
  match (List.rev ctxtrm) with
  | [] -> (false, Ast.Void()) 
  | (y, ty) :: ctxtrm' -> 
    if x = y
    then (true, ty)
    else synth_placeholder x ctxtrm'

let rec is_declared x ctx =
  match (List.rev ctx) with
  | [] -> false
  | (y, _) :: ctx' -> 
    if x = y
    then true
    else is_declared x ctx'

let rec infer_var_ty x ctx = (* raise exception later *)
  match (List.rev ctx) with
  | [] -> Ast.Void()
  | (y, ty) :: ctx' -> 
    if x = y
    then ty
    else infer_var_ty x ctx'

(* 
let rec generate_placeholder = function
| Ast.Id ty -> 0
| Ast.Pi (y, ty1, ty2) -> generate_placeholder ty1 + generate_placeholder ty2
| Ast.Sigma (y, ty1, ty2) -> generate_placeholder ty1 + generate_placeholder ty2
| Ast.App(ty1, ty2) | Ast.Sum (ty1, ty2) -> generate_placeholder ty1 + generate_placeholder ty2
| Ast.Pathd (ty1, e1, e2) -> generate_placeholder ty1
| Ast.Int() | Ast.Nat() | Ast.Bool() | Ast.Unit() | Ast.Void() -> 0
| Ast.Type n -> 0
| Ast.Placeholder n -> int_of_string n + 1
| e -> -10 (*raise (Invalid_argument "not known to be a type")*)
*)

let rec generate_placeholder = function
  | Ast.Id _ -> 0
	| Ast.Abs (_, e) | Ast.Pabs (_, e) -> generate_placeholder e
	| Ast.Pi (_, e1, e2) | Ast.Sigma (_, e1, e2) -> generate_placeholder e1 + generate_placeholder e2
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> generate_placeholder e
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> generate_placeholder e1 + generate_placeholder e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) -> generate_placeholder e + generate_placeholder e1 + generate_placeholder e2
	| Ast.Hole n -> int_of_string n + 1
	| _ -> 0

(* Checks whether the type of a given expression is the given type *)

let is_placeholder = function
| Hole _ -> true
| _ -> false

let rec synthesize vars = function
| _ , Hole _ -> true
| Pi (x, ty1, ty2), Pi (x', ty1', ty2') -> (* group Pi and Sigma together *)
  let var = fresh_var ty2 ty2' vars in
  synthesize (vars+1) (ty1, ty1') && synthesize (vars+1) (subst x (Id var) ty2, subst x' (Id var) ty2')
| Sigma (x, ty1, ty2), Sigma (x', ty1', ty2') ->
  let var = fresh_var ty2 ty2' vars in
  synthesize (vars+1) (ty1, ty1') && synthesize (vars+1) (subst x (Id var) ty2, subst x' (Id var) ty2')
| Sum (ty1, ty2) , Sum (ty1', ty2') ->
  synthesize vars (ty1, ty1') && synthesize vars (ty2, ty2')
| Pathd (ty, e1, e2) , Pathd (ty', e1', e2') -> 
  synthesize vars (ty, ty') && synthesize vars (e1, e1') && synthesize vars (e2, e2')
| Abs (x, e), Abs (x', e') | Pabs (x, e), Pabs (x', e') -> 
  let var = fresh_var e e' vars in
  synthesize (vars+1) (subst x (Id var) e, subst x' (Id var) e')
| App (e1, e2), App (e1', e2') | Pair (e1, e2), Pair (e1', e2') | Let (e1, e2), Let (e1', e2') | At (e1, e2), At (e1', e2') -> 
  synthesize vars (e1, e1') && synthesize vars (e2, e2')
| Fst e, Fst e' | Snd e, Snd e' | Inl e, Inl e' | Inr e, Inr e' | Succ e, Succ e' | Abort e, Abort e' -> 
  synthesize vars (e, e')
| Case (e, e1, e2), Case (e', e1', e2') | Natrec (e, e1, e2), Natrec (e', e1', e2') | If (e, e1, e2), If (e', e1', e2') ->
  synthesize vars (e, e') && synthesize vars (e1, e1') && synthesize vars (e2, e2')
| ty , ty' -> if ty = ty' then true else false 
