(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Call-by-name prenormalization
 *       Performs full β-reduction on β-redexes of all types,
 *       η-reduction for dependent functions and paths,
 *       but not ε-reduction for dependent paths.
 **)

open Substitution

(* Returns a value and a flag determined whether there was a reduction *)

let rec has_reduction = function
	| Ast.Abs (x, e) -> 
		(match e with
		| Ast.App (e1 , e2) ->
			if e2 = Ast.Id x && not (free_var x e1) 
			then e1, true
			else Ast.Abs (x, Ast.App (fst (has_reduction e1), fst (has_reduction e2))),
					 snd (has_reduction e1) || snd (has_reduction e2)
		| _ -> Ast.Abs (x, fst (has_reduction e)), snd (has_reduction e))
	| Ast.App (e1, e2) -> 
		(match e1 with
		| Ast.Abs (x , e) -> (subst x e2 e, true)
		| _ -> Ast.App (fst (has_reduction e1), e2), snd (has_reduction e1))
	| Ast.Pair (e1, e2) -> 
		Ast.Pair (fst (has_reduction e1), fst (has_reduction e2)),
		snd (has_reduction e1) || snd (has_reduction e2)
	| Ast.Fst e ->
	 	(match e with
		| Ast.Pair (e1 , _) -> (e1, true)
		| _ -> Ast.Fst (fst (has_reduction e)), snd (has_reduction e))
	| Ast.Snd e -> 
		(match e with
		| Ast.Pair (_ , e2) -> (e2, true)
		| _ -> Ast.Snd (fst (has_reduction e)), snd (has_reduction e))
	| Ast.Inl e -> 
		Ast.Inl (fst (has_reduction e)), snd (has_reduction e)
	| Ast.Inr e -> 
		Ast.Inr (fst (has_reduction e)), snd (has_reduction e)
	| Ast.Case (e, e1, e2) -> 
	  (match e with
		| Ast.Inl a -> Ast.App (e1,a), true
		| Ast.Inr b -> Ast.App (e2,b), true
		| _ -> Ast.Case (fst (has_reduction e), e1, e2), snd (has_reduction e))
	| Ast.Succ e -> 
		Ast.Succ (fst (has_reduction e)), snd (has_reduction e)
	| Ast.Natrec (e, e1, e2) -> 
		(match e with
		| Ast.Zero() -> e1, true
		| Ast.Succ k -> Ast.App (Ast.App (e2,k),Natrec(k,e1,e2)), true
		| _ -> Ast.Natrec (fst (has_reduction e), e1, e2), snd (has_reduction e))
	| Ast.If (e, e1, e2) -> 
		(match e with
		| Ast.True() -> e1, true
		| Ast.False() -> e2, true
		| _ -> Ast.If (fst (has_reduction e), e1, e2), snd (has_reduction e))
	| Ast.Let (e, e1) -> 
		(match e with
		| Ast.Star() -> e1, true
		| _ -> Ast.Let (fst (has_reduction e), e1), snd (has_reduction e))
	| Ast.Pabs (x, e) -> 
		(match e with
		| Ast.At (e1 , e2) ->
			if e2 = Ast.Id x && not (free_var x e1) 
			then e1, true
			else Ast.Pabs (x, Ast.At (fst (has_reduction e1), fst (has_reduction e2))), 
					 snd (has_reduction e1) || snd (has_reduction e2)
		| _ -> Ast.Pabs (x, fst (has_reduction e)), snd (has_reduction e))
	| Ast.At (e1, e2) -> 
		(match e1 with
		| Ast.Pabs (x , e) -> (subst x e2 e, true)
		| _ -> Ast.At (fst (has_reduction e1), e2), snd (has_reduction e1))
	| Ast.Pi (x, e1, e2) -> 
		Ast.Pi (x, fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e1) || snd (has_reduction e2)
	| Ast.Sigma (x, e1, e2) -> 
		Ast.Sigma (x, fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e1) || snd (has_reduction e2)
	| Ast.Sum (e1, e2) -> 
		Ast.Sum (fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e1) || snd (has_reduction e2)
	| Ast.Pathd (e, e1, e2) -> 
		Ast.Pathd (fst (has_reduction e), fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e)|| snd (has_reduction e1) || snd (has_reduction e2)
	| e -> (e , false)

(* One-step prereduction: does not reduce ε-redexes *)

let reduce e = fst (has_reduction e)

(* Returns the value of an expression (may not terminate if expression is ill-typed) *)

let rec eval e =
	if snd (has_reduction e) = false
	then reduce e
	else eval (reduce e)
