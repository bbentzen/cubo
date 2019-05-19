(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The one-step reduction and evaluation functions
 **)

open Substitution

(* Returns a value and a flag determined whether there was a reduction *)

let has_reduction = function
	| Ast.Abs (x, e) -> 
		(match e with
		| Ast.App (e1 , e2) ->
			if e2 = Ast.Id x && not (free_var x e1) 
			then e1, true
			else Ast.Abs (x, Ast.App (e1, e2)), false
		| _ -> Ast.Abs (x, e), false)
	| Ast.App (e1, e2) -> 
		(match e1 with
		| Ast.Abs (x , e) -> (subst x e2 e, true)
		| _ -> Ast.App (e1, e2), false)
	| Ast.Fst e ->
	 	(match e with
		| Ast.Pair (e1 , _) -> (e1, true)
		| _ -> Ast.Fst e, false)
	| Ast.Snd e -> 
		(match e with
		| Ast.Pair (_ , e2) -> (e2, true)
		| _ -> Ast.Snd e, false)
	| Ast.Case (e, e1, e2) -> 
	  (match e with
		| Ast.Inl a -> Ast.App (e1,a), true
		| Ast.Inr b -> Ast.App (e2,b), true
		| _ -> Ast.Case (e, e1, e2), false)
	| Ast.Natrec (e, e1, e2) -> 
		(match e with
		| Ast.Zero() -> e1, true
		| Ast.Succ k -> Ast.App (Ast.App (e2,k),Natrec(k,e1,e2)), true
		| _ -> Ast.Natrec (e, e1, e2), false)
	| Ast.If (e, e1, e2) -> 
		(match e with
		| Ast.True() -> e1, true
		| Ast.False() -> e2, true
		| _ -> Ast.If (e, e1, e2), false)
	| Ast.Let (e, e1) -> 
		(match e with
		| Ast.Star() -> e1, true
		| _ -> Ast.Let (e, e1), false)
	| Ast.Pabs (x, e) -> 
		(match e with
		| Ast.At (e1 , e2) ->
			if e2 = Ast.Id x && not (free_var x e1) 
			then e1, true
			else Ast.Pabs (x, Ast.At (e1, e2)), false
		| _ -> Ast.Pabs (x, e), false)
	| Ast.At (e1, e2) -> 
		(match e1 with
		| Ast.Pabs (x , e) -> (subst x e2 e, true)
		| _ -> Ast.At (e1, e2), false)
	| e -> (e , false)

(* The evaluation function returns the value of an expression (evaluation needs not terminate) *)

let reduce e = fst (has_reduction e)

let rec eval e =
	if snd (has_reduction e) = false
	then reduce e
	else eval (reduce e)
