(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Operations involving placeholders
 **)

(* Counts the number of placeholders in an expression, generates a new one *)

let rec count = function
	| Ast.Hole (_, _) -> 
		1
	| Ast.Abs (_, e) | Ast.Pabs (_, e) -> 
		count e 
	| Ast.Pi (_, e1, e2) | Ast.Sigma (_, e1, e2) -> 
		count e1 + count e2
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> 
		count e
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> 
		count e1 + count e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) | Ast.Hfill (e, e1, e2) -> 
		count e + count e1 + count e2
	| Ast.Coe (i, j, e1, e2) -> 
		count i + count j + count e1 + count e2
	| _ -> 0

	let generate e hole l = 
		Ast.Hole ((string_of_int ((count e) + hole)), l)

(* Returns the type of a term variable when it has been declared *)

let rec candidates = function (* TODO: remove duplicates *)
	| Ast.Hole (n, l) ->
		[n, l]
	| Ast.Abs (_, e) | Ast.Pabs (_, e) -> 
		candidates e
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> 
		candidates e
	| Ast.Pi (_, e1, e2) | Ast.Sigma (_, e1, e2) -> 
		candidates e1 @ candidates e2
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> 
		candidates e1 @ candidates e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) -> 
		candidates e @ candidates e1 @ candidates e2
	| _ -> []

(* Determines whether an expression is or has a placeholder/underscore *)

let is = function
	| Ast.Hole _ -> true
	| _ -> false

let rec has_placeholder = function
	| Ast.Hole _ -> 
		true
	| Ast.Abs (_, e) | Ast.Pabs (_, e) -> 
		has_placeholder e 
	| Ast.Pi (_, e1, e2) | Ast.Sigma (_, e1, e2) -> 
		has_placeholder e1 || has_placeholder e2
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> 
		has_placeholder e
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> 
		has_placeholder e1 || has_placeholder e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) | Ast.Hfill (e, e1, e2) -> 
		has_placeholder e || has_placeholder e1 || has_placeholder e2
	| Ast.Coe (i, j, e1, e2) -> 
		has_placeholder i || has_placeholder j || has_placeholder e1 || has_placeholder e2
	| _ -> false

(* Determines whether an expression has underscores *)

let rec has_underscore = function
	| Ast.Wild _ -> 
		true
	| Ast.Abs (_, e) | Ast.Pabs (_, e) -> 
		has_underscore e 
	| Ast.Pi (_, e1, e2) | Ast.Sigma (_, e1, e2) -> 
		has_underscore e1 || has_underscore e2
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> 
		has_underscore e
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> 
		has_underscore e1 || has_underscore e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) | Ast.Hfill (e, e1, e2) -> 
		has_underscore e || has_underscore e1 || has_underscore e2
	| Ast.Coe (i, j, e1, e2) -> 
		has_underscore i || has_underscore j || has_underscore e1 || has_underscore e2
	| _ -> false
