(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Performs synthesization of terms
 **)

(* Returns the type of a term variable when it has been declared *)

let rec fresh_index = function
  | Ast.Id _ -> 0
	| Ast.Abs (_, e) | Ast.Pabs (_, e) -> fresh_index e
	| Ast.Pi (_, e1, e2) | Ast.Sigma (_, e1, e2) -> fresh_index e1 + fresh_index e2
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> fresh_index e
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> fresh_index e1 + fresh_index e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) -> fresh_index e + fresh_index e1 +fresh_index e2
	| Ast.Hole (n,_) -> int_of_string n + 1
	| _ -> 0

let generate e hole l = 
	Ast.Hole ((string_of_int ((fresh_index e) + hole)), l)

let rec candidates = function (* TODO: remove duplicates *)
	| Ast.Hole (n, l) -> [n, l]
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

(* Checks whether the type of a given expression is the given type *)

let is = function
| Ast.Hole _ -> true
| _ -> false