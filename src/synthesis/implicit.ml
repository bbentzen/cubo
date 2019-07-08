(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Reads implicit arguments enumerating them
 **)

open Basis

(* Replaces 0-indexed wildcards with uniquely assigned indices starting at n *)

let rec read n = function
	| Ast.Id y -> Ast.Id y, n
	| Ast.Coe (i, j, e1, e2) ->
		Ast.Coe (fst (read n i), 
			fst (read (snd (read n i)) j), 
			fst (read (snd (read (snd (read n i)) j)) e1), 
			fst (read (snd (read (snd (read (snd (read n i)) j)) e1)) e2)),
		snd (read (snd (read (snd (read (snd (read n i)) j)) e1)) e2)
	| Ast.Hfill (e, e1, e2) -> 
		Ast.Hfill (fst (read n e), 
			fst (read (snd (read n e)) e1), 
			fst (read (snd (read (snd (read n e)) e1)) e2)),
		snd (read (snd (read (snd (read n e)) e1)) e2)
	| Ast.Abs (y, e) -> 
		Ast.Abs (y, fst (read n e)), snd (read n e)
	| Ast.App (e1, e2) -> 
		Ast.App (fst (read n e1), fst (read (snd (read n e1)) e2)),
		snd (read (snd (read n e1)) e2)
	| Ast.Pair (e1, e2) -> 
		Ast.Pair (fst (read n e1), fst (read (snd (read n e1)) e2)),
		snd (read (snd (read n e1)) e2)
	| Ast.Fst e -> 
		Ast.Fst (fst (read n e)), snd (read n e)
	| Ast.Snd e -> 
		Ast.Snd (fst (read n e)), snd (read n e)
	| Ast.Pi (y, e1, e2) -> 
		Ast.Pi (y, fst (read n e1), fst (read (snd (read n e1)) e2)), 
		snd (read (snd (read n e1)) e2)
	| Ast.Sigma (y, e1, e2) -> 
		Ast.Sigma (y, fst (read n e1), fst (read (snd (read n e1)) e2)), 
		snd (read (snd (read n e1)) e2)
	| Ast.Inl e -> 
		Ast.Inl (fst (read n e)), snd (read n e)
	| Ast.Inr e -> 
		Ast.Inr (fst (read n e)), snd (read n e)
	| Ast.Case (e, e1, e2) -> 
		Ast.Case (fst (read n e), 
			fst (read (snd (read n e)) e1), 
			fst (read (snd (read (snd (read n e)) e1)) e2)),
		snd (read (snd (read (snd (read n e)) e1)) e2)
	| Ast.Sum (e1, e2) -> 
		Ast.Sum (fst (read n e1), fst (read (snd (read n e1)) e2)),
		snd (read (snd (read n e1)) e2)
	| Ast.Succ e -> 
		Ast.Succ (fst (read n e)), snd (read n e)
	| Ast.Natrec (e, e1, e2) -> 
		Ast.Natrec (fst (read n e), 
			fst (read (snd (read n e)) e1), 
			fst (read (snd (read (snd (read n e)) e1)) e2)),
		snd (read (snd (read (snd (read n e)) e1)) e2)
	| Ast.If (e, e1, e2) -> 
		Ast.If (fst (read n e), 
			fst (read (snd (read n e)) e1), 
			fst (read (snd (read (snd (read n e)) e1)) e2)),
		snd (read (snd (read (snd (read n e)) e1)) e2)
	| Ast.Let (e1, e2) -> 
		Ast.Let (fst (read n e1), fst (read (snd (read n e1)) e2)),
		snd (read (snd (read n e1)) e2)
	| Ast.Abort e -> 
		Ast.Abort (fst (read n e)), snd (read n e)
	| Ast.Pabs (y, e) -> 
		Ast.Pabs (y, fst (read n e)), snd (read n e)
	| Ast.At (e1, e2) -> 
		Ast.At (fst (read n e1), fst (read (snd (read n e1)) e2)),
		snd (read (snd (read n e1)) e2)
	| Ast.Pathd (e, e1, e2) -> 
		Ast.Pathd (fst (read n e), 
			fst (read (snd (read n e)) e1), 
			fst (read (snd (read (snd (read n e)) e1)) e2)),
		snd (read (snd (read (snd (read n e)) e1)) e2)
  | Ast.Wild 0 -> 
		Ast.Wild n, n+1
	| e -> e, n

let convert e =
	fst (read 1 e)
