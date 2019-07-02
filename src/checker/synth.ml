(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Synthesizes placeholders for expressions and universe levels,
         Based on an exhaustive search using the context 
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

(* Synthesizes wildcards *)

	let rec printlist ctx =
		match (List.rev ctx) with
		| [] -> "" 
		| (n, id, ty) :: ctx' -> 
			string_of_int n ^ ", " ^ id ^ " : " ^ Pretty.print ty ^ "\n" ^ printlist ctx'

(* Synthesizes wildcards *)

let rec remove_var var = function
	| [] -> [] 
	| ((var', ty'), b) :: ctx' -> 
		if var = var' then
			ctx'
		else
			((var', ty'), b) :: remove_var var ctx'

let rec remove n var = function
	| [] -> [] 
	| (m, ctx) :: l -> 
		if n = m then
			(m, remove_var var ctx) :: l
		else
		(m, ctx) :: remove n var l

(* Iteration and placeholder synthesis *)

let rec wild global ctx lvl sl e ty = 
  let elab = Elab.elaborate global ctx lvl sl (Eval.eval ty) 0 0 (Eval.reduce e) in (* (Eval.reduce e) *)
  begin 
    match elab with
		| Ok (e', ty', sa) -> (* 	TODO: improve performance *)
			let relab = Elab.elaborate global ctx lvl sl ty' 0 0 e' in
			begin
				match relab with
				| Ok _ -> Ok (e', ty')
				| Error (_, msg) -> 
					witer sa msg global ctx lvl sl e ty
			end
		
		| Error (sa, msg) ->
			witer sa msg global ctx lvl sl e ty
	end

and witer sa msg global ctx lvl sl e ty =
	match sa with
	| [] ->
		Error msg
		
	| (n, id, _) :: _ -> (* l *)
		let e' = Substitution.fullsubst (Wild n) (Id id) e in
		let w = wild global ctx lvl sl e' ty in
		match w with
		| Ok (e', ty') -> 
			Ok (e', ty')
		| Error msg ->
			begin
				match Elab.find_index n (snd sl) with
				| Ok ll ->
					if remove_var id ll = ll then
						Error ("Can't find variable '" ^ id ^ 
							"' in list of candidates\n" ^ Elab.print ll ^ 
							"(You should not see this message, please report)\n" ^ msg)
					else
						wild global ctx lvl ([], remove n id (snd sl)) e ty

				| Error _ ->
					wild global ctx lvl ([], (n, remove_var id ctx) :: (snd sl)) e ty
			end
