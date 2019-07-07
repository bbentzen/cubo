(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Basic operations for synthesis of placeholders for expressions and universe levels,
          
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

(* snd sl operations *)

let rec mem id ty = function
	| [] -> false
	| ((id', ty'), _) :: ctx -> 
		if id = id' && ty = ty' then
			true
		else
			mem id ty ctx

let rec nmem n id ty = function
	| [] -> false
	| (m, ctx) :: l -> 
		if m = n && mem id ty ctx then
			true
		else
			nmem n id ty l

let rec mktrue = function
	| [] -> []
	| ((id, ty), _) :: l ->
		((id, ty), true) :: mktrue l

let rec concat n id ty ctx = function
	| [] -> 
		if mem id ty ctx then
			[(n, ctx)]
		else
			[(n, ((id, ty), true) :: ctx)]
		
	| (m, ctx') :: l ->
		if m = n then
			(n, ((id, ty), true) :: ctx') :: l
		else
			(m, ctx') :: concat n id ty ctx l
		
let make n ctx = (n, mktrue ctx)

(* make false *)

let rec mkfalse_var var = function
	| [] -> [] 
	| ((var', ty'), b) :: ctx' -> 
		if var = var' then
			((var', ty'), false) :: ctx'
		else
			((var', ty'), b) :: mkfalse_var var ctx'

let rec mkfalse n var = function
	| [] -> []
	| (m, ctx) :: l ->
		if n = m then
			(m, mkfalse_var var ctx) :: l
		else
			(m, ctx) :: mkfalse n var l

(* other useful functions *) 

let rec remove_row n = function
	| [] -> [] 
	| (m, ctx) :: l -> 
		if n = m then
			l
		else
			(m, ctx) :: remove_row n l

(*
let rec append_all x = function
	| [] -> []
	| (n, ctxs) :: l ->
		(n, x :: ctxs) ::
			append_all x l
*)

(* concatenates a typed variable to a list of contexts setting it as "true" *)

let rec allconcat id ty = function
	| [] -> []
	| (n, ctx) :: l ->
		if List.mem ((id, ty), false) ctx then
			(n, ctx) :: allconcat id ty l
		else
			(n, ((id, ty), true) :: ctx) :: allconcat id ty l

let rec find_index n = function
	| [] -> Error "Can't find match"
	| (m, sctx) :: l ->
		if m = n then
			Ok sctx
		else
			find_index n l

let uniq ctx =
	let helper = Hashtbl.create (List.length ctx) in
	List.iter (fun x -> Hashtbl.replace helper x ()) ctx;
	Hashtbl.fold (fun x () xs -> x :: xs) helper []

let luniq sl =
	let rec helper = function
	| [] -> []
	| l :: ll -> uniq l :: helper ll in
	(uniq (fst sl), uniq (helper (snd sl)))

(* Combines two contexts keeping a false flag (when it exists) when a type variable occurs in both *)

let rec combine ctx = function
	| [] -> []
	| ((id, ty), b) :: ctx' ->
		if List.mem ((id, ty), false) ctx then
			((id, ty), false) :: combine ctx ctx'
		else
			((id, ty), b) :: combine ctx ctx'

let combines ctx ctx' =
	uniq ((combine ctx ctx') @ (combine ctx' ctx))

let rec merge nctx = function
	| [] -> nctx
	| (n, ctx) :: l ->
		match find_index n nctx with
		| Ok ctx' -> 
			(n, uniq (combines ctx ctx')) :: merge l (remove_row n nctx)
		| Error _ ->
			(n, ctx) :: merge nctx l

let append sl sl' =
	(uniq (fst sl @ fst sl'), uniq (merge (snd sl) (snd sl')))
	(* (uniq (fst sl @ fst sl'), uniq (merge (snd sl) (snd sl'))) *)

let lappend sl sl' sl'' = 
	append sl (append sl' sl'')

let rec lowest = function
	| [] -> 0
	| (n, _) :: [] -> n
	| (n, _) :: l ->
		if n < lowest l then
			n
		else 
			lowest l

