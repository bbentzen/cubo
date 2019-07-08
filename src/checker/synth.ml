(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Basic operations on synthesization lists, i.e. terms of type
 				 (int * string * expr) list * ((int * (string * expr * bool) list) list)
				 Used for implicit arguments and universe levels
 **)

open Basis

(* Print synthesization list *)

let rec printfst synl =
	match synl with
	| [] -> "" 
	| (n, id, ty) :: synl' -> 
		string_of_int n ^ ", " ^ id ^ " : " ^ Pretty.print ty ^ "\n" ^ printfst synl'

let rec printb synl =
	match (List.rev synl) with
	| [] -> "" 
	| ((id, ty), b) :: synl' -> 
		" " ^ id ^ " : " ^ Pretty.print ty ^ "- " ^ string_of_bool b ^ "\n" ^ printb synl'

let rec printsl = function
	| [] -> "" 
	| (n, synl) :: l -> 
		"wildcard " ^ string_of_int n ^ ":\n" ^ printb synl ^ printsl l

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

(* Makes a synthesization list out of a local context *)

let rec mktrue = function
	| [] -> []
	| ((id, ty), _) :: l ->
		((id, ty), true) :: mktrue l

let make n ctx = (n, mktrue ctx)

(* Sets a specific variable as false *)

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

(* Combines two synthesization lists keeping their false flag when there is conflict *)

let combines ctx ctx' =
	let rec combine x = function
	| [] -> []
	| ((id, ty), b) :: ctx' ->
		if List.mem ((id, ty), false) x then
			((id, ty), false) :: combine x ctx'
		else
			((id, ty), b) :: combine x ctx'
	in
	uniq ((combine ctx ctx') @ (combine ctx' ctx))

let rec merge nctx = function
	| [] -> nctx
	| (n, ctx) :: l ->
		match find_index n nctx with
		| Ok ctx' -> 
			(n, uniq (combines ctx ctx')) :: merge l nctx (* (remove_row n nctx) *)
		| Error _ ->
			(n, ctx) :: merge nctx l

let append sl sl' =
	(uniq (fst sl @ fst sl'), uniq (merge (snd sl) (snd sl')))

let lappend sl sl' sl'' = 
	append sl (append sl' sl'')
