(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Basic operations on synthesization stacks, lists of lists
 				   ((int * (string * expr * bool) list) list)
				 used to keep track of which synthetization attempts have been performed
 **)

open Basis

(* Print synthesization list *)

let printb synl =
	let rec printrev = function
	| [] -> "" 
	| (id, ty, b) :: synl' -> 
		" " ^ id ^ " : " ^ Pretty.print ty ^ "- " ^ string_of_bool b ^ "\n" ^ printrev synl'
	in
	printrev (List.rev synl)

let rec printsl = function
	| [] -> "" 
	| (n, synl) :: l -> 
		"wildcard " ^ string_of_int n ^ ":\n" ^ printb synl ^ printsl l

(* Makes a synthesization list out of a local context *)

let rec mktrue = function
	| [] -> []
	| (id, ty, _) :: l ->
		(id, ty, true) :: mktrue l

let make n ctx = (n, mktrue ctx)

(* Sets a specific variable as false *)

let rec mkfalse_var var = function
	| [] -> [] 
	| (var', ty', b) :: ctx' -> 
		if var = var' then
			(var', ty', false) :: ctx'
		else
			(var', ty', b) :: mkfalse_var var ctx'

let rec mkfalse n var = function
	| [] -> []
	| (m, msynl) :: l ->
		if n = m then
			(m, mkfalse_var var msynl) :: l
		else
			(m, msynl) :: mkfalse n var l

(* search *) 

let rec find_index n = function
	| [] -> Error "Can't find match"
	| (m, sctx) :: l ->
		if m = n then
			Ok sctx
		else
			find_index n l

(* concatenates a typed variable to a list of contexts setting it as "true" *)

let rec allconcat id ty = function
	| [] -> []
	| (n, nsynl) :: l ->
		if List.mem (id, ty, false) nsynl then
			(n, nsynl) :: allconcat id ty l
		else
			(n, (id, ty, true) :: nsynl) :: allconcat id ty l

let uniq ctx =
	let helper = Hashtbl.create (List.length ctx) in
	List.iter (fun x -> Hashtbl.replace helper x ()) ctx;
	Hashtbl.fold (fun x () xs -> x :: xs) helper []

(* Combines two synthesization lists keeping their false flag when there is conflict *)

let combines nsynl msynl =
	let rec combine x = function
	| [] -> []
	| (id, ty1, b) :: msynl ->
		if List.mem (id, ty1, false) x then
			(id, ty1, false) :: combine x msynl
		else
			(id, ty1, b) :: combine x msynl
	in
	uniq ((combine nsynl msynl) @ (combine msynl nsynl))

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
