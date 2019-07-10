(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Typechecked definitions are appended to a list containing
 *       their identifiers, the whole term, and their type.
 *       This file handles operations on this 'global environment' list
 **)

open Basis

(* Determines whether a variable has been declared in the global context *)

let is_declared x global =
	let rec helper x = function
	| [] -> false
	| (id, (_, _)) :: global -> 
		if x = id then 
			true
		else 
			helper x global
	in
	helper x (List.rev global)

(* Generates a triple id * term * type from a successfully elaborated triple id * ctx * elab *)

let function_of_def id ctx elab hole =
	let rec helper h' = function
		| [] -> fst elab, snd elab
		| (x, ty, true) :: ctx ->  
			Ast.Abs (x, fst (helper h' ctx )), 
			Ast.Pi (x, ty, snd (helper h' ctx))
		| (x, _, false) :: ctx ->  
			let h = Placeholder.generate (fst (helper (h'+1) ctx)) h' [] in
			Substitution.subst x h (fst (helper (h'+1) ctx)), 
			Substitution.subst x h (snd (helper (h'+1) ctx )) 
		in
	id, helper hole ctx

let rec check_def_id id = function
	| [] -> 
		Error ("No definition or theorem found for the identifier '" ^ id ^ "'") 
  | (id', body) :: global -> 
    if id = id'
    then Ok body
		else check_def_id id global

(* Appends a triple id * term * type to the global context *)

let add_to_global_env global id ctx elab =
	match check_def_id id global with
	| Ok _ -> global
	| Error _ -> function_of_def id ctx elab 0 :: global

(* Returns the body of a definition when given a declared global constant *)

let rec unfold id = function
	| [] -> 
		Error ("No declaration found for identifier '" ^ id ^ "'")
  | (id', (body , ty)) :: global -> 
		if id = id' then 
			Ok (body, ty)
		else 
			unfold id global

(* Unfolds all declared global constants and checks for naming conflicts *)

let rec unfold_all global vars = function
	| Ast.Id x -> 
		begin 
			match unfold x global with
			| Ok (body, _) -> Ok body
			| _ -> Ok (Ast.Id x)
		end

	| Ast.Abs (x, e) ->
		if is_declared x global then
      Error ("Naming conflict with the name '" ^ x ^ "'\nIt occurs as definition/theorem identifier but is used as a variable name ")
		else
			begin match unfold_all global vars e with
			| Ok e' -> 
				Ok (Ast.Abs (x, e'))
			| Error msg -> Error msg
			end

	| Ast.Pabs (x, e) -> 
		if is_declared x global then
      Error ("Naming conflict with the name '" ^ x ^ "'\nIt occurs as definition/theorem identifier but is used as a variable name ")
		else
			begin match unfold_all global vars e with
			| Ok e' -> 
				Ok (Ast.Pabs (x, e'))
			| Error msg -> Error msg
			end

	| Ast.App (e1, e2) ->
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u1, u2 with
			| Ok e1', Ok e2' -> Ok (Ast.App (e1', e2'))
			| Error msg, _ | _, Error msg -> Error msg
		end
		
	| Ast.Pair (e1, e2) ->
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u1, u2 with
			| Ok e1', Ok e2' -> Ok (Ast.Pair (e1', e2'))
			| Error msg, _ | _, Error msg -> Error msg
		end

	| Ast.At (e1, e2) ->
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u1, u2 with
			| Ok e1', Ok e2' -> Ok (Ast.At (e1', e2'))
			| Error msg, _ | _, Error msg -> Error msg
		end

	| Ast.Let (e1, e2) ->
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u1, u2 with
			| Ok e1', Ok e2' -> Ok (Ast.Let (e1', e2'))
			| Error msg, _ | _, Error msg -> Error msg
		end

	| Ast.Fst e ->
		begin match unfold_all global vars e with
		| Ok e' -> 
			Ok (Ast.Fst e')
		| Error msg -> Error msg
		end

	| Ast.Snd e ->
		begin match unfold_all global vars e with
		| Ok e' -> 
			Ok (Ast.Snd e')
		| Error msg -> Error msg
		end

	| Ast.Inl e ->
		begin match unfold_all global vars e with
		| Ok e' -> 
			Ok (Ast.Inl e')
		| Error msg -> Error msg
		end

	| Ast.Inr e ->
		begin match unfold_all global vars e with
		| Ok e' -> 
			Ok (Ast.Inr e')
		| Error msg -> Error msg
		end

	| Ast.Succ e ->
		begin match unfold_all global vars e with
		| Ok e' -> 
			Ok (Ast.Succ e')
		| Error msg -> Error msg
		end

	| Ast.Abort e -> 
		begin match unfold_all global vars e with
		| Ok e' -> 
			Ok (Ast.Abort e')
		| Error msg -> Error msg
		end

	| Ast.Case (e, e1, e2) ->
		let u = unfold_all global vars e in
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u, u1, u2 with
			| Ok e', Ok e1', Ok e2' -> Ok (Ast.Case (e', e1', e2'))
			| Error msg, _, _ | _, Error msg , _ | _, _, Error msg -> Error msg
		end

	| Ast.Natrec (e, e1, e2) ->
		let u = unfold_all global vars e in
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u, u1, u2 with
			| Ok e', Ok e1', Ok e2' -> Ok (Ast.Natrec (e', e1', e2'))
			| Error msg, _, _ | _, Error msg , _ | _, _, Error msg -> Error msg
		end

	| Ast.If (e, e1, e2) ->
		let u = unfold_all global vars e in
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u, u1, u2 with
			| Ok e', Ok e1', Ok e2' -> Ok (Ast.If (e', e1', e2'))
			| Error msg, _, _ | _, Error msg , _ | _, _, Error msg -> Error msg
		end

	| Ast.Pi (x, e1, e2) -> 
		if is_declared x global then
			Error ("Naming conflict with the name '" ^ x ^ "'\nIt occurs as definition/theorem identifier but is used as a variable name ")
		else
			let u1 = unfold_all global vars e1 in
			let u2 = unfold_all global vars e2 in
			begin match u1, u2 with
			| Ok e1', Ok e2' -> Ok (Ast.Pi (x, e1', e2'))
			| Error msg, _ | _, Error msg -> Error msg
			end

	| Ast.Sigma (x, e1, e2) -> 
		if is_declared x global then
			Error ("Naming conflict with the name '" ^ x ^ "'\nIt occurs as definition/theorem identifier but is used as a variable name ")
		else
			let u1 = unfold_all global vars e1 in
			let u2 = unfold_all global vars e2 in
			begin match u1, u2 with
			| Ok e1', Ok e2' -> Ok (Ast.Sigma (x, e1', e2'))
			| Error msg, _ | _, Error msg -> Error msg
			end

	| Ast.Sum (e1, e2) ->
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u1, u2 with
			| Ok e1', Ok e2' -> Ok (Ast.Sum (e1', e2'))
			| Error msg, _ | _, Error msg -> Error msg
		end

	| Ast.Pathd (e, e1, e2) -> 
		let u = unfold_all global vars e in
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u, u1, u2 with
			| Ok e', Ok e1', Ok e2' -> Ok (Ast.Pathd (e', e1', e2'))
			| Error msg, _, _ | _, Error msg , _ | _, _, Error msg -> Error msg
		end
	
	| Ast.Coe (i, j, e1, e2) ->
		let ui = unfold_all global vars i in
		let uj = unfold_all global vars j in
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match ui, uj, u1, u2 with
			| Ok i', Ok j', Ok e1', Ok e2' -> Ok (Ast.Coe (i', j', e1', e2'))
			| Error msg, _, _, _ | _, Error msg , _, _ | _, _, Error msg, _ | _, _, _, Error msg -> 
				Error msg
		end
	
	| Ast.Hfill (e, e1, e2) -> 
		let u = unfold_all global vars e in
		let u1 = unfold_all global vars e1 in
		let u2 = unfold_all global vars e2 in
		begin match u, u1, u2 with
			| Ok e', Ok e1', Ok e2' -> Ok (Ast.Hfill (e', e1', e2'))
			| Error msg, _, _ | _, Error msg , _ | _, _, Error msg -> Error msg
		end 

	| e -> Ok e 