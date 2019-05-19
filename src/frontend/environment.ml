(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Typechecked definitions are appended to a list containing
 *       their identifiers, the whole term, and their type.
 *       This file handles operations on this 'global environment' list
 **)

open Basis
				
(* Generates a triple id * term * type from a successfully elaborated triple id * ctx * elab *)

let function_of_def id ctx elab =
	let rec helper = function
		| [] -> fst elab, snd elab
		| (x, ty') :: ctx ->  
		Ast.Abs (x, fst (helper ctx)), 
		Ast.Pi (x, ty', snd (helper ctx)) in
		id, helper ctx

let rec check_def_id id = function
  | [] -> false 
  | (id', (_, _)) :: global -> 
    if id = id'
    then true
		else check_def_id id global

(* Appends a triple id * term * type to the global enviroment list *)

let add_to_global_env global id ctx elab =
	if check_def_id id global
	then global
	else function_of_def id ctx elab :: global


