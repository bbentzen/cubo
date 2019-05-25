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
  | [] -> Error ("No definition or theorem found for the identifier " ^ id) 
  | (id', body) :: global -> 
    if id = id'
    then Ok body
		else check_def_id id global

(* Appends a triple id * term * type to the global enviroment list *)

let add_to_global_env global id ctx elab =
	match check_def_id id global with
	| Ok _ -> global
	| Error _ -> function_of_def id ctx elab :: global

