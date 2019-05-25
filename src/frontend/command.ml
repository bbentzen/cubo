(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Executes the commands described in a file
 *       Sucessfully type-checked terms are stored in a list
 **)

open Basis
open Checker
open Eval
open File
open Context
open Environment

(* we need a function that takes a global_env, reads an expr, and replaces a def id with the actual definition of the function  *)
(* Have to elaborate ctx and rewrite it, for if p @ i0 occurs in a type in ctx we cant rewrite it *)

let rec compile global = function
| Ast.Thm (cmd, Prf (id, l, ty, e)) ->
	let ctx = create_ctx l in
	(match check_ctx global ctx, check_type global ctx (reduce ty) with
	| Ok elabctx, Ok elabty -> 
		let ctx' = List.rev elabctx in
		let ty' = eval (fst elabty) in
		(match elaborate global ctx' ty' 0 0 (reduce e) with 
		| Ok elab -> 
			(match compile (add_to_global_env global id ctx' elab) cmd with
			| Ok res -> 
				Ok res
			| Error msg -> Error msg)
		| Error msg -> Error msg)
	| Error msg, _ | _, Error msg -> Error msg )
| Ast.Print (cmd, id) -> 
	(match check_def_id id global with
	| Ok (e, ty) ->
		(match compile global cmd with
		| Ok res -> 
			Ok (fst res, 
					id ^ " := " ^ Ast.unparse e ^ ": \n" ^
					String.make (String.length id + 4) ' ' ^ Ast.unparse ty ^ 
					"\n" ^ snd res)
		| Error s -> Error s)
	| Error s -> Ok (global, "Error: " ^ s))
| Ast.Eof() -> Ok (global, "")

let checkfile filename = 
	compile [] (parse_string (concat_string_list (read_file filename)))
