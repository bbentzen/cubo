(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Precontexts are parsed as lists (string list * string)
 *       This file converts precontexts to actual contexts, 
 *       which are lists (string * string)
 **)

open Checker
open File

(* Creates a context (a list string * string) from a list (string list * string) *)

let rec create_ctx = function
	| [] -> []
	| ids_ty :: l ->
		(match ids_ty with
		| (ids, ty) -> 
			(match ids with
			| [] -> []
			| e :: ids' -> 
				(e, ty) :: create_ctx ([(ids', ty)]) @ create_ctx l ))

let ctx_of_string s =
	match (parse_string s) with
	| Thm (_, Prf (_, l, _, _)) -> create_ctx l
	| Print _ -> []
	| Eof () -> []
				
let checkctx filename = 
	check_ctx [] (ctx_of_string (concat_string_list (read_file filename)))

let ctxfile filename = 
	(ctx_of_string (concat_string_list (read_file filename)))

