(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Precontexts are parsed as lists (string list * string)
 *       This file converts precontexts to actual contexts, 
 *       which are lists (string * string)
 **)

(* Creates a context (a list string * string) from a list (string list * string) *)

let rec create_ctx = function
	| [] -> []
	| ((ids, ty), b) :: l ->
		begin match ids with
			| [] -> []
			| e :: ids' -> 
				((e, ty), b) :: create_ctx ([((ids', ty), b)]) @ create_ctx l
		end

(* Determines whether a variable has been declared *)

let rec is_declared x ctx =
	match (List.rev ctx) with
	| [] -> false
	| ((y, _), _) :: ctx' -> 
		if x = y
		then true
		else is_declared x ctx'
				
(* Determines whether a given typed variable occurs in the context *)

let rec check_var_ty x ty ctx =
  match (List.rev ctx) with
  | [] -> false 
  | ((y, ty'), _) :: ctx' -> 
    if x = y && ty' = ty
    then true
    else check_var_ty x ty ctx'

(* Finds a variable of a given type in the context when it exists *)

let rec find_ty ty ctx =
  match (List.rev ctx) with
  | [] -> Error "" 
  | ((y, ty'), _) :: ctx' -> 
    if ty' = ty
    then Ok y
    else find_ty ty ctx'
		
(*
let ctx_of_string s =
	match (File.parse_string s) with
	| Thm (_, Prf (_, l, _, _)) -> create_ctx l
	| Print _ -> []
	| Eof () -> []
				
let checkctx filename = 
	check_ctx [] (ctx_of_string (File.concat_string_list (File.read_file filename)))

let ctxfile filename = 
	(ctx_of_string (File.concat_string_list (File.read_file filename)))
*)
