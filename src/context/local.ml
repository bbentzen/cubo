(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Precontexts are parsed as lists (string list * string)
 *       This file converts precontexts to actual contexts, 
 *       which are lists (string * string)
 **)

open Basis

(* Creates a context (a list string * string) from a list (string list * string) *)

let rec create_ctx = function
	| [] -> []
	| ((ids, ty), b) :: l ->
		begin match ids with
			| [] -> []
			| e :: ids' -> 
				(e, ty, b) :: create_ctx ([((ids', ty), b)]) @ create_ctx l
		end

(* Determines whether a variable has been declared *)

let is_declared x ctx =
	let rec helper x = function
	| [] -> false
	| (y, _, _) :: ctx -> 
		if x = y then
			true
		else
			helper x ctx
	in
	helper x (List.rev ctx)

let rec var_type x ctx =
	match (List.rev ctx) with
	| [] -> Error()
	| (y, ty, _) :: ctx' -> 
		if x = y then 
			Ok ty
		else 
			var_type x ctx'

(* Determines whether a given typed variable occurs in the context *)

let rec check_var_ty x ty ctx =
  match (List.rev ctx) with
  | [] -> false 
  | (y, ty', _) :: ctx -> 
    if x = y && ty' = ty then 
			true
		else
			check_var_ty x ty ctx

(* Finds a variable of a given type in the context when it exists *)

let find_ty ty ctx =
	let rec helper ty = function
	| [] -> Error () 
  | (y, ty', _) :: ctx -> 
    if ty' = ty then 
			Ok y
		else 
			helper ty ctx
	in
	helper ty (List.rev ctx)

let find_true ty ctx =
	let rec helper ty = function
	| [] -> Error () 
	| (y, ty', b) :: ctx' -> 
		if ty' = ty && b then 
			Ok y
		else 
			helper ty ctx'
	in
	helper ty (List.rev ctx)

(*
let rec find_any_true ctx =
	match (List.rev ctx) with
	(*match ctx with*)
	| [] -> Error () 
	| (y, _, b) :: ctx' -> 
		if b then 
			Ok y
		else 
			find_any_true ctx'
*)

(* Prints the context *)

let print ctx = 
	let rec printrev = function
		| [] -> "" 
		| (id, ty, _) :: ctx' -> 
			" " ^ id ^ " : " ^ Pretty.print ty ^ "\n" ^ printrev ctx'
	in
	printrev (List.rev ctx)


