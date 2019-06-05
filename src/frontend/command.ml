(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Executes the commands described in a file
 *       Sucessfully type-checked terms are stored in a global context
 **)

open Basis
open Checker
open Eval
open File
open Context

let rec compile global = function
	| Ast.Thm (cmd, Prf (id, l, ty, e)) ->
		let ctx = Local.create_ctx l in
		begin match Global.unfold_all global 0 ty with
		| Ok ty'' ->
			let cctx = Ctx.check global ctx in
			let cty = Type.check global ctx (reduce ty'') in
			begin match cctx, cty with
			| Ok l, Ok (ty', _) -> 
				let ctx' = List.rev l in
				begin match Global.unfold_all global 0 e with
				| Ok e' ->
					if Global.is_declared id global then 
						Error ("Naming conflict with the identifier '" ^ id ^ 
									"'\nName already exists in the environment (try 'print " ^ id ^ "' for more information)")
					else
						let elab = Elab.elaborate global ctx' (eval ty') 0 0 (reduce e') in
						begin match elab with 
						| Ok elab ->
							compile (Global.add_to_global_env global id ctx' elab) cmd
						| Error msg -> 
							Error ("The following error has been found at '" ^ id ^ "'\n" ^ msg)
						end
					| Error msg -> Error msg
					end
			| Error msg, _ | _, Error msg -> 
				Error ("The following error has been found at '" ^ id ^ "'\n" ^ msg) 
			end
		| Error msg -> Error msg
		end

	| Ast.Print (cmd, id) -> 
		begin match Global.check_def_id id global with
		| Ok (e, ty) ->
			begin match compile global cmd with
			| Ok res -> 
				Ok (fst res, 
						id ^ " := " ^ Ast.unparse e ^ ": \n" ^
						String.make (String.length id + 4) ' ' ^ Ast.unparse ty ^ 
						"\n" ^ snd res)
			| Error s -> Error s
			end
		| Error s -> Ok (global, "Error: " ^ s)
		end
	
	| Ast.Infer (cmd, e) ->
		let h1 = Hole.generate e 0 [] in
		let elab = Elab.elaborate global [] h1 0 0 e in 
		begin match elab with
		| Ok (e, ty) ->
			begin match compile global cmd with
			| Ok res -> 
				Ok (fst res, 
						"infer := " ^ Ast.unparse e ^ ": \n" ^
						"         " ^ Ast.unparse ty ^ 
						"\n" ^ snd res)
			| Error s -> Error s
			end
		| Error s -> Ok (global, "Error: " ^ s)
		end
		
	| Ast.Eof() -> Ok (global, "")

let checkfile filename = 
	compile [] (parse_string (concat_string_list (read_file filename)))
