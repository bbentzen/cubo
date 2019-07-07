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

let rec compile global lopen filename lvl = function
	| Ast.Thm (cmd, Prf (id, l, ty, e)) ->
		begin
			match Global.unfold_all global 0 (Synth.convert ty) with
			| Ok hty ->
				let ctx = Local.create_ctx l in
				let h1 = Ctx.check global ctx lvl in
				let h2 = Type.check global ctx lvl (reduce hty) in
				begin 
					match h1, h2 with
					| Ok l, Ok (ty', _) -> 
						let ctx' = List.rev l in
						begin 
							match Global.unfold_all global 0 (Synth.convert e) with
							| Ok e' ->
								if Global.is_declared id global then 
									Error ("Naming conflict with the identifier '" ^ id ^ 
										"'\nName already exists in the environment (try 'print " ^ id ^ "' for more information)")
								else
									(* let elab = Elab.elaborate global ctx' lvl ([], []) (eval ty') 0 0 (reduce e') in *)
									(* let elab = Check.wild global ctx' lvl ([], []) e' ty' in *)
									let elab = Check.init global ctx' lvl e' ty' in
									begin 
										match elab with 
										| Ok (e1, ty1) ->
											compile (Global.add_to_global_env global id ctx' (e1, ty1)) lopen filename lvl cmd
										| Error msg -> 
											Error ("The following error was found at '" ^ id ^ "'\n" ^ msg)
									end
								| Error msg -> 
									Error msg
								end
						| Error msg, _ | _, Error msg -> 
							Error ("The following error was found at '" ^ id ^ "'\n" ^ msg) 
					end
				| Error msg -> 
					Error msg
		end

	| Ast.Print (cmd, id) -> 
		begin 
			match Global.check_def_id id global with
			| Ok (e, ty) ->
				begin 
					match compile global lopen filename lvl cmd with
					| Ok (global', (s, lopen)) -> 
						Ok (global', (id ^ " := \n  " ^ Pretty.print (e) ^ ": \n  " ^ 
							Pretty.print (Eval.eval ty) ^ "\n" ^ s, lopen))
						(* Ok (global', (id ^ " := \n  " ^ Pretty.print (Eval.eval e) ^ ": \n  " ^ 
							Pretty.print (Eval.eval ty) ^ "\n" ^ s, lopen)) *)
					| Error msg -> 
						Error msg
				end
			| Error msg -> 
				Ok (global, ("Error: " ^ msg, lopen))
		end
	
	| Ast.Infer (cmd, e) ->
		let h1 = Placeholder.generate e 0 [] in
		let elab = Elab.elaborate global [] lvl ([], []) h1 0 0 e in 
		begin 
			match elab with
			| Ok (e, ty, _) ->
				begin 
					match compile global lopen filename lvl cmd with
					| Ok (global', (s, lopen)) -> 
						Ok (global', ("infer := " ^ Pretty.print e ^ ": \n" ^
							"         " ^ Pretty.print ty ^ 
							"\n" ^ s, lopen))
					| Error msg -> Error msg
				end
			| Error (_, msg) -> 
				Ok (global, ("Error: " ^ msg, lopen))
		end
	
	| Ast.Import (cmd, s) ->
		let cd = File.parent filename in
		let path' = File.read_dir cd s in
		if List.mem path' lopen then
			compile global lopen filename lvl cmd
		else
			begin 
				match checkfile global lopen path' lvl with
				| Ok (global', (_, lopen')) -> 
					compile global' (path' :: lopen') filename lvl cmd
				| Error s -> 
					Error ("Failed to open the file '" ^ path' ^ "'\n" ^ s)
			end
	
	| Ast.Level (cmd, lvl') ->
		compile global lopen filename (lvl @ lvl') cmd

	| Ast.Eof() -> Ok (global, ("", lopen))

and checkfile global lopen filename lvl =
	compile global lopen filename lvl (parse_file filename)
