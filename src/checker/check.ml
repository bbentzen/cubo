(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Synthesizes placeholders for expressions and universe levels,
         Based on an exhaustive search using the context 
 **)

open Basis

(* Iteration and placeholder synthesis *)

let rec wild global ctx lvl sl e ty max =
  let elab = Elab.elaborate global ctx lvl sl (Eval.eval ty) 0 0 (Eval.reduce e) in
	begin
    match elab with
		| Ok (e', ty', sl') -> (* TODO: improve performance *)
			(* Error ("worked\n----\n" ^ Pretty.print e' ^ "\n" ^ Pretty.print ty' ^ "\n" ^ Elab.printsl (snd sl')) *)

			let relab = Elab.elaborate global ctx lvl sl ty' 0 0 e' in
			begin
				match relab with
				| Ok _ -> 
					Ok (e', ty')
				| Error (_, msg) -> 
					iter sl' msg global ctx lvl e ty (max+1)
			end
			
		
		| Error (sl', msg) ->
			iter sl' msg global ctx lvl e ty (max+1)
	end

and iter sl' msg global ctx lvl e ty max =
	if max > 100 then
		Error "Maximum number of synthetization steps reached
			\n(You should not see this message, please report)"
	else

		match (fst sl') with
		| [] ->
			(* ----------------------------------------------------------------*)
			Error (msg ^ "\n----\n" ^ Elab.printsl (snd sl'))
		
		| (n, id, _) :: _ ->

			begin match Synth.find_index n (snd sl') with 
			| Ok _ -> (* ll *)

				let e' = Substitution.prefull (Wild n) (Id id) e in
				let w = wild global ctx lvl ([], snd sl') e' ty max in
				begin 
					match w with
					| Ok (e', ty') ->
						Ok (e', ty')
					| Error _ -> (* msg *)
						
						wild global ctx lvl ([], Synth.mkfalse n id (snd sl')) e ty max

					end
					
			| Error _ ->
				Error ("Can't find stack for the placeholder '?" ^ id ^ 
				"'\n(You should not see this message, please report)\n")
			end

let init global ctx lvl e ty =
	wild global ctx lvl ([], []) e ty 0
	