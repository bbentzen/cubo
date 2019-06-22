(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Call-by-name prenormalization
 *       Performs full β-reduction on β-redexes of all types,
 *       η-reduction for dependent functions and paths,
 *       but not ε-reduction for dependent paths.
 **)

open Substitution

(* Returns a value and a flag determining whether there was a reduction *)

let rec has_reduction = function

	| Ast.Coe (i, j, Ast.Abs(k, Pi(x, ty1, ty2)), e) ->	
		let v1 = fresh_var (Pi(x, ty1, ty2)) e 2 in
		let c x = Ast.Coe (j, x, Ast.Abs(k, ty1), Id v1) in
		Ast.Abs(v1, Ast.Coe (i, j, Ast.Abs(k, subst x (c (Id k)) ty2), App(e, c i))), true
	
	| Ast.Coe (i, j, Ast.Abs(k, Sigma(x, ty1, ty2)), e) ->	
		let c x = Ast.Coe (i, x, Ast.Abs(k, ty1), Ast.Fst e) in
		Ast.Pair(c j, Ast.Coe (i, j, Ast.Abs(k, subst x (c (Id k)) ty2), Snd e)), true

	| Ast.Coe (i, j, Ast.Abs(k, Pathd(Abs(v, ty), e1, e2)), e) ->	(* Non-dependent paths *)
		if Substitution.has_var k ty = false then
			let v1 = Substitution.fresh_var (Ast.App(e1, e2)) e 2 in
			Ast.Pabs(v1, Ast.App(Ast.App (Ast.Hfill(
			Ast.Abs(v1, Ast.At(e, Ast.Id v1)), 
			Ast.Abs(k, subst k i e1),
			Ast.Abs(k, subst k i e2)),
			I1()), Id v1)), true
		else
			let v1 = Substitution.fresh_var (Ast.App(e1, e2)) e 2 in
			let v2 = Substitution.fresh_var (Ast.App(e1, e2)) e 3 in
			Ast.Pabs(v1, Ast.App(Ast.App (Ast.Hfill(
			Ast.Abs(v2, Coe(Id v2, Id v1,  Abs(k, subst v (Id k) (subst k j ty)), Ast.Coe (i, j, Abs(k, subst v (Id v2) ty), Ast.At(e, Ast.Id v2)))), 
			Ast.Abs(k, Coe(I0(), Id v1,  Abs(k, subst v (Id k) (subst k j ty)), subst k j e1)),
			Ast.Abs(k, Coe(I1(), Id v1,  Abs(k, subst v (Id k) (subst k j ty)), subst k j e2))),
			I1()), Id v1)), true
	
	| Ast.Coe (i, j, Ast.Abs(k, Pathd(ty, e1, e2)), e) ->	
		let v1 = Substitution.fresh_var (Ast.App(e1, e2)) e 2 in
		let v2 = Substitution.fresh_var (Ast.App(e1, e2)) e 3 in
		Ast.Pabs(v1, Ast.App(Ast.App (Ast.Hfill(
		Ast.Abs(v2, Coe(Id v2, Id v1,  Abs(k, App(subst k j ty, Id k)), Ast.Coe (i, j, Abs(k, App(ty, Id v2)), Ast.At(e, Ast.Id v2)))), 
  	Ast.Abs(k, Coe(I0(), Id v1,  Abs(k, App(subst k j ty, Id k)), subst k j e1)),
		Ast.Abs(k, Coe(I1(), Id v1,  Abs(k, App(subst k j ty, Id k)), subst k j e2))),
		I1()), Id v1)), true

	| Ast.Coe (i, j, e1, e2) ->
		let coe' = 
			Ast.Coe (fst (has_reduction i), fst (has_reduction j), fst (has_reduction e1), fst (has_reduction e2)), 
			snd (has_reduction i) || snd (has_reduction j) || snd (has_reduction e1) || snd (has_reduction e2)
		in
		begin
			if fst (has_reduction i) = fst (has_reduction j) then
				e2, true
			else
				match e1 with
				| Ast.Abs(k, e) -> 
					if Substitution.has_var k e then
						coe'
					else 
						e2, true
				| _ -> 
					coe'
		end
	
	| Ast.Hfill (e, e1, e2) -> 
		Ast.Hfill (fst (has_reduction e), fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e) || snd (has_reduction e1) || snd (has_reduction e2)
	
	| Ast.App (Ast.Hfill (e, _, _), Ast.I0()) -> e, true

	| Ast.App (Ast.App (Ast.Hfill (_, e1, _), i), Ast.I0()) -> fst (has_reduction (Ast.App(e1, i))), true

	| Ast.App (Ast.App (Ast.Hfill (_, _, e2), i), Ast.I1()) -> fst (has_reduction (Ast.App(e2, i))), true

	| Ast.Abs (x, e) -> 
		begin 
			match e with
			| Ast.App (e1 , e2) ->
				if e2 = Ast.Id x && not (has_var x e1) then 
					fst (has_reduction e1), true
				else 
					Ast.Abs (x, fst (has_reduction e)), snd (has_reduction e)
			| _ -> Ast.Abs (x, fst (has_reduction e)), snd (has_reduction e)
		end

	| Ast.App (e1, e2) -> 
		begin 
			match e1 with
			| Ast.Abs (x , e) -> subst x e2 (fst (has_reduction e)), true
			| _ -> 
				Ast.App (fst (has_reduction e1), fst (has_reduction e2)), 
				snd (has_reduction e1) || snd (has_reduction e2)
		end

	| Ast.Pair (e1, e2) ->
		begin
			match e1, e2 with
			| Fst e1', Snd e2' ->
				if e1' = e2' then
					e1', true
				else
					Ast.Pair (fst (has_reduction e1), fst (has_reduction e2)),
					snd (has_reduction e1) || snd (has_reduction e2)
			| _ ->
				Ast.Pair (fst (has_reduction e1), fst (has_reduction e2)),
				snd (has_reduction e1) || snd (has_reduction e2)
		end

	| Ast.Fst e ->
		begin 
			match e with
			| Ast.Pair (e1 , _) -> (e1, true)
			| _ -> Ast.Fst (fst (has_reduction e)), snd (has_reduction e)
		end

	| Ast.Snd e -> 
		begin
			match e with
			| Ast.Pair (_ , e2) -> (e2, true)
			| _ -> Ast.Snd (fst (has_reduction e)), snd (has_reduction e)
		end

	| Ast.Inl e -> 
		Ast.Inl (fst (has_reduction e)), snd (has_reduction e)

	| Ast.Inr e -> 
		Ast.Inr (fst (has_reduction e)), snd (has_reduction e)

	| Ast.Case (e, e1, e2) -> 
		begin
			match e with
			| Ast.Inl a -> Ast.App (e1,a), true
			| Ast.Inr b -> Ast.App (e2,b), true
			| _ -> 
				Ast.Case (fst (has_reduction e), fst (has_reduction e1), fst (has_reduction e2)), 
				snd (has_reduction e) || snd (has_reduction e1) || snd (has_reduction e2)
		end

	| Ast.Succ e -> 
		Ast.Succ (fst (has_reduction e)), snd (has_reduction e)

	| Ast.Natrec (e, e1, e2) -> 
		begin 
			match e with
			| Ast.Zero() -> e1, true
			| Ast.Succ k -> Ast.App (Ast.App (e2,k),Natrec(k,e1,e2)), true
			| _ -> 
				Ast.Natrec (fst (has_reduction e), fst (has_reduction e1), fst (has_reduction e2)), 
				snd (has_reduction e) || snd (has_reduction e1) || snd (has_reduction e2)
		end

	| Ast.If (e, e1, e2) -> 
		begin
			match e with
			| Ast.True() -> e1, true
			| Ast.False() -> e2, true
			| _ -> 
				Ast.If (fst (has_reduction e), fst (has_reduction e1), fst (has_reduction e2)), 
				snd (has_reduction e) || snd (has_reduction e1) || snd (has_reduction e2)
		end

	| Ast.Let (e, e1) -> 
		begin
			match e with
			| Ast.Star() -> e1, true
			| _ -> Ast.Let (fst (has_reduction e), e1), snd (has_reduction e)
		end

	| Ast.Pabs (x, e) -> 
		begin 
			match e with
			| Ast.At (e1 , e2) ->
				if e2 = Ast.Id x && not (free_var x e1) then 
					fst (has_reduction e1), true
				else 
					Ast.Pabs (x, fst (has_reduction e)), snd (has_reduction e)
			| _ -> 
				Ast.Pabs (x, fst (has_reduction e)), snd (has_reduction e)
		end

	| Ast.At (e1, e2) -> 
		begin
			match e1 with
			| Ast.Pabs (x , e) -> (subst x e2 (fst (has_reduction e)), true)
			| _ -> 
				Ast.At (fst (has_reduction e1), fst (has_reduction e2)), 
				snd (has_reduction e1) || snd (has_reduction e2)
		end
	
	| Ast.Pi (x, e1, e2) -> 
		Ast.Pi (x, fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e1) || snd (has_reduction e2)

	| Ast.Sigma (x, e1, e2) -> 
		Ast.Sigma (x, fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e1) || snd (has_reduction e2)

	| Ast.Sum (e1, e2) -> 
		Ast.Sum (fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e1) || snd (has_reduction e2)

	| Ast.Pathd (e, e1, e2) -> 
		Ast.Pathd (fst (has_reduction e), fst (has_reduction e1), fst (has_reduction e2)), 
		snd (has_reduction e)|| snd (has_reduction e1) || snd (has_reduction e2)

	| e -> (e , false)

(* Eager prereduction: does not reduce ε-redexes *)

let reduce e = fst (has_reduction e)

(* Returns the value of an expression (may not terminate if expression is ill-typed) *)

let rec eval e =
	if snd (has_reduction e) = false
	then reduce e
	else eval (reduce e)
