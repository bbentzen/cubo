(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Implements substituition of variables and full terms
 **)

(* Return the least fresh variable of the form v0,..,vn not occuring in two given expressions *)

let rec has_var x = function
	| Ast.Id y -> 
		if x = y then true else false
	| Ast.Abs (y, e) | Ast.Pabs (y, e) -> 
		if x = y then true else has_var x e
	| Ast.Pi (y, e1, e2) | Ast.Sigma (y, e1, e2) -> 
		if x = y then true else has_var x e1 || has_var x e2
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> 
		has_var x e
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> 
		has_var x e1 || has_var x e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) -> 
		has_var x e || has_var x e1 || has_var x e2
	| Ast.Type _ -> false
	| Ast.Hole (_, l) ->
		let rec helper = function
		| [] -> false
		| e :: l' ->
			has_var x e || helper l' in
			helper l
	| _ -> false

let fresh_var_int e = 
	let rec helper i e =
		if has_var ("v" ^ string_of_int i) e = true then 
			helper (i+1) e 
		else i 
	in	(* not free_var *)
	helper 0 e

let fresh_var e1 e2 i = 
	"v" ^ string_of_int (fresh_var_int (Ast.App (e1, e2)) + i)

(* Replaces all occurrences of x with t in a given expression *)

let rec presubst x t hole_flag = function
	| Ast.Id y -> if x = y then t else Ast.Id y
	| Ast.I0() -> Ast.I0()
	| Ast.I1() -> Ast.I1()
	| Ast.Int() -> Ast.Int()
	| Ast.Abs (y, e) -> 
		if x = y then 
			Ast.Abs (y, e) 
		else 
			Ast.Abs (y, presubst x t hole_flag e)
	| Ast.App (e1, e2) -> Ast.App (presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Pi (y, e1, e2) -> 
		if x = y then 
			Ast.Pi (y, e1, e2) 
		else 
			Ast.Pi (y, presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Pair (e1, e2) -> 
		Ast.Pair (presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Fst e -> Ast.Fst (presubst x t hole_flag e)
	| Ast.Snd e -> Ast.Snd (presubst x t hole_flag e)
	| Ast.Sigma (y, e1, e2) ->
		if x = y then
			Ast.Sigma (y, e1, e2) 
		else 
			Ast.Sigma (y, presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Inl e -> Ast.Inl (presubst x t hole_flag e)
	| Ast.Inr e -> Ast.Inr (presubst x t hole_flag e)
	| Ast.Case (e, e1, e2) -> 
		Ast.Case (presubst x t hole_flag e, presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Sum (e1, e2) -> 
		Ast.Sum (presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Zero() -> Ast.Zero()
	| Ast.Succ e -> Ast.Succ (presubst x t hole_flag e)
	| Ast.Natrec (e, e1, e2) -> 
		Ast.Natrec (presubst x t hole_flag e, presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Nat() -> Ast.Nat()
	| Ast.True() -> Ast.True()
	| Ast.False() -> Ast.False()
	| Ast.If (e, e1, e2) -> 
		Ast.If (presubst x t hole_flag e, presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Bool() -> Ast.Bool()
	| Ast.Star() -> Ast.Star()
	| Ast.Let (e, e1) -> Ast.Let (presubst x t hole_flag e, presubst x t hole_flag e1)
	| Ast.Unit() -> Ast.Unit()
	| Ast.Abort e -> Ast.Abort (presubst x t hole_flag e)
	| Ast.Void() -> Ast.Void()
	| Ast.Pabs (y, e) -> 
		if x = y then 
			Ast.Pabs (y, e) 
		else 
			Ast.Pabs (y, presubst x t hole_flag e)
	| Ast.At (e1, e2) -> 
		Ast.At (presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Pathd (e, e1, e2) -> 
		Ast.Pathd (presubst x t hole_flag e, presubst x t hole_flag e1, presubst x t hole_flag e2)
	| Ast.Type n -> Ast.Type n
	| Ast.Hole (n, l) ->
		if hole_flag then
		(let rec helper = function
		| [] -> []
		| e :: l' ->
			presubst x t hole_flag e :: helper l' in
			Ast.Hole (n, helper l))
		else Ast.Hole (n, l)
	| Ast.Wild() -> Ast.Wild()

let rec free_var x = function
	| Ast.Id y -> 
		if x = y then true else false
	| Ast.Abs (y, e) | Ast.Pabs (y, e) -> 
		if x = y then false else free_var x e
	| Ast.Pi (y, e1, e2) | Ast.Sigma (y, e1, e2) -> 
		if x = y then false else free_var x e1 || free_var x e2
	| Ast.Fst e | Ast.Snd e | Ast.Inl e | Ast.Inr e | Ast.Succ e | Ast.Abort e -> 
		free_var x e
	| Ast.App (e1, e2) | Ast.Pair (e1, e2) | Ast.Sum (e1, e2) | Ast.Let (e1, e2) | Ast.At(e1, e2) -> 
		free_var x e1 || free_var x e2
	| Ast.Case (e, e1, e2) | Ast.Natrec (e, e1, e2) | Ast.If (e, e1, e2) | Ast.Pathd (e, e1, e2) -> 
		free_var x e || free_var x e1 || free_var x e2
	| Ast.Type _ -> false
	| Ast.Hole (_, l) ->
		let rec helper = function
		| [] -> false
		| e :: l' ->
			free_var x e || helper l' in
			helper l
	| _ -> false

let rec alphasubst x t flag hole_flag = function
	| Ast.Id y -> 
		if flag = true then 
		if x = y then t else Ast.Id y 
		else 
			Ast.Id y
	| Ast.I0() -> Ast.I0()
	| Ast.I1() -> Ast.I1()
	| Ast.Int() -> Ast.Int()
	| Ast.Abs (y, e) ->
		let var = fresh_var e t 0 in
		if x = y then Ast.Abs (y, e) else 
			if free_var y t = true 
			then Ast.Abs (var, alphasubst y (Ast.Id var) true hole_flag e)
			else Ast.Abs (y, (alphasubst x t flag hole_flag e))
	| Ast.App (e1, e2) -> Ast.App (alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Pi (y, e1, e2) ->
  	let var = fresh_var (Ast.App (e1, e2)) t 0 in
		if x = y then Ast.Pi (y, e1, e2) else 
			if free_var y t = true 
			then Ast.Pi (var, alphasubst y (Ast.Id var) true hole_flag e1, alphasubst y (Ast.Id var) true hole_flag e2)
			else Ast.Pi (y, alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Pair (e1, e2) -> Ast.Pair (alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Fst e -> Ast.Fst (alphasubst x t flag hole_flag e)
	| Ast.Snd e -> Ast.Snd (alphasubst x t flag hole_flag e)
	| Ast.Sigma (y, e1, e2) ->
  	let var = fresh_var (Ast.App (e1, e2)) t 0 in
		if x = y then Ast.Sigma (y, e1, e2) else 
			if free_var y t = true 
			then Ast.Sigma (var, alphasubst y (Ast.Id var) true hole_flag e1, alphasubst y (Ast.Id var) true hole_flag e2)
			else Ast.Sigma (y, alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Inl e -> Ast.Inl (alphasubst x t flag hole_flag e)
	| Ast.Inr e -> Ast.Inr (alphasubst x t flag hole_flag e)
	| Ast.Case (e, e1, e2) -> 
		Ast.Case (alphasubst x t flag hole_flag e, alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Sum (e1, e2) -> 
		Ast.Sum (alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Zero() -> Ast.Zero()
	| Ast.Succ e -> Ast.Succ (alphasubst x t flag hole_flag e)
	| Ast.Natrec (e, e1, e2) -> 
		Ast.Natrec (alphasubst x t flag hole_flag e, alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Nat() -> Ast.Nat()
	| Ast.True() -> Ast.True()
	| Ast.False() -> Ast.False()
	| Ast.If (e, e1, e2) -> 
		Ast.If (alphasubst x t flag hole_flag e, alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Bool() -> Ast.Bool()
	| Ast.Star() -> Ast.Star()
	| Ast.Let (e, e1) -> Ast.Let (alphasubst x t flag hole_flag e, alphasubst x t flag hole_flag e1)
	| Ast.Unit() -> Ast.Unit()
	| Ast.Abort e -> Ast.Abort (alphasubst x t flag hole_flag e)
	| Ast.Void() -> Ast.Void()
	| Ast.Pabs (y, e) ->
		let var = fresh_var e t 0 in
		if x = y then Ast.Pabs (y, e) else 
			if free_var y t = true 
			then Ast.Pabs (var, alphasubst y (Ast.Id var) true hole_flag e)
			else Ast.Pabs (y, alphasubst x t flag hole_flag e)
	| Ast.At (e1, e2) -> Ast.At (alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Pathd (e, e1, e2) -> 
		Ast.Pathd (alphasubst x t flag hole_flag e, alphasubst x t flag hole_flag e1, alphasubst x t flag hole_flag e2)
	| Ast.Type n -> Ast.Type n
	| Ast.Hole (n, l) ->
		if hole_flag then
		let rec helper = function
		| [] -> []
		| e :: l' ->
			alphasubst x t flag hole_flag e :: helper l' in
			Ast.Hole (n, helper l)
		else Ast.Hole (n, l)
	| Ast.Wild n -> Ast.Wild n

let hsubst x t e hole_flag = presubst x t hole_flag (alphasubst x t false hole_flag e) 

let subst x t e = hsubst x t e true

let rec termsubst e t hole_flag = function
	| Ast.Id y -> hsubst y t e hole_flag
	| ex ->
		if e = ex 
		then t 
		else match e with
		| Ast.Id e -> if ex = Ast.Id e then t else Ast.Id e
		| Ast.Abs (y, e1) ->
			let var = fresh_var t t 0 in
			if not (free_var y e1)
			then if ex = e1
				then Ast.Abs (y, hsubst y (Ast.Id var) t hole_flag) 
				else Ast.Abs (y, termsubst e1 t hole_flag ex)
			else Ast.Abs (y, e1)
		| Ast.App (e1, e2) -> 
			if ex = e1 
			then if ex = e2 
				then Ast.App (t, t) 
				else Ast.App (t, termsubst e2 t hole_flag ex)
			else 
				if ex = e2 
				then Ast.App (termsubst e1 t hole_flag ex, t) 
				else Ast.App (termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Pi (y, e1, e2) ->
			let var = fresh_var t t 0 in
			if not (free_var y ex) 
			then if ex = e1 
				then if ex = e2 then Ast.Pi (y, hsubst y (Ast.Id var) t hole_flag, hsubst y (Ast.Id var) t hole_flag) 
				else Ast.Pi (y, hsubst y (Ast.Id var) t hole_flag, termsubst e2 t hole_flag ex) 
			else if ex = e2 
				then Ast.Pi (y, termsubst e1 t hole_flag ex, hsubst y (Ast.Id var) t hole_flag) 
				else Ast.Pi (y, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
			else Ast.Pi (y, e1, e2)
		| Ast.Pair (e1, e2) -> 
			if ex = e1 
			then if ex = e2 
				then Ast.Pair (t, t) 
				else Ast.Pair (t, termsubst e2 t hole_flag ex)
			else 
				if ex = e2 
				then Ast.Pair (termsubst e1 t hole_flag ex, t) 
				else Ast.Pair (termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Fst e -> 
			if ex = e 
			then Ast.Fst t
			else Ast.Fst (termsubst e t hole_flag ex)
		| Ast.Snd e -> 
			if ex = e 
			then Ast.Snd t
			else Ast.Snd (termsubst e t hole_flag ex)
		| Ast.Sigma (y, e1, e2) ->
			let var = fresh_var t t 0 in
			if not (free_var y ex) 
			then if ex = e1 
				then if ex = e2 then Ast.Sigma (y, hsubst y (Ast.Id var) t hole_flag, hsubst y (Ast.Id var) t hole_flag) 
				else Ast.Sigma (y, hsubst y (Ast.Id var) t hole_flag, termsubst e2 t hole_flag ex) 
			else if ex = e2 
				then Ast.Sigma (y, termsubst e1 t hole_flag ex, hsubst y (Ast.Id var) t hole_flag) 
				else Ast.Sigma (y, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
			else Ast.Sigma (y, e1, e2)
		| Ast.Inl e -> 
			if ex = e 
			then Ast.Inl t
			else Ast.Inl (termsubst e t hole_flag ex)
		| Ast.Inr e -> 
			if ex = e 
			then Ast.Inr t
			else Ast.Inr (termsubst e t hole_flag ex)
		| Ast.Case (e, e1, e2) -> 
			if ex = e
			then if ex = e1 
				then if ex = e2 
					then Ast.Case (t, t, t) 
					else Ast.Case (t, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.Case (t, termsubst e1 t hole_flag ex, t)
					else Ast.Case (t, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
			else if ex = e1 
				then if ex = e2 
					then Ast.Case (termsubst e t hole_flag ex, t, t) 
					else Ast.Case (termsubst e t hole_flag ex, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.Case (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, t)
					else Ast.Case (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Sum (e1, e2) -> 
			if ex = e1 
			then if ex = e2 
				then Ast.Sum (t, t) 
				else Ast.Sum (t, termsubst e2 t hole_flag ex)
			else if ex = e2 
				then Ast.Sum (termsubst e1 t hole_flag ex, t) 
				else Ast.Sum (termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Succ e -> 
			if ex = e 
			then Ast.Succ t
			else Ast.Succ (termsubst e t hole_flag ex)
		| Ast.Natrec (e, e1, e2) -> 
			if ex = e
			then if ex = e1 
				then if ex = e2 
					then Ast.Natrec (t, t, t) 
					else Ast.Natrec (t, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.Natrec (t, termsubst e1 t hole_flag ex, t)
					else Ast.Natrec (t, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
			else if ex = e1 
				then if ex = e2 
					then Ast.Natrec (termsubst e t hole_flag ex, t, t) 
					else Ast.Natrec (termsubst e t hole_flag ex, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.Natrec (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, t)
					else Ast.Natrec (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.If (e, e1, e2) -> 
			if ex = e
			then if ex = e1 
				then if ex = e2 
					then Ast.If (t, t, t) 
					else Ast.If (t, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.If (t, termsubst e1 t hole_flag ex, t)
					else Ast.If (t, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
			else if ex = e1 
				then if ex = e2 
					then Ast.If (termsubst e t hole_flag ex, t, t) 
					else Ast.If (termsubst e t hole_flag ex, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.If (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, t)
					else Ast.If (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Let (e1, e2) -> 
			if ex = e1 
			then if ex = e2 
				then Ast.Let (t, t) 
				else Ast.Let (t, termsubst e2 t hole_flag ex)
			else 
				if ex = e2 
				then Ast.Let (termsubst e1 t hole_flag ex, t) 
				else Ast.Let (termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Abort e -> 
				if ex = e 
				then Ast.Abort t
				else Ast.Abort (termsubst e t hole_flag ex)
		| Ast.Pabs (y, e1) ->
			let var = fresh_var t t 0 in
			if not (free_var y e1)
			then if ex = e1
				then Ast.Pabs (y, hsubst y (Ast.Id var) t hole_flag) 
				else Ast.Pabs (y, termsubst e1 t hole_flag ex)
			else Ast.Pabs (y, e1)
		| Ast.At (e1, e2) -> 
			if ex = e1 
			then if ex = e2 
				then Ast.At (t, t) 
				else Ast.At (t, termsubst e2 t hole_flag ex)
			else 
				if ex = e2 
				then Ast.At (termsubst e1 t hole_flag ex, t) 
				else Ast.At (termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Pathd (e, e1, e2) -> 
			if ex = e
			then if ex = e1 
				then if ex = e2 
					then Ast.Pathd (t, t, t) 
					else Ast.Pathd (t, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.Pathd (t, termsubst e1 t hole_flag ex, t)
					else Ast.Pathd (t, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
			else if ex = e1 
				then if ex = e2 
					then Ast.Pathd (termsubst e t hole_flag ex, t, t) 
					else Ast.Pathd (termsubst e t hole_flag ex, t, termsubst e2 t hole_flag ex)
				else if ex = e2 
					then Ast.Pathd (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, t)
					else Ast.Pathd (termsubst e t hole_flag ex, termsubst e1 t hole_flag ex, termsubst e2 t hole_flag ex)
		| Ast.Hole (n, l) ->
			if hole_flag then
				let rec helper = function
					| [] -> []
					| e :: l' ->
						termsubst e t hole_flag ex :: helper l' in
				Ast.Hole (n, helper l)
			else Ast.Hole (n, l)
		| e -> e

let fullsubst e1 t e2 = 
	termsubst e2 t true e1

let hfullsubst e1 t e2 = 
	termsubst e2 t false e1