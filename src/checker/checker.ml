(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The elaborator of the program
 **)

open Basis
open Ast
open Substitution
open Synth
open Eval 

(* Determines whether a given typed variable occurs in the context *)

let rec check_var_ty x ty ctx =
  match (List.rev ctx) with
  | [] -> false 
  | (y, ty') :: ctx' -> 
    if x = y && ty' = ty
    then true
    else check_var_ty x ty ctx'

(* Finds a variable of a given typed in the context when it exists *)

let rec find_ty ty ctx =
  match (List.rev ctx) with
  | [] -> Error "" 
  | (y, ty') :: ctx' -> 
    if ty' = ty
    then Ok y
    else find_ty ty ctx'

(* Checks whether the type of a given expression is the given type *)

let rec elaborate ctx ty ph vars = function
  | Id x ->
    let ty' = infer_var_ty x ctx in
    (match check_var_ty x ty ctx, is_placeholder ty', is_declared x ctx with
    | true , _ , _ | _ , true , _ ->  Ok (Id x, ty)
    | false , false , true -> 
      if synthesize vars (ty', ty) 
      then Ok (Id x, ty') 
      else Error ("Failed to synthesize the types " ^ unparse ty' ^ "and " ^ unparse ty)
    | false , false , false -> 
      Error ("No declaration found for identifier " ^ x))
  | I0() ->
    (match ty with
    | Ast.Int() -> Ok (I0(), Int())
    | Hole _ -> Ok (I0(), Int())
    | _ -> Error ("Type mismatch when checking that the term i0 of type I has type " ^ unparse ty))
  | I1() ->
    (match ty with
    | Ast.Int() -> Ok (I1(), Int())
    | Hole _ -> Ok (I1(), Int())
    | _ -> Error ("Type mismatch when checking that the term i1 of type I has type " ^ unparse ty))
  | Abs (x, e) -> 
    (match ty with
    | Pi (y, ty1, ty2) -> 
      (match elaborate ((x, ty1) :: ctx) (subst y (Ast.Id x) ty2) ph vars e with
      | Ok elab -> Ok (Abs (x, fst elab), Pi (y, ty1, snd elab))
      | Error msg -> Error msg )
    | Hole _ -> 
      let p = generate_placeholder ty + ph in
      elaborate ctx (Pi(x,(Hole (string_of_int p)),(Hole (string_of_int (p+1))))) (ph+2) vars (Abs (x, e))
    | _ -> 
      Error ("Type mismatch when checking that the term λ " ^ x ^ ", " ^ unparse e ^ "of type Π (v? : ?0?) ?1? has type " ^ unparse ty))
  | App (e1, e2) ->
    let p = generate_placeholder ty + ph in
    let var = fresh_var (App(e1, e2)) ty vars in
    (match elaborate ctx (Hole (string_of_int p)) (ph+1) (vars+1) e2 with
    | Ok elab2 -> 
      (match elaborate ctx (Pi(var, (snd elab2), fullsubst e2 (Id var) ty)) (ph+1) (vars+1) e1 with
      | Ok elab1 ->
        (match snd elab1 with
        | Pi(x, _, ty') -> 
          Ok (App (fst elab1, fst elab2), subst x e2 ty') (* Recovers the synthesized type *)
        | _ -> 
        Error ("Type mismatch when checking that the term " ^ unparse e1 ^ " of type Π (v? : ?0?) ?1? has type " ^ unparse ty)) 
      | Error msg -> Error msg)
    | Error msg -> Error msg)
  | Pair (e1, e2) -> 
    (match ty with
    | Sigma(y, ty1, ty2) ->
      (match elaborate ctx ty1 ph vars e1, elaborate ctx (subst y e1 ty2) ph vars e2 with
      | Ok elab1, Ok elab2 ->
        let gen_ty = fullsubst (fst elab1) (Id y) (snd elab2) in
        Ok (Pair (fst elab1, fst elab2), Sigma(y, snd elab1, gen_ty))
      | Error msg, _ | _, Error msg -> Error msg)
    | Hole _ -> 
      let p = generate_placeholder ty in
      let var = fresh_var (App (e1, e2)) ty vars in
      elaborate ctx (Sigma(var, (Hole (string_of_int p)), 
      (Hole (string_of_int (p+1))))) (ph+2) (vars+1) (Pair (e1, e2))
    | _ ->
      Error ("Type mismatch when checking that the term (" ^ unparse e1 ^ ", " ^ unparse e2 ^ ") of type Σ (v? : ?0?) ?1? has type " ^ unparse ty))
  | Ast.Fst e ->
    let p = generate_placeholder ty in
    let var = fresh_var e ty vars in
    (match elaborate ctx (Sigma (var, ty, Hole (string_of_int p))) (ph+1) (vars+1) e with
    | Ok elab ->
      (match snd elab with
      | Sigma(_, ty', _) -> 
        Ok (Fst (fst elab), ty') 
      | _ -> 
        Error ("Type mismatch when checking that the term " ^ unparse e ^ " of type Σ (v0 : ?0?) ?1? has type " ^ unparse ty)) 
    | Error msg -> Error msg)
    (*
    let p = generate_placeholder ty in
    let var = fresh_var e ty in
    (match elaborate ctx (Sigma (var, ty, Hole (string_of_int p))) (ph+1) vars e with
    | Ok elab -> Ok (Fst (fst elab), ty)
    | Error msg -> Error msg)
    *)
  | Snd e ->
    let p = generate_placeholder ty in
    let var = fresh_var e ty vars in
    (match elaborate ctx (Sigma (var, Hole (string_of_int p), fullsubst (Fst e) (Id var) ty)) (ph+1) (vars+1) e with
    | Ok elab -> 
      (match snd elab with
      | Sigma(x, _, ty') -> 
        Ok (Snd (fst elab), subst x (Fst e) ty') (* Recovers the synthesized type *)
      | _ -> 
        Error ("Type mismatch when checking that the term " ^ unparse e ^ " of type Σ (v0 : ?0?) ?1? has type " ^ unparse ty)) 
    | Error msg -> Error msg)
    (*
    let p = generate_placeholder ty in
    let var = fresh_var e ty vars in
    (match elaborate ctx (Sigma (var, Hole (string_of_int p), fullsubst (Fst e) (Id var) ty)) (ph+1) vars e with
    | Ok elab -> Ok (Snd (fst elab), ty)
    | Error msg -> Error msg)
    *)
  | Ast.Inl e ->
    (match ty with
    | Ast.Sum (ty1, ty2) -> 
      (match elaborate ctx ty1 ph vars e with
      | Ok elab -> Ok (Inl (fst elab), Sum(snd elab, ty2))
      | Error msg -> Error msg)
    | Hole _ ->
      let p = generate_placeholder ty in
      elaborate ctx (Sum(Hole (string_of_int p), Hole (string_of_int (p+1)))) (ph+2) vars (Inl e)
    | _ ->
      Error ("Type mismatch when checking that the term inl " ^ unparse e ^ " of type ?0? + ?1? has type " ^ unparse ty)) 
  | Ast.Inr e -> 
    (match ty with
    | Ast.Sum (ty1, ty2) -> 
      (match elaborate ctx ty2 ph vars e with
      | Ok elab -> Ok (Inr (fst elab), Sum(ty1, snd elab))
      | Error msg -> Error msg)
    | Hole _ ->
      let p = generate_placeholder ty in
      elaborate ctx (Sum(Hole (string_of_int p), Hole (string_of_int (p+1)))) (ph+2) vars (Inr e)
    | _ -> 
      Error ("Type mismatch when checking that the term inr " ^ unparse e ^ " of type ?0? + ?1? has type " ^ unparse ty)) 
  | Case (e, e1, e2) ->
    let p = generate_placeholder ty in
    (match elaborate ctx (Sum (Hole (string_of_int p), (Hole (string_of_int (p + 1))))) (ph+2) vars e with
    | Ok elab ->
      (match snd elab with
      | Sum (ty1, ty2) ->
        let var = fresh_var (Sum(ty1,ty2)) ty vars in
        (match elaborate ctx (Pi(var, ty1, fullsubst e (Inl (Id var)) ty)) ph (vars+1) e1, 
               elaborate ctx (Pi(var, ty2, fullsubst e (Inr (Id var)) ty)) ph (vars+1) e2 with
        | Ok elab1, Ok elab2 ->
          Ok (Case(fst elab, fst elab1, fst elab2), ty)
        | Error msg, _ | _, Error msg -> Error msg) 
      | _ -> Error ("Type mismatch when checking that the term " ^ unparse (fst elab) ^ " of type " ^ unparse (snd elab) ^ "has type ?0? + ?1?"))
    | Error msg -> Error msg)
  | Ast.Zero() ->
    (match ty with
    | Nat() -> Ok (Zero(), Nat())
    | Hole _ -> Ok (Zero(), Nat())
    | _ -> Error ("Type mismatch when checking that the term 0 of type nat has type " ^ unparse ty))
  | Ast.Succ e -> 
    (match elaborate ctx (Ast.Nat()) ph vars e, ty with
    | Ok elab, Ast.Nat() -> 
      Ok (Succ (fst elab), Nat())
    | Ok elab, Hole _ ->
      Ok (Succ (fst elab), Nat())
    | Error msg, _ -> Error msg
    | _, _ -> 
      Error ("Type mismatch when checking that the term succ " ^ unparse e ^ " of type nat has type " ^ unparse ty))
  | Ast.Natrec (e, e1, e2) ->
      let var1 = fresh_var (Natrec(e, e1, e2)) ty vars in
      let var2 = fresh_var (Id var1) (Id var1) vars in
      (match elaborate ctx (Ast.Nat()) ph (vars+2) e,
             elaborate ctx (fullsubst e (Ast.Zero()) ty) ph (vars+2) e1,
             elaborate ctx (Pi(var1, Nat(), Pi(var2, fullsubst e (Id var1) ty, fullsubst e (Succ (Id var1)) ty))) ph (vars+2) e2 with
      | Ok elab, Ok elab1, Ok elab2 ->        
        Ok (Natrec (fst elab, fst elab1, fst elab2), ty)
      | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> Error msg)
  | Ast.True() ->
    (match ty with
    | Ast.Bool() -> Ok (True(), Bool())
    | Hole _ -> Ok (True(), Bool()) 
    | _ -> Error ("Type mismatch when checking that the term true of type bool has type " ^ unparse ty))
  | Ast.False() ->
    (match ty with
    | Ast.Bool() -> Ok (False(), Bool())
    | Hole _ -> Ok (False(), Bool())
    | _ -> Error ("Type mismatch when checking that the term false of type bool has type " ^ unparse ty))
  | Ast.If (e, e1, e2) -> 
    (match elaborate ctx (Ast.Bool()) ph vars e,
    elaborate ctx (fullsubst e (Ast.True()) ty) ph vars e1,
    elaborate ctx (fullsubst e (Ast.False()) ty) ph vars e2 with
    | Ok elab, Ok elab1, Ok elab2 ->
      Ok (If (fst elab, fst elab1, fst elab2), ty)
    | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> Error msg)
  | Ast.Star() -> 
    (match ty with
    | Ast.Unit() -> Ok (Star(), Unit())
    | Hole _ -> Ok (Star(), Unit())
    | _ -> Error ("Type mismatch when checking that the term () of type unit has type " ^ unparse ty))
  | Ast.Let (e1, e2) ->
    (match elaborate ctx (Ast.Unit()) ph vars e1, elaborate ctx (fullsubst e1 (Ast.Star()) ty) ph vars e2 with
    | Ok elab1, Ok elab2 ->
      Ok (Let (fst elab1, fst elab2), ty)
      | Error msg, _ | _, Error msg -> Error msg)
  | Ast.Abort e -> 
    elaborate ctx (Ast.Void()) ph vars e
  | Pabs (i, e) -> 
    (match ty with
    | Pathd (ty1, e1, e2) ->
      (match elaborate ((i, Int()) :: ctx) (eval (App(ty1,Id i))) ph vars e,
              elaborate ((i, Int()) :: ctx) (eval (App(ty1,I0()))) ph vars (subst i (I0()) e),
              elaborate ((i, Int()) :: ctx) (eval (App(ty1,I1()))) ph vars (subst i (I1()) e) with
      | Ok _, Ok elab1, Ok elab2 ->
      let e1' = eval (fst elab1) in
      let e2' = eval (fst elab2) in
      if e1 = e1' && e2 = e2' 
      then Ok (Pabs (i, e), Pathd (ty, eval (fst elab1), eval (fst elab2)))
      else if e2 = e2' 
      then Error ("Term mismatch when checking that " ^ unparse e1 ^ "and " ^ unparse e1' ^ "are definitionally equal")
      else Error ("Term mismatch whens checking that " ^ unparse e2 ^ "and " ^ unparse e2' ^ "are definitionally equal") (* HERE *)
      | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> Error msg)
    | Hole _ -> 
      let p = generate_placeholder ty in
      elaborate ctx (Pathd(Hole (string_of_int p), App (e, I0()), App (e, I1()))) (ph+1) vars (Pabs (i, e))
    | _ -> 
      Error ("Type mismatch when checking that the term <" ^ i ^ "> " ^ unparse e ^ " of type path ?0? ?1? ?2? has type " ^ unparse ty))
  | At (e1, e2) ->
    let p = generate_placeholder ty in
    (match elaborate ctx (Int()) ph vars e2, 
            elaborate ctx (Pathd(Hole (string_of_int p), Hole (string_of_int (p+1)), Hole (string_of_int (p+2)))) (ph+3) vars e1 with
    | Ok elab2, Ok elab1 ->
      (match snd elab1 with
      | Pathd (ty',a,b) ->
        if e2 = I0()
        then elaborate ctx (fullsubst (At(e1,I0())) a ty) ph vars a
        else if e2 = I1()
          then elaborate ctx (fullsubst (At(e1,I1())) b ty) ph vars b
          else
            (match ty' with
            | Abs(_, ty') ->
              if synthesize vars (ty', ty) then Ok (At (fst elab1, fst elab2), ty)
              else Error ("Failed to synthesize the types " ^ unparse ty' ^ "and " ^ unparse ty)
            | _ -> 
              (match ty with
              | App(ty, i) ->
                if synthesize vars (ty', ty) && e2 = i 
                then Ok (At (fst elab1, fst elab2), App(ty,i))
                else Error ("Failed to synthesize the types " ^ unparse ty' ^ "and " ^ unparse ty)
              | ty -> 
                if synthesize vars (ty', ty) 
                then Ok (At (fst elab1, fst elab2), ty) 
                else Error ("Failed to synthesize the types " ^ unparse ty' ^ "and " ^ unparse ty)))
      | _ -> Error ("Type mismatch when checking that the term " ^ unparse (fst elab1) ^ " of type " ^ unparse (snd elab1) ^ "has type pathd ?0? ?1? ?2? "))
      | Error msg, _ | _, Error msg -> Error msg)
  | Pi(x, ty1, ty2) ->
    let p = generate_placeholder ty in
    (match elaborate ctx (Hole (string_of_int p)) (ph+1) vars ty1,
            elaborate ((x, ty1) :: ctx) (Hole (string_of_int p)) (ph+1) vars ty2 with
    | Ok elab1, Ok elab2 -> 
      (match snd elab1, snd elab2 with
      | Type n1, Type n2 ->
        (match ty with
        | Type m -> 
          if m >= n1 && m >= n2
          then Ok (Pi(x, fst elab1, fst elab2), Type m) 
          else Error ("Type mismatch when checking that the type Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                      " of the universe type (max(" ^ string_of_int n1 ^ ", " ^ string_of_int n2 ^ ")) is in the universe type " ^ string_of_int m)
        | Hole _ -> 
          if n1 > n2 
          then Ok (Pi(x, fst elab1, fst elab2), Type n1)
          else Ok (Pi(x, fst elab1, fst elab2), Type n2)
        | _ ->
          Error ("Type mismatch when checking that the type Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ " has type " ^ unparse ty))
      | Type _, _ -> Error ("Failed to check that the term " ^ unparse ty1 ^ " is type ")
      | _, _ -> Error ("Failed to check that the term " ^ unparse ty2 ^ " is type "))
    | Error msg, _ | _, Error msg -> Error msg)
  | Sigma(x, ty1, ty2) ->      
    let p = generate_placeholder ty in
    (match elaborate ctx (Hole (string_of_int p)) (ph+1) vars ty1,
            elaborate ((x, ty1) :: ctx) (Hole (string_of_int p)) (ph+1) vars ty2 with
    | Ok elab1, Ok elab2 ->
      (match snd elab1, snd elab2 with
      | Type n1, Type n2 ->
        (match ty with
        | Type m -> 
          if m >= n1 && m >= n2
          then Ok (Sigma(x, fst elab1, fst elab2), Type m) 
          else Error ("Type mismatch when checking that the type Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                      " of the universe type (max(" ^ string_of_int n1 ^ ", " ^ string_of_int n2 ^ ")) is in the universe type " ^ string_of_int m)
        | Hole _ -> 
        if n1 > n2
        then Ok (Sigma(x, fst elab1, fst elab2), Type n1) 
        else Ok (Sigma(x, fst elab1, fst elab2), Type n2)
        | _ ->
        Error ("Type mismatch when checking that the type Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ " has type " ^ unparse ty))
      | Type _, _ -> Error ("Failed to check that the term " ^ unparse ty1 ^ " is type ")
      | _, _ -> Error ("Failed to check that the term " ^ unparse ty2 ^ " is type "))
    | Error msg, _ | _, Error msg -> Error msg)
  | Sum(ty1, ty2) ->
    let p = generate_placeholder ty in
    (match elaborate ctx (Hole (string_of_int p)) (ph+1) vars ty1,
            elaborate ctx (Hole (string_of_int p)) (ph+1) vars ty2 with
    | Ok elab1, Ok elab2 ->
      (match snd elab1, snd elab2 with
      | Type n1, Type n2 ->
        (match ty with
        | Type m ->
          if m >= n1 && m >= n2
          then Ok (Sum(fst elab1, fst elab2), Type m) 
          else Error ("Type mismatch when checking that the type " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ 
                      " of the universe type (max(" ^ string_of_int n1 ^ ", " ^ string_of_int n2 ^ ")) is in the universe type " ^ string_of_int m)
        | Hole _ -> 
          if n1 > n2
          then Ok (Sum (fst elab1, fst elab2), Type n1)
          else Ok (Sum (fst elab1, fst elab2), Type n2) 
        | _ -> Error ("Type mismatch when checking that the type " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ " has type " ^ unparse ty))
      | Type _, _ -> Error ("Failed to check that the term " ^ unparse ty1 ^ " is type ")
      | _, _ -> Error ("Failed to check that the term " ^ unparse ty2 ^ " is type "))
    | Error msg, _ | _, Error msg -> Error msg)
  | Int() ->
    (match ty with
    | Type m -> Ok (Int(), Type m)
    | Hole _ -> Ok (Int(), Type 0) 
    | _ -> Error ("Type mismatch when checking that the type I has type " ^ unparse ty))
  | Nat() ->
    (match ty with
    | Type m -> Ok (Nat(), Type m)
    | Hole _ -> Ok (Nat(), Type 0) 
    | _ -> Error ("Type mismatch when checking that the type nat has type " ^ unparse ty))
  | Bool() ->
    (match ty with
    | Type m -> Ok (Bool(), Type m)
    | Hole _ -> Ok (Bool(), Type 0) 
    | _ -> Error ("Type mismatch when checking that the type bool has type " ^ unparse ty))
  | Unit() ->
    (match ty with
    | Type m -> Ok (Unit(), Type m)
    | Hole _ -> Ok (Unit(), Type 0) 
    | _ -> Error ("Type mismatch when checking that the type unit has type " ^ unparse ty))
  | Void() ->
    (match ty with
    | Type m -> Ok (Void(), Type m)
    | Hole _ -> Ok (Void(), Type 0) 
    | _ -> Error ("Type mismatch when checking that the type void has type " ^ unparse ty))
  | Pathd(ty1, e1, e2) ->
    let p = generate_placeholder (App(ty,Pathd(ty1, e1, e2))) in
    (match elaborate ctx (Hole (string_of_int p)) (ph+1) vars (eval (App (ty1, I0()))),
            elaborate ctx (Hole (string_of_int p)) (ph+1) vars (eval (App (ty1, I1()))) with
    | Ok tyi0, Ok tyi1 ->
      
      (match elaborate ctx (Hole (string_of_int p)) (ph+1) vars ty1,
              elaborate ctx (fst tyi0) (ph+1) vars e1,
              elaborate ctx (fst tyi1) (ph+1) vars e2 with
      | Ok elab, Ok elab1, Ok elab2 ->
        (match snd elab with
        | Pi (_, interval, ty2) ->
          (match interval, ty2 with
          | Int(), Type n | Hole _, Type n ->
            (match ty with
            | Type m ->
              if m >= n 
              then Ok (Pathd(fst elab, fst elab1, fst elab2), Type m) (* IMPROVE ERROR MSGS HERE *)
              else Error ("Failed to check that pathd " ^ unparse (fst elab) ^ " " ^  unparse (fst elab1) ^ " " ^  unparse (fst elab2) ^ "has type " ^ unparse ty)
              | Hole _ -> Ok (Pathd(fst elab, fst elab1, fst elab2), Type n) 
            | _ -> Error ("Failed to check that " ^ unparse ty2 ^ "is a type "))
          | Int() , _ | Hole _, _ -> Error ("Failed to check that " ^ unparse ty2 ^ "is a type ") 
          | _ -> Error ("The term " ^ unparse interval ^ "must be I ") )
        | _ -> Error ("Type mismatch when checking that " ^ unparse ty1 ^ " has type Π (v? : I) ?0? "))
      | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> Error msg)
    | Error msg, _ | _, Error msg -> Error msg)
    
  | Type n ->
    (match ty with
    | Type m -> 
      if m > n 
      then Ok (Type n, Type m) 
      else Error ("Type mismatch: type " ^ string_of_int n ^ " cannot belong to type " ^ string_of_int m ^ " (Girard's paradox) ")
    | Hole _ -> Ok (Type n, Type (n+1)) 
    | _ -> Error ("Type mismatch when checking that type " ^ string_of_int n ^ " has type " ^ unparse ty))
  | Wild() ->
    (match find_ty ty ctx with
    | Ok var -> Ok (Id var, ty)
    | Error _ -> Error ("Failed to synthesize placeholder of type " ^ unparse ty))
  | _ -> Error ("Failed to synthesize placeholder ")

(* Checks whether a given expression is a type *)

let check_type ctx ty =
  let msg = ("Failed to prove that " ^ unparse ty ^ "is a type ") in
  match elaborate ctx (Hole "0") 1 0 (reduce ty) with
  | Ok elab -> 
    (match snd elab with
    | Type _ -> Ok elab
    | _ -> Error msg)
  | _ -> Error msg

(* Checks whether a given context is well-formed *)

let check_ctx ctx =
  let rec helper l = 
    match l with
  | [] -> Ok []
  | (x, ty) :: ctx' ->
    match check_type ctx' ty, helper ctx' with
    | Ok elab, Ok ctx'' -> Ok ((x, eval (fst elab)) :: ctx'')
    | Error msg, _ | _ , Error msg -> 
      Error (msg ^ "\n The specified context is invalid") in
    helper (List.rev ctx)

(* 
let check_ctx ctx =
  let rec helper l = 
    match l with
  | [] -> Ok (Void(), Type 1)
  | (x, ty) :: ctx' ->
    match check_type ctx' ty with
    | Ok _ -> helper ctx' 
    | Error msg -> 
      Error (msg ^ "\n The specified context is invalid") in
    helper (List.rev ctx)

let check_ctx ctx =
  let rec helper l = 
    match l with
  | [] -> true
  | (x, ty) :: ctx' -> 
    check_type ctx' ty && helper ctx' in
    helper (List.rev ctx)

*)

(* Those are tests 

let check_ctx_list ctx =
  let rec helper l = 
    match l with
  | [] -> ["", Void(), ()]
  | (x, ty) :: ctx' ->
    (match check_type ctx' ty with
    | Ok res -> 
      (x, ty, res) :: helper ctx'
    | Error msg -> ["", Void(), ()] ) in
    helper (List.rev ctx)

let listhd ty = function
  | [] -> Error ("Failed to synthesize placeholder " ^ unparse ty)
  | hd :: l -> Ok hd
*)