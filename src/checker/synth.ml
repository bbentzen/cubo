(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Performs synthesization of terms
 **)

open Basis
open Ast
open Substitution

(* Returns the type of a term variable when it has been declared *)

let rec synth_placeholder x ctx =
  match (List.rev ctx) with
  | [] -> (false, Ast.Void()) 
  | ((y, ty), _) :: ctx' -> 
    if x = y
    then (true, ty)
    else synth_placeholder x ctx'

let rec infer_var_ty x ctx =
  match (List.rev ctx) with
  | [] -> Ast.Void()
  | ((y, ty), _) :: ctx' -> 
    if x = y
    then ty
    else infer_var_ty x ctx'

(* Common element of a list *)

let rec commonel = function
  | [], [] -> Error()
  | _, [] | [], _ -> Error()
  | e :: l1 , e' :: l2 ->
    if List.mem e l2 then
      Ok e
    else if List.mem e' l1 then
      Ok e'
    else
      commonel (l1, l2)

(* Unifies two expressions *)

let rec synthesize vars = function
| Hole (n1, l1), Hole (n2, l2) ->
  begin match l1, l2 with
  | [], [] -> Ok (Hole (n1, l1))
  | l1, [] -> Ok (Hole (n1, l1))
  | [], l2 -> Ok (Hole (n2, l2))
  | _ ->
    match commonel (l1,l2) with
    | Ok e -> Ok e
    | Error() ->
      Error ((Hole (n1, l1), Hole (n2, l2)), 
            "Failed to unify the placeholder\n  ?" ^ 
            n1 ^ "?\nwhose suitable candidates are\n" ^ 
            (String.concat " " (List.map Ast.unparse l1)) ^
            "\nwith the placeholder\n  ?" ^ 
            n2 ^ "?\nwhose suitable candidates are\n" ^ 
            (String.concat " " (List.map Ast.unparse l2))) 
  end

| e , Hole (n, l) | Hole (n, l), e ->
  begin match l with
  | [] -> Ok e
  | _ ->
    let rec helper = function
    | [] -> false
    | e' :: l' -> e' = e || helper l' in
    if helper l then 
      Ok e 
    else 
      Error ((e , Hole (n, l)),
              "Failed to unify the placeholder\n  " ^ 
              unparse (Ast.Hole (n, l)) ^ "\nwith the suitable candidates\n" ^ 
              (String.concat " " (List.map Ast.unparse l)))
  end

| Pi (x, ty1, ty2), Pi (x', ty1', ty2') -> 
  let v1 = fresh_var ty2 ty2' vars in
  begin match synthesize (vars+1) (ty1, ty1') with
  | Ok s1 -> 
    let e = fullsubst ty1 s1 (subst x (Id v1) ty2) in
    let e' = fullsubst ty1' s1 (subst x' (Id v1) ty2') in
    begin match synthesize (vars+1) (e, e') with
    | Ok s2 -> Ok (Pi (v1, s1, s2))
    | Error msg -> Error msg
    end
  | Error msg -> Error msg
  end

| Sigma (x, ty1, ty2), Sigma (x', ty1', ty2') ->
  let v1 = fresh_var ty2 ty2' vars in
  begin match synthesize (vars+1) (ty1, ty1') with
  | Ok s1 -> 
    let e = fullsubst ty1 s1 (subst x (Id v1) ty2) in
    let e' = fullsubst ty1' s1 (subst x' (Id v1) ty2') in
    begin match synthesize (vars+1) (e, e') with
    | Ok s2 -> Ok (Sigma (v1, s1, s2))
    | Error (s, msg) -> Error (s, "Don't know how to unify\n  " ^ unparse e ^ "\nwith\n  " ^ unparse e' ^ "\n" ^ msg)
    end
  | Error (s, msg) -> Error (s, "Don't know how to unify\n  " ^ unparse ty1 ^ "\nwith\n  " ^ unparse ty2 ^ "\n" ^ msg)
  end

| Sum (ty1, ty2) , Sum (ty1', ty2') ->
  begin match synthesize vars (ty1, ty1'), synthesize vars (ty2, ty2') with
  | Ok s1, Ok s2 -> Ok (Sum (s1, s2))
  | Error msg, _ | _ , Error msg -> 
    Error msg
  end

| Pathd (ty, e1, e2) , Pathd (ty', e1', e2') -> 
  begin match synthesize vars (ty, ty'), synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s, Ok s1, Ok s2 -> Ok (Pathd (s, s1, s2))
  | Error msg, _, _ | _ , Error msg, _| _ , _, Error msg -> 
    Error msg
  end

| Abs (x, e), Abs (x', e') -> 
  let v1 = fresh_var e e' vars in
  begin match synthesize (vars+1) (subst x (Id v1) e, subst x' (Id v1) e') with
  | Ok s -> Ok (Abs (v1, s))
  | Error msg -> Error msg
  end

| Pabs (x, e), Pabs (x', e') -> 
  let v1 = fresh_var e e' vars in
  begin match synthesize (vars+1) (subst x (Id v1) e, subst x' (Id v1) e') with
  | Ok s -> Ok (Pabs (v1, s))
  | Error msg -> Error msg
  end

| App (e1, e2), App (e1', e2') ->
  begin match synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s1, Ok s2 -> Ok (App (s1, s2))
  | Error msg, _ | _, Error msg -> Error msg
  end

| Pair (e1, e2), Pair (e1', e2') ->
  begin match synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s1, Ok s2 -> Ok (Pair (s1, s2))
  | Error msg, _ | _, Error msg -> Error msg
  end

| At (e1, e2), At (e1', e2') ->
  begin match synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s1, Ok s2 -> Ok (At (s1, s2))
  | Error msg, _ | _, Error msg -> Error msg
  end

| Let (e1, e2), Let (e1', e2') ->
  begin match synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s1, Ok s2 -> Ok (Let (s1, s2))
  | Error msg, _ | _, Error msg -> Error msg
  end

| Fst e, Fst e' ->
  begin match synthesize vars (e, e') with
  | Ok s -> Ok (Fst s)
  | Error msg -> Error msg
  end

| Snd e, Snd e' ->
  begin match synthesize vars (e, e') with
  | Ok s -> Ok (Snd s)
  | Error msg -> Error msg
  end

| Inl e, Inl e' ->
  begin match synthesize vars (e, e') with
  | Ok s -> Ok (Inl s)
  | Error msg -> Error msg
  end

| Inr e, Inr e' ->
  begin match synthesize vars (e, e') with
  | Ok s -> Ok (Inr s)
  | Error msg -> Error msg
  end

| Succ e, Succ e' ->
  begin match synthesize vars (e, e') with
  | Ok s -> Ok (Succ s)
  | Error msg -> Error msg
  end

| Abort e, Abort e' -> 
  begin match synthesize vars (e, e') with
  | Ok s -> Ok (Abort s)
  | Error msg -> Error msg
  end

| Case (e, e1, e2), Case (e', e1', e2') ->
  begin match synthesize vars (e, e'), synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s, Ok s1, Ok s2 -> Ok (Case (s, s1, s2))
  | Error msg, _, _ | _ , Error msg, _| _ , _, Error msg ->
    Error msg
  end

| Natrec (e, e1, e2), Natrec (e', e1', e2') ->
  begin match synthesize vars (e, e'), synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s, Ok s1, Ok s2 -> Ok (Natrec (s, s1, s2))
  | Error msg, _, _ | _ , Error msg, _| _ , _, Error msg ->
    Error msg
  end

| If (e, e1, e2), If (e', e1', e2') ->
  begin match synthesize vars (e, e'), synthesize vars (e1, e1'), synthesize vars (e2, e2') with
  | Ok s, Ok s1, Ok s2 -> Ok (If (s, s1, s2))
  | Error msg, _, _ | _ , Error msg, _| _ , _, Error msg ->
    Error msg
  end

| e , e' -> if e = e' then Ok e else Error ((e, e'), "The terms\n  " ^ unparse e ^ "\nand\n  " ^ unparse e' ^ "\nare not equal")


(*
let rec synthesize vars = function
| e , Hole _ | Hole _, e -> true
| Pi (x, ty1, ty2), Pi (x', ty1', ty2') -> (* group Pi and Sigma together *)
  let v1 = fresh_var ty2 ty2' vars in
  synthesize (vars+1) (ty1, ty1') && synthesize (vars+1) (subst x (Id v1) ty2, subst x' (Id v1) ty2')
| Sigma (x, ty1, ty2), Sigma (x', ty1', ty2') ->
  let var = fresh_var ty2 ty2' vars in
  synthesize (vars+1) (ty1, ty1') && synthesize (vars+1) (subst x (Id var) ty2, subst x' (Id var) ty2')
| Sum (ty1, ty2) , Sum (ty1', ty2') ->
  synthesize vars (ty1, ty1') && synthesize vars (ty2, ty2')
| Pathd (ty, e1, e2) , Pathd (ty', e1', e2') -> 
  synthesize vars (ty, ty') && synthesize vars (e1, e1') && synthesize vars (e2, e2')
| Abs (x, e), Abs (x', e') | Pabs (x, e), Pabs (x', e') -> 
  let var = fresh_var e e' vars in
  synthesize (vars+1) (subst x (Id var) e, subst x' (Id var) e')
| App (e1, e2), App (e1', e2') | Pair (e1, e2), Pair (e1', e2') | Let (e1, e2), Let (e1', e2') | At (e1, e2), At (e1', e2') -> 
  synthesize vars (e1, e1') && synthesize vars (e2, e2')
| Fst e, Fst e' | Snd e, Snd e' | Inl e, Inl e' | Inr e, Inr e' | Succ e, Succ e' | Abort e, Abort e' -> 
  synthesize vars (e, e')
| Case (e, e1, e2), Case (e', e1', e2') | Natrec (e, e1, e2), Natrec (e', e1', e2') | If (e, e1, e2), If (e', e1', e2') ->
  synthesize vars (e, e') && synthesize vars (e1, e1') && synthesize vars (e2, e2')
| ty , ty' -> if ty = ty' then true else false 
*)