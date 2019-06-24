(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether a universe level is lower than or equal to another one
         
 **)

open Ast

let rec leq = function
  | Num n, Num m -> n <= m
  | Var n, Var m -> n = m
  | Num 0, Var _ | Var _, Num 0 -> true
  | Num _, Var _ | Var _, Num _ -> false
  | Max (n, n'), Max (m, m') -> (leq (n, m) && leq (n', m')) || (leq (n', m) && leq (n, m'))
  | Num n, Max (Num m, Num m') | Max (Num m, Num m'), Num n -> n <= m + m'
  | n, Max (m, m') | Max (m, m'), n -> leq (n, m) || leq (n, m')
  | n, Next m | Next m, n -> leq (n, m)

let rec reduce = function
  | Next n -> Next (fst (reduce n)), snd (reduce n)
  | Max (Next n, m) | Max (m, Next n) -> Next (Max (n, m)), true
  | Max (Num n, Num m) ->
    if n <= m then
      (Ast.Num m), true
    else
      (Ast.Num n), true
  | Max (n, m) ->
    Max (fst (reduce n), fst (reduce m)),
    snd (reduce n) || snd (reduce m)
  | l -> l, false

let rec eval e =
  match reduce e with
  | e', b ->
    if b then 
      eval (e')
    else 
      e'

let rec decl lvl = function
| Num _ -> Ok ()
| Var n -> 
  if List.mem n lvl then 
    Ok ()
  else
    Error ("No declaration found for the universe level '" ^ n ^ "'")
| Next n ->
  begin
    match decl lvl n with
    | Ok _ -> Ok ()
    | Error msg ->
      Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
  end
| Max (n, m) ->
  begin
    match decl lvl n, decl lvl m with
    | Ok _, Ok _ -> Ok ()
    | Error msg, _ ->
      Error ("Invalid universe level:\n  " ^ Pretty.print_level n ^ "\n" ^ msg)
    | _, Error msg ->
      Error ("Invalid universe level:\n  " ^ Pretty.print_level m ^ "\n" ^ msg)
  end
  