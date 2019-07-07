(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether a given context is well-formed
 **)

open Basis
open Context
open Eval 

let check global ctx lvl =
  let rec helper l = 
    match l with
  | [] -> Ok []
  | ((x, ty), b) :: ctx' ->
    match Type.check global ctx' lvl ty, helper ctx' with
    | Ok elab, Ok ctx'' -> 
      if Global.is_declared x global then
        Error ("Naming conflict with the identifier '" ^ x ^ 
          "'\nIt occurs as a definition/theorem name but is declared as a local variable")
      else
        Ok (((x, eval (fst elab)), b) :: ctx'')
    | Error msg, _ -> 
      Error ("The specified context is invalid: " ^ msg)
    | _ , Error msg -> Error msg
  in
  helper (List.rev ctx)

let rec or_all = function
	| [] -> false
	| (_, b) :: ctx -> 
    b || (or_all ctx)

let rec count_true = function
  | [] -> 0
  | (_, false) :: ctx -> 
    count_true ctx
  | (_, true) :: ctx ->
    count_true ctx +1
