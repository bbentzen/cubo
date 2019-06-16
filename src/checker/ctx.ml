(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether a given context is well-formed
 **)

open Basis
open Context
open Eval 

let check global ctx =
  let rec helper l = 
    match l with
  | [] -> Ok []
  | ((x, ty), b) :: ctx' ->
    match Type.check global ctx' ty, helper ctx' with
    | Ok elab, Ok ctx'' -> 
      if Global.is_declared x global 
      then Error ("Naming conflict with the identifier '" ^ x ^ 
                 "'\nIt occurs as a definition/theorem name but is declared as a local variable")
      else Ok (((x, eval (fst elab)), b) :: ctx'')
    | Error msg, _ | _ , Error msg -> 
      Error (msg ^ "\nThe specified context is invalid") in
    helper (List.rev ctx)
