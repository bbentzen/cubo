(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Checks whether an expression is a type
         Allows for placeholders to stand for types
 **)

open Basis
open Ast

let check global ctx ty =
  match ty with
  | Hole _ -> Ok (Hole ("0",[]), ty)
  | _ ->
    let s = ("Failed to prove that \n  " ^ unparse (Eval.eval ty) ^ "\nis a type") in
    match Elab.elaborate global ctx (Hole ("0",[])) 1 0 (Eval.reduce ty) with
    | Ok elab -> 
      begin match snd elab with
      | Type _ | Hole _ -> (* Hole _ has been added for tests*)
        Ok elab
      | _ -> Error s
      end
    | Error msg -> Error (s ^ "\n " ^ msg)