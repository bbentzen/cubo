(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Performs file operations
 **)

open Basis

let read_file filename = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines ;;

let rec concat_string_list = function
  | [] -> ""
  | s :: l -> s ^ concat_string_list l

(* Parses a string *)

let parse_string s =
  let lb = Lexing.from_string s in
  Syntax.command Scanner.token lb

let token_list_of_string s =
  let lb = Lexing.from_string s in
  let rec helper l =
    try
      let t = Scanner.token lb in
      if t = Syntax.EOF then List.rev l else helper (t::l)
    with _ -> List.rev l in 
  helper []
  
let parsefile filename = 
  parse_string (concat_string_list (read_file filename))
  