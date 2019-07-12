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
  
let parse_file filename = 
  parse_string (concat_string_list (read_file filename))

(* Handles directories *)

let parent dir =
  match String.rindex_opt dir '/' with
  | Some n ->
    String.sub dir 0 n
  | None -> ""

let rec dot_dir cd s =
  let n = String.length s in
  if s.[0] = '.' && s.[1] = '/' then
    let s = String.sub s 1 (n - 1) in
	  cd ^ s
  else if s.[0] = '.' && s.[1] = '.' && s.[2] = '/' then
	  let s' = String.sub s  2 (n - 2) in
    dot_dir (parent cd) s'
  else
  cd ^ s
	
let read_dir cd s =
  let n = String.length s in
  if n > 2 then
    if s.[0] = '.' then
      let s' = dot_dir cd s in
      if s'.[0] = '/' then
        String.sub s 1 (n - 1)
      else 
        s'
    else
      s
  else 
    s