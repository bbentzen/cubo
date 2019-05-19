(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The main program
 **)

open Frontend
open Command

let () =
  let filename = "tests/test.cubo" in
  match checkfile filename with 
  | Ok env ->
    (match (List.length env) with
    | 1 ->
      print_endline (" 1 definition/theorem compiled successfully. " );
    | n ->  
      print_endline (string_of_int n ^ " definitions/theorems compiled successfully. " );)
  | Error msg -> print_endline (" Error: " ^ msg);
