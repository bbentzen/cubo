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
  | Ok (env, s) ->
    let n = String.length s in
    let s' = 
      if n > 0 && s.[n-1] = '\n' then 
        String.sub s 0 (n-1)
      else 
        s 
    in
    print_endline s';
    print_endline (string_of_int (List.length env) ^ " definition(s)/theorem(s) compiled successfully. " );
  | Error msg -> print_endline (" Error: " ^ msg);
