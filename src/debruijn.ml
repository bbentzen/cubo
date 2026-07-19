(**
 * (c) Copyright 2026 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: Translation between user raw AST and internal de Bruijn AST.
 *       Free identifiers remain globals and bound identifiers become local indices.
 **)

let rec index_of x = function
  | [] -> None
  | y :: env -> if x = y then Some 0 else Option.map (fun n -> n + 1) (index_of x env)

let rec name_at n hint = function
  | [] -> hint
  | x :: _ when n = 0 -> x
  | _ :: env -> name_at (n - 1) hint env

let rec level_of_raw = function
  | Ast.Num n -> Core_ast.Num n
  | Ast.Var x -> Core_ast.Var x
  | Ast.Suc l -> Core_ast.Suc (level_of_raw l)
  | Ast.Max (l1, l2) -> Core_ast.Max (level_of_raw l1, level_of_raw l2)

let rec level_to_raw = function
  | Core_ast.Num n -> Ast.Num n
  | Core_ast.Var x -> Ast.Var x
  | Core_ast.Suc l -> Ast.Suc (level_to_raw l)
  | Core_ast.Max (l1, l2) -> Ast.Max (level_to_raw l1, level_to_raw l2)

let rec of_raw_expr_with_env env = function
  | Ast.Id x ->
    begin
      match index_of x env with
      | Some index -> Core_ast.Local { hint = x; index }
      | None -> Core_ast.Global x
    end
  | Ast.Int () -> Core_ast.Int ()
  | Ast.I1 () -> Core_ast.I1 ()
  | Ast.I0 () -> Core_ast.I0 ()
  | Ast.Coe (i, j, e1, e2) ->
    Core_ast.Coe (
      of_raw_expr_with_env env i,
      of_raw_expr_with_env env j,
      of_raw_expr_with_env env e1,
      of_raw_expr_with_env env e2)
  | Ast.Hfill (e, e1, e2) ->
    Core_ast.Hfill (
      of_raw_expr_with_env env e,
      of_raw_expr_with_env env e1,
      of_raw_expr_with_env env e2)
  | Ast.Abs (x, e) -> Core_ast.Abs (x, of_raw_expr_with_env (x :: env) e)
  | Ast.App (e1, e2) -> Core_ast.App (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Pi (x, e1, e2) ->
    Core_ast.Pi (x, of_raw_expr_with_env env e1, of_raw_expr_with_env (x :: env) e2)
  | Ast.Pair (e1, e2) -> Core_ast.Pair (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Fst e -> Core_ast.Fst (of_raw_expr_with_env env e)
  | Ast.Snd e -> Core_ast.Snd (of_raw_expr_with_env env e)
  | Ast.Sigma (x, e1, e2) ->
    Core_ast.Sigma (x, of_raw_expr_with_env env e1, of_raw_expr_with_env (x :: env) e2)
  | Ast.Inl e -> Core_ast.Inl (of_raw_expr_with_env env e)
  | Ast.Inr e -> Core_ast.Inr (of_raw_expr_with_env env e)
  | Ast.Case (e, e1, e2) ->
    Core_ast.Case (of_raw_expr_with_env env e, of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Sum (e1, e2) -> Core_ast.Sum (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Star () -> Core_ast.Star ()
  | Ast.Let (e1, e2) -> Core_ast.Let (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Unit () -> Core_ast.Unit ()
  | Ast.True () -> Core_ast.True ()
  | Ast.False () -> Core_ast.False ()
  | Ast.If (e, e1, e2) ->
    Core_ast.If (of_raw_expr_with_env env e, of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Bool () -> Core_ast.Bool ()
  | Ast.Zero () -> Core_ast.Zero ()
  | Ast.Succ e -> Core_ast.Succ (of_raw_expr_with_env env e)
  | Ast.Natrec (e, e1, e2) ->
    Core_ast.Natrec (of_raw_expr_with_env env e, of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Nat () -> Core_ast.Nat ()
  | Ast.Abort e -> Core_ast.Abort (of_raw_expr_with_env env e)
  | Ast.Void () -> Core_ast.Void ()
  | Ast.Pabs (x, e) -> Core_ast.Pabs (x, of_raw_expr_with_env (x :: env) e)
  | Ast.At (e1, e2) -> Core_ast.At (of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Pathd (e, e1, e2) ->
    Core_ast.Pathd (of_raw_expr_with_env env e, of_raw_expr_with_env env e1, of_raw_expr_with_env env e2)
  | Ast.Type l -> Core_ast.Type (level_of_raw l)
  | Ast.Hole (n, l) -> Core_ast.Hole (n, List.map (of_raw_expr_with_env env) l)
  | Ast.Wild n -> Core_ast.Wild n
  | Ast.Subgoal() -> Core_ast.Subgoal()

let of_raw_expr e = of_raw_expr_with_env [] e

let rec to_raw_expr_with_env env = function
  | Core_ast.Local { hint; index } -> Ast.Id (name_at index hint env)
  | Core_ast.Global x -> Ast.Id x
  | Core_ast.Int () -> Ast.Int ()
  | Core_ast.I1 () -> Ast.I1 ()
  | Core_ast.I0 () -> Ast.I0 ()
  | Core_ast.Coe (i, j, e1, e2) ->
    Ast.Coe (
      to_raw_expr_with_env env i,
      to_raw_expr_with_env env j,
      to_raw_expr_with_env env e1,
      to_raw_expr_with_env env e2)
  | Core_ast.Hfill (e, e1, e2) ->
    Ast.Hfill (
      to_raw_expr_with_env env e,
      to_raw_expr_with_env env e1,
      to_raw_expr_with_env env e2)
  | Core_ast.Abs (x, e) -> Ast.Abs (x, to_raw_expr_with_env (x :: env) e)
  | Core_ast.App (e1, e2) -> Ast.App (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Pi (x, e1, e2) ->
    Ast.Pi (x, to_raw_expr_with_env env e1, to_raw_expr_with_env (x :: env) e2)
  | Core_ast.Pair (e1, e2) -> Ast.Pair (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Fst e -> Ast.Fst (to_raw_expr_with_env env e)
  | Core_ast.Snd e -> Ast.Snd (to_raw_expr_with_env env e)
  | Core_ast.Sigma (x, e1, e2) ->
    Ast.Sigma (x, to_raw_expr_with_env env e1, to_raw_expr_with_env (x :: env) e2)
  | Core_ast.Inl e -> Ast.Inl (to_raw_expr_with_env env e)
  | Core_ast.Inr e -> Ast.Inr (to_raw_expr_with_env env e)
  | Core_ast.Case (e, e1, e2) ->
    Ast.Case (to_raw_expr_with_env env e, to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Sum (e1, e2) -> Ast.Sum (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Star () -> Ast.Star ()
  | Core_ast.Let (e1, e2) -> Ast.Let (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Unit () -> Ast.Unit ()
  | Core_ast.True () -> Ast.True ()
  | Core_ast.False () -> Ast.False ()
  | Core_ast.If (e, e1, e2) ->
    Ast.If (to_raw_expr_with_env env e, to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Bool () -> Ast.Bool ()
  | Core_ast.Zero () -> Ast.Zero ()
  | Core_ast.Succ e -> Ast.Succ (to_raw_expr_with_env env e)
  | Core_ast.Natrec (e, e1, e2) ->
    Ast.Natrec (to_raw_expr_with_env env e, to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Nat () -> Ast.Nat ()
  | Core_ast.Abort e -> Ast.Abort (to_raw_expr_with_env env e)
  | Core_ast.Void () -> Ast.Void ()
  | Core_ast.Pabs (x, e) -> Ast.Pabs (x, to_raw_expr_with_env (x :: env) e)
  | Core_ast.At (e1, e2) -> Ast.At (to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Pathd (e, e1, e2) ->
    Ast.Pathd (to_raw_expr_with_env env e, to_raw_expr_with_env env e1, to_raw_expr_with_env env e2)
  | Core_ast.Type l -> Ast.Type (level_to_raw l)
  | Core_ast.Hole (n, l) -> Ast.Hole (n, List.map (to_raw_expr_with_env env) l)
  | Core_ast.Wild n -> Ast.Wild n
  | Core_ast.Subgoal() -> Ast.Subgoal()

let to_raw_expr e = to_raw_expr_with_env [] e

let normalize_expr e =
  e
  |> of_raw_expr
  |> to_raw_expr

let normalize_ctx ctx =
  let rec helper env acc = function
    | [] -> List.rev acc
    | (x, ty, b) :: rest ->
      let ty' =
        ty
        |> of_raw_expr_with_env env
        |> to_raw_expr_with_env env
      in
      helper (x :: env) ((x, ty', b) :: acc) rest
  in
  helper [] [] ctx

let normalize_decl ((ids, ty), b) =
  ((ids, normalize_expr ty), b)

let normalize_proof = function
  | Ast.Prf (id, l, ty, e) ->
    Ast.Prf (id, List.map normalize_decl l, normalize_expr ty, normalize_expr e)

let rec normalize_command = function
  | Ast.Import (cmd, s) -> Ast.Import (normalize_command cmd, s)
  | Ast.Thm (cmd, prf) -> Ast.Thm (normalize_command cmd, normalize_proof prf)
  | Ast.Print (cmd, s) -> Ast.Print (normalize_command cmd, s)
  | Ast.Infer (cmd, e) -> Ast.Infer (normalize_command cmd, normalize_expr e)
  | Ast.Eval (cmd, e) -> Ast.Eval (normalize_command cmd, normalize_expr e)
  | Ast.Level (cmd, l) -> Ast.Level (normalize_command cmd, l)
  | Ast.Eof () -> Ast.Eof ()
