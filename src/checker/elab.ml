(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The elaborator of the program
 **)

open Basis
open Context
open Local
open Ast
open Substitution
open Synth
open Eval 

let rec print ctx =
	match (List.rev ctx) with
	| [] -> "" 
	| ((id, ty), _) :: ctx' -> 
		" " ^ id ^ " : " ^ unparse ty ^ "\n" ^ print ctx'

let goal_msg ctx e ty =
  
  "when checking that\n  " ^ unparse e ^ "\nhas the expected type\n" ^ print ctx ^ 
  "-------------------------------------------\n ⊢ " ^ unparse ty

(* Checks whether the type of a given expression is the given type *)

let rec elaborate global ctx ty ph vars = function
  | Id x ->
    let ty' = infer_var_ty x ctx in
    let c = check_var_ty x ty ctx in
    let h = Hole.is ty' in
    let d = is_declared x ctx in
    begin match c, h, d with
    | true , _ , _ | _ , true , _ ->  Ok (Id x, ty)
    | false , false , true -> 
      begin match synthesize vars (ty', ty) with
      | Ok s -> Ok (Id x, s) 
      | Error (_, msg) ->
        Error ("The variable " ^ x ^ " has type\n   " ^ unparse ty' ^ 
              "\nbut is expected to have type\n  " ^ unparse ty ^ "\n" ^ msg)
      end
    | false , false , false ->
      begin match Global.unfold x global with
      | Ok (body, ty') -> 
        (match synthesize vars (ty', ty) with
        | Ok s -> Ok (body, s)
        | _ -> 
          Error (x ^ " has type \n  " ^ unparse ty' ^ "\nbut is expected to have type\n  " ^ unparse ty))
      | Error msg -> 
        Error msg
      end
    end
  
  | I0() ->
    begin match ty with
    | Ast.Int() -> 
      Ok (I0(), Int())
    | Hole _ -> 
      Ok (I0(), Int())
    | _ -> Error ("Type mismatch when checking that the term i0 of type I has type " ^ unparse ty)
  end
  
  | I1() ->
    begin match ty with
    | Ast.Int() -> 
      Ok (I1(), Int())
    | Hole _ -> 
      Ok (I1(), Int())
    | _ -> Error ("Type mismatch when checking that the term i1 of type I has type " ^ unparse ty)
    end

  | Abs (x, e) -> 
    begin match ty with
    | Pi (y, ty1, ty2) ->
      let elab = elaborate global (((x, ty1), true) :: ctx) (subst y (Ast.Id x) ty2) ph vars e in
      begin match elab with
      | Ok (e', ty2') -> Ok (Abs (x, e'), Pi (y, ty1, ty2'))
      | Error msg -> Error msg
      end
    | Hole _ -> 
      let h1 = Hole.generate ty ph [] in
      let h2 = Hole.generate ty (ph+1) [] in
      elaborate global ctx (Pi(x, h1, h2)) (ph+2) vars (Abs (x, e))
    | _ -> 
      Error ("The term\n  λ " ^ x ^ ", " ^ unparse e ^ "\nhas type\n  " ^ unparse ty ^ "but is expected to have type\n  Π (v? : ?0?) ?1?")
    end
    
  | App (e1, e2) ->
    let h1 = Hole.generate ty ph [] in
    let v1 = fresh_var (App(e1, e2)) ty vars in
    let elab2 = elaborate global ctx h1 (ph+1) (vars+1) e2 in
    begin match elab2 with
    | Ok (e2', ty2') ->
      let elab1 = elaborate global ctx (Pi(v1, ty2', fullsubst e2 (Id v1) ty)) (ph+1) (vars+1) e1 in
      begin match elab1 with
      | Ok (e1', Pi(x, _, ty')) ->
        Ok (App (e1', e2'), subst x e2 ty')
      | Ok _ -> 
        Error ("The term\n  " ^ unparse e1 ^ 
                "\nhas type\n  " ^ unparse ty ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1? ") 
      | Error msg -> 
        Error ("The term\n  " ^ unparse e1 ^ 
              "\nhas type\n  " ^ unparse ty ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1? \n" ^ msg)
      end
    | Error msg -> Error msg
    end
  
  | Pair (e1, e2) -> 
    begin match ty with
    | Sigma(y, ty1, ty2) ->
      let elab1 = elaborate global ctx ty1 ph vars e1 in
      let elab2 = elaborate global ctx (subst y e1 ty2) ph vars e2 in
      begin match elab1, elab2 with
      | Ok (e1', ty1'), Ok (e2', ty2') ->
        begin match ty2 with
        | Hole (n, l) ->
          let ty' = fullsubst e1' (Hole (n, e1 :: e1' :: Id y :: l)) ty2' in
          Ok (Pair (e1', e2'), Sigma(y, ty1', ty'))
        | _ ->
          let ty' = fullsubst e1' (Id y) ty2' in
          Ok (Pair (e1', e2'), Sigma(y, ty1', ty'))
        end
      | Error msg, _ | _, Error msg -> 
        Error msg
      end
    | Hole _ -> 
      let v1 = fresh_var (App (e1, e2)) ty vars in
      let h1 = Hole.generate ty 0 [] in
      let h2 = Hole.generate ty 1 [] in
      elaborate global ctx (Sigma(v1, h1, h2)) (ph+2) (vars+1) (Pair (e1, e2))
    | _ ->
      Error ("Type mismatch when checking that the term (" ^ unparse e1 ^ ", " ^ unparse e2 ^ ") of type Σ (v? : ?0?) ?1? has type " ^ unparse ty)
    end
    
  | Ast.Fst e ->
    let h1 = Hole.generate ty 0 [] in
    let elab = elaborate global ctx h1 (ph+1) (vars+1) e in
    begin match elab with
    | Ok (e', Sigma(_, ty', _)) ->  
      let synt = synthesize vars (ty, ty') in
      begin match synt with
      | Ok _ ->
        Ok (Fst e', ty') 
      | Error (_, msg) ->
        Error ("Don't know how to unify\n  " ^ unparse ty ^ "\nwith\n  " ^ unparse ty' ^ "\n" ^ msg)
      end
    | Ok (e', ty') -> 
      Error ("The term\n  " ^ unparse e' ^ "\nhas type\n  " ^ unparse ty' ^ "\nbut is expected to have type\n  Σ (v0 : ?0?) ?1?")
    | Error msg ->
      Error ("The term\n  " ^ unparse e ^ "\nis expected to have type\n  Σ (v0 : ?0?) ?1?" ^ "\n" ^ msg)
    end

  | Snd e ->
    let h1 = Hole.generate ty 0 [] in
    let elab = elaborate global ctx h1 (ph+1) (vars+1) e in
    begin match elab with
    | Ok (e', Sigma(x, _, ty2)) ->
      let ty' = subst x (Fst e') ty2 in
      let synt = synthesize vars (ty, ty') in
      begin match synt with
      | Ok _ ->
        Ok (Snd e', ty')
      | Error (_, msg) ->
        Error ("Don't know how to unify\n  " ^ unparse ty ^ "\nwith\n  " ^ unparse ty' ^ "\n" ^ msg)
      end
    | Ok (e', ty') -> 
      Error ("The term\n  " ^ unparse e' ^ "\nhas type\n  " ^ unparse ty' ^ "\nbut is expected to have type\n  Σ (v0 : ?0?) ?1?")
    | Error msg ->
      Error ("The term\n  " ^ unparse e ^ "\nis expected to have type\n  Σ (v0 : ?0?) ?1?" ^ "\n" ^ msg)
    end
  
  | Ast.Inl e ->
    begin match ty with
    | Ast.Sum (ty1, ty2) ->
      let elab = elaborate global ctx ty1 ph vars e in
      begin match elab with
      | Ok (e', ty1') -> Ok (Inl e', Sum(ty1', ty2))
      | Error msg -> Error msg
      end
    | Hole _ ->
      let h1 = Hole.generate ty 0 [] in
      let h2 = Hole.generate ty 1 [] in
      elaborate global ctx (Sum(h1, h2)) (ph+2) vars (Inl e)
    | _ ->
      Error ("Type mismatch when checking that the term inl " ^ unparse e ^ " of type ?0? + ?1? has type " ^ unparse ty)
    end

  | Ast.Inr e -> 
    begin match ty with
    | Ast.Sum (ty1, ty2) ->
      let elab = elaborate global ctx ty2 ph vars e in
      begin match elab with
      | Ok (e', ty2') -> Ok (Inr e', Sum(ty1, ty2'))
      | Error msg -> Error msg
      end
    | Hole _ ->
      let h1 = Hole.generate ty 0 [] in
      let h2 = Hole.generate ty 1 [] in
      elaborate global ctx (Sum(h1, h2)) (ph+2) vars (Inr e)
    | _ -> 
      Error ("Type mismatch when checking that the term inr " ^ unparse e ^ " of type ?0? + ?1? has type " ^ unparse ty)
    end
  
  | Case (e, e1, e2) ->
    let h1 = Hole.generate ty 0 [] in
    let h2 = Hole.generate ty 1 [] in
    let elab = elaborate global ctx (Sum (h1, h2)) (ph+2) vars e in
    begin match elab with
    | Ok (e', Sum (ty1, ty2)) ->
      begin match ty with
      | Hole (n, l) ->
        let elab1 = elaborate global ctx (Hole (n, l)) ph (vars+1) e1 in
        let elab2 = elaborate global ctx (Hole (n, l)) ph (vars+1) e2 in
        begin match elab1, elab2 with
        | Ok (e1', Ast.Pi(x, ty1', tyl)), Ok (e2', Ast.Pi(y, ty2', tyr)) ->
          let syn1 = synthesize vars (ty1, ty1') in
          let syn2 = synthesize vars (ty2, ty2') in
          let tyl' = hfullsubst (Ast.Inl(Id x)) h1 tyl in
          let tyr' = hfullsubst (Ast.Inr(Id y)) h1 tyr in
          let synt = synthesize vars (tyl', tyr') in
          begin match syn1, syn2, synt with
          | Ok _, Ok _, Ok st ->
            let st' = hfullsubst h1 e st in
            Ok (Case(e', e1', e2'), st')
          | Ok _, Ok _, _ ->
            Error ("Failed to unify\n  " ^ unparse tyl' ^ "\nwith\n  " ^ unparse tyr')
          | Ok _, _, _ ->
            Error ("The term\n  " ^ unparse e2' ^ "\nhas type\n  " ^ unparse (Ast.Pi(y, ty2', tyr)) ^ 
            "\nbut is expected to have type\n  Π (" ^ y ^ " : " ^ unparse ty2 ^ ") ?1?")
          | _ ->
            Error ("The term\n  " ^ unparse e1' ^ "\nhas type\n  " ^ unparse (Ast.Pi(x, ty1', tyl)) ^ 
                  "\nbut is expected to have type\n  Π (" ^ x ^ " : " ^ unparse ty1 ^ ") ?1?")
          end
        | Ok (e1', ty'), Ok (_, Pi(_,_,_)) -> 
          Error ("The term\n  " ^ unparse e1' ^ "\nhas type\n  " ^ unparse ty' ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1?")
        | Ok _, Ok (e2', ty') -> 
          Error ("The term\n  " ^ unparse e2' ^ "\nhas type\n  " ^ unparse ty' ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1?")
        | Error msg, _ | _, Error msg -> Error msg
        end
      | _ -> 
        let v1 = fresh_var (Sum(ty1,ty2)) ty vars in
        let elab1 = elaborate global ctx (Pi(v1, ty1, fullsubst e (Inl (Id v1)) ty)) ph (vars+1) e1 in
        let elab2 = elaborate global ctx (Pi(v1, ty2, fullsubst e (Inr (Id v1)) ty)) ph (vars+1) e2 in
        begin match elab1, elab2 with
        | Ok (e1', _), Ok (e2', _) ->
          Ok (Case(e', e1', e2'), ty)
        | Error msg, _ | _, Error msg -> Error msg
        end
      end
    | Ok (e', ty') -> Error ("Type mismatch when checking that the term " ^ unparse e' ^ " of type " ^ unparse ty' ^ "has type ?0? + ?1?")
    | Error msg -> Error msg
    end

  | Ast.Zero() ->
    begin match ty with
    | Nat() -> 
      Ok (Zero(), Nat())
    | Hole _ -> 
      Ok (Zero(), Nat())
    | _ -> 
      Error ("Type mismatch when checking that the term 0 of type nat has type " ^ unparse ty)
     end

  | Ast.Succ e ->
    let elab = elaborate global ctx (Ast.Nat()) ph vars e in
    begin match elab, ty with
    | Ok (e', _), Ast.Nat() -> 
      Ok (Succ e', Nat())
    | Ok (e', _), Hole _ ->
      Ok (Succ e', Nat())
    | Error msg, _ -> Error msg
    | _, _ -> 
      Error ("Type mismatch when checking that the term succ " ^ unparse e ^ " of type nat has type " ^ unparse ty)
    end

  | Ast.Natrec (e, e1, e2) ->
      let v1 = fresh_var (Natrec(e, e1, e2)) ty vars in
      let v2 = fresh_var (Id v1) (Id v1) vars in
      let elab = elaborate global ctx (Ast.Nat()) ph (vars+2) e in
      begin match elab with
      | Ok (e', _) ->  
        begin match ty with
        | Hole (n, l) ->
          let elab1 = elaborate global ctx (Hole (n, l)) ph (vars+1) e1 in
          begin match elab1 with
          | Ok (e1', ty0) ->
            let h1 = Hole.generate (App(ty,ty0)) ph [] in
            let ty' = hfullsubst (Zero()) h1 ty0 in
            let tys = Pi(v1, h1, Ast.Pi(v2, ty', ty')) in
            let elab2 = elaborate global ctx tys ph (vars+1) e2 in (* call elab with ty0' *)
            begin match elab2 with
            | Ok (e2', Ast.Pi(_, nat, Ast.Pi(_, _, _))) ->
              let synt = synthesize vars (nat, Nat()) in
              begin match synt with
              | Ok _ ->
                Ok (Natrec(e', e1', e2'), ty')
              | Error (_, msg) ->
                Error ("Don't know how to unify\n  " ^ unparse nat ^ "\nwith\n  nat\n" ^ msg)
              end
            | Ok (e2', ty') -> 
              Error ("The term\n  " ^ unparse e2' ^ "\nhas type\n  " ^ unparse ty' ^ 
                  "\nbut is expected to have type\n  Π (v? : nat) ?0? → ?1?")  
            | Error msg -> 
              Error msg
            end
          
          | Error msg -> 
            Error msg
          end
        
        | _ -> 
          let elab1 = elaborate global ctx (fullsubst e (Ast.Zero()) ty) ph (vars+2) e1 in
          let tyx = (Pi(v1, Nat(), Pi(v2, fullsubst e (Id v1) ty, fullsubst e (Succ (Id v1)) ty))) in
          let elab2 = elaborate global ctx tyx ph (vars+2) e2 in
          begin match elab1, elab2 with
          | Ok (e1', _), Ok (e2', _) ->
            Ok (Natrec (e', e1', e2'), ty)
          | Error msg, _| _, Error msg -> Error msg
          end
        end
    | Error msg -> 
      Error msg
    end

  | Ast.True() ->
    begin match ty with
    | Ast.Bool() -> 
      Ok (True(), Bool())
    | Hole _ -> 
      Ok (True(), Bool()) 
    | _ -> 
      Error ("Type mismatch when checking that the term true of type bool has type " ^ unparse ty)
    end
  
    | Ast.False() ->
    begin match ty with
    | Ast.Bool() -> 
      Ok (False(), Bool())
    | Hole _ -> 
      Ok (False(), Bool())
    | _ -> 
      Error ("Type mismatch when checking that the term false of type bool has type " ^ unparse ty)
    end
    
  | Ast.If (e, e1, e2) ->
    let elab = elaborate global ctx (Ast.Bool()) ph vars e in
    let elab1 = elaborate global ctx (fullsubst e (Ast.True()) ty) ph vars e1 in
    let elab2 = elaborate global ctx (fullsubst e (Ast.False()) ty) ph vars e2 in
    begin match elab, elab1, elab2 with
    | Ok (e', _), Ok (e1', ty1'), Ok (e2', ty2') ->
      begin match ty with
      | Hole _ ->
        let h1 = Hole.generate ty 0 [] in
        let tyt = hfullsubst (Ast.True()) h1 ty1' in
        let tyf = hfullsubst (Ast.False()) h1 ty2' in
        begin match synthesize vars (tyt, tyf) with 
        | Ok sty ->
          let tyt' = fullsubst h1 (Ast.True()) sty in
          let tyf' = fullsubst h1 (Ast.False()) sty in
          let elabt = elaborate global ctx tyt' ph vars e1' in
          let elabf = elaborate global ctx tyf' ph vars e2' in
          begin match elabt, elabf with
          | Ok _, Ok _ ->
            Ok (If (e', e1', e2'), fullsubst h1 e' sty)
          | _ -> 
            Error ("Failed to unify the types\n  " ^ unparse (fullsubst (Ast.True()) h1 ty1') ^ 
                  "\nand\n  " ^ unparse (fullsubst (Ast.False()) h1 ty2'))
          end
        | _ ->
          let tyt' = fullsubst (Ast.False()) h1 ty1' in
          let tyf' = fullsubst (Ast.True()) h1 ty2' in
          let elabt = elaborate global ctx tyf' ph vars e1' in
          let elabf = elaborate global ctx tyt' ph vars e2' in
          begin match elabt, elabf with
          | Ok _, _ | _, Ok _ -> Ok (If (e', e1', e2'), ty)
          | _ ->
            Error ("Failed to unify the types\n  " ^ unparse (fullsubst (Ast.True()) h1 ty1') ^ 
                  "\nand\n  " ^ unparse (fullsubst (Ast.False()) h1 ty2'))
          end
        end
      | _ ->
        Ok (If (e', e1', e2'), ty)
      end
    | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> 
      Error msg
    end

  | Ast.Star() -> 
    begin match ty with
    | Ast.Unit() -> 
      Ok (Star(), Unit())
    | Hole _ -> 
      Ok (Star(), Unit())
    | _ -> 
      Error ("Type mismatch when checking that the term () of type unit has type " ^ unparse ty)
    end
  
  | Ast.Let (e1, e2) ->
    let elab1 = elaborate global ctx (Ast.Unit()) ph vars e1 in
    begin match elab1 with
    | Ok (e1', _) ->
      begin match ty with
      | Hole (n, l) ->
        let elab2 = elaborate global ctx (Hole (n, l)) ph vars e2 in
        begin match elab2 with
        | Ok (e2', ty2) ->
          let h1 = Hole.generate ty 0 [e1; e1'; Ast.Star()] in
          let ty' = hfullsubst (Ast.Star()) h1 ty2 in
          Ok (Let (e1', e2'), ty')
        | Error msg ->
          Error msg
        end
      | _ ->
        let elab2 = elaborate global ctx (fullsubst e1 (Ast.Star()) ty) ph vars e2 in
        begin match elab2 with
        | Ok (e2', _) ->
          Ok (Let (e1', e2'), ty)
        | Error msg -> Error msg
        end
      end
    | Error msg -> Error msg
    end
  
  | Ast.Abort e -> 
    elaborate global ctx (Ast.Void()) ph vars e
  
  | Pabs (i, e) ->
    let h0 = Hole.generate ty 0 [] in
    let elabt = elaborate global ctx h0 ph vars (eval ty) in
    begin match elabt with
    | Ok (Pathd (Hole (n, l), e1, e2), _) ->
      let h0 = Hole.generate ty 0 [] in
      let elab = elaborate global (((i, Int()), true) :: ctx) (Hole (n, l)) ph vars e in
      let elab1 = elaborate global (((i, Int()), true) :: ctx) h0 ph vars (subst i (I0()) e) in
      let elab2 = elaborate global (((i, Int()), true) :: ctx) h0 ph vars (subst i (I1()) e) in
      begin match elab, elab1, elab2 with
      | Ok (e', _), Ok (ei0, tyi0), Ok (ei1, tyi1) ->
        let synt1 = synthesize vars (eval e1, eval ei0) in
        let synt2 = synthesize vars (eval e2, eval ei1) in
        begin match synt1, synt2 with
        | Ok si0, Ok si1 ->
          let v1 = fresh_var (App(tyi0, tyi1)) ty vars in
          let ty' = fullsubst (I0()) (Id v1) tyi0 in
          let ty'' = fullsubst (I1()) (Id v1) tyi1 in
          let synt = synthesize vars (ty', ty'') in
          begin match synt with
          | Ok st ->
            Ok (Pabs (i, e'), Pathd (Abs(v1,st), si0, si1))
          | Error (_, msg) -> Error msg
          end
        | _ , Ok _ ->
          Error ("Failed to unify\n  " ^
                  unparse e1 ^ "\nwith\n  " ^ unparse ei0 ^ "≡ " ^ unparse e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                  goal_msg ctx (Pabs (i, e)) ty) 
        | _ ->
          Error ("Failed to unify\n  " ^ 
                  unparse e2 ^ "\nwith\n  " ^ unparse ei1 ^ "≡ " ^ unparse e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                  goal_msg ctx (Pabs (i, e)) ty)
        end
      | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> Error msg
      end
    | Ok (Pathd (ty1, e1, e2), _) ->
      let elab = elaborate global (((i, Int()), true) :: ctx) (eval (App(ty1,Id i))) ph vars e in
      let elab1 = elaborate global (((i, Int()), true) :: ctx) (eval (App(ty1,I0()))) ph vars (subst i (I0()) e) in
      let elab2 = elaborate global (((i, Int()), true) :: ctx) (eval (App(ty1,I1()))) ph vars (subst i (I1()) e) in
      begin match elab, elab1, elab2 with
      | Ok (e', _), Ok (ei0, _), Ok (ei1, _) ->
        let synt1 = synthesize vars (eval e1, eval ei0) in
        let synt2 = synthesize vars (eval e2, eval ei1) in
        begin match synt1, synt2 with
        | Ok si0, Ok si1 -> 
          Ok (Pabs (i, e'), Pathd (ty1, si0, si1))
        | Error ((s,s'), msg) , Ok _ ->
          begin match s, s' with
          | At(s',I0()), s | s, At(s',I0()) ->
            let h1 = Hole.generate ty 0 [] in
            let elab0 = elaborate global ctx h1 ph vars s' in
            begin match elab0 with
            | Ok (_, Pathd(_,sa,_)) ->
              let synt = synthesize vars (s, sa) in
              begin match synt with
              | Ok _ -> Ok (Pabs (i, e'), Pathd (ty1, ei0, ei1))
              | Error (_, msg) ->
                Error ("Failed to unify\n  " ^ 
                unparse e1 ^ "\nwith\n  " ^ unparse ei0 ^ "≡ " ^ unparse e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
              end
            | _ -> 
              Error ("Failed to unify\n  " ^ 
                      unparse e1 ^ "\nwith\n  " ^ unparse ei0 ^ "≡ " ^ unparse e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                      msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty)
            end
          | _ ->
            Error ("Failed to unify\n  " ^ 
                  unparse e1 ^ "\nwith\n  " ^ unparse ei0 ^ "≡ " ^ unparse e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                  msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty)
          end
        | _ , Error ((s,s'), msg) ->
          begin match s, s' with
          | At(s',I1()), s | s, At(s',I1()) ->
            let h1 = Hole.generate ty 0 [] in
            let elab0 = elaborate global ctx h1 ph vars s' in
            begin match elab0 with
            | Ok (_, Pathd(_,_,sb)) ->
              let synt = synthesize vars (s, sb) in
              begin match synt with
              | Ok _ -> Ok (Pabs (i, e'), Pathd (ty1, ei0, ei1))
              | Error (_, msg) ->
                Error ("Failed to unify\n  " ^ 
                unparse e2 ^ "\nwith\n  " ^ unparse ei1 ^ "≡ " ^ unparse e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
              end

            | _ -> 
              Error ("Failed to unify\n  " ^ 
                      unparse e2 ^ "\nwith\n  " ^ unparse ei1 ^ "≡ " ^ unparse e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                      msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
            end
          | _ ->
            Error ("Failed to unify\n  " ^ 
                  unparse e2 ^ "\nwith\n  " ^ unparse ei1 ^ "≡ " ^ unparse e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                  msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
          end
        end
      | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> Error msg
      end
    | Ok (Hole _, _) ->
      let h1 = Hole.generate ty 0 [] in
      let ei0 = subst i (I0()) e in
      let ei1 = subst i (I1()) e in
      let elab0 = elaborate global ctx h1 (ph+1) vars ei0 in
      let elab1 = elaborate global ctx h1 (ph+1) vars ei1 in
      begin match elab0, elab1 with
      | Ok (_, tyi0), Ok (_, tyi1) ->
        let v1 = fresh_var (App(tyi0, tyi1)) ty vars in
        let ty' = fullsubst (I0()) (Id v1) tyi0 in
        let ty'' = fullsubst (I1()) (Id v1) tyi1 in
        let synt = synthesize vars (ty', ty'') in
        begin match synt with
        | Ok st ->
          elaborate global ctx (Pathd(Abs(v1,st), ei0, ei1)) (ph+1) vars (Pabs (i, e))
        | Error (_, msg) -> Error msg (* TODO: better error msg *)
        end
      | Error msg, _ | _, Error msg -> Error msg
      end
    | Ok (ty', _) -> 
      Error ("The expression\n  <" ^ i ^ "> " ^ unparse e ^ "\nis expected to have type\n  pathd ?0? ?1? ?2?\nbut has type\n  " ^ unparse ty')
    | Error msg -> 
      Error ("Failed to prove that\n  " ^ unparse ty ^ "\nis a type\n" ^ msg)
    end
  
  | At (e1, e2) ->
    let h1 = Hole.generate ty 0 [] in
    let h2 = Hole.generate ty 1 [] in
    let h3 = Hole.generate ty 2 [] in
    let elab1 = elaborate global ctx (Pathd(h1, h2, h3)) (ph+3) vars e1 in
    let elab2 = elaborate global ctx (Int()) ph vars e2 in
    begin match elab1, elab2 with
    | Ok (e1', ty1'), Ok (e2', _) ->
      begin match ty1' with
      | Pathd (ty', a, b) ->
        if eval e2' = I0() then
          match a, ty' with
          | Hole _, Abs(v, ty') -> (* synthesize ty' and ty*)
            Ok (At (e1', I0()), subst v (I0()) ty')
          | Hole _, Hole _ -> 
            Ok (At (e1', I0()), ty)
          | Hole _, ty' -> 
            Ok (At (e1', I0()), App(ty', I0()))
          | _ -> 
            elaborate global ctx ty ph vars a
        else if eval e2' = I1() then
          match b, ty' with
          | Hole _, Abs(v, ty') -> Ok (At (e1', I1()), subst v (I1()) ty')
          | Hole _, Hole _ -> Ok (At (e1', I1()), ty)
          | Hole _, ty' -> Ok (At (e1', I1()), App(ty', I1()))
          | _ -> 
            elaborate global ctx ty ph vars b
        else
          begin match ty' with
          | Abs(_, ty') ->
            (match synthesize vars (ty', ty) with
            | Ok _ -> Ok (At (e1', e2'), ty)
            | _ -> Error ("Failed to unify\n  " ^ unparse ty' ^ "\nwith\n  " ^ unparse ty))
          | _ -> 
            begin match ty with
            | App(ty, i) ->
              (match synthesize vars (ty', ty), e2 = i with 
              | Ok _, true -> Ok (At (e1', e2'), App(ty, i))
              | _ -> Error ("Failed to unify\n  " ^ unparse ty' ^ "\nwith\n  " ^ unparse ty))
            | ty -> 
              (match synthesize vars (ty', ty) with
              | Ok _ -> Ok (At (e1', e2'), ty) 
              | _ -> Error ("Failed to unify\n  " ^ unparse ty' ^ "\nwith\n  " ^ unparse ty))
            end
          end
      | _ -> 
        Error ("Type mismatch when checking that\n  " ^ unparse e1' ^ 
        "\nof type\n  " ^ unparse ty1' ^ "\nhas type\n  pathd ?0? ?1? ?2? ")
      end
    | Error msg, _ | _, Error msg -> Error msg
    end

  | Pi(x, ty1, ty2) ->
    let h1 = Hole.generate ty 0 [] in
    let elab1 = elaborate global ctx h1 (ph+1) vars ty1 in
    let elab2 = elaborate global (((x, ty1), true) :: ctx) h1 (ph+1) vars ty2 in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1), Ok (ty2', Type n2) -> 
      begin match ty with
      | Type m -> 
        if m >= n1 && m >= n2 then 
          Ok (Pi(x, ty1', ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                "\nof type \n  type (max(" ^ string_of_int n1 ^ ", " ^ string_of_int n2 ^ "))\n has type\n  " ^ string_of_int m)
      | Hole _ -> 
        if n1 > n2 then 
          Ok (Pi(x, ty1', ty2'), Type n1)
        else 
          Ok (Pi(x, ty1', ty2'), Type n2)
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (ty1', Type n), Ok (Hole (k,l), _) -> 
      begin match ty with
      | Type m -> 
        if m >= n then 
          Ok (Pi(x, ty1', Hole (k,l)), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                "\nof type \n  type " ^ string_of_int n ^ "))\n has type\n  " ^ string_of_int m)
      | Hole _ -> 
        Ok (Pi(x, ty1', Hole (k,l)), Type n)
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (Hole (k,l), _), Ok (ty2', Type n) -> 
      begin match ty with
      | Type m -> 
        if m >= n then 
          Ok (Pi(x, Hole (k,l), ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                "\nof type \n  type " ^ string_of_int n ^ "))\n has type\n  " ^ string_of_int m)
      | Hole _ -> 
        Ok (Pi(x, Hole (k,l), ty2'), Type n)
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (Hole (k1,l1), _), Ok (Hole (k2,l2), _) ->
      begin match ty with
      | Type m -> 
          Ok (Pi(x, Hole (k1,l1), Hole (k2,l2)), Type m) 
      | Hole (k, l) -> 
          Ok (Pi(x, Hole (k1,l1), Hole (k2,l2)), Hole(k, l))
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    
    | Ok (ty1', Type _), _ -> 
      Error ("Failed to check that\n  " ^ unparse ty1' ^ "\nis type ")
    | _ -> Error ("Failed to check that\n  " ^ unparse ty2 ^ "\nis type ")
    end
  
  | Sigma(x, ty1, ty2) ->
    let h1 = Hole.generate ty 0 [] in
    let elab1 = elaborate global ctx h1 (ph+1) vars ty1 in
    let elab2 = elaborate global (((x, ty1), true) :: ctx) h1 (ph+1) vars ty2 in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1), Ok (ty2', Type n2) -> 
      begin match ty with
      | Type m -> 
        if m >= n1 && m >= n2 then 
          Ok (Sigma(x, ty1', ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                "\nof type \n  type (max(" ^ string_of_int n1 ^ ", " ^ string_of_int n2 ^ "))\n has type\n  " ^ string_of_int m)
      | Hole _ -> 
        if n1 > n2 then 
          Ok (Sigma(x, ty1', ty2'), Type n1)
        else 
          Ok (Sigma(x, ty1', ty2'), Type n2)
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    
    | Ok (ty1', Type n), Ok (Hole (k,l), _) -> 
      begin match ty with
      | Type m -> 
        if m >= n then 
          Ok (Sigma(x, ty1', Hole (k,l)), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                "\nof type \n  type " ^ string_of_int n ^ "))\n has type\n  " ^ string_of_int m)
      | Hole _ -> 
        Ok (Sigma(x, ty1', Hole (k,l)), Type n)
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (Hole (k,l), _), Ok (ty2', Type n) -> 
      begin match ty with
      | Type m -> 
        if m >= n then 
          Ok (Sigma(x, Hole (k,l), ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ 
                "\nof type \n  type " ^ string_of_int n ^ "))\n has type\n  " ^ string_of_int m)
      | Hole _ -> 
        Ok (Sigma(x, Hole (k,l), ty2'), Type n)
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (Hole (k1,l1), _), Ok (Hole (k2,l2), _) ->
      begin match ty with
      | Type m -> 
          Ok (Sigma(x, Hole (k1,l1), Hole (k2,l2)), Type m)
      | Hole (k, l) ->
          Ok (Sigma(x, Hole (k1,l1), Hole (k2,l2)), Hole(k, l))
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ unparse ty1 ^ ") " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (ty1', Type _), _ -> 
      Error ("Failed to check that\n  " ^ unparse ty1' ^ "\nis type ")
    | _ -> Error ("Failed to check that\n  " ^ unparse ty2 ^ "\nis type ")
    end
  
  | Sum(ty1, ty2) ->
    let h1 = Hole.generate ty 0 [] in
    let elab1 = elaborate global ctx h1 (ph+1) vars ty1 in
    let elab2 = elaborate global ctx h1 (ph+1) vars ty2 in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1), Ok (ty2', Type n2) -> 
      begin match ty with
      | Type m -> 
        if m >= n1 && m >= n2 then 
          Ok (Sum(ty1', ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ 
                "\nof type \n  type (max(" ^ string_of_int n1 ^ ", " ^ string_of_int n2 ^ "))\n has type\n  " ^ string_of_int m)
      | Hole _ -> 
        if n1 > n2 then 
          Ok (Sum(ty1', ty2'), Type n1)
        else 
          Ok (Sum(ty1', ty2'), Type n2)
      | _ ->
        Error ("Type mismatch when checking that\n  " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (ty1', Type n), Ok (Hole (k,l), _) -> 
      begin match ty with
      | Type m -> 
        if m >= n then 
          Ok (Sum(ty1', Hole (k,l)), Type m) 
        else 
          Error ("Type mismatch when checking that \n  " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ 
                "\nof type \n  type " ^ string_of_int n ^ "\nhas type\n  " ^ string_of_int m)
      | Hole _ -> 
        Ok (Sum(ty1', Hole (k,l)), Type n)
      | _ ->
        Error ("Type mismatch when checking that\n  " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (Hole (k,l), _), Ok (ty2', Type n) -> 
      begin match ty with
      | Type m -> 
        if m >= n then 
          Ok (Sum(Hole (k,l), ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ 
                "\nof type \n  type " ^ string_of_int n ^ "\nhas type\n  " ^ string_of_int m)
      | Hole _ -> 
        Ok (Sum(Hole (k,l), ty2'), Type n)
      | _ ->
        Error ("Type mismatch when checking that\n  " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (Hole (k1, l1), _), Ok (Hole (k2, l2), _) ->
      begin match ty with
      | Type m -> 
          Ok (Sum(Hole (k1, l1), Hole (k2, l2)), Type m) 
      | Hole (k, l) -> 
          Ok (Sum(Hole (k1, l1), Hole (k2, l2)), Hole(k, l))
      | _ ->
        Error ("Type mismatch when checking that\n  " ^ unparse ty1 ^ "+ " ^ unparse ty2 ^ "\nhas type\n  " ^ unparse ty)
      end
    | Ok (ty1', Type _), _ -> 
      Error ("Failed to check that\n  " ^ unparse ty1' ^ "\nis type ")
    | _ -> Error ("Failed to check that\n  " ^ unparse ty2 ^ "\nis type ")
    end
  
  | Int() ->
    (match ty with
    | Type m -> Ok (Int(), Type m)
    | Hole _ -> Ok (Int(), Type 0) 
    | _ -> Error ("Type mismatch when checking that\n  I\nhas type\n  " ^ unparse ty))

  | Nat() ->
    (match ty with
    | Type m -> Ok (Nat(), Type m)
    | Hole _ -> Ok (Nat(), Type 0) 
    | _ -> Error ("Type mismatch when checking that\n  nat\nhas type\n  " ^ unparse ty))

  | Bool() ->
    (match ty with
    | Type m -> Ok (Bool(), Type m)
    | Hole _ -> Ok (Bool(), Type 0) 
    | _ -> Error ("Type mismatch when checking that\n  bool\nhas type\n  " ^ unparse ty))

  | Unit() ->
    (match ty with
    | Type m -> Ok (Unit(), Type m)
    | Hole _ -> Ok (Unit(), Type 0) 
    | _ -> Error ("Type mismatch when checking that\n  unit\n has type\n  " ^ unparse ty))

  | Void() ->
    (match ty with
    | Type m -> Ok (Void(), Type m)
    | Hole _ -> Ok (Void(), Type 0) 
    | _ -> Error ("Type mismatch when checking that\n  void\n has type\n  " ^ unparse ty))

  | Pathd(ty1, e1, e2) ->
    let h1 = Hole.generate (App(ty,Pathd(ty1, e1, e2))) 0 [] in
    begin match ty1 with
    | Hole (n,l) ->
      begin match e1, e2 with 
      | Hole (n1,l1), Hole (n2,l2) ->
          begin match ty with
          | Type m ->
            Ok (Pathd(Hole (n,l), Hole (n1,l1), Hole (n2,l2)), Type m)
          | Hole (m,k) ->
            Ok (Pathd(Hole (n,l), Hole (n1,l1), Hole (n2,l2)), Hole (m,k))
          | _ -> Error ("Failed to check that\n  " ^ unparse ty ^ "\nis a type")
          end
      | _ ->
        let elab1 = elaborate global ctx (Hole (n,l)) (ph+1) vars e1 in
        let elab2 = elaborate global ctx (Hole (n,l)) (ph+1) vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', _), Ok (e2', _) ->
          begin match ty with
          | Type m ->
            Ok (Pathd(Hole (n,l), e1', e2'), Type m)
          | Hole (m,k) ->
            Ok (Pathd(Hole (n,l), e1', e2'), Hole (m,k))
          | _ -> Error ("Failed to check that\n  " ^ unparse ty ^ "\nis a type")
          end
          | _ -> Error ("Failed to check that\n  " ^ unparse e1 ^ "\nhas type\n ?0?")
        end
      end
    | Abs(x, Hole (n,l)) ->
      begin match e1, e2 with 
      | Hole (n1,l1), Hole (n2,l2) ->
          begin match ty with
          | Type m ->
            Ok (Pathd(Abs(x, Hole (n,l)), Hole (n1,l1), Hole (n2,l2)), Type m)
          | Hole (m,k) ->
            Ok (Pathd(Abs(x, Hole (n,l)), Hole (n1,l1), Hole (n2,l2)), Hole (m,k))
          | _ -> Error ("Failed to check that\n  " ^ unparse ty ^ "\nis a type")
          end
      | _ ->
        let elab1 = elaborate global ctx (Hole (n,l)) (ph+1) vars e1 in
        let elab2 = elaborate global ctx (Hole (n,l)) (ph+1) vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', _), Ok (e2', _) ->
          begin match ty with
          | Type m ->
            Ok (Pathd(Abs(x,Hole (n,l)), e1', e2'), Type m)
          | Hole (m,k) ->
            Ok (Pathd(Abs(x,Hole (n,l)), e1', e2'), Hole (m,k))
          | _ -> Error ("Failed to check that\n  " ^ unparse ty ^ "\nis a type")
            end
        | Ok _, Error msg -> Error ("Failed to check that\n  " ^ unparse e2 ^ "\nhas type\n ?0?\n" ^ msg)
        | Error msg, _ -> Error ("Failed to check that\n  " ^ unparse e1 ^ "\nhas type\n " ^ unparse (Hole (n,l)) ^ "\n" ^ msg)
        end
      end
    | ty1 ->
      let elabi0 = elaborate global ctx h1 (ph+1) vars (eval (App (ty1, I0()))) in
      let elabi1 = elaborate global ctx h1 (ph+1) vars (eval (App (ty1, I1()))) in
      begin match elabi0, elabi1 with
      | Ok (tyi0, _), Ok (tyi1, _) ->
        let elab = elaborate global ctx h1 (ph+1) vars (eval ty1) in
        let elab1 = elaborate global ctx tyi0 (ph+1) vars (eval e1) in
        let elab2 = elaborate global ctx tyi1 (ph+1) vars (eval e2) in
        begin match elab, elab1, elab2 with
        | Ok (ty1', Pi(_, i, ty2)), Ok (e1', _), Ok (e2', _) ->
          begin match eval i, eval ty2 with
          | Int(), Type n | Hole _, Type n ->
            begin match ty with
            | Type m ->
              if m >= n then 
                Ok (Pathd(ty1', e1', e2'), Type m) 
              else 
                Error ("Failed to check that\n  pathd " ^ 
                        unparse ty1' ^ " " ^  unparse e1' ^ " " ^  unparse e2' ^ 
                        "\nhas type\n  " ^ unparse ty)
            | Hole _ -> 
              Ok (Pathd(ty1', e1', e2'), Type n)
            | _ -> Error ("Failed to check that\n  " ^ unparse ty2 ^ "\nis a type")
            end
          | Int() , _ | Hole _, _ -> Error ("Failed to check that\n  " ^ unparse ty2 ^ "\nis a type ") 
          | _ -> Error ("Failed to unify \n  " ^ unparse i ^ "with\n  I ")
          end
        | Ok (ty1', _), Ok _, Ok _ ->
          Error ("Type mismatch when checking that\n  " ^ unparse ty1' ^ "\nhas type\n  Π (v? : I) ?0? ")
        | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> 
          Error msg
        end
      | Error msg, _ | _, Error msg -> 
        Error msg
      end
    end
    
  | Type n ->
    (match ty with
    | Type m -> 
      if m > n 
      then Ok (Type n, Type m) 
      else Error ("Universe level conflict\n  " ^ string_of_int n ^ "\ncannot have type\n  " ^ string_of_int m ^ "\n(This is known as Girard's paradox)")
    | Hole _ -> Ok (Type n, Type (n+1)) 
    | _ -> Error ("Type mismatch when checking that\n  " ^ string_of_int n ^ "\nhas type\n  " ^ unparse ty))
  | Wild() ->
    begin match find_ty ty ctx with
    | Ok var -> Ok (Id var, ty)
    | Error _ -> 
      Error ("Failed to synthesize placeholder for the current goal:\n" ^ 
      print ctx ^ "-------------------------------------------\n ⊢ " ^ unparse ty)
    end
    
  | Hole (n, l) -> 
    Ok (Hole (n, l), ty) (* used for tests *)
    (*Error ("Failed to synthesize placeholder ?" ^ n ^ "? for type\n  " ^ unparse ty)*)
