(**
 * (c) Copyright 2019 Bruno Bentzen. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Desc: The elaborator performs the endpoint ε-reductions for dependent paths.
         The unifier implements the boundary separation rule
 **)

open Basis
open Context
open Local
open Ast
open Substitution
open Eval 

let rec print ctx =
	match (List.rev ctx) with
	| [] -> "" 
	| ((id, ty), _) :: ctx' -> 
		" " ^ id ^ " : " ^ Pretty.print ty ^ "\n" ^ print ctx'

let goal_msg ctx e ty =
  "when checking that\n  " ^ Pretty.print e ^ "\nhas the expected type\n" ^ print ctx ^ 
  "-------------------------------------------\n ⊢ " ^ Pretty.print ty

(* Checks whether the type of a given expression is the given type *)

let rec elaborate global ctx lvl ty ph vars = function
  | Id x ->
    begin match var_type x ctx with
    | Ok ty' ->
      let c = check_var_ty x ty ctx in
      let h = Hole.is ty in
      let h' = Hole.is ty' in
      let d = is_declared x ctx in
      begin match c, h, h', d with
      | true , _, _ , _ | _ , _, true , _ ->  Ok (Id x, ty)
      | _ , true, _ , _ ->  Ok (Id x, ty')
      | false , false, false , true ->
        let h1 = Hole.generate ty ph [] in
        begin match elaborate global ctx lvl h1 ph vars ty' with
        | Ok (_, tTy') ->
          let u = unify global ctx lvl ph vars (eval ty', eval ty, tTy') true in
          begin match u with
          | Ok s -> Ok (Id x, s) 
          | Error (_, msg) ->
            Error ("The variable " ^ x ^ " has type\n   " ^ Pretty.print (eval ty') ^ 
                  "\nbut is expected to have type\n  " ^ Pretty.print ty ^ "\n" ^ msg)
          end
        | Error msg -> (* This case is impossible *)
          Error msg
        end
      | false , false, false , false -> 
        begin match Global.unfold x global with
        | Ok (body, ty') ->
          let h1 = Hole.generate ty ph [] in
          begin match elaborate global ctx lvl h1 ph vars ty' with
          | Ok (_, tTy') ->
            let u = unify global ctx lvl ph vars (eval ty', eval ty, tTy') true in
            begin match u with
            | Ok s -> Ok (body, s)
            | _ -> 
              Error (x ^ " has type \n  " ^ Pretty.print ty' ^ "\nbut is expected to have type\n  " ^ Pretty.print ty)
            end
          | Error msg -> (* This case is impossible *)
            Error msg
          end
        | Error msg -> Error msg
        end
      end
    | Error _ -> Error ("No declaration for the variable " ^ x)
    end
    
  | I0() ->
    begin match ty with
    | Ast.Int() -> 
      Ok (I0(), Int())
    | Hole _ -> 
      Ok (I0(), Int())
    | _ -> Error ("Type mismatch when checking that the term i0 of type I has type " ^ Pretty.print ty)
  end
  
  | I1() ->
    begin match ty with
    | Ast.Int() -> 
      Ok (I1(), Int())
    | Hole _ -> 
      Ok (I1(), Int())
    | _ -> Error ("Type mismatch when checking that the term i1 of type I has type " ^ Pretty.print ty)
    end

  | Abs (x, e) -> 
    begin match ty with
    | Pi (y, ty1, ty2) ->
      if has_var x ty then
        let v1 = fresh_var e ty vars in
        let elab = elaborate global (((v1, ty1), true) :: ctx) lvl (subst y (Ast.Id v1) ty2) ph vars e in
        begin match elab with
        | Ok (e', ty2') -> Ok (Abs (v1, e'), Pi (y, ty1, ty2'))
        | Error msg -> Error msg
        end
      else
        let elab = elaborate global (((x, ty1), true) :: ctx) lvl (subst y (Ast.Id x) ty2) ph vars e in
        begin match elab with
        | Ok (e', ty2') -> Ok (Abs (x, e'), Pi (y, ty1, ty2'))
        | Error msg -> Error msg
        end
    | Hole _ -> 
      let h1 = Hole.generate ty ph [] in
      let h2 = Hole.generate ty (ph+1) [] in
      elaborate global ctx lvl (Pi(x, h1, h2)) (ph+2) vars (Abs (x, e))
    | _ -> 
      Error ("The term\n  λ " ^ x ^ ", " ^ Pretty.print e ^ "\nhas type\n  " ^ Pretty.print ty ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1?")
    end
  
  | App (e1, e2) ->
    let h1 = Hole.generate ty ph [] in
    let v1 = fresh_var (App(e1, e2)) ty vars in
    let elab2 = elaborate global ctx lvl h1 (ph+1) (vars+1) e2 in
    begin match elab2 with
    | Ok (e2', ty2') ->
      let h2 = Hole.generate ty (ph+1) [Id v1; e2; e2'] in
      let helper ty1' =
        let elab1 = elaborate global ctx lvl ty1' (ph+1) (vars+1) e1 in
        begin match elab1 with
        | Ok (e1', Pi(x, _, ty')) ->
          Ok (App (e1', e2'), subst x e2 ty')
        | Ok _ -> 
          Error ("The term\n  " ^ Pretty.print e1 ^ 
                  "\nis expected to have type\n " ^ Pretty.print ty1') 
        | Error msg -> 
          Error ("The term\n  " ^ Pretty.print e1 ^ 
                "\nis expected to have type\n  " ^ Pretty.print ty1' ^ "\n" ^ msg)
        end
      in
      if e2 = e2' then
        let ty1' = Pi(v1, fullsubst e2 h2 ty2', fullsubst e2 h2 ty) in
        helper ty1'
      else
        let subs x = hfullsubst e2' h2 (fullsubst e2 h2 x) in
        let ty1' = Pi(v1, subs ty2', subs ty) in
        helper ty1'
    | Error msg -> Error msg
    end
  
  | Pair (e1, e2) -> 
    begin match ty with
    | Sigma(y, ty1, ty2) ->
      let elab1 = elaborate global ctx lvl ty1 ph vars e1 in
      let elab2 = elaborate global ctx lvl (subst y e1 ty2) ph vars e2 in
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
      elaborate global ctx lvl (Sigma(v1, h1, h2)) (ph+2) (vars+1) (Pair (e1, e2))
    | _ ->
      Error ("Type mismatch when checking that the term (" ^ Pretty.print e1 ^ ", " ^ Pretty.print e2 ^ ") of type Σ (v? : ?0?) ?1? has type " ^ Pretty.print ty)
    end
    
  | Ast.Fst e ->
    let h1 = Hole.generate ty 0 [] in
    let elab = elaborate global ctx lvl h1 (ph+1) (vars+1) e in
    begin match elab with
    | Ok (e', Sigma(_, ty', _)) ->
      let elabTy = elaborate global ctx lvl h1 ph vars ty in
      begin match elabTy with
      | Ok (_, tTy) ->
        let u = unify global ctx lvl ph vars (eval ty, eval ty', tTy) false in
        begin match u with
        | Ok _ ->
          Ok (Fst e', ty') 
        | Error (_, msg) ->
          Error ("Don't know how to unify\n  " ^ Pretty.print ty ^ "\nwith\n  " ^ Pretty.print ty' ^ "\n" ^ msg)
        end
      | Error msg -> (* This case is impossible *)
        Error msg
      end
    | Ok (e', ty') -> 
      Error ("The term\n  " ^ Pretty.print e' ^ "\nhas type\n  " ^ Pretty.print ty' ^ "\nbut is expected to have type\n  Σ (v0 : ?0?) ?1?")
    | Error msg ->
      Error ("The term\n  " ^ Pretty.print e ^ "\nis expected to have type\n  Σ (v0 : ?0?) ?1?" ^ "\n" ^ msg)
    end

  | Snd e ->
    let h1 = Hole.generate ty 0 [] in
    let elab = elaborate global ctx lvl h1 (ph+1) (vars+1) e in
    begin match elab with
    | Ok (e', Sigma(x, _, ty2)) ->
      let ty' = subst x (Fst e') ty2 in
      let elabTy = elaborate global ctx lvl h1 ph vars ty in
      begin match elabTy with
      | Ok (_, tTy) ->
        let u = unify global ctx lvl ph vars (eval ty, eval ty', tTy) false in
        begin match u with
        | Ok _ ->
          Ok (Snd e', ty')
        | Error (_, msg) ->
          Error ("Don't know how to unify\n  " ^ Pretty.print ty ^ "\nwith\n  " ^ Pretty.print ty' ^ "\n" ^ msg)
        end
      | Error msg -> (* This case is impossible *)
        Error msg
      end
      
    | Ok (e', ty') -> 
      Error ("The term\n  " ^ Pretty.print e' ^ "\nhas type\n  " ^ Pretty.print ty' ^ "\nbut is expected to have type\n  Σ (v0 : ?0?) ?1?")
    | Error msg ->
      Error ("The term\n  " ^ Pretty.print e ^ "\nis expected to have type\n  Σ (v0 : ?0?) ?1?" ^ "\n" ^ msg)
    end
  
  | Ast.Inl e ->
    begin match ty with
    | Ast.Sum (ty1, ty2) ->
      let elab = elaborate global ctx lvl ty1 ph vars e in
      begin match elab with
      | Ok (e', ty1') -> Ok (Inl e', Sum(ty1', ty2))
      | Error msg -> Error msg
      end
    | Hole _ ->
      let h1 = Hole.generate ty 0 [] in
      let h2 = Hole.generate ty 1 [] in
      elaborate global ctx lvl (Sum(h1, h2)) (ph+2) vars (Inl e)
    | _ ->
      Error ("Type mismatch when checking that the term inl " ^ Pretty.print e ^ " of type ?0? + ?1? has type " ^ Pretty.print ty)
    end

  | Ast.Inr e -> 
    begin match ty with
    | Ast.Sum (ty1, ty2) ->
      let elab = elaborate global ctx lvl ty2 ph vars e in
      begin match elab with
      | Ok (e', ty2') -> Ok (Inr e', Sum(ty1, ty2'))
      | Error msg -> Error msg
      end
    | Hole _ ->
      let h1 = Hole.generate ty 0 [] in
      let h2 = Hole.generate ty 1 [] in
      elaborate global ctx lvl (Sum(h1, h2)) (ph+2) vars (Inr e)
    | _ -> 
      Error ("Type mismatch when checking that the term inr " ^ Pretty.print e ^ " of type ?0? + ?1? has type " ^ Pretty.print ty)
    end
  
  | Case (e, e1, e2) ->
    let h1 = Hole.generate ty 0 [] in
    let h2 = Hole.generate ty 1 [] in
    let elab = elaborate global ctx lvl (Sum (h1, h2)) (ph+2) vars e in
    begin match elab with
    | Ok (e', Sum (ty1, ty2)) ->
      begin match ty with
      | Hole (n, l) ->
        let elab1 = elaborate global ctx lvl (Hole (n, l)) ph (vars+1) e1 in
        let elab2 = elaborate global ctx lvl (Hole (n, l)) ph (vars+1) e2 in
        begin match elab1, elab2 with
        | Ok (e1', Ast.Pi(x, ty1', tyl)), Ok (e2', Ast.Pi(y, ty2', tyr)) ->
          let elabTy = elaborate global ctx lvl h1 ph vars (Ast.Pi(x, ty1', tyl)) in
          begin match elabTy with
          | Ok (_, tTy) ->
            let u1 = unify global ctx lvl ph vars (ty1, ty1', tTy) false in
            let u2 = unify global ctx lvl ph vars (ty2, ty2', tTy) false in
            let tyl' = hfullsubst (Ast.Inl(Id x)) h1 tyl in
            let tyr' = hfullsubst (Ast.Inr(Id y)) h1 tyr in
            begin
              match tyl', tyr' with
              | Type n, Type m ->
                if n > m then
                  Ok (Case(e', e1', e2'), Type n)
                else
                Ok (Case(e', e1', e2'), Type m)
              | _ ->
                let u = unify global ctx lvl ph vars (tyl', tyr', tTy) false in
                begin match u1, u2, u with
                | Ok _, Ok _, Ok st ->
                  let st' = hfullsubst h1 e st in
                  Ok (Case(e', e1', e2'), st')
                | Ok _, Ok _, _ ->
                  Error ("Failed to unify\n  " ^ Pretty.print tyl' ^ "\nwith\n  " ^ Pretty.print tyr')
                | Ok _, _, _ ->
                  Error ("The term\n  " ^ Pretty.print e2' ^ "\nhas type\n  " ^ Pretty.print (Ast.Pi(y, ty2', tyr)) ^ 
                  "\nbut is expected to have type\n  Π (" ^ y ^ " : " ^ Pretty.print ty2 ^ ") ?1?")
                | _ ->
                  Error ("The term\n  " ^ Pretty.print e1' ^ "\nhas type\n  " ^ Pretty.print (Ast.Pi(x, ty1', tyl)) ^ 
                        "\nbut is expected to have type\n  Π (" ^ x ^ " : " ^ Pretty.print ty1 ^ ") ?1?")
              end
            end
          | Error msg -> (* This case is impossible *)
            Error msg
          end

        | Ok (e1', ty'), Ok (_, Pi(_,_,_)) -> 
          Error ("The term\n  " ^ Pretty.print e1' ^ "\nhas type\n  " ^ Pretty.print ty' ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1?")
        | Ok _, Ok (e2', ty') -> 
          Error ("The term\n  " ^ Pretty.print e2' ^ "\nhas type\n  " ^ Pretty.print ty' ^ "\nbut is expected to have type\n  Π (v? : ?0?) ?1?")
        | Error msg, _ | _, Error msg -> Error msg
        end
      | _ -> 
        let v1 = fresh_var (Sum(ty1, ty2)) ty vars in
        let elab1 = elaborate global ctx lvl (Pi(v1, ty1, fullsubst e (Inl (Id v1)) ty)) ph (vars+1) e1 in
        let elab2 = elaborate global ctx lvl (Pi(v1, ty2, fullsubst e (Inr (Id v1)) ty)) ph (vars+1) e2 in
        begin match elab1, elab2 with
        | Ok (e1', _), Ok (e2', _) ->
          Ok (Case(e', e1', e2'), ty)
        | Error msg, _ | _, Error msg -> Error msg
        end
      end
    | Ok (e', ty') -> Error ("Type mismatch when checking that the term " ^ Pretty.print e' ^ " of type " ^ Pretty.print ty' ^ "has type ?0? + ?1?")
    | Error msg -> Error msg
    end

  | Ast.Zero() ->
    begin match ty with
    | Nat() -> 
      Ok (Zero(), Nat())
    | Hole _ -> 
      Ok (Zero(), Nat())
    | _ -> 
      Error ("Type mismatch when checking that the term 0 of type nat has type " ^ Pretty.print ty)
     end

  | Ast.Succ e ->
    let elab = elaborate global ctx lvl (Ast.Nat()) ph vars e in
    begin match elab, ty with
    | Ok (e', _), Ast.Nat() -> 
      Ok (Succ e', Nat())
    | Ok (e', _), Hole _ ->
      Ok (Succ e', Nat())
    | Error msg, _ -> Error msg
    | _, _ -> 
      Error ("Type mismatch when checking that the term succ " ^ Pretty.print e ^ " of type nat has type " ^ Pretty.print ty)
    end

  | Ast.Natrec (e, e1, e2) ->
      let v1 = fresh_var (Natrec(e, e1, e2)) ty vars in
      let v2 = fresh_var (Id v1) (Id v1) (vars+1) in
      let elab = elaborate global ctx lvl (Ast.Nat()) ph (vars+2) e in
      begin match elab with
      | Ok (e', _) ->  
        begin match ty with
        | Hole (n, l) ->
          let elab1 = elaborate global ctx lvl (Hole (n, l)) ph (vars+1) e1 in
          begin match elab1 with
          | Ok (e1', ty0) ->
            let h1 = Hole.generate (App(ty,ty0)) ph [] in
            let ty' = hfullsubst (Zero()) h1 ty0 in
            let tys = Pi(v1, h1, Ast.Pi(v2, ty', ty')) in
            let elab2 = elaborate global ctx lvl tys ph (vars+1) e2 in (* call elab with ty0' *)
            begin match elab2 with
            | Ok (e2', Ast.Pi(_, nat, Ast.Pi(_, _, _))) ->
              let u = unify global ctx lvl ph vars (Nat(), nat, Type (Num 0)) false in
              begin match u with
              | Ok _ ->
                Ok (Natrec(e', e1', e2'), ty')
              | Error (_, msg) ->
                Error ("Don't know how to unify\n  " ^ Pretty.print nat ^ "\nwith\n  nat\n" ^ msg)
              end
            | Ok (e2', ty') -> 
              Error ("The term\n  " ^ Pretty.print e2' ^ "\nhas type\n  " ^ Pretty.print ty' ^ 
                  "\nbut is expected to have type\n  Π (v? : nat) ?0? → ?1?")  
            | Error msg -> 
              Error msg
            end
          
          | Error msg -> 
            Error msg
          end
        
        | _ -> 
          let elab1 = elaborate global ctx lvl (eval (fullsubst e (Ast.Zero()) ty)) ph (vars+2) e1 in
          let tyx = (Pi(v1, Nat(), Pi(v2, fullsubst e (Id v1) ty, fullsubst e (Succ (Id v1)) ty))) in
          let elab2 = elaborate global ctx lvl tyx ph (vars+2) e2 in
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
      Error ("Type mismatch when checking that the term true of type bool has type " ^ Pretty.print ty)
    end
  
    | Ast.False() ->
    begin match ty with
    | Ast.Bool() -> 
      Ok (False(), Bool())
    | Hole _ -> 
      Ok (False(), Bool())
    | _ -> 
      Error ("Type mismatch when checking that the term false of type bool has type " ^ Pretty.print ty)
    end
    
  | Ast.If (e, e1, e2) ->
    let elab = elaborate global ctx lvl (Ast.Bool()) ph vars e in
    let elab1 = elaborate global ctx lvl (fullsubst e (Ast.True()) ty) ph vars e1 in
    let elab2 = elaborate global ctx lvl (fullsubst e (Ast.False()) ty) ph vars e2 in
    begin match elab, elab1, elab2 with
    | Ok (e', _), Ok (e1', ty1'), Ok (e2', ty2') ->
      begin match ty with
      | Hole _ ->
        let h1 = Hole.generate ty 0 [] in
        let tyt = hfullsubst (Ast.True()) h1 ty1' in
        let tyf = hfullsubst (Ast.False()) h1 ty2' in
        begin
          match tyt, tyf with
          | Type n, Type m ->
            if n > m then
              Ok (If(e', e1', e2'), Type n)
            else
            Ok (If(e', e1', e2'), Type m)
          | _ ->
            let elabTy = elaborate global ctx lvl h1 ph vars ty in
            begin match elabTy with
            | Ok (_, tTy) ->
              let u = unify global ctx lvl ph vars (tyt, tyf, tTy) false in
              begin match u with 
              | Ok sty ->
                let tyt' = fullsubst h1 (Ast.True()) sty in
                let tyf' = fullsubst h1 (Ast.False()) sty in
                let elabt = elaborate global ctx lvl tyt' ph vars e1' in
                let elabf = elaborate global ctx lvl tyf' ph vars e2' in
                begin match elabt, elabf with
                | Ok _, Ok _ ->
                  Ok (If (e', e1', e2'), fullsubst h1 e' sty)
                | _ -> 
                  Error ("Failed to unify the types\n  " ^ Pretty.print (fullsubst (Ast.True()) h1 ty1') ^ 
                        "\nand\n  " ^ Pretty.print (fullsubst (Ast.False()) h1 ty2'))
                end
              | _ ->
                let tyt' = fullsubst (Ast.False()) h1 ty1' in
                let tyf' = fullsubst (Ast.True()) h1 ty2' in
                let elabt = elaborate global ctx lvl tyf' ph vars e1' in
                let elabf = elaborate global ctx lvl tyt' ph vars e2' in
                begin match elabt, elabf with
                | Ok _, _ | _, Ok _ -> Ok (If (e', e1', e2'), ty)
                | _ ->
                  Error ("Failed to unify the types\n  " ^ Pretty.print (fullsubst (Ast.True()) h1 ty1') ^ 
                        "\nand\n  " ^ Pretty.print (fullsubst (Ast.False()) h1 ty2'))
                end
              end
            | Error msg -> (* This case is impossible *)
              Error msg
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
      Error ("Type mismatch when checking that the term () of type unit has type " ^ Pretty.print ty)
    end
  
  | Ast.Let (e1, e2) ->
    let elab1 = elaborate global ctx lvl (Ast.Unit()) ph vars e1 in
    begin match elab1 with
    | Ok (e1', _) ->
      begin match ty with
      | Hole (n, l) ->
        let elab2 = elaborate global ctx lvl (Hole (n, l)) ph vars e2 in
        begin match elab2 with
        | Ok (e2', ty2) ->
          let h1 = Hole.generate ty 0 [e1; e1'; Ast.Star()] in
          let ty' = hfullsubst (Ast.Star()) h1 ty2 in
          Ok (Let (e1', e2'), ty')
        | Error msg ->
          Error msg
        end
      | _ ->
        let elab2 = elaborate global ctx lvl (fullsubst e1 (Ast.Star()) ty) ph vars e2 in
        begin match elab2 with
        | Ok (e2', _) ->
          Ok (Let (e1', e2'), ty)
        | Error msg -> Error msg
        end
      end
    | Error msg -> Error msg
    end
  
  | Ast.Abort e ->
    let elab = elaborate global ctx lvl (Ast.Void()) ph vars e in
    begin
      match elab with
      | Ok (e', _) ->
        Ok (Abort e', ty)
      | Error msg -> Error msg
    end
  
  | Ast.Coe(i, j, ety, e) ->
    begin
      let h0 = Hole.generate ty 0 [] in
      let elabi = elaborate global ctx lvl (Int()) ph vars i in
      let elabj = elaborate global ctx lvl (Int()) ph vars j in
      let elabti = elaborate global ctx lvl h0 ph vars (eval (App(ety, i))) in
      let elabtj = elaborate global ctx lvl h0 ph vars (eval (App(ety, j))) in
      begin
        match elabi, elabj, elabti, elabtj with
        | Ok (i', _), Ok (j', _), Ok (tyi, eTy), Ok (tyj, _) ->
          let elab = elaborate global ctx lvl (eval tyi) ph vars e in
          let elabt = elaborate global ctx lvl h0 ph vars ty in
          begin
            match elab, elabt with
            | Ok (e', _), Ok (ty', _) ->
              let u = unify global ctx lvl ph vars (eval tyj, ty', eTy) false in
              begin match u with
              | Ok st ->
                Ok (Coe (i', j', eval ety, e'), st)
              | Error (_, msg) -> 
                Error ("Failed to unify the terms\n  " ^ Pretty.print tyj ^ "\nand\n  " ^ Pretty.print ty' ^ 
                "\nwhen checking that the coercion\n  " ^ Pretty.print (Coe(i, j, ety, e)) ^ (* Improve error msg *)
                "\nhas type\n  " ^ Pretty.print (eval ty) ^
                "\n" ^ msg)
              end
            | Error msg, _ ->
              Error ("The coercion failed because\n  " ^ Pretty.print e ^ "\ndoes not have type\n  " ^ Pretty.print tyi ^ "\n" ^ msg)
            | _, Error msg ->
              Error msg
          end

        | Error msg, _, _, _ | _, Error msg, _, _ | _, _, Error msg, _ | _, _, _, Error msg ->
          Error msg
      end
    end
  
  | Ast.Hfill(e, e1, e2) ->
    begin
      match ty with
      | Ast.Pi(_, int, Pi(j, int', ty')) ->
        if eval int = Int() && eval int = eval int' then
          begin
            let jty = Pi(j, Int(), ty') in
            let elabi0 = elaborate global ctx lvl jty ph vars (Abs("v?", eval (App(e, I0())))) in
            let elabi1 = elaborate global ctx lvl jty ph vars (Abs("v?", eval (App(e, I1())))) in
            let elab1i0 = elaborate global ctx lvl jty ph vars (Abs("v?", eval (App(e1, I0())))) in
            let elab2i0 = elaborate global ctx lvl jty ph vars (Abs("v?", eval (App(e2, I0())))) in
            begin
              
              match elabi0, elabi1, elab1i0, elab2i0 with
              | Ok (ei0, _), Ok (ei1, _), Ok (e1i0, _), Ok (e2i0, _) ->
                begin
                  let elab1i1 = elaborate global ctx lvl jty ph vars (Abs("v?", eval (App(e1, I1())))) in
                  let elab2i1 = elaborate global ctx lvl jty ph vars (Abs("v?", eval (App(e2, I1())))) in
                  match elab1i1, elab2i1 with
                  | Ok _, Ok _ ->

                      let u1 = unify global ctx lvl ph vars (eval ei0, e1i0, jty) false in
                      let u2 = unify global ctx lvl ph vars (eval ei1, e2i0, jty) false in
                      begin 
                        match u1, u2 with
                        | Ok _, Ok _ ->
                          Ok (Hfill(e, e1, e2), ty)
                        | Error (_, msg), _ ->
                          Error ("Error when unifying the terms\n  " ^ 
                          Pretty.print (eval ei0) ^ "\nand\n  " ^ Pretty.print (eval e1i0) ^
                          "\n" ^ msg)
                        | _, Error (_, msg) -> 
                        Error ("Error when unifying the terms\n  " ^ 
                        Pretty.print (eval ei1) ^ "\nand\n  " ^ Pretty.print (eval e2i0) ^
                        "\n" ^ msg)
                      end
                      
                  | Error msg, _ | _, Error msg -> Error msg                  
                end
                
              | Error msg, _, _, _ ->
                Error ("Error when checking that the homogeneous filling\n  " ^ Pretty.print (Hfill(e, e1, e2)) ^ 
                "\nhas type\n  I → I → " ^ Pretty.print ty' ^ 
                "\nThe i0-face of the lid\n  " ^ Pretty.print (eval (App(e, I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.print ty' ^ 
                "\n" ^ msg)
              | _, Error msg, _, _ ->
                Error ("Error when checking that the homogeneous filling\n  " ^ Pretty.print (Hfill(e, e1, e2)) ^ 
                "\nhas type\n  I → I → " ^ Pretty.print ty' ^ 
                "\nThe i1-face of the lid\n  " ^ Pretty.print (eval (App(e, I1()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.print ty' ^ 
                "\n" ^ msg)
              | _, _, Error msg, _ ->
                Error ("Error when checking that the homogeneous filling\n  " ^ Pretty.print (Hfill(e, e1, e2)) ^ 
                "\nhas type\n  I → I → " ^ Pretty.print ty' ^ 
                "\nThe i0-face of the i0-tube\n  " ^ Pretty.print (eval (App(e1, I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.print ty' ^ 
                "\n" ^ msg)
              | _, _, _, Error msg ->
                Error ("Error when checking that the homogeneous filling\n  " ^ Pretty.print (Hfill(e, e1, e2)) ^ 
                "\nhas type\n  I → I → " ^ Pretty.print ty' ^ 
                "\nThe i0-face of the i1-tube\n  " ^ Pretty.print (eval (App(e2, I0()))) ^ "\ndoes not have the expected type\n  " ^ Pretty.print ty' ^ 
                "\n" ^ msg)
            end

          end
        else
          Error ("The homogeneous filling\n  " ^ Pretty.print (Hfill(e, e1, e2)) ^ 
            "\nhas type\n  " ^ Pretty.print int ^ "→  " ^ Pretty.print int' ^ "→ " ^ Pretty.print ty' ^
            "\nbut is expected to have type\n  I → I → ?0?")
      
      | Hole (_, _) | Pi(_, _, Hole (_, _)) -> 
        let h0 = Hole.generate ty 0 [] in
        let elabi0 = elaborate global ctx lvl h0 ph vars (eval (Ast.App(e, Ast.I0()))) in
        begin
          match elabi0 with
          | Ok (ei0, ty') ->
            let elabi1 = elaborate global ctx lvl ty' ph vars (eval (Ast.App(e, Ast.I1()))) in
            let elab1i0 = elaborate global ctx lvl ty' ph vars (eval (Ast.App(e1, Ast.I0()))) in
            let elab2i1 = elaborate global ctx lvl ty' ph vars (eval (Ast.App(e2, Ast.I0()))) in
            begin
              match elabi1, elab1i0, elab2i1 with
              | Ok (ei1, _), Ok (e1i0, _), Ok (e2i0, _) ->
                begin
                  let u1 = unify global ctx lvl ph vars (eval ei0, e1i0, ty') false in
                  let u2 = unify global ctx lvl ph vars (eval ei1, e2i0, ty') false in
                  begin 
                    match u1, u2 with
                    | Ok _, Ok _ ->
                      Ok (Hfill(e, e1, e2), Ast.Pi("v?", Int(), Pi("v?", Int(), ty')))
                    | Error (_, msg), _ | _, Error (_, msg) -> 
                      Error ("Failed composition, endpoints do not match:\n" ^ msg)
                  end
                end

              | Error msg, _, _ ->
                Error ("Error when checking that the line\n  " ^ Pretty.print (eval (Ast.App(e, Ast.I1()))) ^ "\nhas type\n  " ^ Pretty.print ty' ^ 
                  "\nin the homogeneous filling\n  hfill (" ^ Pretty.print e ^ 
                  ")\n    | i0 → " ^ Pretty.print e1 ^
                   "\n    | i1 → " ^ Pretty.print e2 ^ "\n" ^ msg)
              | _, Error msg, _ | _, _, Error msg ->
                Error ("Failed composition: " ^ msg)
            end
          | Error msg -> Error msg
        end
      | ty ->
        Error ("The homogeneous filling\n  " ^ Pretty.print (Hfill(e, e1, e2)) ^ 
        "\nis expected to have type\n  I → I → ?0?\nand not\n  " ^ Pretty.print ty)
      end
  
  | Pabs (i, e) ->
    let h0 = Hole.generate ty 0 [] in
    let elabt = elaborate global ctx lvl h0 ph vars (eval ty) in
    begin match elabt with
    | Ok (Pathd (Hole (n, l), e1, e2), _) ->
      let h0 = Hole.generate ty 0 [] in
      let elab = elaborate global (((i, Int()), true) :: ctx) lvl (Hole (n, l)) ph vars e in
      let elab1 = elaborate global (((i, Int()), true) :: ctx) lvl h0 ph vars (subst i (I0()) e) in
      let elab2 = elaborate global (((i, Int()), true) :: ctx) lvl h0 ph vars (subst i (I1()) e) in
      begin match elab, elab1, elab2 with
      | Ok (e', _), Ok (ei0, tyi0), Ok (ei1, tyi1) ->
        let u1 = unify global ctx lvl ph vars (eval ei0, eval e1, tyi0) false in
        let u2 = unify global ctx lvl ph vars (eval ei1, eval e2, tyi1) false in
        begin match u1, u2 with
        | Ok ui0, Ok ui1 ->
          let v1 = fresh_var (App(tyi0, tyi1)) ty vars in
          let ty' = fullsubst (I0()) (Id v1) tyi0 in
          let ty'' = fullsubst (I1()) (Id v1) tyi1 in
          let elabTy = elaborate global ctx lvl h0 ph vars ty in

          begin match elabTy with
          | Ok (_, tTy) ->
            let u = unify global ctx lvl ph vars (ty', ty'', tTy) false in
            begin match u with
            | Ok st ->
              Ok (Pabs (i, e'), Pathd (Abs(v1,st), ui0, ui1))
            | Error (_, msg) -> Error msg
            end

          | Error msg -> (* This case is impossible *)
            Error msg
          end
        | _ , Ok _ ->
          Error ("Failed to unify\n  " ^
                  Pretty.print e1 ^ "\nwith\n  " ^ Pretty.print ei0 ^ "≡ " ^ Pretty.print e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                  goal_msg ctx (Pabs (i, e)) ty) 
        | _ ->
          Error ("Failed to unify\n  " ^ 
                  Pretty.print e2 ^ "\nwith\n  " ^ Pretty.print ei1 ^ "≡ " ^ Pretty.print e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                  goal_msg ctx (Pabs (i, e)) ty)
        end
      | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> Error msg
      end
    | Ok (Pathd (ty1, e1, e2), _) ->
      let elab = elaborate global (((i, Int()), true) :: ctx) lvl (eval (App(ty1,Id i))) ph vars e in
      let elab1 = elaborate global ctx lvl (eval (App(ty1, I0()))) ph vars (eval (subst i (I0()) e)) in
      let elab2 = elaborate global ctx lvl (eval (App(ty1, I1()))) ph vars (eval (subst i (I1()) e)) in
      begin match elab, elab1, elab2 with
      | Ok (e', _), Ok (ei0, tyi0), Ok (ei1, tyi1) ->
        let u1 = unify global ctx lvl ph vars (eval ei0, eval e1, tyi0) false in
        let u2 = unify global ctx lvl ph vars (eval ei1, eval e2, tyi1) false in
        begin match u1, u2 with
        | Ok ui0, Ok ui1 -> 
          Ok (Pabs (i, e'), Pathd (ty1, ui0, ui1))
        | Error ((s,s'), msg) , Ok _ ->
          begin match s, s' with
          | At(s',I0()), s | s, At(s',I0()) ->
            let h1 = Hole.generate ty 0 [] in
            let elab0 = elaborate global ctx lvl h1 ph vars s' in
            begin match elab0 with
            | Ok (_, Pathd(sty, sa, _)) ->
              let u = unify global ctx lvl ph vars (s, sa, eval (App(sty, I0()))) false in
              begin match u with
              | Ok _ -> 
                Ok (Pabs (i, e'), Pathd (ty1, ei0, ei1))
              | Error (_, msg) ->
                Error ("Failed to unify\n  " ^ 
                Pretty.print e1 ^ "\nwith\n  " ^ Pretty.print ei0 ^ "≡ " ^ Pretty.print e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
              end
            | _ -> 
              Error ("Failed to unify\n  " ^ 
                      Pretty.print e1 ^ "\nwith\n  " ^ Pretty.print ei0 ^ "≡ " ^ Pretty.print e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                      msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty)
            end
          | _ ->
            Error ("Failed to unify\n  " ^ 
                  Pretty.print e1 ^ "\nwith\n  " ^ Pretty.print ei0 ^ "≡ " ^ Pretty.print e ^ "[i0/" ^ i ^ "]" ^ "\n" ^
                  msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty)
          end
        | _ , Error ((s,s'), msg) ->
          begin match s, s' with
          | At(s',I1()), s | s, At(s',I1()) ->
            let h1 = Hole.generate ty 0 [] in
            let elab0 = elaborate global ctx lvl h1 ph vars s' in
            begin match elab0 with
            | Ok (_, Pathd(sty,_,sb)) ->
              let u = unify global ctx lvl ph vars (s, sb, eval (App(sty, I1()))) false in
              begin match u with
              | Ok _ -> Ok (Pabs (i, e'), Pathd (ty1, ei0, ei1))
              | Error (_, msg) ->
                Error ("Failed to unify\n  " ^ 
                Pretty.print e2 ^ "\nwith\n  " ^ Pretty.print ei1 ^ "≡ " ^ Pretty.print e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
              end

            | _ -> 
              Error ("Failed to unify\n  " ^ 
                      Pretty.print e2 ^ "\nwith\n  " ^ Pretty.print ei1 ^ "≡ " ^ Pretty.print e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                      msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
            end
          | _ ->
            Error ("Failed to unify\n  " ^
                  Pretty.print e2 ^ "\nwith\n  " ^ Pretty.print ei1 ^ "≡ " ^ Pretty.print e ^ "[i1/" ^ i ^ "]" ^ "\n" ^
                  msg ^ "\n" ^ goal_msg ctx (Pabs (i, e)) ty )
          end
        end
      | Error msg, _, _ ->
        Error ("Error when checking that the path abstracted term\n  " ^ 
        Pretty.print (Pabs(i, eval e)) ^ "\nhas type\n  " ^ Pretty.print ty ^ "\n" ^ msg)
      | _, Error msg, _->
        Error ("Error when checking that the path abstracted term\n  " ^ 
        Pretty.print (Pabs(i, eval e)) ^ "\nhas type\n  " ^ Pretty.print ty ^ 
        "\nThe i0-endpoint\n  " ^ Pretty.print (eval (subst i (I0()) e)) ^ 
        "\ndoes not have type\n  " ^ Pretty.print (eval (App(ty1, I0()))) ^
        "\n" ^ msg)
      | _, _, Error msg -> 
        Error ("Error when checking that the path abstracted term\n  " ^ 
        Pretty.print (Pabs(i, eval e)) ^ "\nhas type\n  " ^ Pretty.print ty ^ 
        "\nThe i1-endpoint\n  " ^ Pretty.print (eval (subst i (I1()) e)) ^ 
        "\ndoes not have type\n  " ^ Pretty.print (eval (App(ty1, I1()))) ^ 
        "\n" ^ msg)
      end
    | Ok (Hole _, _) ->
      let h1 = Hole.generate ty 0 [] in
      let ei0 = subst i (I0()) e in
      let ei1 = subst i (I1()) e in
      begin 
        let elab0 = elaborate global ctx lvl h1 (ph+1) vars ei0 in
        let elab1 = elaborate global ctx lvl h1 (ph+1) vars ei1 in
        match elab0, elab1 with
        | Ok (_, tyi0), Ok (_, tyi1) ->
          let v1 = fresh_var (App(tyi0, tyi1)) ty vars in
          let ty' = fullsubst (I0()) (Id v1) tyi0 in
          let ty'' = fullsubst (I1()) (Id v1) tyi1 in
          begin 
            match elaborate global ctx lvl h1 (ph+1) vars ty' with
            | Ok (ty', tTy') ->
              let u = unify global ctx lvl ph vars (ty', ty'', tTy') false in
              begin match u with
              | Ok st ->
                elaborate global ctx lvl (Pathd(Abs(v1,st), ei0, ei1)) (ph+1) vars (Pabs (i, e))
              | Error (_, msg) ->
                Error ("Failed to unify the types\n  " ^ Pretty.print ty' ^ "\nand\n  " ^ Pretty.print ty'' ^ "\n" ^ msg)
                
              end
            | Error msg -> (* This case never occurs *)
              Error msg
          end
        | Error msg, _ | _, Error msg -> Error msg
      end
    | Ok (ty', _) -> 
      Error ("The expression\n  <" ^ i ^ "> " ^ Pretty.print e ^ "\nis expected to have type\n  pathd ?0? ?1? ?2?\nbut has type\n  " ^ Pretty.print ty')
    | Error msg -> 
      Error ("Failed to prove that\n  " ^ Pretty.print (eval ty) ^ "\nis a type\n" ^ msg)
    end
  
  | At (e1, e2) ->
    let h1 = Hole.generate ty 0 [] in
    let h2 = Hole.generate ty 1 [] in
    let h3 = Hole.generate ty 2 [] in
    let elab1 = elaborate global ctx lvl (Pathd(h1, h2, h3)) (ph+3) vars e1 in
    let elab2 = elaborate global ctx lvl (Int()) ph vars e2 in
    begin match elab1, elab2 with
    | Ok (e1', ty1'), Ok (e2', _) ->
      begin match ty1' with
      | Pathd (ty', a, b) ->
        if eval e2' = I0() then
          match a, ty' with
          | Hole _, Abs(v, ty') -> (* unify ty' and ty*)
            Ok (At (e1', I0()), subst v (I0()) ty')
          | Hole _, Hole _ -> 
            Ok (At (e1', I0()), ty)
          | Hole _, ty' -> 
            Ok (At (e1', I0()), App(ty', I0()))
          | _ -> 
            elaborate global ctx lvl ty ph vars a
        else if eval e2' = I1() then
          match b, ty' with
          | Hole _, Abs(v, ty') -> Ok (At (e1', I1()), subst v (I1()) ty')
          | Hole _, Hole _ -> Ok (At (e1', I1()), ty)
          | Hole _, ty' -> Ok (At (e1', I1()), App(ty', I1()))
          | _ -> 
            elaborate global ctx lvl ty ph vars b
        else
          begin match ty' with
          | Abs(i, ty') ->
            let ty2' = subst i e2 ty' in
            let elabTy = elaborate global ctx lvl h1 ph vars ty2' in
            begin
              match elabTy with
              | Ok (_, tTy) ->
                let u = unify global ctx lvl ph vars (ty2', ty, tTy) false in
                begin
                  match u with
                  | Ok st -> Ok (At (e1', e2'), st)
                  | _ -> 
                    Error ("Failed to unify\n  " ^ Pretty.print ty2' ^ "\nwith\n  " ^ Pretty.print ty)
                end
              | Error msg -> (* This case is impossible *)
                Error msg
            end
            
          | _ -> 
            begin match ty with
            | App(ty, i) ->
              let elabTy = elaborate global ctx lvl h1 ph vars ty' in
              begin
                match elabTy with
                | Ok (_, tTy) ->
                  let u = unify global ctx lvl ph vars (ty', ty, tTy) false in
                  begin 
                    match u, e2 = i with 
                    | Ok st, true -> Ok (At (e1', e2'), App(st, i))
                    | _ -> Error ("Failed to unify\n  " ^ Pretty.print ty' ^ "\nwith\n  " ^ Pretty.print ty)
                  end
                | Error msg -> (* This case is impossible *)
                  Error msg
              end
            | ty ->
              let elabTy = elaborate global ctx lvl h1 ph vars ty' in
              begin
                match elabTy with
                | Ok (_, tTy) ->
                  let u = unify global ctx lvl ph vars (ty', ty, tTy) false in
                  begin
                    match u with
                    | Ok st -> Ok (At (e1', e2'), st) 
                    | _ -> Error ("Failed to unify\n  " ^ Pretty.print ty' ^ "\nwith\n  " ^ Pretty.print ty)
                  end
              | Error msg -> (* This case is impossible *)
                Error msg
            end
            end
          end
      | _ -> 
        Error ("Type mismatch when checking that\n  " ^ Pretty.print e1' ^ 
        "\nof type\n  " ^ Pretty.print ty1' ^ "\nhas type\n  pathd ?0? ?1? ?2? ")
      end
    | Error msg, _ | _, Error msg -> Error msg
    end

  | Pi(x, ty1, ty2) ->
    let h1 = Hole.generate ty 0 [] in
    let elab1 = elaborate global ctx lvl h1 (ph+1) vars ty1 in
    let elab2 = elaborate global (((x, ty1), true) :: ctx) lvl h1 (ph+1) vars ty2 in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1), Ok (ty2', Type n2) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n1, m) && Universe.leq (n2, m) then 
          Ok (Pi(x, ty1', ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Π ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ 
                "\nof type \n  " ^ Pretty.print (eval (Type (Max (n1, n2)))) ^ "\nhas type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Pi(x, ty1', ty2'), Type (Universe.eval (Max(n1, n2))))
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end

    | Ok (ty1', Type n), Ok (Hole (k,l), _) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n, m) then 
          Ok (Pi(x, ty1', Hole (k,l)), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Π ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ 
                "\nof type \n  " ^ Pretty.print (Type n) ^ "\nhas type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Pi(x, ty1', Hole (k,l)), Type n) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (Hole (k,l), _), Ok (ty2', Type n) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n, m) then 
          Ok (Pi(x, Hole (k,l), ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Π ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ 
                "\nof type \n  " ^ Pretty.print (Type n) ^ "\n has type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Pi(x, Hole (k,l), ty2'), Type n) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (Hole (k1,l1), _), Ok (Hole (k2,l2), _) ->
      begin match ty with
      | Type m -> 
          Ok (Pi(x, Hole (k1,l1), Hole (k2,l2)), Type m) 
      | Hole (k, l) -> 
          Ok (Pi(x, Hole (k1,l1), Hole (k2,l2)), Hole(k, l))
      | _ ->
        Error ("Type mismatch when checking that\n  Π ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    
    | Ok (_, Type _), Error msg -> 
      Error ("Failed to check that\n  " ^ Pretty.print (eval ty2) ^ "\nis a type\n" ^ msg)
    | Error msg, _ -> Error ("Failed to check that\n  " ^ Pretty.print (eval ty1) ^ "\nis a type\n" ^ msg)
    | _ -> Error ("Failed to check that\n  " ^ Pretty.print (eval ty1) ^ "\nis a type")
    end
  
  | Sigma(x, ty1, ty2) ->
    let h1 = Hole.generate ty 0 [] in
    let elab1 = elaborate global ctx lvl h1 (ph+1) vars ty1 in
    let elab2 = elaborate global (((x, ty1), true) :: ctx) lvl h1 (ph+1) vars ty2 in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1), Ok (ty2', Type n2) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n1, m) && Universe.leq (n2, m) then 
          Ok (Sigma(x, ty1', ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ 
                "\nof type \n  " ^ Pretty.print (eval (Type (Max(n1, n2)))) ^ "\n has type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Sigma(x, ty1', ty2'), Type (Universe.eval (Max(n1, n2))))
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    
    | Ok (ty1', Type n), Ok (Hole (k,l), _) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n, m) then 
          Ok (Sigma(x, ty1', Hole (k,l)), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ 
                "\nof type \n  " ^ Pretty.print (Type n) ^ "\n has type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Sigma(x, ty1', Hole (k,l)), Type n) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (Hole (k,l), _), Ok (ty2', Type n) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n, m) then 
          Ok (Sigma(x, Hole (k,l), ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  Σ ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ 
                "\nof type \n  type " ^ Pretty.print (Type n) ^ "))\n has type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Sigma(x, Hole (k,l), ty2'), Type n) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (Hole (k1,l1), _), Ok (Hole (k2,l2), _) ->
      begin match ty with
      | Type m -> 
          Ok (Sigma(x, Hole (k1,l1), Hole (k2,l2)), Type m)
      | Hole (k, l) ->
          Ok (Sigma(x, Hole (k1,l1), Hole (k2,l2)), Hole(k, l))
      | _ ->
        Error ("Type mismatch when checking that\n  Σ ( " ^ x ^ " : " ^ Pretty.print ty1 ^ ") " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (_, Type _), Error msg -> 
      Error ("Failed to check that\n  " ^ Pretty.print ty2 ^ "\nis a type\n" ^ msg)
    | _ -> Error ("Failed to check that\n  " ^ Pretty.print ty1 ^ "\nis a type")
    end
  
  | Sum(ty1, ty2) ->
    let h1 = Hole.generate ty 0 [] in
    let elab1 = elaborate global ctx lvl h1 (ph+1) vars ty1 in
    let elab2 = elaborate global ctx lvl h1 (ph+1) vars ty2 in
    begin match elab1, elab2 with
    | Ok (ty1', Type n1), Ok (ty2', Type n2) -> 
      begin 
        match ty with
        | Type m -> 
          if Universe.leq (n1, m) && Universe.leq (n2, m) then 
            Ok (Sum(ty1', ty2'), Type m) 
          else 
            Error ("Type mismatch when checking that \n  " ^ Pretty.print ty1 ^ "+ " ^ Pretty.print ty2 ^ 
                  "\nof type \n  " ^ Pretty.print (eval (Type (Max(n1, n2)))) ^ "\n has type\n  " ^ Pretty.print (Type m))
        | Hole _ -> 
          Ok (Sum(ty1', ty2'), Type (Universe.eval (Max(n1, n2))))
        | _ ->
          Error ("Type mismatch when checking that\n  " ^ Pretty.print ty1 ^ "+ " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (ty1', Type n), Ok (Hole (k,l), _) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n, m) then 
          Ok (Sum(ty1', Hole (k,l)), Type m) 
        else 
          Error ("Type mismatch when checking that \n  " ^ Pretty.print ty1 ^ "+ " ^ Pretty.print ty2 ^ 
                "\nof type \n  " ^ Pretty.print (Type n) ^ "\nhas type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Sum(ty1', Hole (k,l)), Type n) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error ("Type mismatch when checking that\n  " ^ Pretty.print ty1 ^ "+ " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (Hole (k,l), _), Ok (ty2', Type n) -> 
      begin match ty with
      | Type m -> 
        if Universe.leq (n, m) then 
          Ok (Sum(Hole (k,l), ty2'), Type m) 
        else 
          Error ("Type mismatch when checking that \n  " ^ Pretty.print ty1 ^ "+ " ^ Pretty.print ty2 ^ 
                "\nof type \n  " ^ Pretty.print (Type n) ^ "\nhas type\n  " ^ Pretty.print (Type m))
      | Hole _ -> 
        Ok (Sum(Hole (k,l), ty2'), Type n) (* TODO: hole might have live in a higher universe *)
      | _ ->
        Error ("Type mismatch when checking that\n  " ^ Pretty.print ty1 ^ "+ " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (Hole (k1, l1), _), Ok (Hole (k2, l2), _) ->
      begin match ty with
      | Type m -> 
          Ok (Sum(Hole (k1, l1), Hole (k2, l2)), Type m) 
      | Hole (k, l) -> 
          Ok (Sum(Hole (k1, l1), Hole (k2, l2)), Hole(k, l))
      | _ ->
        Error ("Type mismatch when checking that\n  " ^ Pretty.print ty1 ^ "+ " ^ Pretty.print ty2 ^ "\nhas type\n  " ^ Pretty.print ty)
      end
    | Ok (_, Type _), Error msg -> 
      Error ("Failed to check that\n  " ^ Pretty.print ty2 ^ "\nis type\n" ^ msg)
    | _ -> Error ("Failed to check that\n  " ^ Pretty.print ty1 ^ "\nis type")
    end
  
  | Int() ->
    (match ty with
    | Type m -> Ok (Int(), Type m)
    | Hole _ -> Ok (Int(), Type (Num 0)) 
    | _ -> Error ("Type mismatch when checking that\n  I\nhas type\n  " ^ Pretty.print ty))

  | Nat() ->
    (match ty with
    | Type m -> Ok (Nat(), Type m)
    | Hole _ -> Ok (Nat(), Type (Num 0)) 
    | _ -> Error ("Type mismatch when checking that\n  nat\nhas type\n  " ^ Pretty.print ty))

  | Bool() ->
    (match ty with
    | Type m -> Ok (Bool(), Type m)
    | Hole _ -> Ok (Bool(), Type (Num 0)) 
    | _ -> Error ("Type mismatch when checking that\n  bool\nhas type\n  " ^ Pretty.print ty))

  | Unit() ->
    (match ty with
    | Type m -> Ok (Unit(), Type m)
    | Hole _ -> Ok (Unit(), Type (Num 0)) 
    | _ -> Error ("Type mismatch when checking that\n  unit\n has type\n  " ^ Pretty.print ty))

  | Void() ->
    (match ty with
    | Type m -> Ok (Void(), Type m)
    | Hole _ -> Ok (Void(), Type (Num 0)) 
    | _ -> Error ("Type mismatch when checking that\n  void\n has type\n  " ^ Pretty.print ty))

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
          | _ -> Error ("Failed to check that\n  " ^ Pretty.print ty ^ "\nis a type")
          end
      | _ ->
        let elab1 = elaborate global ctx lvl (Hole (n,l)) (ph+1) vars e1 in
        let elab2 = elaborate global ctx lvl (Hole (n,l)) (ph+1) vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', tye1), Ok (e2', tye2) ->
          begin match ty with
          | Type m ->
            if eval tye1 = eval tye2 then
              Ok (Pathd(tye1, e1', e2'), Type m)
            else
              Ok (Pathd(Hole (n,l), e1', e2'), Type m)
          | Hole (m,k) ->
            if eval tye1 = eval tye2 then
              Ok (Pathd(eval tye1, e1', e2'), Hole (m,k))
            else 
              Ok (Pathd(Hole (n,l), e1', e2'), Hole (m,k))
          | _ -> Error ("Failed to check that\n  " ^ Pretty.print ty ^ "\nis a type")
          end
        | _ -> Error ("Failed to check that\n  " ^ Pretty.print e1 ^ "\nhas type\n ?0?")
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
          | _ -> Error ("Failed to check that\n  " ^ Pretty.print ty ^ "\nis a type")
          end
      | _ ->
        let elab1 = elaborate global ctx lvl (Hole (n,l)) (ph+1) vars e1 in
        let elab2 = elaborate global ctx lvl (Hole (n,l)) (ph+1) vars e2 in
        begin match elab1, elab2 with
        | Ok (e1', _), Ok (e2', _) ->
          begin match ty with
          | Type m ->
            Ok (Pathd(Abs(x,Hole (n,l)), e1', e2'), Type m)
          | Hole (m,k) ->
            Ok (Pathd(Abs(x,Hole (n,l)), e1', e2'), Hole (m,k))
          | _ -> Error ("Failed to check that\n  " ^ Pretty.print ty ^ "\nis a type")
            end
        | Ok _, Error msg -> Error ("Failed to check that\n  " ^ Pretty.print e2 ^ "\nhas type\n ?0?\n" ^ msg)
        | Error msg, _ -> Error ("Failed to check that\n  " ^ Pretty.print e1 ^ "\nhas type\n " ^ Pretty.print (Hole (n,l)) ^ "\n" ^ msg)
        end
      end
    | ty1 ->
      let elabi0 = elaborate global ctx lvl h1 (ph+1) vars (eval (App (ty1, I0()))) in
      let elabi1 = elaborate global ctx lvl h1 (ph+1) vars (eval (App (ty1, I1()))) in
      begin match elabi0, elabi1 with
      | Ok (tyi0, tTyi0), Ok (tyi1, _) ->
        let elab = elaborate global ctx lvl h1 (ph+1) vars (eval ty1) in
        let elab1 = elaborate global ctx lvl tyi0 (ph+1) vars (eval e1) in
        let elab2 = elaborate global ctx lvl tyi1 (ph+1) vars (eval e2) in
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
                        Pretty.print ty1' ^ " " ^  Pretty.print e1' ^ " " ^  Pretty.print e2' ^ 
                        "\nhas type\n  " ^ Pretty.print ty)
            | Hole _ -> 
              Ok (Pathd(ty1', e1', e2'), Type n)
            | _ -> Error ("Failed to check that\n  " ^ Pretty.print ty2 ^ "\nis a type")
            end
          | Int() , Hole _ | Hole _, Hole _ -> 
            Ok (Pathd(ty1', e1', e2'), tTyi0)
          | _ -> Error ("Failed to unify \n  " ^ Pretty.print i ^ "with\n  I ")
          end
        | Ok (ty1', _), Ok _, Ok _ ->
          Error ("Type mismatch when checking that\n  " ^ Pretty.print ty1' ^ "\nhas type\n  Π (v? : I) ?0?")
        | Error msg, _, _| _, Error msg, _ | _, _, Error msg -> 
          Error msg
        end
      | Error msg, _ | _, Error msg -> 
        Error msg
      end
    end
    
  | Type n ->
    begin
      match Universe.decl lvl n with
      | Ok _ ->
        begin
          match ty with
          | Type m -> 
            if Universe.leq (n, m) then 
              Ok (Type n, Type m) 
            else 
              Error ("Universe inconsistency: the universe level of\n  " ^ Pretty.print (Type n) ^ 
              "\nmust be inferior to the universe level of\n  " ^ Pretty.print (Type m) ^ 
              "\nFailed to prove that" ^ Pretty.print_level n ^ "≤" ^ Pretty.print_level m)
          | Hole _ -> Ok (Type n, Type (Suc n))
          | _ -> 
            Error ("Type mismatch when checking that\n  " ^ Pretty.print (Type n) ^ 
            "\nhas type\n  " ^ Pretty.print ty)
        end
      | Error msg -> Error msg
    end


    
  
  | Wild() ->
    (*begin match find_ty ty ctx with
    | Ok var -> Ok (Id var, ty)
    | Error _ -> *)
      Error ("Failed to synthesize placeholder for the current goal:\n" ^ 
      print ctx ^ "-------------------------------------------\n ⊢ " ^ Pretty.print (eval ty))
    (* end *)

  | Hole (n, l) -> 
    Ok (Hole (n, l), ty) (* used for tests *)
    (*Error ("Failed to synthesize placeholder ?" ^ n ^ "? for type\n  " ^ Pretty.print ty)*)

(* Unifies two expressions at type *)

and unify global ctx lvl ph vars x lift =
  match x with
  | e, e', ty ->
    if e = e' then
      Ok e
    else
      match e, e', ty with
      | Hole (n1, l1), Hole (n2, l2), _ ->
        begin match l1, l2 with
        | [], [] -> Ok (Hole (n1, l1))
        | l1, [] -> Ok (Hole (n1, l1))
        | [], l2 -> Ok (Hole (n2, l2))
        | _ ->
          let rec common_el = function
          | [], [] -> Error()
          | _, [] | [], _ -> Error()
          | e :: l1 , e' :: l2 ->
            if List.mem e l2 then
              Ok e
            else if List.mem e' l1 then
              Ok e'
            else
              common_el (l1, l2)
          in
          match common_el (l1,l2) with
          | Ok e -> Ok e
          | Error() ->
            Error ((Hole (n1, l1), Hole (n2, l2)), 
                  "Failed to unify the placeholder\n  ?" ^ 
                  n1 ^ "?\nwhose suitable candidates are\n" ^ 
                  (String.concat " " (List.map Pretty.print l1)) ^
                  "\nwith the placeholder\n  ?" ^ 
                  n2 ^ "?\nwhose suitable candidates are\n" ^ 
                  (String.concat " " (List.map Pretty.print l2))) 
        end

      | e , _, Pathd(_, _, _) ->
        Ok e

      | e , Hole (n, l), _ | Hole (n, l), e, _ ->
        begin match l with
        | [] -> Ok e
        | _ ->
          let rec helper = function
          | [] -> false
          | e' :: l' -> e' = e || helper l' in
          if helper l then 
            Ok e 
          else 
            Error ((e , Hole (n, l)),
                    "Failed to unify the placeholder\n  " ^ 
                    Pretty.print (Ast.Hole (n, l)) ^ "\nwith the suitable candidates\n" ^ 
                    (String.concat " " (List.map Pretty.print l)))
        end
      
      | Pi (x, ty1, ty2), Pi (x', ty1', ty2'), ty -> 
        let v1 = fresh_var ty2 ty2' vars in
        let u1 = unify global ctx lvl ph (vars+1) (ty1, ty1', ty) lift in
        begin match u1 with
        | Ok s1 -> 
          let x2 = fullsubst ty1 s1 (subst x (Id v1) ty2) in
          let x2' = fullsubst ty1' s1 (subst x' (Id v1) ty2') in
          let u2 = unify global (((v1, s1), true) :: ctx) lvl ph (vars+1) (x2, x2', ty) lift in
          begin match u2 with
          | Ok s2 -> Ok (Pi (v1, s1, s2))
          | Error msg -> Error msg
          end
        | Error msg -> Error msg
        end

      | Sigma (x, ty1, ty2), Sigma (x', ty1', ty2'), ty ->
        let v1 = fresh_var ty2 ty2' vars in
        let u1 = unify global ctx lvl ph (vars+1) (ty1, ty1', ty) lift in
        begin match u1 with
        | Ok s1 -> 
          let x2 = fullsubst ty1 s1 (subst x (Id v1) ty2) in
          let x2' = fullsubst ty1' s1 (subst x' (Id v1) ty2') in
          let u2 = unify global (((v1, s1), true) :: ctx) lvl ph (vars+1) (x2, x2', ty) lift in
          begin match u2 with
          | Ok s2 -> Ok (Sigma (v1, s1, s2))
          | Error (s, msg) -> Error (s, "Don't know how to unify\n  " ^ Pretty.print ty2 ^ "\nwith\n  " ^ Pretty.print ty2' ^ "\n" ^ msg)
          end
        | Error (s, msg) -> Error (s, "Don't know how to unify\n  " ^ Pretty.print ty1 ^ "\nwith\n  " ^ Pretty.print ty1' ^ "\n" ^ msg)
        end

      | Sum (ty1, ty2) , Sum (ty1', ty2'), ty ->
        let u1 = unify global ctx lvl ph vars (ty1, ty1', ty) lift in
        let u2 = unify global ctx lvl ph vars (ty2, ty2', ty) lift in
        begin match u1, u2 with
        | Ok s1, Ok s2 -> Ok (Sum (s1, s2))
        | Error msg, _ | _ , Error msg -> 
          Error msg
        end

      | Pathd (e, e1, e2) , Pathd (e', e1', e2'), ty ->
        let u = unify global ctx lvl ph vars (e, e', Pi("v?", Int(), ty)) lift in
        let u1 = unify global ctx lvl ph vars (e1, e1', eval (App(e, I0()))) lift in
        let u2 = unify global ctx lvl ph vars (e2, e2', eval (App(e, I1()))) lift in
        begin match u, u1, u2 with
        | Ok s, Ok s1, Ok s2 -> 
          Ok (Pathd (s, s1, s2))

          (* If not unifiable, we give it the benefit of the doubt *)

        | Ok s, _, Ok s2 -> 
          let h1 = Hole.generate (App(s, s2)) ph [] in
          let h2 = Hole.generate (App(s, s2)) (ph+1) [] in
          Ok (Pathd (s, At(h1, h2), s2))
        | Ok s, Ok s1, _ ->
          let h1 = Hole.generate (App(s, s1)) ph [] in
          let h2 = Hole.generate (App(s, s1)) (ph+1) [] in
          Ok (Pathd (s, s1, At(h1, h2)))
        | Error msg, _, _ | _ , Error msg, _ -> 
          Error (fst msg, "Don't know how to unify the pathd types due to the following errors:\n " ^ snd msg)
        end

      | Abs (x, e), Abs (x', e'), Pi(y, ty1 , ty2) ->
        if e = e' then
          Ok (Abs (x, e))
        else if Hole.is e' then
          Ok (Abs (x, e))
        else if Hole.is e then
          Ok (Abs (x, e'))
        else 
          begin match eval ty1 with
          | Int() | Hole(_,_) ->
            let h1 = Hole.generate ty2 ph [] in
            let elabt0 = elaborate global ctx lvl h1 ph vars (subst y (I0()) ty2) in
            let elabt1 = elaborate global ctx lvl h1 ph vars (subst y (I1()) ty2) in
            begin match elabt0, elabt1 with
            | Ok (tyi0, _), Ok (tyi1, _) ->
              let elab0 = elaborate global ctx lvl tyi0 ph vars (subst x (I0()) e) in
              let elab0' = elaborate global ctx lvl tyi0 ph vars (subst x' (I0()) e') in
              let elab1 = elaborate global ctx lvl tyi1 ph vars (subst x (I1()) e) in
              let elab1' = elaborate global ctx lvl tyi1 ph vars (subst x' (I1()) e') in
              begin match elab0, elab0', elab1, elab1' with
              | Ok (ei0, _), Ok (ei0', _), Ok (ei1, _), Ok (ei1', _) -> 
                let u0 = unify global ctx lvl ph (vars+1) (ei0, ei0', tyi0) lift in
                let u1 = unify global ctx lvl ph (vars+1) (ei1, ei1', tyi1) lift in
                begin match u0, u1 with
                | Ok _, Ok _ -> Ok (Abs (x, e))
                | Error msg, _ | _, Error msg -> Error msg
                end
              | Error msg, _, _, _ | _, Error msg, _, _ | _, _, Error msg, _ | _, _, _, Error msg -> 
                Error ((Abs (x, e), Abs (x', e')), "Failed endpoint unification of\n  " ^ Pretty.print e ^ 
                  "[" ^ x ^ "/i0]\nwith\n  " ^ Pretty.print e' ^ "[" ^ x' ^ "/i0]\nand\n  " ^ Pretty.print e ^ 
                  "[" ^ x ^ "/i1]\nwith\n  " ^ Pretty.print e' ^ "[" ^ x' ^ "/i1]\n" ^ msg)
              end
            | Error msg, _ | _, Error msg -> (* This case is impossible *)
              Error ((Abs (x, e), Abs (x', e')), msg)
            end
          | _ ->
            let v1 = fresh_var e e' vars in
            let u = unify global (((v1, ty1), true) :: ctx) lvl ph (vars+1) (subst x (Id v1) e, subst x' (Id v1) e', subst y (Id v1) ty2) lift in
            begin match u with
            | Ok s -> Ok (Abs (v1, s))
            | Error msg -> Error msg
            end
          end

      | App (e1, e2), App (e1', e2'), ty ->
        let h1 = Hole.generate ty ph [] in
        let elab2 = elaborate global ctx lvl h1 ph vars e2 in
        begin 
          match elab2 with
          | Ok (_, ty2) ->
            let u2 = unify global ctx lvl ph vars (e2, e2', ty2) lift in
            let v1 = fresh_var (App(e1, e1')) ty vars in
            let u1 = unify global ctx lvl ph vars (e1, e1', Pi(v1, ty2, fullsubst e2 (Id v1) ty)) lift in
            begin 
              match u1, u2 with
              | Ok s1, Ok s2 -> Ok (App (s1, s2))
              | Error msg, _ | _, Error msg ->
                  
                (* If not unifiable check endpoints *)

                begin
                  let helper x y = 
                    match x, y with
                    | Ok _, Ok _ -> Ok (App (e1, e2))
                    | Error msg, _ | _, Error msg -> Error msg
                  in

                  match eval e2, eval e2', eval ty2 with
                  | Id _, Id _, Int() ->
                    let i0 x = eval (App (x, I0())) in
                    let i1 x = eval (App (x, I1())) in
                    let ui0 = unify global ctx lvl ph vars (i0 e1, i0 e1', ty2) lift in
                    let ui1 = unify global ctx lvl ph vars (i1 e1, i1 e1', ty2) lift in
                    helper ui0 ui1
                  
                  | _, Id _, Int() ->
                    let i0 x = eval (App (x, I0())) in
                    let i1 x = eval (App (x, I1())) in
                    let ui0 = unify global ctx lvl ph vars (App (e1, e2), i0 e1', ty2) lift in
                    let ui1 = unify global ctx lvl ph vars (App (e1, e2), i1 e1', ty2) lift in
                    helper ui0 ui1
                  
                  | Id _, _, Int() ->
                    let i0 x = eval (App (x, I0())) in
                    let i1 x = eval (App (x, I1())) in
                    let ui0 = unify global ctx lvl ph vars (i0 e1, App (e1', e2'), ty2) lift in
                    let ui1 = unify global ctx lvl ph vars (i1 e1, App (e1', e2'), ty2) lift in
                    helper ui0 ui1

                  | _ ->
                    Error msg
              end
          end
        | Error msg -> (* This case is impossible *)
          Error ((App (e1, e2), App (e1', e2')), msg)
        end
      
      | App (e, i), e', _ | e', App (e, i), _ ->
        begin
          let h1 = Hole.generate ty ph [] in
          let elab2 = elaborate global ctx lvl h1 ph vars i in
          begin 
            match elab2, i with
            | Ok (_, Int()), Id _ ->
              let e0 = eval (App (e, I0())) in
              let e1 = eval (App (e, I1())) in
              let e0' = eval (fullsubst i (I0()) e') in
              let e1' = eval (fullsubst i (I1()) e') in
              let ui0 = unify global ctx lvl ph vars (e0, e0', ty) lift in
              let ui1 = unify global ctx lvl ph vars (e1, e1', ty) lift in
              begin 
                match ui0, ui1 with
                | Ok _, Ok _ -> Ok (App (e, i))
                | Error msg, _ -> 
                  Error ((e0, e0'), "Don't know how to unify\n  " ^ Pretty.print e0 ^ "\nwith\n  " ^ Pretty.print e0' ^ "\n" ^ Pretty.print (eval e0') ^ "\n" ^ snd msg ) 
                | _, Error msg -> Error ((e1, e1'), "Don't know how to unify\n  " ^ Pretty.print e1 ^ "\nwith\n  " ^ Pretty.print e1' ^ "\n" ^ snd msg)

              end
            | _ ->
              Error ((e, e'), "Don't know how to unify\n  " ^ Pretty.print (App (e, i)) ^ "\nwith\n  " ^ Pretty.print e')
          end
          
        end
      
      | Pair (e1, e2), Pair (e1', e2'), Sigma(y, ty1, ty2) ->
        let u1 = unify global ctx lvl ph vars (e1, e1', ty1) lift in
        let u2 = unify global ctx lvl ph vars (e2, e2', subst y (Fst e1) ty2) lift in
        begin match u1, u2 with
        | Ok s1, Ok s2 -> Ok (Pair (s1, s2))
        | Error msg, _ | _, Error msg -> Error msg
        end
      
      | Coe (i, j, e1, e2) , Coe (i', j', e1', e2'), ty ->
        let ui = unify global ctx lvl ph vars (i, i', Int()) lift in
        let uj = unify global ctx lvl ph vars (j, j', Int()) lift in
        let h0 = Hole.generate ty ph [] in
        let elab = elaborate global ctx lvl h0 ph vars e1 in
        begin
          match elab with
          | Ok (_, eTy) ->
            let u1 = unify global ctx lvl ph vars (e1, e1', eTy) lift in
            let u2 = unify global ctx lvl ph vars (e2, e2', eval (App(e1', i'))) lift in
            begin match ui, uj, u1, u2 with
            | Ok si, Ok sj, Ok s1, Ok s2 -> Ok (Coe (si, sj, s1, s2))
            | Error msg, _, _, _ | _ , Error msg, _, _ | _ , _, Error msg, _ | _ , _, _, Error msg -> 
              Error msg
            end
          | Error msg -> Error ((Coe (i, j, e1, e2) , Coe (i', j', e1', e2')), msg)
        end
      
      | Hfill (e, e1, e2) , Hfill (e', e1', e2'), ty ->
        let h0 = Hole.generate ty ph [] in
        let elab = elaborate global ctx lvl h0 ph vars e in
        begin
          match elab with
          | Ok (_, eTy) ->
            let u = unify global ctx lvl ph vars (e, e', eTy) lift in
            let u1 = unify global ctx lvl ph vars (e1, e1', eTy) lift in
            let u2 = unify global ctx lvl ph vars (e2, e2', eTy) lift in
            begin match u, u1, u2 with
            | Ok se, Ok se1, Ok se2 -> Ok (Hfill (se, se1, se2))
            | Error msg, _, _ | _ , Error msg, _ | _ , _, Error msg -> 
              Error msg
            end
          | Error msg -> Error ((Hfill (e, e1, e2) , Hfill (e', e1', e2')), msg)
        end

      | At (Hole _, Hole _), e', _ | e', At (Hole _, Hole _), _ ->
        Ok e'
      
      | At (e1, e2), At (e1', e2'), ty ->
        let u2 = unify global ctx lvl ph vars (e2, e2', Int()) lift in
        let h1 = Hole.generate ty ph [] in
        let h2 = Hole.generate ty (ph+2) [] in
        let i = fresh_var (App(e1, e1')) ty vars in
        let elab1 = elaborate global ctx lvl (Pathd (Pi(i, Int(), fullsubst e2 (Id i) ty), h1, h2)) ph vars e1 in
        begin match elab1 with
        | Ok (_, ety) ->
          let u1 = unify global ctx lvl ph vars (e1, e1', ety) lift in
          begin match u1, u2 with
          | Ok s1, Ok s2 -> Ok (At (s1, s2))
          | Error msg, _ | _, Error msg -> Error msg
          end
        | Error msg ->
          Error ((At (e1, e2), At (e1', e2')), msg)
        end

      | At (e, i), e', ty | e', At (e, i), ty ->

        (* if i = ε we elaborate and unify e @ ε with e' : ty *)

        if eval i = I0() || eval i = I1() then
        
          let elab = elaborate global ctx lvl ty ph vars (At (e, eval i)) in
          begin match elab with
          | Ok (ei, ety) ->
            let u1 = unify global ctx lvl ph vars (ei, e', ety) lift in
            begin match u1 with
            | Ok se -> Ok se
            | Error msg -> Error msg
            end
          | Error msg ->
            Error ((At (e, eval i), e'), msg)
          end

        else

        (* if i is a variable, we elaborate and unify e @ ε with e' [ε/i] : ty [ε/i] *)

          begin
            let h1 = Hole.generate ty ph [] in
            
            begin 
              match i with
              | Id x ->
                
                let elabt0 = elaborate global ctx lvl h1 ph vars (eval (subst x (I0()) ty)) in
                let elabt1 = elaborate global ctx lvl h1 ph vars (eval (subst x (I1()) ty)) in
                begin
                  match elabt0, elabt1 with
                  | Ok (ty0, _), Ok (ty1, _) ->

                    let elab0 = elaborate global ctx lvl ty0 ph vars (At (eval (subst x (I0()) e), I0())) in
                    let elab1 = elaborate global ctx lvl ty1 ph vars (At (eval (subst x (I1()) e), I1())) in
                    let elab0' = elaborate global ctx lvl ty0 ph vars (eval (subst x (I0()) e')) in
                    let elab1' = elaborate global ctx lvl ty1 ph vars (eval (subst x (I1()) e')) in

                    begin
                      match elab0, elab1, elab0', elab1' with
                      | Ok (e0, _), Ok (e1, _), Ok (e0', _), Ok (e1', _) ->

                        let ui0 = unify global ctx lvl ph vars (e0, e0', ty0) lift in
                        let ui1 = unify global ctx lvl ph vars (e1, e1', ty1) lift in
                        
                        begin 
                          match ui0, ui1 with
                          | Ok _, Ok _ -> Ok (App (e, i))
                          | Error msg, _ -> 
                            Error ((e0, e0'), "Don't know how to unify\n  " ^ Pretty.print e0 ^ "\nwith\n  " ^ Pretty.print e0' ^ "\n" ^ Pretty.print (eval e0') ^ "\n" ^ snd msg ) 
                          | _, Error msg -> 
                            Error ((e1, e1'), "Don't know how to unify\n  " ^ Pretty.print e1 ^ "\nwith\n  " ^ Pretty.print e1' ^ "\n" ^ snd msg)
                        end
                      | Error msg, _, _, _ | _, Error msg, _, _ | _, _, Error msg, _ |  _, _, _, Error msg ->
                        Error ((At (e, i), e'), msg)
                    end

                  | Error msg, _ | _, Error msg -> Error ((At (e, i), e'), msg) (* This case is impossible *)
                end
              | _ ->
                Error ((e, e'), "Don't know how to unify\n  " ^ Pretty.print (App (e, i)) ^ "\nwith\n  " ^ Pretty.print e')
            end
            
          end

      | Let (e1, e2), Let (e1', e2'), ty ->
        let u1 = unify global ctx lvl ph vars (e1, e1', Unit()) lift in
        let u2 = unify global ctx lvl ph vars (e2, e2', fullsubst e1 (Star()) ty) lift in
        begin match u1, u2 with
        | Ok s1, Ok s2 -> Ok (Let (s1, s2))
        | Error msg, _ | _, Error msg -> Error msg
        end

      | Fst e, Fst e', ty ->
        let v1 = fresh_var e e' vars in
        let h1 = Hole.generate ty ph [] in
        let elab = elaborate global ctx lvl (Sigma(v1, ty, h1)) ph vars e in
        begin match elab with
        | Ok (_, ety) ->
          let u = unify global ctx lvl ph vars (e, e', ety) lift in
          begin match u with
          | Ok s -> Ok (Fst s)
          | Error msg -> Error msg
          end
        | Error msg -> (* This case is impossible *)
          Error ((Fst e, Fst e'), msg)
        end
        

      | Snd e, Snd e', ty ->
        let v1 = fresh_var e e' vars in
        let h1 = Hole.generate ty ph [] in
        let elab = elaborate global ctx lvl (Sigma(v1, h1, fullsubst (Fst e) (Id v1) ty)) ph vars e in
        begin match elab with
        | Ok (_, ety) ->
          let u = unify global ctx lvl ph vars (e, e', ety) lift in
          begin match u with
          | Ok s -> Ok (Snd s)
          | Error msg -> Error msg
          end
        | Error msg -> (* This case is impossible *)
          Error ((Fst e, Fst e'), msg)
        end

      | Inl e, Inl e', Sum(ty1, _) ->
        let u = unify global ctx lvl ph vars (e, e', ty1) lift in
        begin match u with
        | Ok s -> Ok (Inl s)
        | Error msg -> Error msg
        end

      | Inr e, Inr e', Sum(_, ty2) ->
        let u = unify global ctx lvl ph vars (e, e', ty2) lift in
        begin match u with
        | Ok s -> Ok (Inr s)
        | Error msg -> Error msg
        end

      | Succ e, Succ e', Nat() ->
        let u = unify global ctx lvl ph vars (e, e', Nat()) lift in
        begin match u with
        | Ok s -> Ok (Succ s)
        | Error msg -> Error msg
        end

      | Abort e, Abort e', _ ->
        let u = unify global ctx lvl ph vars (e, e', Void()) lift in
        begin match u with
        | Ok s -> Ok (Abort s)
        | Error msg -> Error msg
        end

      | Case (e, e1, e2), Case (e', e1', e2'), ty ->
        let h1 = Hole.generate ty ph [] in
        let h2 = Hole.generate ty (ph+1) [] in
        let elab = elaborate global ctx lvl (Sum(h1, h2)) ph vars e in
        begin match elab with
        | Ok (_, Sum(ty1, ty2)) ->
          let u = unify global ctx lvl ph vars (e, e', Sum(ty1, ty2)) lift in
          let v1 = fresh_var e e' vars in
          let u1 = unify global ctx lvl ph vars (e1, e1', Pi(v1, ty1, fullsubst e (Inl (Id v1)) ty)) lift in
          let u2 = unify global ctx lvl ph vars (e2, e2', Pi(v1, ty2, fullsubst e (Inr (Id v1)) ty)) lift in
          begin match u, u1, u2 with
          | Ok s, Ok s1, Ok s2 -> Ok (Case (s, s1, s2))
          | Error msg, _, _ | _ , Error msg, _| _ , _, Error msg ->
            Error msg
          end
        | _ -> (* This case never occurs *)
          Error ((Case (e, e1, e2), Case (e', e1', e2')), "Unification error")
        end

      | Natrec (e, e1, e2), Natrec (e', e1', e2'), ty ->
        let u = unify global ctx lvl ph vars (e, e', Nat()) lift in
        let u1 = unify global ctx lvl ph vars (e1, e1', fullsubst e (Zero()) ty) lift in
        let v1 = fresh_var e e' vars in
        let v2 = fresh_var e e' (vars+1) in
        let tys = (Pi(v1, Nat(), Pi(v2, fullsubst e (Id v1) ty, fullsubst e (Succ (Id v1)) ty))) in
        let u2 = unify global ctx lvl ph vars (e2, e2', tys) lift in
        begin match u, u1, u2 with
        | Ok s, Ok s1, Ok s2 -> Ok (Natrec (s, s1, s2))
        | Error msg, _, _ | _ , Error msg, _| _ , _, Error msg ->
          Error msg
        end

      | If (e, e1, e2), If (e', e1', e2'), ty ->
        let u = unify global ctx lvl ph vars (e, e', Bool()) lift in
        let u1 = unify global ctx lvl ph vars (e1, e1', fullsubst e (True()) ty) lift in
        let u2 = unify global ctx lvl ph vars (e2, e2', fullsubst e (False()) ty) lift in
        begin match u, u1, u2 with
        | Ok s, Ok s1, Ok s2 -> Ok (If (s, s1, s2))
        | Error msg, _, _ | _ , Error msg, _| _ , _, Error msg ->
          Error msg
        end

      | Type m, Type n, _ ->
        let msg = (Type m, Type n), "The types\n  " ^ Pretty.print (Type m) ^ "\nand\n  " ^ Pretty.print (Type n) ^ "\nhave incompatible universe levels" in
        if lift then
          if Universe.leq (n, m) then
            Ok (Type n)
          else
            Error msg
        else
          Error msg
      
      | e , e', _ -> 
        if eval e = eval e' then 
          Ok e 
        else 
          Error ((e, e'), "The terms\n  " ^ Pretty.print e ^ "\nand\n  " ^ Pretty.print e' ^ "\nare not equal")
