open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory
     agree_fullTheory ASCIInumbersLib;

val _ = intLib.prefer_int();

val _ = new_theory "squash_full";

(*---------------------------------------------------------------------------*)
(* Varible reference for replacing FbyExpr with CondExpr:                    *)
(*   (FbyExpr e1 e2) = (CondExpr init e1 e2)                                 *)
(*---------------------------------------------------------------------------*)

Definition initPortName_def :
  initPortName = "isInit"
End

Definition init_def :
  init = Var initPortName
End

(*---------------------------------------------------------------------------*)
(* Auxilliary variable generator                                             *)
(*---------------------------------------------------------------------------*)

Definition newAux_def :
  newAux n = STRCAT "a" (num_to_dec_string n)
End

(*---------------------------------------------------------------------------*)
(* Re-write so there are no PreExpr and FbyExpr instances                    *)
(*---------------------------------------------------------------------------*)

Definition exprSquash_def :
  exprSquash A M (Var s) = (A,M,Var s)                                   /\
  exprSquash A M (IntLit i)  = (A,M,IntLit i)                            /\
  exprSquash A M (BoolLit b) = (A,M,BoolLit b)                           /\
  exprSquash A M (AddExpr e1 e2) = binarySquash A M e1 e2 AddExpr        /\
  exprSquash A M (SubExpr e1 e2) = binarySquash A M e1 e2 SubExpr        /\
  exprSquash A M (MultExpr e1 e2) = binarySquash A M e1 e2 MultExpr      /\
  exprSquash A M (DivExpr e1 e2) = binarySquash A M e1 e2 DivExpr        /\
  exprSquash A M (ModExpr e1 e2) = binarySquash A M e1 e2  ModExpr       /\
  exprSquash A M (NotExpr e) = unarySquash A M e NotExpr                 /\
  exprSquash A M (OrExpr e1 e2) = binarySquash A M e1 e2 OrExpr          /\
  exprSquash A M (AndExpr e1 e2) = binarySquash A M e1 e2 AndExpr        /\
  exprSquash A M (ImpExpr e1 e2) = binarySquash A M e1 e2 ImpExpr        /\
  exprSquash A M (IffExpr e1 e2) = binarySquash A M e1 e2 IffExpr        /\
  exprSquash A M (EqExpr e1 e2) = binarySquash A M e1 e2 EqExpr          /\
  exprSquash A M (LeqExpr e1 e2) = binarySquash A M e1 e2 LeqExpr        /\
  exprSquash A M (LtExpr e1 e2) = binarySquash A M e1 e2 LtExpr          /\
  exprSquash A M (RecdExpr fields) =
  (let
     fn = \(fields1,A1,M1) (s,e).
                          (let
                             (A2,M2,e') = exprSquash A1 M1 e;
                             fields1' = fields1 ++ [(s,e')];
                           in
                             (fields1',A2,M2));
     (fields',A1,M1) = FOLDL fn ([],A,M) fields;
   in
     (A1,M1,RecdExpr fields'))       /\
  exprSquash A M (RecdProj e s) = unarySquash A M e (\e'.RecdProj e' s)  /\
  exprSquash A M (ArrayExpr elist) =
  (let
     fn = \(elist1,A1,M1) e.
                          (let
                             (A2,M2,e') = exprSquash A1 M1 e;
                             elist1' = elist1 ++ [e'];
                           in
                             (elist1',A2,M2));
     (elist',A1,M1) = FOLDL fn ([],A,M) elist;
   in
     (A1,M1,ArrayExpr elist'))                                           /\
  exprSquash A M (ArraySub e1 e2) = binarySquash A M e1 e2 ArraySub      /\
  exprSquash A M (PortEvent e) = unarySquash A M e PortEvent             /\
  exprSquash A M (PortData e) = unarySquash A M e PortData               /\
  exprSquash A M (PreExpr e) =
  (if e ∈ FDOM M then
     (A,M,M ' e)
   else
     (let
        (A1,M1,e1) = exprSquash A M e;
        s = newAux (LENGTH A1);
        e2 = Var s;
        A2 = Stmt s e1::A1;
        M2 = M1 |+ (e,e2);
      in
        (A2,M2,e2)))                                                     /\
  exprSquash A M (FbyExpr e1 e2) = exprSquash A M (CondExpr init e1 e2)  /\
  exprSquash A M (CondExpr b e1 e2) = ternarySquash A M b e1 e2 CondExpr /\
  exprSquash A M (HistExpr e) = unarySquash A M e HistExpr               /\

  unarySquash A M e fn =
  (let
     (A1,M1,e') = exprSquash A M e;
   in
     (A1,M1,fn e'))                                                      /\
  binarySquash A M e1 e2 fn = 
  (let
     (A1,M1,e1') = exprSquash A M e1;
     (A2,M2,e2') = exprSquash A1 M1 e2;
   in
     (A2,M2,fn e1' e2'))                                                 /\
  ternarySquash A M e1 e2 e3 fn =
  (let
     (A1,M1,e1') = exprSquash A M e1;
     (A2,M2,e2') = exprSquash A1 M1 e2;
     (A3,M3,e3') = exprSquash A2 M2 e3;
   in
     (A3,M3,fn e1' e2' e3'))
Termination
  cheat
End

(*
exprSquash A M (ArrayExpr elist) =
  (let
     fn = \e (elist1,A1,M1).
                          (let
                             (A2,M2,e') = exprSquash A1 M1 e;
                             elist1' = e'::elist1;
                           in
                             (elist1',A2,M2));
     (elist',A1,M1) = FOLDR fn ([],A,M) elist;
   in
        (A1,M1,ArrayExpr elist'))
*)

Definition squashStmt_def :
  squashStmt (Stmt s e) (S,A,M) =
  let
    (A1,M1,e') = exprSquash A M e
  in
    (Stmt s e'::S,A1,M1)
End

Definition squashOutputStmt_def :
  squashOutputStmt (Stmt s e) (S,A,M) =
  let
    (A1,M1,e') = exprSquash A M e;
    s' = newAux (LENGTH A1)
  in
    if e = e' then
      (Stmt s e::S,A1,M1)
    else
      (Stmt s (Var s')::S, Stmt s' e'::A1,M1)
End

Definition squashStmts_def :
  squashStmts fn (S,A,M) stmts = FOLDR fn (S,A,M) stmts
End

Definition squash_comp_def :
  squash_comp comp =
  let
    (out_defs,aux_defs,M) = squashStmts squashOutputStmt ([],[],FEMPTY) comp.out_defs;
    (var_defs,aux_defs',M')  = squashStmts squashStmt ([],aux_defs,M) comp.var_defs;
  in
    <| inports  := initPortName::comp.inports;
       var_defs := var_defs ++ aux_defs';
       out_defs  := out_defs;
       assumptions := comp.assumptions;
       guarantees := comp.guarantees |>
End

(*---------------------------------------------------------------------------*)
(* Version with lookback to depths one and two.                              *)
(*                                                                           *)
(*  inports = [input]                                                        *)
(*       N = 0 -> 1 + pre N                                                  *)
(*  isProg = if N ≤ 1 then                                                   *)
(*              T                                                            *)
(*           else                                                            *)
(*              pre isProg and                                               *)
(*                  (input - pre input = pre input - pre(pre input))         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)
        
Definition arithprog_def:
  arithprog =
  <| inports  := ["input"];
     var_defs :=
     [Stmt "N" (FbyExpr (IntLit 0)
                (AddExpr (PreExpr (Var "N")) (IntLit 1)));
      Stmt "isProg"
           (CondExpr
            (LeqExpr (Var "N") (IntLit 1))
            (BoolLit T)
            (AndExpr
             (EqExpr (SubExpr (Var "input") (PreExpr (Var "input")))
              (SubExpr (PreExpr (Var "input"))
               (PreExpr (PreExpr(Var "input")))))
             (PreExpr (Var "isProg"))))];
     out_defs := [Stmt "out" (Var "isProg")];
     assumptions := [];
     guarantees  := []
  |>
End

EVAL “squash_comp arithprog”;

(*---------------------------------------------------------------------------*)
(* Nesting of "pre" in order to look both 1 and 2 steps back in the          *)
(* computation. Simulates a recursive Fibonacci                              *)
(*                                                                           *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [fib = 1 -> pre(1 -> fib + pre fib)]                                 *)
(*  O = [output = fib]                                                       *)
(*  G = [0 ≤ output]                                                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition recFib_def:
  recFib =
  <| inports := [];
     var_defs :=
     [Stmt "recFib"
      (FbyExpr (IntLit 1)
       (PreExpr (FbyExpr (IntLit 1)
                 (AddExpr (Var "recFib") (PreExpr (Var "recFib"))))))];
     out_defs := [Stmt "output" (Var "recFib")];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (Var"output")]
  |>
End

EVAL “squash_comp recFib”;

(*---------------------------------------------------------------------------*)
(* Array Expressions                                                         *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [fib = 1 -> pre(1 -> fib + pre fib);                                 *)
(*       array = [recFib ; 1 ; 0 -> pre recFib]]                             *)
(*  O = [output1 = fib ; output2 = array]                                    *)
(*  G = [0 ≤ output]                                                         *)
(*---------------------------------------------------------------------------*)

Definition arrayExprInput_def:
  arrayExprInput =
  <| inports := [];
     var_defs :=
     [Stmt "recFib"
      (FbyExpr (IntLit 1)
       (PreExpr (FbyExpr (IntLit 1)
                 (AddExpr (Var "recFib") (PreExpr (Var "recFib"))))));
      Stmt "array"
           (ArrayExpr [
               (Var "recFib");
               (IntLit 1);
               (FbyExpr (IntLit 0) (PreExpr (Var "recFib")))])];
     out_defs := [Stmt "output1" (Var "recFib");
                  Stmt "output2" (Var "array")];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (Var"output")]
  |>  
End

EVAL “squash_comp arrayExprInput”;

(*---------------------------------------------------------------------------*)
(* Record Expressions                                                        *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [fib = 1 -> pre(1 -> fib + pre fib);                                 *)
(*       recd = [("a",recFib) ; ("b",1) ; ("c",0 -> pre recFib)]]            *)
(*  O = [output1 = fib ; output2 = array]                                    *)
(*  G = [0 ≤ output]                                                         *)
(*---------------------------------------------------------------------------*)

Definition recdExprInput_def:
  recdExprInput =
  <| inports := [];
     var_defs :=
     [Stmt "recFib"
      (FbyExpr (IntLit 1)
       (PreExpr (FbyExpr (IntLit 1)
                 (AddExpr (Var "recFib") (PreExpr (Var "recFib"))))));
      Stmt "recd"
           (RecdExpr [
               ("a", (Var "recFib"));
               ("b", (IntLit 1));
               ("c", (FbyExpr (IntLit 0) (PreExpr (Var "recFib"))))])];
     out_defs := [Stmt "output1" (Var "recFib");
                  Stmt "output2" (Var "recd")];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (Var"output")]
  |>
End

EVAL “squash_comp recdExprInput”;
        
(*---------------------------------------------------------------------------*)
(* Bigger example with more common subexpressions and nesting of pre's       *)
(*                                                                           *)
(*  I = [input]                                                              *)
(*  A = []                                                                   *)
(*  V = [fib = 1 -> pre(1 -> fib + pre fib)                                  *)
(*       x = 0 -> pre(1 -> pre(1 -> fib + pre fib))                          *)
(*       y = x -> pre(x -> pre(x) - pre(pre(x)))]                            *)
(*  O = [output1 = fib                                                       *)
(*       output2 = 1 -> pre(1 -> input + pre(input))]                        *)
(*  G = [0 ≤ output]                                                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition testInput_def:
  testInput =
  <| inports := ["input"];
     var_defs :=
     [Stmt "fib"
      (FbyExpr (IntLit 1)
       (PreExpr (FbyExpr (IntLit 1)
                 (AddExpr (Var "Fib") (PreExpr (Var "Fib"))))));
      Stmt "x"
           (FbyExpr (IntLit 0)
            (PreExpr (FbyExpr (IntLit 1)
                      (PreExpr (FbyExpr (IntLit 1)
                                (AddExpr (Var "Fib") (PreExpr (Var "Fib"))))))));
      Stmt "y"
           (FbyExpr (Var "x")
            (PreExpr (FbyExpr (Var "x")
                      (SubExpr (PreExpr (Var "x")) (PreExpr (PreExpr (Var "Fib")))))))];
     out_defs := [Stmt "output1" (Var "Fib");
                  Stmt "output2"
                       (FbyExpr (IntLit 1)
                        (PreExpr (FbyExpr (IntLit 1)
                                  (AddExpr (Var "input") (PreExpr (Var "input"))))))];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (Var"output")]
  |>
End

EVAL “squash_comp testInput”;
