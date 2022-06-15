open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory
     agree_fullTheory ASCIInumbersLib;

val _ = intLib.prefer_int();

val _ = new_theory "squash_full";

(*---------------------------------------------------------------------------*)
(* Misc. helper lemmas                                                       *)
(*---------------------------------------------------------------------------*)

Theorem pair_list_lem:
  ∀list alist blist.
      UNZIP list = (alist,blist)
      ==>
      list_size f blist = list_size (f o SND) list
Proof
  simp[UNZIP_MAP] >> Induct >> rw[list_size_def]
QED

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
  exprSquash A M (Var s) = (A,M,Var s)         /\
  exprSquash A M (IntLit i)  = (A,M,IntLit i)  /\
  exprSquash A M (BoolLit b) = (A,M,BoolLit b) /\
  exprSquash A M (PreExpr e) =
    (if e ∈ FDOM M then
      (A,M,M ' e)
     else
      let (A1,M1,e1) = exprSquash A M e;
          s = newAux (LENGTH A1);
          e2 = Var s;
          A2 = Stmt s e1::A1;
          M2 = M1 |+ (e,e2);
      in
        (A2,M2,e2))                            /\
  exprSquash A M (AddExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,AddExpr e1' e2'))                /\
  exprSquash A M (SubExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,SubExpr e1' e2'))                /\
  exprSquash A M (MultExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,MultExpr e1' e2'))               /\
  exprSquash A M (DivExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,DivExpr e1' e2'))                /\
  exprSquash A M (ModExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,ModExpr e1' e2'))                /\
  exprSquash A M (NotExpr e)     =
    (let (A1,M1,e') = exprSquash A M e
     in (A1,M1,NotExpr e'))                    /\
  exprSquash A M (OrExpr e1 e2)  =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,OrExpr e1' e2'))                 /\
  exprSquash A M (AndExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,AndExpr e1' e2'))                /\
  exprSquash A M (ImpExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,ImpExpr e1' e2'))                /\
  exprSquash A M (IffExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,IffExpr e1' e2'))                /\
  exprSquash A M (EqExpr e1 e2)  =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,EqExpr e1' e2'))                  /\
  exprSquash A M (LeqExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,LeqExpr e1' e2'))                 /\
  exprSquash A M (LtExpr e1 e2)  =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,LtExpr e1' e2'))                  /\
  exprSquash A M (ArraySub e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,LtExpr e1' e2'))                  /\
  exprSquash A M (PortEvent e) =
    (let (A1,M1,e') = exprSquash A M e
     in (A1,M1,PortEvent e'))                   /\
  exprSquash A M (PortData e) =
    (let (A1,M1,e') = exprSquash A M e
     in (A1,M1,PortData e'))                    /\
  exprSquash A M (RecdProj e s) =
    (let (A1,M1,e') = exprSquash A M e
     in (A1,M1,RecdProj e' s))                  /\
  exprSquash A M (HistExpr e) =
    (let (A1,M1,e') = exprSquash A M e
     in (A1,M1,HistExpr e'))                    /\
  exprSquash A M (CondExpr b e1 e2) =
    (let
       (A1,M1,b') = exprSquash A M b;
       (A2,M2,e1') = exprSquash A1 M1 e1;
       (A3,M3,e2') = exprSquash A2 M2 e2;
     in
       (A3,M3,CondExpr b' e1' e2'))             /\
  exprSquash A M (FbyExpr e1 e2) =
    (let (A1,M1,e1') = exprSquash A M e1;
         (A2,M2,e2') = exprSquash A1 M1 e2;
     in
       (A2,M2,CondExpr init e1' e2'))           /\
  exprSquash A M (ArrayExpr elist) =
    (let (elist',A',M') = exprSquashList A M elist
     in (A',M',ArrayExpr elist'))               /\
  exprSquash A M (RecdExpr fields) =
    (let (fnames,elts) = UNZIP fields;
         (elist,A',M') = exprSquashList A M elts
     in (A',M', RecdExpr (MAP2 (,) fnames elist)))
  /\
  exprSquashList A M list =
    FOLDR (\e (elts,A1,M1).
       let (A2,M2,e') = exprSquash A1 M1 e in (e'::elts, A2, M2))
      ([],A,M) list
Termination
 WF_REL_TAC ‘measure
              (sum_size (esize o SND o SND)
                        (list_size esize o SND o SND))’
 >> rw [esize_def,ETA_THM] >> drule (GSYM pair_list_lem) >> rw[]
End



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
(*  V = [recd = [("a",1 -> pre(1 -> fib + pre fib) ;                         *)
(*               ("b",1) ;                                                   *)
(*               ("c",0 -> pre fib)]]                                        *)
(*  O = [output1 = recd]                                                     *)
(*  G = [0 ≤ output]                                                         *)
(*---------------------------------------------------------------------------*)

Definition recdExprInput_def:
  recdExprInput =
  <| inports := [];
     var_defs :=
     [Stmt "recd"
      (RecdExpr [
          ("a", (FbyExpr (IntLit 1)
                 (PreExpr (FbyExpr (IntLit 1)
                           (AddExpr (Var "recFib") (PreExpr (Var "recFib")))))));
          ("b", (IntLit 1));
          ("c", (FbyExpr (IntLit 0) (PreExpr (Var "recFib"))))])];
     out_defs := [Stmt "output" (Var "recd")];
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
