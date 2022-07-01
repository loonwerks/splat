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
(* Variable reference for replacing FbyExpr with CondExpr:                   *)
(*   (FbyExpr e1 e2) = (CondExpr init e1 e2)                                 *)
(*---------------------------------------------------------------------------*)

Definition initPortName_def :
  initPortName = "isInit"
End

Definition init_def :
  init = VarExpr initPortName
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
  exprSquash A M (VarExpr s) = (A,M,VarExpr s) /\
  exprSquash A M (IntLit i)  = (A,M,IntLit i)  /\
  exprSquash A M (BoolLit b) = (A,M,BoolLit b) /\
  exprSquash A M (PreExpr e) =
    (if e ∈ FDOM M then
      (A,M,M ' e)
     else
      let (A1,M1,e1) = exprSquash A M e;
          s = newAux (LENGTH A1);
          e2 = VarExpr s;
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
 >> rw [esize_def,ETA_THM]
 >> drule (GSYM pair_list_lem)
 >> rw[]
End


Definition squashStmt_def :
  squashStmt (Stmt s e) (S,A,M) =
  let
    (A1,M1,e') = exprSquash A M e
  in
    (Stmt s e'::S,A1,M1)
End

Definition squashOStmt_def :
  squashOstmt (Output_Event s e) (S,A,M) =
    (let
      (S1,A1,M1) = squashStmt (Stmt s e) ([],A,M);
      e' = bodyOf(HD S1);
    in
      (Output_Event s e'::S,A1,M1))                    /\
  squashOstmt (Output_Data s e) (S,A,M) =
    (let
       (S1,A1,M1) = squashStmt (Stmt s e) ([],A,M);
       e' = bodyOf(HD S1);
     in
       (Output_Data s e'::S,A1,M1))                    /\
  squashOstmt (Output_Event_Data s e1 e2) (S,A,M) =
    (let
       (S1,A1,M1) = squashStmt (Stmt s e1) ([],A,M);
       e1' = bodyOf(HD S1);
       (S2,A2,M2) = squashStmt (Stmt s e2) ([],A1,M1);
       e2' = bodyOf(HD S2);
     in
       (Output_Event_Data s e1' e2'::S,A2,M2))       
End

Definition squashStmts_def :
  squashStmts fn (S,A,M) stmts = FOLDR fn (S,A,M) stmts
End

Definition squash_comp_def :
  squash_comp comp =
  let
    (out_defs,aux_defs,M) = squashStmts squashOstmt ([],[],FEMPTY) comp.out_defs;
    (var_defs,aux_defs1,M1) = squashStmts squashStmt ([],aux_defs,M) comp.var_defs;                      
  in
    <| inports  := initPortName::comp.inports;
       var_defs := var_defs ++ aux_defs1;
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
                (AddExpr (PreExpr (VarExpr "N")) (IntLit 1)));
      Stmt "isProg"
           (CondExpr
            (LeqExpr (VarExpr "N") (IntLit 1))
            (BoolLit T)
            (AndExpr
             (EqExpr (SubExpr (VarExpr "input") (PreExpr (VarExpr "input")))
              (SubExpr (PreExpr (VarExpr "input"))
               (PreExpr (PreExpr(VarExpr "input")))))
             (PreExpr (VarExpr "isProg"))))];
     out_defs := [Output_Event "out" (VarExpr "isProg")];
     assumptions := [];
     guarantees  := []
  |>
End

val squashed_arithprog = EVAL “squash_comp arithprog”;

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
                 (AddExpr (VarExpr "recFib") (PreExpr (VarExpr "recFib"))))))];
     out_defs := [Output_Data "output" (VarExpr "recFib")];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (VarExpr"output")]
  |>
End

val squashed_recFib = EVAL “squash_comp recFib”;

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
                 (AddExpr (VarExpr "recFib") (PreExpr (VarExpr "recFib"))))));
      Stmt "array"
           (ArrayExpr [
               (VarExpr "recFib");
               (IntLit 1);
               (FbyExpr (IntLit 0) (PreExpr (VarExpr "recFib")))])];
     out_defs := [Output_Data "output1" (VarExpr "recFib");
                  Output_Data "output2" (VarExpr "array")];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (VarExpr"output")]
  |>
End

val squashed_arrayExprInput = EVAL “squash_comp arrayExprInput”;

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
                           (AddExpr (VarExpr "recFib") (PreExpr (VarExpr "recFib")))))));
          ("b", (IntLit 1));
          ("c", (FbyExpr (IntLit 0) (PreExpr (VarExpr "recFib"))))])];
     out_defs := [Output_Data "output" (VarExpr "recd")];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (VarExpr"output")]
  |>
End

val squashed_recdExpr = EVAL “squash_comp recdExprInput”;

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
                 (AddExpr (VarExpr "Fib") (PreExpr (VarExpr "Fib"))))));
      Stmt "x"
           (FbyExpr (IntLit 0)
            (PreExpr (FbyExpr (IntLit 1)
                      (PreExpr (FbyExpr (IntLit 1)
                                (AddExpr (VarExpr "Fib") (PreExpr (VarExpr "Fib"))))))));
      Stmt "y"
           (FbyExpr (VarExpr "x")
            (PreExpr (FbyExpr (VarExpr "x")
                      (SubExpr (PreExpr (VarExpr "x")) (PreExpr (PreExpr (VarExpr "Fib")))))))];
     out_defs := [Output_Data "output1" (VarExpr "Fib");
                  Output_Data "output2"
                       (FbyExpr (IntLit 1)
                        (PreExpr (FbyExpr (IntLit 1)
                                  (AddExpr (PortData (VarExpr "input")) (PreExpr (PortData (VarExpr "input")))))))];
     assumptions := [];
     guarantees := [LeqExpr (IntLit 0) (VarExpr"output")]
  |>
End

val squashed_test = EVAL “squash_comp testInput”;

val _ = export_theory();
