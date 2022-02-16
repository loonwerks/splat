(*---------------------------------------------------------------------------*)
(* Arithmetic progressions, detection of.                                    *)
(*---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory
     agreeTheory stateTheory;

val _ = intLib.prefer_int();

val _ = new_theory "aprog";

(*---------------------------------------------------------------------------*)
(* Version with lookback to depths one and two.                              *)
(*                                                                           *)
(*  inports = [in]                                                           *)
(*       N = 0 -> 1 + pre N                                                  *)
(*  isProg = if N ≤ 1 then                                                   *)
(*              T                                                            *)
(*           else                                                            *)
(*              pre isProg and (in - pre in = pre in - pre(pre in))          *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition arithprog_def:
  arithprog =
    <| inports  := ["in"];
       var_defs :=
          [IntStmt "N" (FbyExpr (IntLit 0)
                                (AddExpr (PreExpr (IntVar "N")) (IntLit 1)));
           BoolStmt "isProg"
            (BoolCondExpr
                 (LeqExpr (IntVar "N") (IntLit 1))
                 (BoolLit T)
                 (AndExpr
                    (EqExpr (SubExpr (IntVar "in") (PreExpr (IntVar "in")))
                            (SubExpr (PreExpr (IntVar "in"))
                                     (PreExpr (PreExpr(IntVar "in")))))
                    (BoolPreExpr (BoolVar "isProg"))))];
         out_defs := [BoolStmt "out" (BoolVar "isProg")];
      assumptions := [];
      guarantees  := []
      |>
End

val th0 = EVAL“(strmSteps E arithprog 0 ' "out") 0”
val th1 = EVAL“(strmSteps E arithprog 1 ' "out") 1”
val th2 = EVAL“(strmSteps E arithprog 2 ' "out") 2”
val th3 = EVAL“(strmSteps E arithprog 3 ' "out") 3”
val th4 = EVAL“(strmSteps E arithprog 4 ' "out") 4”
val th5 = EVAL“(strmSteps E arithprog 5 ' "out") 5”
val th6 = EVAL“(strmSteps E arithprog 6 ' "out") 6”

(*---------------------------------------------------------------------------*)
(* Iterative version: set up so that lookback is exactly 1. Also, add var    *)
(* to hold state of input. Also add a supplementary input stream that tells  *)
(* whether the programs is in the first step or not. As a stream it would    *)
(* be written                                                                *)
(*                                                                           *)
(*   isInit = T -> F                                                         *)
(*                                                                           *)
(* but we will just add a constraint in theorems saying that the inputs      *)
(* contain a stream with the above behaviour. The semantics of Fby in        *)
(* stateScript.sml expresses this.                                           *)
(*                                                                           *)
(*  inports = [in,isInit]                                                    *)
(*     N = if isInit then 0 else 1 + pre N                                   *)
(*   in2 = if isInit then 42 else pre in1                                    *)
(*   in1 = if isInit then 42 else pre inVar                                  *)
(*   inVar = in                                                              *)
(*   ap = if N ≤ 1 then                                                      *)
(*          T                                                                *)
(*        else                                                               *)
(*          pre(ap) and (in - in1 = in1 - in2)                               *)
(*---------------------------------------------------------------------------*)


Definition iter_arithprog_def:
  iter_arithprog =
    <| inports  := ["in"];
       var_defs :=
          [IntStmt "N" (FbyExpr (IntLit 0)
                                (AddExpr (PreExpr (IntVar "N")) (IntLit 1)));
           IntStmt "in2" (FbyExpr (IntLit 42) (PreExpr (IntVar "in1")));
           IntStmt "in1" (FbyExpr (IntLit 42) (PreExpr (IntVar "in")));
           IntStmt "inVar" (IntVar "in");
           BoolStmt "ap"
            (BoolCondExpr
                 (LeqExpr (IntVar "N") (IntLit 1))
                 (BoolLit T)
                 (AndExpr
                    (EqExpr (SubExpr (IntVar "in") (IntVar "in1"))
                            (SubExpr (IntVar "in1") (IntVar "in2")))
                    (BoolPreExpr (BoolVar "ap"))))];
         out_defs := [BoolStmt "out" (BoolVar "ap")];
      assumptions := [];
      guarantees  := []
      |>
End

val th0 = EVAL“(strmSteps E iter_arithprog 0 ' "out") 0”
val th1 = EVAL“(strmSteps E iter_arithprog 1 ' "out") 1”
val th2 = EVAL“(strmSteps E iter_arithprog 2 ' "out") 2”
val th3 = EVAL“(strmSteps E iter_arithprog 3 ' "out") 3”
val th4 = EVAL“(strmSteps E iter_arithprog 4 ' "out") 4”
val th5 = EVAL“(strmSteps E iter_arithprog 5 ' "out") 5”
val th6 = EVAL“(strmSteps E iter_arithprog 6 ' "out") 6”
;

val arithprog_effect =
   EVAL “strmStep E arithprog t ' "isProg" t” |> SIMP_RULE (srw_ss()) [];

val iter_arithprog_effect =
   EVAL “strmStep E iter_arithprog t ' "ap" t” |> SIMP_RULE (srw_ss()) [];

val arithprog_out_effect =
  EVAL “strmStep E arithprog t ' "out" t” |> SIMP_RULE (srw_ss()) [];

val iter_arithprog_out_effect =
   EVAL “strmStep E iter_arithprog t ' "out" t” |> SIMP_RULE (srw_ss()) [];


Theorem arithprog_Vars_Eq[local] :
 ∀t E. strmSteps E arithprog t ' "out" t = strmSteps E arithprog t ' "isProg" t
Proof
  Induct >> rw [strmSteps_def,arithprog_effect,arithprog_out_effect]
QED

Theorem iter_arithprog_Vars_Eq[local] :
 ∀t E. strmSteps E iter_arithprog t ' "out" t = strmSteps E iter_arithprog t ' "ap" t
Proof
  Induct >> rw [strmSteps_def,iter_arithprog_effect,iter_arithprog_out_effect]
QED

(*
Theorem arithprog_equiv:
  strmStep E arithprog t ' "out" t = strmStep E iter_arithprog t ' "out" t
Proof
 EVAL_TAC >> rw[arithprog_Vars_Eq,iter_arithprog_Vars_Eq]
QED
*)

val _ = export_theory();
