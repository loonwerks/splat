(*---------------------------------------------------------------------------*)
(* Arithmetic progressions, detection of.                                    *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(* A Clustre program (comp) starts out being defined with reference to an    *)
(* environment. At first the env is a finite map from variable names to      *)
(* value streams.                                                            *)
(*                                                                           *)
(*   type strmEnv = string |-> (num -> value)                                *)
(*                                                                           *)
(* An evaluation step of a component is then a map from an input env to an   *)
(* output env.                                                               *)
(*                                                                           *)
(*   strmStep  : comp -> strmEnv -> strmEnv                                  *)
(*                                                                           *)
(* After "temporal squashing" the program---if it looks back in time for the *)
(* earlier value of a variable---looks back exactly one step. Another way of *)
(* stating this: all pre(-) expressions are on variables. This means that    *)
(* the time index on variable references can be eliminated. Consequently,    *)
(* evaluation is with respect to value environments:                         *)
(*                                                                           *)
(*   type valEnv = string |-> value                                          *)
(*                                                                           *)
(* We also separate the environment into inputs, outputs, and state vars.    *)
(* An evaluation step of a component is a map from an (input,state) env pair *)
(* to a (state,output) pair, where the envs are valEnvs.                     *)
(*                                                                           *)
(*   stateStep : comp -> (valEnv * valEnv) -> (valEnv * valEnv)              *)
(*                                                                           *)
(* At this point, the environments can be made explicit as parameters to a   *)
(* function definition.                                                      *)
(*                                                                           *)
(*   fnStep : input-tuple * state-tuple -> state-tuple * output-tuple        *)
(*                                                                           *)
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
          [IntStmt "N" (FbyExpr (IntLit 0)
                                (AddExpr (PreExpr (IntVar "N")) (IntLit 1)));
           BoolStmt "isProg"
            (BoolCondExpr
                 (LeqExpr (IntVar "N") (IntLit 1))
                 (BoolLit T)
                 (AndExpr
                    (EqExpr (SubExpr (IntVar "input") (PreExpr (IntVar "input")))
                            (SubExpr (PreExpr (IntVar "input"))
                                     (PreExpr (PreExpr(IntVar "input")))))
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

val arithprog_isProg =
   EVAL “strmStep E arithprog t ' "isProg" t” |> SIMP_RULE (srw_ss()) [];

val arithprog_out =
  EVAL “strmStep E arithprog t ' "out" t” |> SIMP_RULE (srw_ss()) [];

Theorem arithprog_Eq_out_isProg[local] :
 ∀t E. strmStep E arithprog t ' "out" t = strmStep E arithprog t ' "isProg" t
Proof
  rw [arithprog_isProg,arithprog_out]
QED

Theorem arithprog_Vars_Eq[local] :
 ∀t E. strmSteps E arithprog t ' "out" t = strmSteps E arithprog t ' "isProg" t
Proof
  Induct >> rw [strmSteps_def,arithprog_isProg,arithprog_out]
QED

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
(*  inports = [input,isInit]                                                 *)
(*    N = if isInit then 0 else 1 + pre N                                    *)
(*   ap = if N ≤ 1 then                                                      *)
(*          T                                                                *)
(*        else                                                               *)
(*          pre(ap) and (input - pre in1 = pre in1 - pre in2)                *)
(*   in2 = if isInit then 42 else pre in1                                    *)
(*   in1 = input                                                             *)
(*---------------------------------------------------------------------------*)


Definition iter_arithprog_def:
  iter_arithprog =
    <| inports  := ["input"];
       var_defs :=
          [IntStmt "N" (FbyExpr (IntLit 0)
                                (AddExpr (PreExpr (IntVar "N")) (IntLit 1)));
           BoolStmt "ap"
            (BoolCondExpr
                 (LeqExpr (IntVar "N") (IntLit 1))
                 (BoolLit T)
                 (AndExpr
                    (EqExpr (SubExpr (IntVar "input") (PreExpr (IntVar "in1")))
                            (SubExpr (PreExpr (IntVar "in1")) (PreExpr (IntVar "in2"))))
                    (BoolPreExpr (BoolVar "ap"))));
           IntStmt "in2" (FbyExpr (IntLit 42) (PreExpr (IntVar "in1")));
           IntStmt "in1" (IntVar "input")];
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

(*--------------------------------------------------------------------------*)
(* Show that the original program is equivalent to the version with nested  *)
(* "pre"s squashed out.                                                     *)
(*--------------------------------------------------------------------------*)

val iter_arithprog_ap =
   EVAL “strmStep E iter_arithprog t ' "ap" t” |> SIMP_RULE (srw_ss()) [];

val iter_arithprog_out =
   EVAL “strmStep E iter_arithprog t ' "out" t” |> SIMP_RULE (srw_ss()) [];


Theorem iter_arithprog_Eq_out_ap[local] :
 ∀t E. strmStep E iter_arithprog t ' "out" t = strmStep E iter_arithprog t ' "ap" t
Proof
  rw [iter_arithprog_ap,iter_arithprog_out]
QED

Theorem iter_arithprog_Vars_Eq[local] :
 ∀t E. strmSteps E iter_arithprog t ' "out" t = strmSteps E iter_arithprog t ' "ap" t
Proof
  Induct >> rw [strmSteps_def,iter_arithprog_ap,iter_arithprog_out]
QED

(* Probably needs to be generalized to include more vars.
Theorem equiv1:
  ∀E t. strmSteps E arithprog t ' "out" t = strmSteps E iter_arithprog t ' "out" t
Proof
  simp [arithprog_Vars_Eq, iter_arithprog_Vars_Eq]
  >> Induct_on ‘t’
  >-  (EVAL_TAC >> rw[])
  >-  (EVAL_TAC >> rw[GSYM arithprog_def, GSYM iter_arithprog_def]
       >- (‘t = 0n’ by decide_tac >> rw [] >> EVAL_TAC >> rw[])
       >-
QED
 *)

(* Relates a stream step to a state step.
    - Think about whether it needs to relate strmSteps and stateSteps
    - stateIn is taken at time t and so is stateOut. Probably needs to be t and SUC t
    -

Theorem equiv2 :
  ∀E E' t inE outE stateIn stateOut.
    Supports E iter_arithprog ∧
    inE = strmIndex (input_of iter_arithprog E) t ∧
    stateIn = strmIndex (state_of iter_arithprog E) t
    (stateOut,outE) = stateStep iter_arithprog (inE,stateIn)
    E' = strmStep E iter_arithprog t ∧
    ⇒
      (strmIndex (state_of iter_arithprog E') t,
       strmIndex (output_of iter_arithprog E') t)
      =
     (stateOut,outE)
Proof
  EVAL_TAC >> rw []
QED
*)

(*---------------------------------------------------------------------------*)
(* "pre-CakeML" logic function version of iter_arithprog. Note that variable *)
(* in2 is a parameter when it doesn't strictly have to be.                   *)
(*---------------------------------------------------------------------------*)

Definition aprogFn_def :
  aprogFn (input,isInit) (N,ap,in2,in1) =
    let N = if isInit then 0i else 1 + N ;
        ap = if N ≤ 1 then
              T
             else ap ∧ (input - in1 = in1 - in2);
        in2 = if isInit then 42i else in1;
        in1 = input
    in
      ((N,ap,in2,in1), ap)
End

(*---------------------------------------------------------------------------*)
(* Now interpret iter_arithprog in a setting where the environments are      *)
(* string |-> value maps, instead of the string |-> value stream maps being  *)
(* used in agreeScript.                                                      *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Lemma that state_ap = out_ap. Not used.                                   *)
(*---------------------------------------------------------------------------*)

Theorem out_eq_ap :
  ∀inE stateIn stateOut outE.
      (stateOut,outE) = stateStep iter_arithprog (inE,stateIn)
  ⇒
  (outE ' "out") = (stateOut ' "ap")
Proof
  EVAL_TAC >> rw[] >> rpt(pop_assum mp_tac) >> rw[] >> EVAL_TAC
QED

Theorem equiv3 :
  ∀input isInit N ap in2 in1.
     let inE = FEMPTY |++ [("input",IntValue input);("isInit", BoolValue isInit)] ;
         stateIn = FEMPTY
                   |++ [("N",    IntValue N);
                        ("ap",   BoolValue ap);
                        ("in2",  IntValue in2);
                        ("in1",  IntValue in1)];
         (stateOut,outE) = stateStep iter_arithprog (inE,stateIn) ;
         state_N     = int_of(stateOut ' "N");
         state_ap    = bool_of(stateOut ' "ap");
         state_in2   = int_of(stateOut ' "in2");
         state_in1   = int_of(stateOut ' "in1");
         output_ap   = bool_of(outE ' "out")
     in
       ((state_N, state_ap,state_in2, state_in1), output_ap)
       =
      aprogFn (input,isInit) (N,ap,in2,in1)
Proof
  rpt gen_tac
  >> EVAL_TAC
  >> rw[FUNION_DEF]
  >> rpt(pop_assum mp_tac)
  >> EVAL_TAC
  >> rw_tac bool_ss [Once integerTheory.INT_ADD_SYM]
  >> metis_tac[]
QED



val _ = export_theory();
