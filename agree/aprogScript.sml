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
(* We now separate the environment into inputs, outputs, and state vars.     *)
(* An evaluation step of a component is a map from an (input,state) env pair *)
(* to a (state,output) pair, where the envs are valEnvs.                     *)
(*                                                                           *)
(*   stateStep : comp -> (valEnv # valEnv) -> (valEnv # valEnv)              *)
(*                                                                           *)
(* At this point, the environments can be made explicit as parameters to a   *)
(* function definition.                                                      *)
(*                                                                           *)
(*   fnStep : input-tuple * state-tuple -> state-tuple * output-tuple        *)
(*                                                                           *)
(* where tuple elements are values.                                          *)
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

(*---------------------------------------------------------------------------*)
(* Set up some overloading, which will improve readability                   *)
(*---------------------------------------------------------------------------*)

overload_on ("/\\", ``AndExpr``);
overload_on ("COND",``BoolCondExpr``);
overload_on ("=",   ``EqExpr``);
overload_on ("pre", ``PreExpr``);
overload_on ("pre", ``BoolPreExpr``);
overload_on ("<=",  ``LeqExpr``);
overload_on ("<",   ``LessExpr``);
overload_on ("+",   ``AddExpr``);
overload_on ("-",   ``SubExpr``);
overload_on ("=",   ``BoolStmt``);
overload_on ("=",   ``IntStmt``);
overload_on ("-->", ``FbyExpr``);


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


Definition itprog_def:
  itprog =
    <| inports  := ["input"; "isInit"];
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

val th0 = EVAL“(strmSteps E itprog 0 ' "out") 0”
val th1 = EVAL“(strmSteps E itprog 1 ' "out") 1”
val th2 = EVAL“(strmSteps E itprog 2 ' "out") 2”
val th3 = EVAL“(strmSteps E itprog 3 ' "out") 3”
val th4 = EVAL“(strmSteps E itprog 4 ' "out") 4”
val th5 = EVAL“(strmSteps E itprog 5 ' "out") 5”
val th6 = EVAL“(strmSteps E itprog 6 ' "out") 6”
;

(*--------------------------------------------------------------------------*)
(* Show that the original program is equivalent to the version with nested  *)
(* "pre"s squashed out.                                                     *)
(*--------------------------------------------------------------------------*)

val itprog_ap =
   EVAL “strmStep E itprog t ' "ap" t” |> SIMP_RULE (srw_ss()) [];

val itprog_out =
   EVAL “strmStep E itprog t ' "out" t” |> SIMP_RULE (srw_ss()) [];


Theorem itprog_Eq_out_ap[local] :
 ∀t E. strmStep E itprog t ' "out" t = strmStep E itprog t ' "ap" t
Proof
  rw [itprog_ap,itprog_out]
QED

Theorem itprog_Vars_Eq[local] :
 ∀t E. strmSteps E itprog t ' "out" t = strmSteps E itprog t ' "ap" t
Proof
  Induct >> rw [strmSteps_def,itprog_ap,itprog_out]
QED

(*---------------------------------------------------------------------------*)
(* Equivalence of original program in strmSteps, with squash program, also   *)
(* in strmSteps. This is somewhat different than the discussion in the header*)
(* of this file. Dealing with the finite maps is cumbersome; that will have  *)
(* be improved in order to see the proof through.                            *)
(*---------------------------------------------------------------------------*)

Theorem equiv1:
  ∀E t. strmSteps E arithprog t ' "out" t = strmSteps E itprog t ' "out" t
Proof
  simp [arithprog_Vars_Eq, itprog_Vars_Eq]
  >> Induct_on ‘t’
  >> cheat

QED

(*---------------------------------------------------------------------------*)
(* Equiv of strmSteps itprog with stateSteps. Expressed in theorem equiv2    *)
(* below.                                                                    *)
(*---------------------------------------------------------------------------*)

val expand_Supports = CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (PATH_CONV "lr" EVAL)));

val itprog_inports = (EVAL THENC SIMP_CONV (srw_ss()) []) “itprog.inports” ;
val itprog_var_defs = (EVAL THENC SIMP_CONV (srw_ss()) []) “itprog.var_defs” ;
val itprog_out_defs = (EVAL THENC SIMP_CONV (srw_ss()) []) “itprog.out_defs” ;
val itprog_varDecs = (EVAL THENC SIMP_CONV (srw_ss()) []) “varDecs itprog” ;


Theorem strmIndex_DRESTRICT :
 ∀E P t. strmIndex (DRESTRICT E P) t = DRESTRICT (strmIndex E t) P
Proof
 rw [strmIndex_def,fmap_EXT,FMAP_MAP2_def,FUN_FMAP_DEF,DRESTRICT_DEF]
QED

Triviality lem :
  "input" IN FDOM E ∧
  "isInit" IN FDOM E ∧
  isInit_Stream (E ' "isInit")
   ⇒
  DRESTRICT (strmIndex E t) {"input";"isInit"}
   =
  (FEMPTY |++ [("input", E ' "input" t) ;
               ("isInit", BoolValue (t=0))])
Proof
  rw [fmap_EXT,DRESTRICT_DEF,strmIndex_def,EXTENSION,IN_INTER,
      FMAP_MAP2_def,FUN_FMAP_DEF,isInit_Stream_def,FUPDATE_LIST_THM]
  >- metis_tac[]
  >- EVAL_TAC
  >- (EVAL_TAC >> rw[])
QED

Definition initState_def:
  initState = (FEMPTY |++
    [("N",    IntValue ARB);
     ("ap",   BoolValue ARB);
     ("in2",  IntValue ARB);
     ("in1",  IntValue ARB)])
End

Theorem equiv2_step:
  Supports E itprog ∧
  0 < t ∧
  isInit_Stream (E ' "isInit") ∧
  inE = strmIndex (input_of itprog E) t ∧
  stE = state_of itprog (strmIndex E (t-1)) ∧
  E' = strmStep E itprog t
  ⇒
  stateStep itprog (inE, stE)
   =
  (state_of itprog (strmIndex E' t),
   output_of itprog (strmIndex E' t))
Proof
  expand_Supports
  >> simp[]
  >> EVAL_TAC
  >> rw [FUPDATE_LIST_THM,FUNION_FUPDATE_1,FUNION_FUPDATE_2,DRESTRICT_FUPDATE,FDOM_DRESTRICT]
  >- (qpat_x_assum ‘bool_of _’ mp_tac
       >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [FUNION_DEF]))
       >> ASM_REWRITE_TAC[]
       >> rw [DRESTRICT_DEF,EXTENSION,IN_INTER,FUN_FMAP_DEF]
       >> fs[bool_of_def])

  >- (qpat_x_assum ‘bool_of _’ mp_tac
       >> CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [FUNION_DEF]))
       >> ASM_REWRITE_TAC[]
       >> rw [DRESTRICT_DEF,EXTENSION,IN_INTER,FUN_FMAP_DEF]
       >> fs[bool_of_def])

  >- (rw[fmap_EXT,FDOM_DRESTRICT,SUBSET_DEF]
      >> rw [DRESTRICT_DEF,EXTENSION,IN_INTER,FUN_FMAP_DEF]
      >- rw [EQ_IMP_THM]
      >> rw[FUNION_DEF,DRESTRICT_DEF,EXTENSION,IN_INTER,FUN_FMAP_DEF,combinTheory.APPLY_UPDATE_THM]
      >> rw [FAPPLY_FUPDATE_THM])

  >- (rw[fmap_EXT,FDOM_DRESTRICT,SUBSET_DEF]
      >> rw [DRESTRICT_DEF,EXTENSION,IN_INTER,FUN_FMAP_DEF]
      >- rw [EQ_IMP_THM]
      >> rw[FUNION_DEF,DRESTRICT_DEF,EXTENSION,IN_INTER,FUN_FMAP_DEF,combinTheory.APPLY_UPDATE_THM]
      >> rw [FAPPLY_FUPDATE_THM])
QED

Theorem equiv2 :
  ∀E E't t inputs.
    Supports E itprog ∧
    isInit_Stream (E ' "isInit") ∧
    E't = strmIndex (strmSteps E itprog t) t ∧
    inputs = input_of itprog E
    ⇒
      (state_of itprog E't, output_of itprog E't)
      =
      stateSteps inputs initState itprog t
Proof
  simp[]
  >> Induct_on ‘t’
  >- (expand_Supports
      >> rw [stateSteps_def, strmSteps_def,stateStep_def,input_of_def,
             itprog_inports, itprog_var_defs,itprog_out_defs]
      >> rw [strmIndex_DRESTRICT,lem]
      >> rw [FUPDATE_LIST_THM,FUNION_FUPDATE_1]
      >> CONV_TAC (RAND_CONV EVAL)
      >> CONV_TAC (PATH_CONV "rlr" finite_mapLib.fupdate_NORMALISE_CONV)
      >> rw [DRESTRICT_FUPDATE]
      >> rw [strmStep_def,itprog_inports,itprog_var_defs,itprog_out_defs]
      >> rw[fmap_EXT]
      >> CONV_TAC (RATOR_CONV EVAL)
      >- (rw [DRESTRICT_DEF,EXTENSION,IN_INTER] >> metis_tac[])
      >- (rw [DRESTRICT_DEF,FUN_FMAP_DEF] >> EVAL_TAC >> metis_tac[])
      >- (rw [DRESTRICT_DEF,EXTENSION,IN_INTER] >> metis_tac[])
      >- (rw [DRESTRICT_DEF,FUN_FMAP_DEF] >> EVAL_TAC >> metis_tac[])
     )

  >- (rpt strip_tac
      >> ‘Supports (strmSteps E itprog t) itprog’ by metis_tac [Supports_strmSteps]
      >> ‘isInit_Stream (strmSteps E itprog t ' "isInit")’
            by (‘Wellformed itprog’ by (EVAL_TAC >> simp[]) >>
                ‘MEM "isInit" itprog.inports’ by EVAL_TAC >>
                metis_tac [isInit_Stable])
      >> ‘stateSteps (input_of itprog E) initState itprog t
          =
         (state_of itprog (strmIndex (strmSteps E itprog t) t),
          output_of itprog (strmIndex (strmSteps E itprog t) t))’ by metis_tac[]
      >> WEAKEN_TAC is_forall
      >> rw [stateSteps_def]
      >> rw [Once EQ_SYM_EQ]
      >> irule equiv2_step
      >> rw[]
      >> qexists_tac ‘strmSteps E itprog t’
      >> rw[]
         >- rw [strmSteps_def]
         >- (‘Wellformed itprog’ by (EVAL_TAC >> rw[]) >> metis_tac[input_of_stable])
     )
QED

(*---------------------------------------------------------------------------*)
(* "pre-CakeML" logic function version of itprog. Note that variable in2 is  *)
(* a parameter when it doesn't strictly have to be.                          *)
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
(* Show that aprogFn is equal to stateStep, i.e. that the logic function is  *)
(* equal to the valEnv transformer.                                          *)
(*---------------------------------------------------------------------------*)

Theorem equiv3 :
  ∀input isInit N ap in2 in1.
     let inE = FEMPTY |++ [("input",IntValue input);("isInit", BoolValue isInit)] ;
         stateIn = FEMPTY
                   |++ [("N",    IntValue N);
                        ("ap",   BoolValue ap);
                        ("in2",  IntValue in2);
                        ("in1",  IntValue in1)];
         (stateOut,outE) = stateStep itprog (inE,stateIn) ;
         state_N   = int_of(stateOut ' "N");
         state_ap  = bool_of(stateOut ' "ap");
         state_in2 = int_of(stateOut ' "in2");
         state_in1 = int_of(stateOut ' "in1");
         output_ap = bool_of(outE ' "out")
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


(*---------------------------------------------------------------------------*)
(* Lemma that state_ap = out_ap. Not used.                                   *)
(*---------------------------------------------------------------------------*)

Theorem out_eq_ap :
  ∀inE stateIn stateOut outE.
      (stateOut,outE) = stateStep itprog (inE,stateIn)
  ⇒
  (outE ' "out") = (stateOut ' "ap")
Proof
  EVAL_TAC >> rw[] >> rpt(pop_assum mp_tac) >> rw[] >> EVAL_TAC
QED

val _ = export_theory();
