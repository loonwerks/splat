open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory
     intboolTheory;

val _ = intLib.prefer_int();

val _ = new_theory "examples";

val conj_lemma = DECIDE “!a b. a /\ (a ==> b) ==> a /\ b”;

(* ========================================================================== *)
(*                                                                            *)
(*                Examples                                                    *)
(*                                                                            *)
(* ========================================================================== *)

(*---------------------------------------------------------------------------*)
(* Trivial beginning example                                                 *)
(*  I = [input]                                                              *)
(*  A = []                                                                   *)
(*  V = []                                                                   *)
(*  O = [output = input]                                                     *)
(*  G = [input ≤ ouput]                                                      *)
(*---------------------------------------------------------------------------*)

Definition comp1_def :
  comp1 =
     <|    inports := ["input"];
          var_defs := [];
          out_defs := [IntStmt "output" (IntVar "input")];
       assumptions := [];
        guarantees := [NotExpr (LtExpr (IntVar "output") (IntVar "input"))]
     |>
End

Theorem comp1_correct :
  Component_Correct comp1
Proof
  EVAL_TAC >> simp [] >> Cases_on ‘t’ >> EVAL_TAC >> rw []
QED

(*---------------------------------------------------------------------------*)
(* Simple use of variable assignments                                        *)
(*  I = [input]                                                              *)
(*  V = [v = input + 1]                                                      *)
(*  O = [output = v]                                                         *)
(*  A = []                                                                   *)
(*  G = [input < output]                                                     *)
(*---------------------------------------------------------------------------*)

Definition comp2_def:
  comp2 =
     <| inports  := ["input"];
        var_defs := [IntStmt "v" (AddExpr (IntVar "input") (IntLit 1))];
        out_defs := [IntStmt "output" (IntVar "v")];
        assumptions := [];
        guarantees := [LtExpr (IntVar "input") (IntVar "output")]
     |>
End

Theorem comp2_correct :
  Component_Correct comp2
Proof
 EVAL_TAC >> simp [] >> Cases_on ‘t’ >> EVAL_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Trivial use of Hist                                                       *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = []                                                                   *)
(*  O = [output = 42]                                                        *)
(*  G = [Hist(output = 42)]                                                  *)
(*---------------------------------------------------------------------------*)

Definition comp3_def:
  comp3 =
     <| inports  := [];
        var_defs := [];
        out_defs := [IntStmt "output" (IntLit 42)];
        assumptions := [];
        guarantees := [HistExpr (EqExpr (IntVar "output") (IntLit 42))]
     |>
End

Theorem comp3_correct :
  Component_Correct comp3
Proof
  EVAL_TAC
  >> simp []
  >> Induct_on ‘t’
  >> EVAL_TAC
  >- rw[int_of_def]
  >- (fs[GSYM comp3_def] >> rw[] >> rw[int_of_def])
QED

(*---------------------------------------------------------------------------*)
(* Fby and Pre                                                               *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [steps = 1 -> 1 + pre steps]                                         *)
(*  O = [output = steps]                                                     *)
(*  G = [0 < output]                                                         *)
(*                                                                           *)
(* Needs some lemmas in order to do the proof                                *)
(*---------------------------------------------------------------------------*)

Definition comp4_def:
   comp4 =
       <| inports := [];
          var_defs :=
              [IntStmt "steps"
                 (FbyExpr (IntLit 1)
                    (AddExpr (IntLit 1) (PreExpr (IntVar "steps"))))];
          out_defs := [IntStmt "output" (IntVar "steps")];
       assumptions := [];
        guarantees := [LtExpr (IntLit 0) (IntVar "output")]|>
End

val output_effect = EVAL “componentFn E itFact t ' "output" t” |> SIMP_RULE (srw_ss()) [];
val steps_effect  = EVAL “componentFn E comp4 t ' "steps" t”   |> SIMP_RULE (srw_ss()) [];

Theorem Vars_Eq[local] :
  ∀t E. iterateFn E comp4 t ' "steps" t = iterateFn E comp4 t ' "output" t
Proof
  Induct
  >> rw [iterateFn_def,steps_effect]
  >> EVAL_TAC
  >> rw [GSYM comp4_def]
QED

Theorem comp4_correct :
  Component_Correct comp4
Proof
 EVAL_TAC
  >> simp []
  >> rw [GSYM comp4_def]
  >> Induct_on ‘t’
  >> EVAL_TAC
  >> rw [GSYM comp4_def,Vars_Eq]
QED

(*---------------------------------------------------------------------------*)
(* Iterative factorial is implemented by the rewrite system                  *)
(*                                                                           *)
(*   (n,fact) --> (n+1,fact * (n+1))                                         *)
(*                                                                           *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [n    = 0 -> 1 + pre n;                                              *)
(*       fact = 1 -> pre fact * n]                                           *)
(*  O = [output = fact]                                                      *)
(*  G = [0 < fact]                                                           *)
(*                                                                           *)
(* We can take the iteration of this transition system into HOL and show     *)
(* that it implements the usual recursion equation for factorial.            *)
(*---------------------------------------------------------------------------*)

Definition itFact_def:
   itFact =
     <| inports := [];
        var_defs :=
          [IntStmt "n"
             (FbyExpr (IntLit 0) (AddExpr (IntLit 1) (PreExpr (IntVar "n"))));
           IntStmt "fact"
                 (FbyExpr (IntLit 1)
                    (MultExpr (PreExpr (IntVar "fact")) (IntVar "n")))];
        out_defs := [IntStmt "output" (IntVar "fact")];
        assumptions := [];
        guarantees := [LtExpr (IntLit 0) (IntVar "output")]|>
End

val output_effect = EVAL “componentFn E itFact t ' "output" t” |> SIMP_RULE (srw_ss()) [];
val n_effect      = EVAL “componentFn E itFact t ' "n" t”      |> SIMP_RULE (srw_ss()) [];
val fact_effect   = EVAL “componentFn E itFact t ' "fact" t”   |> SIMP_RULE (srw_ss()) [];

Theorem Vars_Eq[local] :
 ∀t E. iterateFn E itFact t ' "output" t = iterateFn E itFact t ' "fact" t
Proof
  Induct >> rw [iterateFn_def,output_effect,fact_effect]
QED

Theorem n_is_N:
  ∀t E. int_of (iterateFn E itFact t ' "n" t) = int_of_num t
Proof
  Induct
   >> rw [iterateFn_def,n_effect,integerTheory.int_of_num,integerTheory.INT_1,int_of_def]
   >> pop_assum kall_tac
   >> intLib.ARITH_TAC
QED

Theorem itFact_Meets_Spec :
  Component_Correct itFact
Proof
 EVAL_TAC
  >> simp [GSYM itFact_def]
  >> Induct_on ‘t’
  >> EVAL_TAC
  >> fs [GSYM itFact_def,Vars_Eq,n_is_N]
  >> rw[] >> res_tac
  >> pop_assum mp_tac
  >> qspec_tac (‘iterateFn E itFact t ' "fact" t’,‘i’)
  >> rpt strip_tac
  >> match_mp_tac int_arithTheory.positive_product_implication
  >> intLib.ARITH_TAC
QED

(*---------------------------------------------------------------------------*)
(* Iterative factorial is equal to recursive factorial (arithmeticTheory.FACT*)
(*---------------------------------------------------------------------------*)

val num_mult_int = CONJUNCT1 integerTheory.INT_MUL_CALCULATE;

Theorem itFact_eq_FACT :
 ∀t E. iterateFn E itFact t ' "fact" t = IntValue(&(FACT t))
Proof
  Induct_on ‘t’
  >> EVAL_TAC
  >> fs [GSYM itFact_def]
  >> fs[Vars_Eq,n_is_N]
  >> rw_tac std_ss [arithmeticTheory.FACT,Once (GSYM num_mult_int)]
  >> rw_tac std_ss [integerTheory.int_of_num,integerTheory.INT_1,int_of_def]
  >> intLib.ARITH_TAC
QED

(*---------------------------------------------------------------------------*)
(* Iterative Fibonacci is implemented by the rewrite system                  *)
(*                                                                           *)
(*       (x,y) --> (y,x+y)                                                   *)
(*                                                                           *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [x = 0 -> pre y;                                                     *)
(*       y = 1 -> pre x + pre y]                                             *)
(*  O = [output = y]                                                         *)
(*  G = [0 <= x and 0 < output]                                              *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition itFib_def:
   itFib =
      <| inports := [];
         var_defs :=
             [IntStmt "x"
               (FbyExpr (IntLit 0) (PreExpr (IntVar "y")));
              IntStmt "y"
                 (FbyExpr (IntLit 1)
                    (AddExpr (PreExpr (IntVar "x")) (PreExpr (IntVar "y"))))];
         out_defs := [IntStmt "output" (IntVar "y")];
       assumptions := [];
       guarantees := [AndExpr (NotExpr (LtExpr (IntVar "x") (IntLit 0)))
                              (LtExpr (IntLit 0) (IntVar "output"))]
      |>
End

val output_effect = EVAL “componentFn E itFib t ' "output" t” |> SIMP_RULE (srw_ss()) [];
val x_effect      = EVAL “componentFn E itFib t ' "x" t”      |> SIMP_RULE (srw_ss()) [];
val y_effect      = EVAL “componentFn E itFib t ' "y" t”      |> SIMP_RULE (srw_ss()) [];

Theorem Vars_Eq[local] :
   ∀t E. iterateFn E itFib t ' "output" t = iterateFn E itFib t ' "y" t
Proof
  Induct >> rw [iterateFn_def,output_effect,y_effect]
QED

Theorem itFib_Meets_Spec :
  Component_Correct itFib
Proof
 EVAL_TAC
  >> simp [GSYM itFib_def]
  >> Induct_on ‘t’
  >> EVAL_TAC
  >- rw[]
  >- (simp_tac arith_ss [GSYM itFib_def]
       >> fs[Vars_Eq]
       >> rw []
       >> res_tac
       >> intLib.ARITH_TAC)
QED

(*---------------------------------------------------------------------------*)
(* Monitor an input stream for sortedness (w/o boolean vars)                 *)
(*                                                                           *)
(*  I = [input]                                                              *)
(*  A = []                                                                   *)
(*  V = [diff  = 0 -> input - pre input]                                     *)
(*       alert = 0 -> if diff < 0 then 1 else pre alert                      *)
(*  O = [output = (alert = 0)]                                               *)
(*  G = [output iff Hist (0 <= diff)]                                        *)
(*---------------------------------------------------------------------------*)

Definition sorted_def:
   sorted =
      <| inports := ["input"];
         var_defs :=
             [IntStmt "diff"
               (FbyExpr (IntLit 0)
                        (SubExpr (IntVar "input")
                                 (PreExpr (IntVar "input"))));
              IntStmt "alert"
                (FbyExpr (IntLit 0)
                         (CondExpr (LtExpr (IntVar "diff") (IntLit 0))
                                   (IntLit 1)
                                   (PreExpr (IntVar "alert"))))] ;
         out_defs := [BoolStmt "output" (EqExpr (IntVar"alert") (IntLit 0))] ;
       assumptions := [];
       guarantees := [IffExpr (BoolVar"output")
                              (HistExpr (LeqExpr (IntLit 0) (IntVar "diff")))]
      |>
End

Triviality int_lem = intLib.ARITH_PROVE “i < 0i <=> ~(0i <= i)”;


Theorem output_equal_alert[local] :
 ∀E t.
    bool_of (iterateFn E sorted t ' "output" t)
     <=>
    int_of (iterateFn E sorted t ' "alert" t) = 0
Proof
  gen_tac >> Cases_on ‘t’ >> EVAL_TAC
QED

Theorem sorted_Meets_Spec :
  Component_Correct sorted
Proof
 EVAL_TAC
  >> simp [GSYM sorted_def,output_equal_alert]
  >> rpt strip_tac
  >> Induct_on ‘t’
  >> EVAL_TAC
  >> simp [GSYM sorted_def,int_of_def]
  >> rw []
    >- (qexists_tac ‘SUC t’
        >> rw[]
        >> qpat_x_assum ‘x - y < 0i’ mp_tac
        >> qspec_tac (‘iterateFn E sorted t ' "input" (SUC t)’,‘j’)
        >> qspec_tac (‘iterateFn E sorted t ' "input" t’,‘i’)
        >> rw [int_of_def]
        >> pop_assum mp_tac
        >> qspec_tac (‘int_of j - int_of i’,‘k’)
        >> gen_tac >> rpt (pop_assum kall_tac)
        >> intLib.ARITH_TAC)
    >- (rw[EQ_IMP_THM]
        >> rw[]
          >- (qpat_x_assum ‘~(x - y < 0i)’ mp_tac
              >> qspec_tac (‘iterateFn E sorted t ' "input" (SUC t)’,‘j’)
              >> qspec_tac (‘iterateFn E sorted t ' "input" t’,‘i’)
              >> rw [int_of_def]
              >> pop_assum mp_tac
              >> qspec_tac (‘int_of j - int_of i’,‘k’)
              >> gen_tac >> rpt (pop_assum kall_tac)
              >> intLib.ARITH_TAC)
          >- (qpat_x_assum ‘∀n. n ≤ SUC t ⇒ P’ (mp_tac o Q.SPEC ‘n’) >> rw[])
       )
QED


(*---------------------------------------------------------------------------*)
(* A division node implementing summation of pointwise division of stream    *)
(* i1 by i2. This example uses constraints on the assumptions.               *)
(*                                                                           *)
(*  I = [i1,i2]                                                              *)
(*  A = [0 ≤ i1, 0 < i2]                                                     *)
(*  V = [divsum = (i1 / i2) -> pre divsum + (i1/i2)]                         *)
(*  O = [output = divsum]                                                    *)
(*  G = [0 ≤ output]                                                         *)
(*                                                                           *)
(* Subtlety: one might think that we could have written                      *)
(*                                                                           *)
(*  V = []                                                                   *)
(*  O = [output = (i1 / i2) -> pre output + (i1/i2)]                         *)
(*                                                                           *)
(* but output variables aren't allowed to be state-holding                   *)
(*---------------------------------------------------------------------------*)

Definition divsum_def:
  divsum =
     <| inports := ["i1";"i2"];
        var_defs :=
          [IntStmt "divsum"
               (FbyExpr (DivExpr (IntVar "i1") (IntVar "i2"))
                        (AddExpr (PreExpr (IntVar "divsum"))
                                 (DivExpr (IntVar "i1") (IntVar "i2"))))];
         out_defs := [IntStmt "output" (IntVar "divsum")];
      assumptions := [LtExpr (IntLit 0) (IntVar"i2");
                      LeqExpr (IntLit 0) (IntVar"i1")];
       guarantees := [LeqExpr (IntLit 0) (IntVar"output")]
      |>
End

val divsum_effect = EVAL “componentFn E divsum t ' "divsum" t” |> SIMP_RULE (srw_ss()) [];
val output_effect = EVAL “componentFn E divsum t ' "output" t” |> SIMP_RULE (srw_ss()) [];

Theorem Vars_Eq[local] :
 ∀t E. iterateFn E divsum t ' "output" t = iterateFn E divsum t ' "divsum" t
Proof
  Induct >> rw [iterateFn_def,output_effect,divsum_effect]
QED

Theorem divsum_Meets_Spec :
  Component_Correct divsum
Proof
 simp [Component_Correct_def]
  >> irule conj_lemma
  >> conj_tac
  >- (EVAL_TAC >> rw[])
  >- (disch_tac
      >> gen_tac
      >> Induct_on ‘t’
      >- (EVAL_TAC
          >> rw [GSYM divsum_def]
          >> ntac 2 (pop_assum mp_tac)
          >> rpt (pop_assum kall_tac)
          >> qspec_tac(‘int_of(E ' "i2" 0)’,‘j’)
          >> qspec_tac(‘int_of(E ' "i1" 0)’,‘i’)
          >> rpt gen_tac
          >> rw []
          >> ‘~(j=0)’ by intLib.ARITH_TAC
          >> rw [integerTheory.int_div])
      >- (strip_tac
          >> ‘assumsVal E divsum t’ by (rpt (pop_assum mp_tac) >> EVAL_TAC >> fs[] >> rw[])
          >> fs[]
          >> pop_assum kall_tac
          >> pop_assum mp_tac
          >> EVAL_TAC
          >> rw [GSYM divsum_def]
          >> ‘0 < int_of (E ' "i2" (SUC t)) ∧ 0 ≤ int_of (E ' "i1" (SUC t))’
             by metis_tac[LESS_EQ_REFL]
          >> WEAKEN_TAC is_forall
          >> ‘MEM "i1" divsum.inports ∧ MEM "i2" divsum.inports’ by EVAL_TAC
          >> rw[Inputs_Stable]
          >> ntac 2 (pop_assum kall_tac)
          >> qpat_x_assum ‘guarsVal x y z’ mp_tac
          >> EVAL_TAC
          >> rw[GSYM divsum_def]
          >> fs[Vars_Eq]
          >> irule integerTheory.INT_LE_ADD
          >> rw[]
          >> pop_assum kall_tac
          >> ntac 2 (pop_assum mp_tac)
          >> qspec_tac(‘int_of(E ' "i2" (SUC t))’,‘j’)
          >> qspec_tac(‘int_of(E ' "i1" (SUC t))’,‘i’)
          >> rpt gen_tac
          >> rw []
          >> ‘~(j=0)’ by intLib.ARITH_TAC
          >> rw [integerTheory.int_div])
     )
QED

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

val example =
 “exprVal E
    (FbyExpr (IntLit 1)
             (PreExpr (FbyExpr (IntLit 1)
                               (AddExpr (IntVar "fib") (PreExpr (IntVar "fib"))))))
    t”
 |> EVAL
 |> SIMP_RULE (srw_ss()) [numLib.ARITH_PROVE ``n - 1n -1 = n - 2``];

Definition recFib_def:
  recFib =
     <| inports := [];
        var_defs :=
          [IntStmt "recFib"
             (FbyExpr (IntLit 1)
                (PreExpr (FbyExpr (IntLit 1)
                         (AddExpr (IntVar "recFib") (PreExpr (IntVar "recFib"))))))];
         out_defs := [IntStmt "output" (IntVar "recFib")];
      assumptions := [];
       guarantees := [LeqExpr (IntLit 0) (IntVar"output")]
      |>
End

val th0 = EVAL“(iterateFn E recFib 0 ' "output") 0”
val th1 = EVAL“(iterateFn E recFib 1 ' "output") 1”
val th2 = EVAL“(iterateFn E recFib 2 ' "output") 2”
val th3 = EVAL“(iterateFn E recFib 3 ' "output") 3”
val th4 = EVAL“(iterateFn E recFib 4 ' "output") 4”
val th5 = EVAL“(iterateFn E recFib 5 ' "output") 5”
val th6 = EVAL“(iterateFn E recFib 6 ' "output") 6”

val recFib_effect = EVAL “componentFn E recFib t ' "recFib" t” |> SIMP_RULE (srw_ss()) [];
val output_effect = EVAL “componentFn E recFib t ' "output" t” |> SIMP_RULE (srw_ss()) [];

Theorem Vars_Eq[local] :
 ∀t E. iterateFn E recFib t ' "output" t = iterateFn E recFib t ' "recFib" t
Proof
  Induct >> rw [iterateFn_def,output_effect,recFib_effect]
QED

Theorem recFib_Meets_Spec :
  Component_Correct recFib
Proof
 EVAL_TAC
  >> simp [GSYM recFib_def,Vars_Eq]
  >> gen_tac
  >> completeInduct_on ‘t’
  >> EVAL_TAC
  >> fs [GSYM recFib_def,output_effect]
  >> rw []
  >> fs[]
  >> Cases_on ‘t’
  >- (EVAL_TAC >> rw [GSYM recFib_def])
  >- (Cases_on ‘n’
      >- (EVAL_TAC >> rw [GSYM recFib_def])
      >- (‘n' < SUC (SUC n') /\ SUC n' < SUC (SUC n')’ by decide_tac
          >> res_tac
          >> rpt (WEAKEN_TAC numSyntax.is_less)
          >> ntac 2 (pop_assum mp_tac)
          >> EVAL_TAC
          >> rw [GSYM recFib_def,int_of_def]))
QED

(*---------------------------------------------------------------------------*)
(* Check that recFib is indeed Fibonacci as we know it.                      *)
(*---------------------------------------------------------------------------*)

Definition Fib_def :
  Fib 0n = 1n ∧
  Fib (SUC 0) = 1 ∧
  Fib (SUC (SUC n)) = Fib n + Fib (SUC n)
End

Theorem recFib_Sanity:
  ∀t E. (iterateFn E recFib t ' "output") t = IntValue(&(Fib t))
Proof
 recInduct Fib_ind
 >> rw[Vars_Eq]
 >- (EVAL_TAC >> rw[])
 >- (EVAL_TAC >> metis_tac [ONE, Fib_def])
 >- (pop_assum mp_tac
      >> EVAL_TAC
      >> fs[GSYM recFib_def,int_of_def]
      >> disch_then kall_tac
      >> intLib.ARITH_TAC)
QED


(*###########################################################################*)
(* Some examples of stream elements being accessed at depth > 1              *)
(*###########################################################################*)

  N = 0 -> pre N + 1;
  Fib = if N < 2 then 1 else pre Fib + pre (pre Fib)
  ArithProg = if N < 2 then true
                else input - pre input = pre input - pre(pre input)

val _ = export_theory();
