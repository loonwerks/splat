(*===========================================================================*)
(* Definition of Lustre as a shallow embedding.                              *)
(* Author: Mike Gordon (mjcg@cl.cam.ac.uk)                                   *)
(* Tweaks: Konrad Slind (klslind@rockwellcollins.com)                        *)
(*                                                                           *)
(* Examples from Pascal Raymond, Verimag-CNRS, in the slides of the talk     *)
(* "The Lustre language"                                                     *)
(*                                                                           *)
(*  http://www.cmi.univ-mrs.fr/epit32/Documents/Raymond_lustre.pdf           *)
(*                                                                           *)
(*===========================================================================*)

open HolKernel boolLib Parse bossLib pairLib
     pairTheory numTheory prim_recTheory arithmeticTheory
     combinTheory pred_setTheory pred_setLib;

val _ = new_theory "Lustre";

(*---------------------------------------------------------------------------*)
(* Used when accessing before the beginning of a stream. Never needs to be   *)
(* expanded.                                                                 *)
(*---------------------------------------------------------------------------*)

Definition Lustre_nil_def :
  nil = ARB
End

(*---------------------------------------------------------------------------*)
(* Basic Lustre operators and lifted expressions                             *)
(*---------------------------------------------------------------------------*)

val lustre_defs =
 TotalDefn.multiDefine
  `(Lustre_init_stream P Q t <=> if t=0 then P t else Q t)  /\ (* stream init *)
   (Lustre_pre P t ⇔ if t=0 then nil else P (t-1)) /\  (* predecessor element *)
   (Lustre_true t ⇔ T) /\
   (Lustre_false t ⇔ F) /\
   (Lustre_const c t ⇔ c) /\
   (Lustre_not B t ⇔ ~(B t)) /\
   (Lustre_and B1 B2 t ⇔ (B1 t) /\ (B2 t)) /\
   (Lustre_or B1 B2 t  ⇔ (B1 t) \/ (B2 t)) /\
   (Lustre_eq P Q t    ⇔ (P t = Q t))      /\
   (Lustre_add X Y t   ⇔ (X t) + (Y t))    /\
   (Lustre_sub X Y t   ⇔ (X t) - (Y t))    /\
   (Lustre_mult X Y t  ⇔ (X t) * (Y t))    /\
   (Lustre_div X Y t   ⇔ (X t) DIV (Y t))  /\
   (Lustre_mod X Y t   ⇔ (X t) MOD (Y t))  /\
   (Lustre_exp X Y t   ⇔ (X t) ** (Y t))   /\
   (Lustre_lt X Y t    ⇔ (X t) < (Y t))    /\
   (Lustre_lte X Y t   ⇔ (X t) <= (Y t))   /\
   (Lustre_gt X Y t    ⇔ (X t) > (Y t))    /\
   (Lustre_gte X Y t   ⇔ (X t) >= (Y t))   /\
   (Lustre_if_then_else B P Q t ⇔ if B t then P t else Q t)`;

val [Lustre_init_stream_def,
     Lustre_pre_def,Lustre_true_def, Lustre_false_def, Lustre_const_def,
     Lustre_not_def,
     Lustre_and_def,Lustre_or_def,Lustre_eq_def,
     Lustre_add_def,Lustre_sub_def,Lustre_mult_def,
     Lustre_div_def,Lustre_mod_def,Lustre_exp_def,
     Lustre_lt_def,Lustre_lte_def,Lustre_gt_def,Lustre_gte_def,
     Lustre_if_then_else_def] = List.rev lustre_defs;

(*---------------------------------------------------------------------------*)
(* Simplification set that replaces Lustre constructs by their semantics     *)
(*---------------------------------------------------------------------------*)

val lustre_ss = bossLib.arith_ss ++ rewrites (FUN_EQ_THM :: lustre_defs);

(*---------------------------------------------------------------------------*)
(* Set up parsing and prettyprinting for Lustre operators.                   *)
(*---------------------------------------------------------------------------*)

val _ = overload_on("->",``Lustre_init_stream``);
val _ = overload_on("pre",``Lustre_pre``);
val _ = overload_on("true",``Lustre_true``);
val _ = overload_on("false",``Lustre_false``);
val _ = overload_on("const",``Lustre_const``);
val _ = overload_on("and",``Lustre_and``);
val _ = overload_on("or",``Lustre_or``);
val _ = overload_on("not",``Lustre_not``);
val _ = overload_on("==",``Lustre_eq``);
val _ = overload_on("+",``Lustre_add``);
val _ = overload_on("-",``Lustre_sub``);
val _ = overload_on("*",``Lustre_mult``);
val _ = overload_on("**",``Lustre_exp``);
val _ = overload_on("DIV",``Lustre_div``);
val _ = overload_on("MOD",``Lustre_mod``);
val _ = overload_on("<",``Lustre_lt``);
val _ = overload_on("<=",``Lustre_lte``);
val _ = overload_on(">",``Lustre_gt``);
val _ = overload_on(">=",``Lustre_gte``);
val _ = overload_on("COND",``Lustre_if_then_else``);
val _ = overload_on("COND",``bool$COND``);

val _ = set_fixity "->" (Infixr 470);
val _ = set_fixity "not" (Prefix 900);
val _ = set_fixity "and" (Infixr 399);
val _ = set_fixity "or" (Infixr 299);
val _ = set_fixity "==" (Infixl 99);

(*---------------------------------------------------------------------------*)
(* Node semantics uses Hilbert choice for return values and existential for  *)
(* local variables.                                                          *)
(*                                                                           *)
(* Lustre: "node N X = returns A; let A = E tel"                             *)
(* in HOL: "N X = returns A. var v1 ... vn. E"                               *)
(*    i.e. "N X = @A. ?v1 ... vn. E"                                         *)
(*                                                                           *)
(* In other words, pick return value(s) such that there exist variables      *)
(* v1 ... vn making the equations true. Note that this is a contextual and   *)
(* non-constructive definition of the node behavior and proving any          *)
(* properties of the node will first require proving the existence of the    *)
(* specified return stream. This often reduces to providing witnesses for    *)
(* equations specified in the body of the node.                              *)
(*---------------------------------------------------------------------------*)

fun lustre_syntax b =   (* turns treatment of "returns" and "var" on and off *)
 if b then
   (set_fixity "returns" Binder;
    set_fixity "var" Binder;
    overload_on ("returns", boolSyntax.select);
    overload_on ("var",     boolSyntax.existential))
 else
  (clear_overloads_on "returns";
   clear_overloads_on "var")
;

val _ = lustre_syntax true;


(*---------------------------------------------------------------------------*)
(* Support for making Lustre-like definitions.                               *)
(*---------------------------------------------------------------------------*)

val ERR = mk_HOL_ERR "Lustre Theory";

fun Lustre_Def tm =
 let val (left,right) = dest_eq (snd (strip_forall tm))
     val (a,args) = strip_comb left
     val a' = if is_var a then a else
              if is_const a then mk_var(dest_const a)
              else raise ERR "Lustre_Def" "unexpected syntax on lhs"
     val (defName,ty) = dest_var a'
     val exVar = mk_var(defName,type_of left)
     val _ = if Lib.all is_var args then () else
             raise ERR "Lustre_Def" "unexpected syntax on lhs"
     val def_tm = list_mk_forall(args,mk_exists(exVar, mk_eq(exVar,right)))
  in
  new_specification
   (defName^"_def", [defName],
    Ho_Rewrite.PURE_REWRITE_RULE [SKOLEM_THM] (METIS_PROVE [] def_tm))
  end;

(*===========================================================================*)
(* Example definitions and subsequent derivation of desired eqns.            *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Max (pointwise)                                                           *)
(*---------------------------------------------------------------------------*)

val Max_def =
 Lustre_Def
  “Max A B = returns M:num->num.
      M = (if A >= B then A else B)”;

Theorem Max_thm :
  Max A B t = MAX (A t) (B t)
Proof
 rw_tac lustre_ss [MAX_DEF,Max_def]
QED


(*---------------------------------------------------------------------------*)
(* Iterative Max on stream                                                   *)
(*---------------------------------------------------------------------------*)

val Max_Stream_def =
 Lustre_Def
  “Max_Stream A = returns M:num->num.
      M = (A -> (if A >= pre M then A else pre M))”;

(*---------------------------------------------------------------------------*)
(* Witness                                                                   *)
(*---------------------------------------------------------------------------*)

Definition MaxFn_def :
  MaxFn X 0 = X 0 ∧
  MaxFn X (SUC t) = MAX (X (SUC t)) (MaxFn X t)
End

Theorem Max_Stream_inhabits :
  ∀t. ∃n. n ≤ t ∧ Max_Stream A t = A n
Proof
 rw_tac lustre_ss [Max_Stream_def]
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- (qexists_tac ‘MaxFn A’ >> Induct >> rw[MaxFn_def,MAX_DEF])
  >- (rpt strip_tac
      >> Induct_on ‘t’
      >> ONCE_ASM_REWRITE_TAC[]
      >> REWRITE_TAC [NOT_LESS_0,NOT_SUC,SUC_SUB1]
      >- simp[]
      >- (WEAKEN_TAC is_forall
          >> rw[]
          >> metis_tac [LESS_EQ_REFL,DECIDE “a <= SUC b ⇔ a≤b ∨ a = SUC b”]))
QED

Theorem Max_Stream_is_max :
  ∀t n. n ≤ t ⇒ A n ≤ Max_Stream A t
Proof
 rw_tac lustre_ss [Max_Stream_def]
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- (qexists_tac ‘MaxFn A’ >> Induct >> rw[MaxFn_def,MAX_DEF])
  >- (rpt strip_tac
      >> Induct_on ‘t’
      >> ONCE_ASM_REWRITE_TAC[]
      >> REWRITE_TAC [NOT_LESS_0,NOT_SUC,SUC_SUB1]
      >> WEAKEN_TAC is_forall
      >> rw [DECIDE “a >= b ⇔ b ≤ a”]
      >> fs [DECIDE “a <= SUC b ⇔ a≤b ∨ a = SUC b”])
QED

Theorem Max_Stream_is_MaxFn :
  Max_Stream X = MaxFn X
Proof
 rw_tac lustre_ss [Max_Stream_def]
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- (qexists_tac ‘MaxFn X’ >> Induct >> rw[MaxFn_def,MAX_DEF])
  >- (rpt strip_tac
      >> Induct_on ‘x’
      >> ONCE_ASM_REWRITE_TAC[]
      >> REWRITE_TAC [NOT_LESS_0,NOT_SUC,SUC_SUB1,MaxFn_def,MAX_DEF]
      >> rw[])
QED

(*---------------------------------------------------------------------------*)
(* Average                                                                   *)
(*---------------------------------------------------------------------------*)

val Average_def =
 Lustre_Def
  “Average X Y = returns A.
     var S. (A = S DIV const 2) /\
            (S = X + Y)”;

Theorem Average_thm :
  Average X Y t = ((X t + Y t) DIV 2)
Proof
  rw_tac lustre_ss [Average_def]
   >> SELECT_ELIM_TAC
   >> rw []
   >> qexists_tac ‘\a. (X a + Y a) DIV 2’  (* trivial instantiation *)
   >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Edge (rising)                                                             *)
(*---------------------------------------------------------------------------*)

val Edge_def =
 Lustre_Def
  “Edge X = returns E:num->bool.
      E = (false -> (X and not(pre X)))”;

(*---------------------------------------------------------------------------*)
(* Characterization                                                          *)
(*---------------------------------------------------------------------------*)

Theorem Edge_thm :
  Edge X 0 = F /\
  Edge X (SUC t) = (~X t /\ X(t+1))
Proof
 rw_tac lustre_ss [Edge_def] >> metis_tac[ADD1]
QED


(*---------------------------------------------------------------------------*)
(* Iterative MinMax on stream                                                *)
(*---------------------------------------------------------------------------*)

val MinMax_def =
 Lustre_Def
   “MinMax X = returns p.
       (FST p = (X -> if X < pre (FST p) then X else pre (FST p))) ∧
       (SND p = (X -> if X > pre (SND p) then X else pre (SND p)))”;

Theorem MinMax_Named :
 !X. MinMax X = returns (Min,Max).
       (Min = (X -> if X < pre Min then X else pre Min)) /\
       (Max = (X -> if X > pre Max then X else pre Max))
Proof
  RW_TAC std_ss [pairTheory.LAMBDA_PROD,MinMax_def]
QED

(*---------------------------------------------------------------------------*)
(* Specify MinMax in terms of a pair of functions                            *)
(*---------------------------------------------------------------------------*)

Definition MinFn_def :
  MinFn X 0 = X 0 /\
  MinFn X (SUC t) = MIN (X (SUC t)) (MinFn X t)
End

Theorem MinMax_thm :
 ∀X. MinMax X = (MinFn X, MaxFn X)
Proof
  simp_tac lustre_ss [MinMax_Named]
  >> rpt gen_tac
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- (qexists_tac ‘(MinFn X,MaxFn X)’
        >> rw []
        >> Induct_on ‘x’
        >> rw [MinFn_def,MaxFn_def]
        >> rw_tac bool_ss [ONE,MIN_DEF,MAX_DEF]
        >> fs [ADD1])
  >- (Ho_Rewrite.REWRITE_TAC [FORALL_PROD]
        >> rw []
        >> REWRITE_TAC [FUN_EQ_THM]
        >> Induct
        >> ONCE_ASM_REWRITE_TAC []
        >> rpt(WEAKEN_TAC is_forall)
        >> REWRITE_TAC [NOT_SUC]
        >> rw[MinFn_def,MIN_DEF,MaxFn_def,MAX_DEF])
QED


(*---------------------------------------------------------------------------*)
(* Somewhat more abstract property                                           *)
(*---------------------------------------------------------------------------*)

Theorem MinFn_is_min :
  ∀X t. (∃i. i ≤ t ∧ X i = MinFn X t) ∧
         ∀n. n ≤ t ⇒ MinFn X t ≤ X n
Proof
 Induct_on ‘t’
  >> rw [MinFn_def,MIN_DEF]
  >> metis_tac [DECIDE “x ≤ SUC y ⇔ x ≤ y ∨ x = SUC y”,
      LESS_EQ_TRANS,NOT_LESS,LESS_EQ_REFL,LESS_IMP_LESS_OR_EQ]
QED

Theorem MaxFn_is_max :
  ∀X t. (∃i. i ≤ t ∧ X i = MaxFn X t) ∧
         (∀n. n ≤ t ⇒ X n ≤ MaxFn X t)
Proof
 Induct_on ‘t’
  >> rw [MaxFn_def,MAX_DEF]
  >> metis_tac [DECIDE “x ≤ SUC y ⇔ x ≤ y ∨ x = SUC y”,
      LESS_EQ_TRANS,NOT_LESS,LESS_EQ_REFL,LESS_IMP_LESS_OR_EQ]
QED

Theorem FINITE_LEQ :
∀t. FINITE {i | i <= t}
Proof
 Induct
  >> rw []
  >> ‘{i | i ≤ SUC t} = SUC t INSERT {i | i ≤ t}’ by rw [EXTENSION]
  >> metis_tac[FINITE_INSERT]
QED

Theorem MinMax_Prop :
 ∀X Min Max.
     MinMax X = (Min,Max)
      ⇒
      ∀t. Min t = MIN_SET{X i | i ≤ t} ∧
           Max t = MAX_SET{X i | i ≤ t}
Proof
 rw[MinMax_thm]
 >- (HO_MATCH_MP_TAC MIN_SET_ELIM
     >> rw[EXTENSION,PULL_EXISTS]
     >- metis_tac [LESS_EQ_REFL]
     >- metis_tac [EQ_LESS_EQ,MinFn_is_min])
 >- (HO_MATCH_MP_TAC MAX_SET_ELIM
     >> rw[EXTENSION,PULL_EXISTS]
     >- (‘FINITE{i | i ≤ t}’ by metis_tac [FINITE_LEQ] >>
         ‘FINITE (IMAGE X {i | i ≤ t})’ by metis_tac [IMAGE_FINITE] >>
          fs [GSPEC_IMAGE, combinTheory.o_DEF])
     >- metis_tac [LESS_EQ_REFL]
     >- metis_tac [EQ_LESS_EQ,MaxFn_is_max])
QED

(*---------------------------------------------------------------------------*)
(* MinMaxAverage                                                             *)
(*---------------------------------------------------------------------------*)

val MinMaxAverage_def =
 Lustre_Def
  “MinMaxAverage X = returns A.
    var min max.
      (A = Average min max) /\
      ((min,max) = MinMax X)”;

Theorem MinMaxAverage_thm :
  MinMaxAverage X =
   let (min,max) = MinMax X
   in Average min max
Proof
  rw_tac std_ss [MinMaxAverage_def]
End

(*---------------------------------------------------------------------------*)
(* Examples of recursive definitions.                                        *)
(*                                                                           *)
(*    N = 0 -> pre(N) + 1                                                    *)
(*    A = F -> not (pre(N))                                                  *)
(*---------------------------------------------------------------------------*)

val Nat_def =
 Lustre_Def
   “Nat = returns N. N = (const 0 -> pre N + const 1)”;

val Odd_def =
 Lustre_Def
  “Odd = returns A. A = (false -> not(pre A))”;
;

Theorem Nat_thm :
 ∀t . Nat t = t
Proof
 rw_tac lustre_ss [Nat_def]
  >> SELECT_ELIM_TAC
  >> conj_tac
  >- (qexists_tac `I` >> Induct >> rw[combinTheory.I_THM])
  >- (rpt strip_tac
       >> Induct_on `t`
       >> ONCE_ASM_REWRITE_TAC[]
       >> WEAKEN_TAC is_forall
       >> rw [])
QED

Theorem Odd_thm :
  !n. Odd n = ODD n
Proof
rw_tac lustre_ss [Odd_def]
 >> SELECT_ELIM_TAC
 >> conj_tac
 >- (qexists_tac ‘ODD’ >> Induct >> rw[ODD])
 >- (rpt strip_tac
       >> Induct_on `n`
       >> ONCE_ASM_REWRITE_TAC[]
       >> WEAKEN_TAC is_forall
       >> rw [ODD])
QED

(*---------------------------------------------------------------------------*)
(* Factorial                                                                 *)
(*                                                                           *)
(*   Fact = 1 -> N * pre(Fact)                                               *)
(*   N    = 0 -> pre(N) + 1                                                  *)
(*                                                                           *)
(* This describes an iterative implementation of factorial with two state    *)
(* variables, (N,Fact), initially (1,0), with the step transition            *)
(*                                                                           *)
(*   (N,Fact) --> (N+1,Fact * N+1)                                           *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val Fact_def =
 Lustre_Def
  “Fact = returns product.
     var N.
      (product = (const 1 -> N * pre(product))) ∧
      (N       = (const 0 -> pre(N) + const 1))”
;

Theorem Fact_thm :
  ∀n. Fact n = FACT n
Proof
 rw_tac lustre_ss [Fact_def]
 >> SELECT_ELIM_TAC
 >> conj_tac
 >- (qexists_tac ‘FACT’ >> qexists_tac ‘Nat’
     >> conj_tac
     >> Cases
     >- metis_tac [FACT]
     >- metis_tac [FACT,NOT_SUC,Nat_thm,MULT_SYM,SUC_SUB1]
     >- metis_tac [Nat_thm]
     >- metis_tac [Nat_thm,NOT_SUC,ADD1,SUC_SUB1])
 >- (Ho_Rewrite.REWRITE_TAC [PULL_EXISTS]
      >> rpt strip_tac
      >> Induct_on `n`
      >> ONCE_ASM_REWRITE_TAC[FACT]
      >- metis_tac[]
      >- (REWRITE_TAC [NOT_SUC,ADD1,SUC_SUB1]
          >> ‘∀t. N t = t’
               by (Induct >> ONCE_ASM_REWRITE_TAC[]
                   >> metis_tac [NOT_SUC,ADD1,SUC_SUB1])
          >> fs[]))
QED

(*---------------------------------------------------------------------------*)
(* Fibonacci                                                                 *)
(*                                                                           *)
(*   Fib = 1 -> pre(Fib + (0 -> pre Fib))                                    *)
(*                                                                           *)
(* For clarity, we drag the inner stream def out to the top level, rendering *)
(* the computation as an iteration over (presum,sum), initially (0,1), with  *)
(* transition function                                                       *)
(*                                                                           *)
(*   (presum,sum) --> (sum,presum + sum)                                     *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val Fib_def =
 Lustre_Def
  “Fib =  returns sum.
     var presum.
       (sum    = (const 1 -> pre(sum + presum))) ∧
       (presum = (const 0 -> pre sum))”;
;


(*
Theorem Fib_thm :
  ∀n. Fib n =
         if n = 0 ∨ n = 1 then
           1
         else Fib (n-1) + Fib (n-2)
Proof
 rw_tac lustre_ss [Fib_def]
 >> SELECT_ELIM_TAC
 >> conj_tac
 >-
End
*)


(*  Still to convert over ...

(*---------------------------------------------------------------------------*)
(* Switch                                                                    *)
(*---------------------------------------------------------------------------*)

val Switch_def =
 Define
  `(Switch (on,off) 0 = on 0) /\
   (Switch (on,off) (SUC t) =
      if Switch (on,off) t
       then (not off) (SUC t)
         else on (SUC t))`;

val SwitchEq =
 prove
  (``Switch (on,off) = if (false -> pre(Switch(on,off))) then not off else  on``,
   CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
    THEN RW_TAC arith_ss [Lustre_not_def,Lustre_false_def,Lustre_pre_def,
                          Lustre_if_then_else_def,Lustre_init_stream_def]
    THEN Induct_on `n`
    THEN RW_TAC arith_ss [Switch_def,Lustre_not_def,Lustre_false_def,Lustre_pre_def,
                          Lustre_if_then_else_def,Lustre_init_stream_def]);

val SwitchUniqueImp =
 prove
  (``!s on off. (s = if (false -> pre s) then not off else on) ==> (s = Switch (on,off))``,
    REPEAT GEN_TAC
     THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
     THEN REWRITE_TAC[Switch_def,Lustre_not_def,Lustre_false_def,
                      Lustre_pre_def,Lustre_if_then_else_def,Lustre_init_stream_def]
     THEN DISCH_TAC
     THEN Induct
     THEN ONCE_ASM_REWRITE_TAC[]
     THEN REWRITE_TAC[Switch_def,Lustre_not_def,Lustre_false_def, Lustre_pre_def,
                      Lustre_if_then_else_def,Lustre_init_stream_def,
                      DECIDE``~(SUC n = 0) /\ (SUC n - 1 = n)``]
     THEN POP_ASSUM(fn th => REWRITE_TAC[th]));

val SwitchUnique =
 prove
  (``!s on off. (s = if (false -> pre s) then not off else on) = (s = Switch (on,off))``,
   METIS_TAC[SwitchUniqueImp, SwitchEq]);

val Switch =
 prove
  (``Switch (on,off) =
     returns s.
      (s = if (false -> pre s) then not off else on)``,
   METIS_TAC[SwitchUnique]);

(*---------------------------------------------------------------------------*)
(* Counter                                                                   *)
(*---------------------------------------------------------------------------*)

val Count_def =
 Define
  `(Count (reset,x) 0 =
     if reset 0 then 0 else if x 0 then 1 else 0)
   /\
   (Count (reset,x) (SUC t) =
     if reset(SUC t)
      then 0 else
     if x(SUC t) then Count (reset,x) t + 1 else Count (reset,x) t)`;

val CountEq =
 prove
  (``Count (reset,x) =
      if reset  then
       (const 0)
      else
       if x then
         ((const 0 -> pre(Count(reset,x))) + const 1)
       else
         (const 0 -> pre(Count(reset,x)))``,
   CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
    THEN SIMP_TAC arith_ss [Lustre_not_def,Lustre_false_def,Lustre_pre_def,
          Lustre_if_then_else_def,Lustre_const_def,Lustre_init_stream_def,Lustre_add_def]
    THEN Induct_on `n`
    THEN RW_TAC arith_ss [Count_def,Lustre_not_def,Lustre_false_def,
			  Lustre_pre_def,Lustre_if_then_else_def,Lustre_init_stream_def]);

val CountUniqueImp =
 prove
  (``!c reset x.
      (c = if reset then const 0
            else if x then (const 0 -> pre c) + const 1
            else (const 0 -> pre c))
      ==>
      (c = Count (reset,x))``,
    REPEAT GEN_TAC
     THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
     THEN REWRITE_TAC[Count_def,Lustre_not_def,Lustre_false_def,Lustre_pre_def,
          Lustre_if_then_else_def,Lustre_init_stream_def,Lustre_const_def,Lustre_add_def]
     THEN DISCH_TAC
     THEN Induct
     THEN ONCE_ASM_REWRITE_TAC[]
     THEN REWRITE_TAC[Count_def,Lustre_not_def,Lustre_false_def,Lustre_pre_def,
                      Lustre_if_then_else_def,Lustre_init_stream_def,
                      DECIDE``~(SUC n = 0) /\ (SUC n - 1 = n)``]
     THEN EVAL_TAC
     THEN POP_ASSUM(fn th => REWRITE_TAC[th]));

val CountUnique =
 prove
  (``!c reset x.
      (c = if reset then const 0
            else if x then (const 0 -> pre c) + const 1
            else (const 0 -> pre c))
      =
      (c = Count (reset,x))``,
   METIS_TAC[CountUniqueImp, CountEq]);

val Count =
 prove
  (``Count (reset,x) =
     returns c.
      (c = if reset then const 0
            else if x then (const 0 -> pre c) + const 1
            else (const 0 -> pre c))``,
   METIS_TAC[CountUnique]);

*)