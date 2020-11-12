(*===========================================================================*)
(* Definition of Lustre as a shallow embedding.                              *)
(* Author: Mike Gordon (mjcg@cl.cam.ac.uk)                                   *)
(* Tweaks: Konrad Slind (klslind@rockwellcollins.com)                        *)
(*                                                                           *)
(* Used to define past-time LTL operators and proof their properties.        *)
(*===========================================================================*)

open HolKernel boolLib Parse bossLib pairLib
     pairTheory numTheory prim_recTheory arithmeticTheory
     combinTheory pred_setTheory pred_setLib;

val _ = new_theory "Past_Time";

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

val _ = set_fixity "->"  (Infix(NONASSOC,90));
val _ = set_fixity "not" (Prefix 900);
val _ = set_fixity "and" (Infixr 399);
val _ = set_fixity "or"  (Infixr 299);
val _ = set_fixity "=="  (Infixl 99);

(*---------------------------------------------------------------------------*)
(* Support for Lustre-like syntax.                                           *)
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
(* Past-time temporal logic                                                  *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* node Yesterday(i: bool) returns (o: bool);                                *)
(* 	let                                                                  *)
(*		o = false -> pre(i);                                         *)
(*	tel;                                                                 *)
(*                                                                           *)
(* node Zyesterday(i: bool) returns (o: bool);                               *)
(* 	let                                                                  *)
(*		o = true -> pre(i);                                          *)
(*	tel;                                                                 *)
(*---------------------------------------------------------------------------*)

val Yesterday_def =
 Lustre_Def
  “Yesterday A = returns Out. Out = (const F -> pre A)”;

val Zyesterday_def =
 Lustre_Def
   “Zyesterday A = returns Out. Out = (const T -> pre A)”;

Theorem Yesterday_thm :
  ∀P t. Yesterday P t = if t = 0n then F else P (t-1)
Proof
 rw_tac lustre_ss [Yesterday_def]
QED

Theorem Zyesterday_thm :
  ∀P t. Zyesterday P t = if t = 0n then T else P (t-1)
Proof
 rw_tac lustre_ss [Zyesterday_def]
QED

Theorem DeMorgan_Yesterdays :
 !X. Yesterday X = not (Zyesterday(not X))
Proof
 rw_tac lustre_ss [Yesterday_def, Zyesterday_def]
QED

(*---------------------------------------------------------------------------*)
(* node Historically(i: bool) returns (o: bool);                             *)
(* let                                                                       *)
(*  -- some candidates                                                       *)
(*	o = i and (true -> pre(o));                                          *)
(*	o = true -> i and pre(o));                                           *)
(*	o = i -> i and pre(o));                                              *)
(*	o = i and Zyesterday (o);                                            *)
(* tel;                                                                      *)
(*---------------------------------------------------------------------------*)

val Historically_def =
 Lustre_Def
   “Historically A = returns H. H = (A -> A and pre H)”;

(*---------------------------------------------------------------------------*)
(* Something subtle that plagues me: it is important to draw the distinction *)
(* between *time* and *steps in the computation*, (or "thread invocations"). *)
(* A memory-based stream needs to be given an initial value at time t=0,     *)
(* while the first read of input streams happens at t=1. Thus input streams  *)
(* are shifted by one. For example, at t=1, P(0) is accessed. Thus           *)
(*                                                                           *)
(*   Historically P t = P(0) and ... and P(t-1)                              *)
(*                                                                           *)
(* One might instead think that                                              *)
(*                                                                           *)
(*   Historically P t <=> !n. n <= t ==> P n,                                *)
(*                                                                           *)
(* but that would mean that P would hold for t+1 invocations, which is one   *)
(* step in the future.                                                       *)
(*---------------------------------------------------------------------------*)


Triviality leq_suc = DECIDE “a ≤ SUC b ⇔ a≤ b ∨ a = SUC b”;
Triviality leq_zero = DECIDE “a ≤ 0 ⇔ a = 0”;


Theorem Historically_thm :
 ∀t. Historically P t ⇔ ∀n. n ≤ t ⇒ P n
Proof
 rw_tac lustre_ss [Historically_def]
 >> SELECT_ELIM_TAC
 >> conj_tac
 >- (qexists_tac ‘\i. ∀j. j ≤ i ⇒ P j’
      >> Induct
      >> rw [EQ_IMP_THM]
      >> metis_tac[leq_suc])
 >- (rpt strip_tac
      >> Induct_on ‘t’
      >> ONCE_ASM_REWRITE_TAC[]
      >> REWRITE_TAC [leq_zero,NOT_SUC,SUC_SUB1]
      >> metis_tac [leq_zero,leq_suc])
QED

(*---------------------------------------------------------------------------*)
(* node Once (i: bool) returns (o: bool);                                    *)
(* let                                                                       *)
(*	o = i or (false -> pre(o));                                          *)
(*	o = false ->  pre(i or o);                                          *)
(* tel;                                                                      *)
(*---------------------------------------------------------------------------*)

val Once_def =
 Lustre_Def
  “Once A = returns H. H = (A -> A or pre H)”;

Theorem Once_thm :
 ∀t. Once P t ⇔ ∃n. n ≤ t ∧ P n
Proof
 rw_tac lustre_ss [Once_def]
 >> SELECT_ELIM_TAC
 >> conj_tac
 >- (qexists_tac ‘\i. ∃j. j ≤ i ∧ P j’
      >> Induct
      >> rw [EQ_IMP_THM]
      >> metis_tac [leq_suc])
 >- (rpt strip_tac
      >> Induct_on ‘t’
      >> ONCE_ASM_REWRITE_TAC[]
      >> REWRITE_TAC [leq_zero,NOT_SUC,SUC_SUB1]
      >> metis_tac [leq_suc])
QED

(*---------------------------------------------------------------------------*)
(* node Since (a: bool, b:bool) returns (o: bool);                           *)
(* let                                                                       *)
(*	o = b or (a and (false -> pre(o)));                                  *)
(* tel;                                                                      *)
(*                                                                           *)
(* The intuition is that there is a time where b is high and in the next     *)
(* step a sequence of a's goes all the way to the end of the trace. As a     *)
(* regexp it would be .*ba*                                                  *)
(*---------------------------------------------------------------------------*)

val Since_def =
 Lustre_Def
   “Since A B = returns S.
     var X.
       (S = (B or (A and X))) ∧
       (X = (const F -> pre S))”;

(*---------------------------------------------------------------------------*)
(* Recursive function modelling Since                                        *)
(*---------------------------------------------------------------------------*)

Definition Since_Rec_def :
  (Since_Rec A B 0 ⇔ B 0) ∧
  (Since_Rec A B (SUC n) ⇔ B n ∨ (A n ∧ Since_Rec A B n))
End

(*---------------------------------------------------------------------------*)
(* Recall that P and Q are being looked at strictly below t                  *)
(*---------------------------------------------------------------------------*)

Theorem Since_lr :
 ∀P Q t. Since P Q t ⇒ ∃i. i < t ∧ Q i ∧ ∀j. i < j ∧ j < t ⇒ P j
Proof
simp_tac lustre_ss [Since_def]
 >> rpt gen_tac
 >> SELECT_ELIM_TAC
 >> conj_tac
 >- (qexists_tac ‘Since_Rec P Q’
     >> Induct >> rw [Since_Rec_def,EQ_IMP_THM])
 >- (rpt strip_tac
      >> Induct_on ‘t’
      >> ONCE_ASM_REWRITE_TAC[]
      >> REWRITE_TAC [NOT_LESS_0,NOT_SUC,SUC_SUB1]
      >> rpt strip_tac
      >- (WEAKEN_TAC is_forall >> qexists_tac ‘t’ >> simp[])
      >- (fs []
          >> qexists_tac ‘i’
          >> qpat_x_assum ‘∀a. p ⇔ q’ kall_tac
          >> rw []
          >> metis_tac [DECIDE “a < SUC b ⇔ a<b ∨ a = b”]))
QED

Theorem Since_rl :
 ∀P Q t i. i < t ∧ Q i ∧ (∀j. i < j ∧ j < t ⇒ P j) ⇒ Since P Q t
Proof
rw_tac lustre_ss [Since_def]
 >> SELECT_ELIM_TAC
 >> conj_tac
 >- (qexists_tac ‘Since_Rec P Q’
     >> Induct >> rw [Since_Rec_def,EQ_IMP_THM])
 >- (rpt strip_tac
      >> Induct_on ‘t’
      >> ONCE_ASM_REWRITE_TAC[]
      >> REWRITE_TAC [NOT_LESS_0,NOT_SUC,SUC_SUB1]
      >> rpt strip_tac
      >> ‘i < t ∨ i = t’ by decide_tac
      >- fs[]
      >- metis_tac[])
QED

Theorem Since_thm :
 ∀P Q t. Since P Q t ⇔ ∃i. i < t ∧ Q i ∧ ∀j. i < j ∧ j < t ⇒ P j
Proof
 metis_tac [Since_lr,Since_rl]
QED

(*---------------------------------------------------------------------------*)
(* node Weak_Since (a: bool, b:bool) returns (o: bool);                      *)
(* let                                                                       *)
(*	o = b or (a and (true -> pre(o)));                                   *)
(* tel;                                                                      *)
(*                                                                           *)
(* Weak_Since differs from Since by being true if a holds through the entire *)
(* trace. So it looks (in regexp notation) like                              *)
(*                                                                           *)
(*    a* + .*ba*                                                             *)
(*---------------------------------------------------------------------------*)

val Weak_Since_def =
 Lustre_Def
   “Weak_Since P Q = returns S. S = (const T -> pre (Q or (P and S)))”;

(*---------------------------------------------------------------------------*)
(* Recursive definition modelling the Lustre definition                      *)
(*---------------------------------------------------------------------------*)

Definition Weak_Since_Rec_def :
 (Weak_Since_Rec P Q 0 ⇔ T) ∧
 (Weak_Since_Rec P Q (SUC n) ⇔ Q n \/ (P n /\ Weak_Since_Rec P Q n))
End

(*---------------------------------------------------------------------------*)
(* Equation between pLTL expressions                                         *)
(*---------------------------------------------------------------------------*)
(*
Theorem Weak_Since_eqn :
 ∀P Q. Weak_Since P Q = (Historically P or Since P Q)
Proof

QED
*)

(*---------------------------------------------------------------------------*)
(* node Trigger (a: bool, b:bool) returns (o: bool);                         *)
(* let                                                                       *)
(*	o = b and (a or (true -> pre(o)));                                   *)
(* tel;                                                                      *)
(*---------------------------------------------------------------------------*)

val Trigger_def =
 Lustre_Def
   “Trigger P Q = returns S. S = (const T -> pre (Q and (P or S)))”;

Definition Trigger_Rec_def :
 (Trigger_Rec P Q 0 ⇔ T) ∧
 (Trigger_Rec P Q (SUC t) ⇔ Q t ∧ (P t ∨ Trigger_Rec P Q t))
End

(*---------------------------------------------------------------------------*)
(* Needs spec and proof                                                      *)
(*---------------------------------------------------------------------------*)


val _ = export_theory();
