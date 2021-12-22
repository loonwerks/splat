open HolKernel Parse boolLib bossLib BasicProvers
     optionTheory listTheory;

(*---------------------------------------------------------------------------*)
(* Rename some common proof functions                                        *)
(*---------------------------------------------------------------------------*)

val _ = overload_on ("++", ``list$APPEND``);

infix byA;
val op byA = BasicProvers.byA;

val decide = bossLib.DECIDE;
val qdecide = decide o Parse.Term;

val sym = SYM;
val subst_all_tac = SUBST_ALL_TAC;
val popk_tac = pop_assum kall_tac;
val pop_subst_tac = pop_assum subst_all_tac;
val pop_sym_subst_tac = pop_assum (subst_all_tac o sym);
val qpat_k_assum = C qpat_x_assum kall_tac;
val var_eq_tac = rpt BasicProvers.VAR_EQ_TAC;

fun qspec q th = th |> Q.SPEC q
fun qspec_arith q th = qspec q th |> SIMP_RULE arith_ss [];

val _ = new_theory "concatPartial";

(*---------------------------------------------------------------------------*)
(* Definition of a concatenation function                                    *)
(*                                                                           *)
(*    concatPartial : 'a option list -> 'a list option                       *)
(*                                                                           *)
(* The final definition could be made directly, but we proceed by making an  *)
(* iterative version that is more computationally efficient.                 *)
(*---------------------------------------------------------------------------*)

Definition concatPartial_acc_def :
  concatPartial_acc [] acc = SOME acc /\
  concatPartial_acc (NONE::t) acc = NONE /\
  concatPartial_acc (SOME x::t) acc = concatPartial_acc t (x::acc)
End

Definition concatPartial_def :
  concatPartial optlist =
    case concatPartial_acc optlist []
     of NONE => NONE
      | SOME list => SOME (FLAT (REVERSE list))
End

Theorem concatPartial_acc_NONE :
 !optlist acc list.
  (concatPartial_acc optlist acc = NONE)
   <=>
  EXISTS (\x. x=NONE) optlist
Proof
recInduct concatPartial_acc_ind
 >> rw[]
 >> full_simp_tac list_ss [concatPartial_acc_def]
QED

Theorem concatPartial_acc_SOME :
 !optlist acc list.
  (concatPartial_acc optlist acc = SOME list)
   <=>
  EVERY IS_SOME optlist ∧
  (list = REVERSE (MAP THE optlist) ++ acc)
Proof
recInduct concatPartial_acc_ind
 >> rw[]
 >> full_simp_tac list_ss [concatPartial_acc_def]
 >> metis_tac []
QED

Theorem concatPartial_NONE :
 !optlist.
  (concatPartial optlist = NONE)
   =
  EXISTS (\x. x=NONE) optlist
Proof
  simp_tac list_ss [concatPartial_def,option_case_eq]
   >> metis_tac[concatPartial_acc_NONE]
QED

Theorem concatPartial_SOME :
 !optlist list.
  (concatPartial optlist = SOME list)
  <=>
  EVERY IS_SOME optlist ∧
  (list = FLAT (MAP THE optlist))
Proof
  rw_tac list_ss [concatPartial_def,option_case_eq,concatPartial_acc_SOME]
  >> metis_tac[]
QED

Triviality IS_SOME_NEG :
 IS_SOME = \x. ~(x=NONE)
Proof
  rw [FUN_EQ_THM] >> metis_tac [NOT_IS_SOME_EQ_NONE]
QED

Theorem concatPartial_thm :
 concatPartial optlist =
    if EXISTS (\x. x=NONE) optlist
       then NONE
    else SOME (FLAT (MAP THE optlist))
Proof
 rw[concatPartial_NONE,concatPartial_SOME]
 >> fs [NOT_EXISTS,combinTheory.o_DEF,IS_SOME_NEG]
QED

Theorem concatPartial_nil :
 concatPartial [] = SOME []
Proof
 EVAL_TAC
QED

val _ = export_theory();
