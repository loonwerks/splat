(*===========================================================================*)
(* Working out some ideas for modelling CASE threads in the case of a simple *)
(* "Streaming Max" function.                                                 *)
(*===========================================================================*)

open HolKernel boolLib Parse bossLib pairLib
     pairTheory numTheory prim_recTheory arithmeticTheory
     combinTheory pred_setTheory pred_setLib;

val _ = new_theory "Max";

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

(*---------------------------------------------------------------------------*)
(* Max on a stream (up to a bound)                                           *)
(*---------------------------------------------------------------------------*)

Definition MaxFn_def :
  MaxFn X 0 = X 0 ∧
  MaxFn X (SUC t) = MAX (X (SUC t)) (MaxFn X t)
End

Theorem MaxFn_inhabits :
 ∀t. ∃n. n ≤ t ∧ MaxFn A t = A n
Proof
Induct
  >> rw [MaxFn_def]
  >> rw [MAX_DEF]
  >> metis_tac [DECIDE “x ≤ SUC y ⇔ x ≤ y ∨ x = SUC y”,
      LESS_EQ_TRANS,NOT_LESS,LESS_EQ_REFL,LESS_IMP_LESS_OR_EQ]
QED

Theorem MaxFn_is_max :
  ∀t n. n ≤ t ⇒ A n ≤ MaxFn A t
Proof
Induct
  >> rw [MaxFn_def,MAX_DEF]
  >> metis_tac [DECIDE “x ≤ SUC y ⇔ x ≤ y ∨ x = SUC y”,
      LESS_EQ_TRANS,NOT_LESS,LESS_EQ_REFL,LESS_IMP_LESS_OR_EQ]
QED

(*---------------------------------------------------------------------------*)
(* Note that MaxFn won't work with our CASE thread model, because it uses A  *)
(* at time starting from 0.                                                  *)
(*---------------------------------------------------------------------------*)

val Max_Stream_def =
 Lustre_Def
  “Max_Stream A = returns M:num->num.
      M = (const 0 -> (if pre A >= pre M then pre A else pre M))”;

Theorem Max_Stream_inhabits :
  ∀t. ∃n. n < t ∧ Max_Stream A t = A n
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
