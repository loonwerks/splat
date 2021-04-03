open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib regexpLib ASCIInumbersLib;

open pairTheory arithmeticTheory listTheory rich_listTheory pred_setTheory
     stringTheory combinTheory optionTheory numposrepTheory FormalLangTheory;

open finite_mapTheory bagTheory;  (* For termination of predFn, need to use mlt_list *)

val _ = numLib.prefer_num();
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

val _ = new_theory "abscontig";

(*---------------------------------------------------------------------------*)
(* The types of interest: lvals, arithmetic expressions over lvals, boolean  *)
(* expressions, atomic types, and contiguity types.                          *)
(*---------------------------------------------------------------------------*)

Datatype:
  lval = VarName string
       | RecdProj lval string
       | ArraySub lval exp
  ;
  exp = Loc lval
      | numLit num
      | Add exp exp
End

Datatype:
  bexp = boolLit bool
       | BLoc lval
       | Bnot bexp
       | Bor  bexp bexp
       | Band bexp bexp
       | Beq exp exp
       | Blt exp exp
End

Datatype:
  atom = Bool
       | Char
       | Unsigned num
End

Datatype:
  contig = Basic atom
         | Void
         | Recd ((string # contig) list)
         | Array contig exp
         | Alt bexp contig contig
End

val contig_size_def = fetch "-" "contig_size_def";

(*---------------------------------------------------------------------------*)
(* Expression evaluation. Looking up lvals is partial, which infects evalExp *)
(*---------------------------------------------------------------------------*)

Definition evalExp_def :
 evalExp (lvalMap,valFn) (Loc lval) =
   (case FLOOKUP lvalMap lval
     of SOME s => valFn s
      | NONE => NONE) /\
 evalExp E (numLit n)  = SOME n /\
 evalExp E (Add e1 e2) =
   (case evalExp E e1
     of NONE => NONE
      | SOME n1 =>
    case evalExp E e2
     of NONE => NONE
      | SOME n2 => SOME (n1+n2))

End

(*---------------------------------------------------------------------------*)
(* Boolean expression evaluation. Also partial                               *)
(*---------------------------------------------------------------------------*)

Definition evalBexp_def :
 (evalBexp E (boolLit b) = SOME b) /\
 (evalBexp (lvalMap,valFn) (BLoc lval) =
    case FLOOKUP lvalMap lval
     of NONE => NONE
      | SOME s =>
     case valFn s
      of NONE => NONE
      | SOME n => SOME (~(n = 0n))) /\
 (evalBexp E (Bnot b) =
   case evalBexp E b
     of NONE => NONE
      | SOME bval => SOME (~bval)) /\
 (evalBexp E (Bor b1 b2) =
   case evalBexp E b1
     of NONE => NONE
     |  SOME bv1 =>
    case evalBexp E b2
     of NONE => NONE
      | SOME bv2 => SOME (bv1 \/ bv2)) /\
 (evalBexp E (Band b1 b2) =
   case evalBexp E b1
     of NONE => NONE
      | SOME bv1 =>
    case evalBexp E b2
     of NONE => NONE
      | SOME bv2 => SOME (bv1 /\ bv2)) /\
 (evalBexp E (Beq e1 e2) =
   case evalExp E e1
     of NONE => NONE
      | SOME n1 =>
    case evalExp E e2
     of NONE => NONE
      | SOME n2 => SOME (n1 = n2)) /\
 (evalBexp E (Blt e1 e2) =
   case evalExp E e1
     of NONE => NONE
      | SOME n1 =>
    case evalExp E e2
     of NONE => NONE
      | SOME n2 => SOME (n1 < n2))
End


(*---------------------------------------------------------------------------*)
(* Formal language of a contiguity type. The definition is somewhat non-self-*)
(* contained, i.e., its theta parameter is a map that may lead to partiality.*)
(* But a theta computed by matchFn will be OK. I call this a "double-clutch" *)
(* semantics, since one has to process a string to get theta, then use theta *)
(* in the semantics.                                                         *)
(*---------------------------------------------------------------------------*)

Definition atomWidth_def:
 atomWidth Bool = 1 /\
 atomWidth Char = 1 /\
 atomWidth (Unsigned n) = n
End

val layout_def =  (* LSB with padding to width *)
 Define
  `layout b n width = PAD_RIGHT 0n width (n2l b n)`;

val repFn_def = Define `repFn w n = MAP CHR (layout 256 n w)`;
val valFn_def = Define `valFn s = if s = "" then NONE else SOME (l2n 256 (MAP ORD s))`;

Theorem contig_size_lem:
 !plist p. MEM p plist ==> contig_size (SND p) < contig1_size plist
Proof
 simp_tac list_ss [FORALL_PROD] >> Induct
 >> rw_tac list_ss [contig_size_def]
 >- rw_tac list_ss [contig_size_def]
 >- (‘contig_size p_2 < contig1_size plist’ by metis_tac[] >> decide_tac)
QED

(*---------------------------------------------------------------------------*)
(* Semantics (formal language style)                                         *)
(*---------------------------------------------------------------------------*)

Definition Contig_Lang_def:
  Contig_Lang theta (Basic a) = {s | LENGTH s = atomWidth a} /\
  Contig_Lang theta Void = {} /\
  Contig_Lang theta (Recd fields) =
    {CONCAT slist
      | LIST_REL (\s contig. s IN Contig_Lang theta contig) slist (MAP SND fields)} /\
  Contig_Lang theta (Array c e) =
    (case evalExp (theta,valFn) e
      of NONE => {}
       | SOME n =>
     {CONCAT slist
       | (LENGTH slist = n) /\ EVERY (Contig_Lang theta c) slist}) /\
  Contig_Lang theta (Alt bexp c1 c2) =
    (case evalBexp (theta,valFn) bexp
      of NONE => {}
       | SOME T => Contig_Lang theta c1
       | SOME F => Contig_Lang theta c2)
Termination
  WF_REL_TAC ‘measure (contig_size o SND)’
  >> rw [contig_size_def,MEM_MAP]
  >> imp_res_tac contig_size_lem
  >> decide_tac
End

Theorem IN_Contig_Lang :
  ∀s.
     (s IN Contig_Lang theta (Basic a) ⇔ LENGTH s = atomWidth a) ∧
     (s IN Contig_Lang theta Void ⇔ F) ∧
     (s IN Contig_Lang theta (Recd fields) ⇔
        ∃slist. s = CONCAT slist ∧
                LIST_REL (\s contig. s IN Contig_Lang theta contig) slist (MAP SND fields)) /\
     (s IN Contig_Lang theta (Array c e) ⇔
        ∃slist.
            evalExp (theta,valFn) e = SOME (LENGTH slist) ∧
            s = CONCAT slist ∧
            EVERY (Contig_Lang theta c) slist) ∧
     (s IN Contig_Lang theta (Alt bexp c1 c2) ⇔
         ∃b. evalBexp (theta,valFn) bexp = SOME b ∧
              if b then s IN Contig_Lang theta c1
                   else s IN Contig_Lang theta c2)
Proof
 rw [Contig_Lang_def,EXTENSION]
  >> every_case_tac
  >> rw []
  >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Support definitions                                                       *)
(*---------------------------------------------------------------------------*)

Definition optFirst_def :
  optFirst f [] = NONE /\
  optFirst f (h::t) =
    case f h
     of NONE => optFirst f t
      | SOME x => SOME h
End

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
  simp_tac list_ss [concatPartial_def,option_case_eq] >> metis_tac[concatPartial_acc_NONE]
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
    else SOME (CONCAT (MAP THE optlist))
Proof
 rw[concatPartial_NONE,concatPartial_SOME]
 >> fs [NOT_EXISTS,combinTheory.o_DEF,IS_SOME_NEG]
QED

Theorem concatPartial_nil :
 concatPartial [] = SOME []
Proof
 EVAL_TAC
QED

(*---------------------------------------------------------------------------*)
(* break off a prefix of a string                                            *)
(*---------------------------------------------------------------------------*)

Definition tdrop_def:
 tdrop 0 list acc = SOME (REVERSE acc, list) /\
 tdrop n [] acc = NONE /\
 tdrop (SUC n) (h::t) acc = tdrop n t (h::acc)
End

Theorem tdrop_thm :
 ∀n list acc acc'.
     tdrop n list acc = SOME (acc',suf)
     ⇒ (acc' ++ suf = REVERSE acc ++ list) /\
        (LENGTH acc' = n + LENGTH acc)
Proof
 recInduct tdrop_ind >> rw [tdrop_def] >> metis_tac [LENGTH_REVERSE]
QED

Definition take_drop_def :
  take_drop n list = tdrop n list []
End

Theorem take_drop_thm :
  ∀n list.
      take_drop n list = SOME (pref,suf) ⇒ pref ++ suf = list /\ (n = LENGTH pref)
Proof
  rw_tac list_ss [take_drop_def] >> imp_res_tac tdrop_thm >> fs []
QED


Definition upto_def:
  upto lo hi = if lo > hi then [] else lo::upto (lo+1) hi
Termination
  WF_REL_TAC ‘measure (\(a,b). b+1n - a)’
End

Theorem upto_interval_thm :
  !lo hi. set(upto lo hi) = {n | lo <= n /\ n <= hi}
Proof
 recInduct upto_ind
  >> rw_tac list_ss []
  >> rw_tac list_ss [Once upto_def]
  >> fs[]
  >> rw [pred_setTheory.EXTENSION]
QED

Theorem length_upto :
  !lo hi. lo <= hi ==> LENGTH(upto lo hi) = (hi-lo) + 1
Proof
 recInduct upto_ind
  >> rw_tac list_ss []
  >> rw_tac list_ss [Once upto_def]
  >> fs[]
  >> ‘lo=hi \/ lo+1 <= hi’ by decide_tac
      >- rw[Once upto_def]
      >- fs[]
QED

(*---------------------------------------------------------------------------*)
(* Size of a contig. The system-generated contig_size goes through a lot of  *)
(* other types, including field names, and those shouldn't be counted because*)
(* field name size shouldn't count in the size of the expression.            *)
(*---------------------------------------------------------------------------*)

val _ = DefnBase.add_cong list_size_cong;

Definition csize_def :
  (csize (Basic a)     = 0) /\
  (csize (Recd fields) = 1 + list_size (\(a,c). csize  c) fields) /\
  (csize (Array c dim) = 1 + csize c) /\
  (csize (Alt b c1 c2)   = 1 + csize c1 + csize c2)
Termination
  WF_REL_TAC `measure contig_size`
  >> rw_tac list_ss [contig_size_def]
  >- (Induct_on `fields`
      >> rw_tac list_ss [contig_size_def]
      >> full_simp_tac list_ss [contig_size_def])
End

Triviality list_size_append :
 !L1 L2 f. list_size f (L1 ++ L2) = (list_size f L1 + list_size f L2)
Proof
 Induct_on ‘L1’ >> rw_tac list_ss [list_size_def]
QED

Definition choiceFn_def :
  choiceFn theta valFn bexp =
    case evalBexp (theta,valFn) bexp
     of NONE => F
      | SOME bval => bval
End

Definition indexFn_def :
  indexFn lval c n = (ArraySub lval (numLit n),c)
End

Definition fieldFn_def :
  fieldFn lval (fName,c) = (RecdProj lval fName,c)
End

(*---------------------------------------------------------------------------*)
(* contig-specified predicate on strings.                                    *)
(*---------------------------------------------------------------------------*)

Definition predFn_def :
 predFn (atomWidths,vFn) (worklist,s,theta) =
  case worklist
   of [] => T
    | (lval,Basic a)::t =>
        (case take_drop (atomWidths a) s
           of NONE => F
            | SOME (segment,rst) =>
              predFn (atomWidths,vFn) (t, rst, theta |+ (lval,segment)))
   | (lval,Void)::t => F
   | (lval,Recd fields)::t =>
       predFn (atomWidths,vFn) (MAP (fieldFn lval) fields ++ t,s,theta)
   | (lval,Array c exp)::t =>
       (case evalExp (theta,vFn) exp
         of NONE => F
          | SOME dim =>
            predFn (atomWidths,vFn)
                   (MAP (indexFn lval c) (COUNT_LIST dim) ++ t,s,theta))
   | (lval,Alt bexp c1 c2)::t =>
       case evalBexp (theta,vFn) bexp
        of NONE => F
         | SOME T => predFn (atomWidths,vFn) ((lval,c1)::t,s,theta)
         | SOME F => predFn (atomWidths,vFn) ((lval,c2)::t,s,theta)
Termination
 WF_REL_TAC `inv_image (mlt_list (measure (csize o SND))) (FST o SND)`
   >> rw [APPEND_EQ_SELF]
   >> rw [csize_def]
   >> fs [MEM_MAP,MEM_SPLIT]
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,fieldFn_def])
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,indexFn_def])
End

(*---------------------------------------------------------------------------*)
(* Worklist-based matcher. When it comes to add a new (lval |-> string)      *)
(* element to theta, it first checks that lval is not in FDOM(theta).        *)
(*---------------------------------------------------------------------------*)

Definition matchFn_def :
 matchFn (atomicWidths,vFn) (worklist,s,theta) =
 case worklist
  of [] => SOME (s,theta)
   | (lval,Basic a)::t =>
       (case take_drop (atomicWidths a) s
         of NONE => NONE
          | SOME (segment,rst) =>
        if lval IN FDOM theta then
            NONE
        else matchFn (atomicWidths,vFn) (t, rst, theta |+ (lval,segment)))
   | (lval,Void)::t => NONE
   | (lval,Recd fields)::t =>
        matchFn (atomicWidths,vFn)
                (MAP (fieldFn lval) fields ++ t,s,theta)
   | (lval,Array c exp)::t =>
       (case evalExp (theta,vFn) exp
         of NONE => NONE
          | SOME dim =>
             matchFn (atomicWidths,vFn)
                     (MAP (indexFn lval c) (COUNT_LIST dim) ++ t,s,theta))
   | (lval,Alt bexp c1 c2)::t =>
       case evalBexp (theta,vFn) bexp
        of NONE => NONE
         | SOME T => matchFn (atomicWidths,vFn) ((lval,c1)::t,s,theta)
         | SOME F => matchFn (atomicWidths,vFn) ((lval,c2)::t,s,theta)
Termination
 WF_REL_TAC `inv_image (mlt_list (measure (csize o SND))) (FST o SND)`
   >> rw [APPEND_EQ_SELF]
   >> rw [csize_def]
   >> fs [MEM_MAP,MEM_SPLIT]
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,fieldFn_def])
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,indexFn_def])
End


(*---------------------------------------------------------------------------*)
(* Apply a substitution to a contig. And to a worklist.                      *)
(*---------------------------------------------------------------------------*)

Definition substFn_def :
 substFn vFn theta (lval,contig) =
  case contig
   of Basic _ => FLOOKUP theta lval
    | Void  => NONE
    | Recd fields =>
       concatPartial
         (MAP (\(fName,c). substFn vFn theta (RecdProj lval fName,c)) fields)
    | Array c exp =>
       (case evalExp (theta,vFn) exp
         of NONE => NONE
          | SOME dim =>
            concatPartial
               (MAP (\i. substFn vFn theta (ArraySub lval (numLit i), c))
                    (COUNT_LIST dim)))
    | Alt bexp c1 c2 =>
       (case evalBexp (theta,vFn) bexp
         of NONE => NONE
          | SOME T => substFn vFn theta (lval,c1)
          | SOME F => substFn vFn theta (lval,c2))
Termination
 WF_REL_TAC `measure (csize o SND o SND o SND)`
   >> rw [csize_def]
   >- (Induct_on `fields`  >> rw[list_size_def] >> rw[] >> fs[])
End

Definition substWk_def :
 substWk vFn theta wklist = concatPartial (MAP (substFn vFn theta) wklist)
End

Theorem match_submap :
  !atomicWidths vFn wklist s theta s2 theta'.
   matchFn (atomicWidths,vFn) (wklist,s,theta) = SOME (s2, theta')
   ==>
   finite_map$SUBMAP theta theta'
Proof
 recInduct matchFn_ind >>
 rpt gen_tac >> strip_tac >>
 rw_tac list_ss [Once matchFn_def] >>
 every_case_tac
  >> rw[]
  >> fs [SUBMAP_FUPDATE]
  >> rfs[]
  >> rw[]
  >> metis_tac [SUBMAP_DOMSUB_gen,DOMSUB_NOT_IN_DOM]
QED

Theorem evalExp_submap :
 ∀e vFn theta1 theta2 v.
   theta1 SUBMAP theta2 ∧
   evalExp(theta1,vFn) e = SOME v
   ⇒
   evalExp(theta2,vFn) e = SOME v
Proof
Induct
 >> rw [evalExp_def]
 >> every_case_tac >> fs []
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11]
QED

Theorem evalBexp_submap :
 ∀bexp vFn theta1 theta2 v.
   theta1 SUBMAP theta2 ∧
   evalBexp(theta1,vFn) bexp = SOME v
   ⇒
   evalBexp(theta2,vFn) bexp = SOME v
Proof
Induct
 >> rw [evalBexp_def]
 >> every_case_tac
 >> fs []
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11,evalExp_submap]
QED

Theorem match_lem :
!atomicWidths vFn wklist (s:string) theta s2 theta'.
   matchFn (atomicWidths,vFn) (wklist,s,theta) = SOME (s2, theta')
   ==>
   ?s1. substWk vFn theta' wklist = SOME s1 /\  s1 ++ s2 = s
Proof
 simp_tac list_ss [substWk_def]
 >> recInduct matchFn_ind
 >> rpt gen_tac
 >> strip_tac
 >> rw_tac list_ss [Once matchFn_def]
 >> every_case_tac
 >> rw[] >> fs[] >> rfs[] >> rw []
   >- rw[concatPartial_thm]
   >- (rw[Once substFn_def]
       >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,fieldFn_def,LAMBDA_PROD,IS_SOME_NEG]
       >> rw []
       >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
       >> metis_tac [NOT_EXISTS])
   >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
       >> ‘evalExp (theta',vFn) e = SOME x’ by metis_tac [evalExp_submap]
       >> rw[Once substFn_def]
       >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,indexFn_def,LAMBDA_PROD,IS_SOME_NEG]
       >> rw []
       >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
       >> metis_tac [NOT_EXISTS])
   >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
       >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
       >> rw[]
       >> ‘evalBexp (theta',vFn) b = SOME T’ by metis_tac [evalBexp_submap]
       >> rw[Once substFn_def]
       >> every_case_tac
       >> rw [])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
        >> rw[]
        >> ‘evalBexp (theta',vFn) b = SOME F’ by metis_tac [evalBexp_submap]
        >> rw[Once substFn_def]
        >> every_case_tac
        >> rw [])
    >- (qexists_tac ‘q' ++ s1’
        >> ‘s = STRCAT q' (STRCAT s1 s2)’ by metis_tac [take_drop_thm]
        >> rw []
        >> rw [Once substFn_def]
        >> ‘(theta |+ (q,q')) SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘FLOOKUP (theta |+ (q,q')) q = SOME q'’ by metis_tac [FLOOKUP_UPDATE]
        >> ‘FLOOKUP theta' q = SOME q'’ by metis_tac [FLOOKUP_SUBMAP]
        >> rw[]
        >> fs [concatPartial_thm])
    >- (rw[Once substFn_def]
        >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,fieldFn_def,LAMBDA_PROD,IS_SOME_NEG]
        >> rw []
        >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
        >> metis_tac [NOT_EXISTS])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap] >>
        ‘evalExp (theta',vFn) e = SOME x’ by metis_tac [evalExp_submap]
        >> rw[Once substFn_def]
        >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,indexFn_def,LAMBDA_PROD,IS_SOME_NEG]
        >> rw []
        >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
        >> metis_tac [NOT_EXISTS])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
        >> rw[]
        >> ‘evalBexp (theta',vFn) b = SOME T’ by metis_tac [evalBexp_submap]
        >> rw[Once substFn_def]
        >> every_case_tac
        >> rw [])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
        >> rw[]
        >> ‘evalBexp (theta',vFn) b = SOME F’ by metis_tac [evalBexp_submap]
        >> rw[Once substFn_def]
        >> every_case_tac
        >> rw [])
QED

Theorem match_subst_thm :
!atomicWidths vFn wklist (s:string) theta s2 theta'.
   matchFn (atomicWidths,vFn) (wklist,s,theta) = SOME (s2, theta')
   ==>
     THE (substWk vFn theta' wklist) ++ s2 = s
Proof
 metis_tac [match_lem,optionTheory.THE_DEF]
QED

val n2l_256 = save_thm
("n2l_256",
 n2l_def
  |> Q.SPECL [`n`,`256`]
  |> SIMP_RULE arith_ss []
  |> Q.GEN `n`
);

Theorem ORD_EQ :
 !c n. (ORD c = n) <=> ((CHR n = c) /\ n < 256)
Proof
  metis_tac [CHR_ORD,ORD_CHR_RWT,ORD_BOUND]
QED

Theorem ord_mod_256 :
 !c. ORD c MOD 256 = ORD c
Proof
 rw_tac arith_ss [ORD_BOUND]
QED

Theorem valFn_char :
  !c. valFn [c] = SOME (ORD c)
Proof
 rw_tac list_ss [valFn_def,l2n_def,ord_mod_256]
QED

Theorem valFn_rec :
  valFn [] = NONE /\
  valFn [c] = SOME (ORD c) /\
  valFn (c1::c2::t) = SOME (ORD c1 + 256 * THE (valFn (c2::t)))
Proof
  rw_tac list_ss [valFn_def,l2n_def,ORD_BOUND]
QED

Theorem valFn_bound :
  !s. s <> "" ==> (THE (valFn s) < 256 ** (STRLEN s))
Proof
simp_tac std_ss [valFn_def]
  >> Induct
  >> rw_tac list_ss [l2n_def,ord_mod_256,EXP]
  >> `ORD h < 256` by metis_tac [ORD_BOUND]
  >> Cases_on ‘s=""’
     >- rw[]
     >- (res_tac >> decide_tac)
QED

Definition arb_label_recd_def:
  arb_label_recd clist = Recd (MAP (\c. (ARB, c)) clist)
End

Theorem field_names_ignored:
  ∀plist1 plist2 theta.
     (MAP SND plist1 = MAP SND plist2)
    ⇒
    Contig_Lang theta (Recd plist1) = Contig_Lang theta (Recd plist2)
Proof
  fs [Contig_Lang_def]
QED

Triviality map_snd_fieldFn :
∀plist x. MAP SND (MAP (fieldFn x) plist) = MAP SND plist
Proof
  Induct >> fs [fieldFn_def,FORALL_PROD]
QED

Triviality snd_indexFn :
 !n q c. (SND o indexFn q c) n = c
Proof
 rw[combinTheory.o_DEF, indexFn_def]
QED

Triviality map_snd_indexFn :
∀n q c. MAP SND (MAP (indexFn q c) (COUNT_LIST n)) = REPLICATE n c
Proof
  fs [MAP_MAP_o,MAP_COUNT_LIST,REPLICATE_GENLIST,GENLIST_FUN_EQ,snd_indexFn]
QED

Theorem every_list_rel_replicate :
  !list a R.
    EVERY (R a) list <=> LIST_REL (\x y. R y x)  list (REPLICATE (LENGTH list) a)
Proof
 Induct >> rw[]
QED

Triviality map_snd_lem :
∀list x. MAP SND (MAP (\c. (x,c)) list) = list
Proof
  Induct >> fs []
QED

Theorem Recd_flatA :
 ∀s plist1 plist2 theta fName.
   s IN Contig_Lang theta (Recd ((fName,Recd plist1)::plist2)) ==>
   s IN Contig_Lang theta (Recd (plist1 ++ plist2))
Proof
 rw [Contig_Lang_def]
 >> qexists_tac ‘slist' ++ xs’
 >> rw[] >> metis_tac [LIST_REL_APPEND_suff]
QED

Theorem Recd_flatB :
 ∀s fields1 fields2 theta fName.
    s IN Contig_Lang theta (Recd (fields1 ++ fields2))
    ==>
    s IN Contig_Lang theta (Recd ((fName,Recd fields1)::fields2))
Proof
 rw [Contig_Lang_def]
 >> fs [LIST_REL_SPLIT2]
 >> rw[PULL_EXISTS]
 >> metis_tac []
QED

Theorem Recd_flat :
 ∀s plist1 plist2 theta fName.
   s IN Contig_Lang theta (Recd ((fName,Recd plist1)::plist2)) <=>
   s IN Contig_Lang theta (Recd (plist1 ++ plist2))
Proof
  metis_tac [Recd_flatA,Recd_flatB]
QED

Theorem Recd_Array_flat :
 ∀s e n c clist theta.
  evalExp (theta,valFn) e = SOME n
   ==>
   (s IN Contig_Lang theta (arb_label_recd (Array c e::clist))
    <=>
    s IN Contig_Lang theta (arb_label_recd (REPLICATE n c ⧺ clist)))
Proof
 rw[IN_Contig_Lang,arb_label_recd_def,EQ_IMP_THM,PULL_EXISTS]
 >- (qexists_tac ‘slist' ++ xs’
     >> fs[map_snd_lem]
     >> match_mp_tac LIST_REL_APPEND_suff
     >> rw[]
     >> imp_res_tac every_list_rel_replicate
     >> fs [IN_DEF])
 >- (fs[map_snd_lem,LIST_REL_SPLIT2]
     >> rw[]
     >> qexists_tac ‘ys2’
     >> qexists_tac ‘ys1’
     >> rw[]
     >- metis_tac [LENGTH_REPLICATE,LIST_REL_LENGTH]
     >- (rw[every_list_rel_replicate]
         >> ‘LENGTH ys1 = LENGTH (REPLICATE n c)’ by metis_tac [LIST_REL_LENGTH]
         >> fs [LENGTH_REPLICATE,IN_DEF]))
QED

Theorem Recd_Alt_flatA :
 ∀s b c1 c2 clist theta.
  evalBexp (theta,valFn) b = SOME T
   ==>
   (s IN Contig_Lang theta (arb_label_recd (Alt b c1 c2::clist))
    <=>
    s IN Contig_Lang theta (arb_label_recd (c1::clist)))
Proof
 rw[IN_Contig_Lang,arb_label_recd_def,EQ_IMP_THM,PULL_EXISTS]
QED

Theorem Recd_Alt_flatB :
 ∀s b c1 c2 clist theta.
  evalBexp (theta,valFn) b = SOME F
   ==>
   (s IN Contig_Lang theta (arb_label_recd (Alt b c1 c2::clist))
    <=>
    s IN Contig_Lang theta (arb_label_recd (c2::clist)))
Proof
 rw[IN_Contig_Lang,arb_label_recd_def,EQ_IMP_THM,PULL_EXISTS]
QED

Theorem matchFn_wklist_sound :
 !widths vFn wklist s fmap suffix theta.
   (widths = atomWidth) ∧ (vFn = valFn)
    ==>
   matchFn (widths,vFn) (wklist,s,fmap) = SOME (suffix, theta)
    ==>
   ∃prefix. (s = prefix ++ suffix) ∧ prefix IN Contig_Lang theta (arb_label_recd (MAP SND wklist))
Proof
 recInduct matchFn_ind
  >> simp_tac list_ss []
  >> rpt gen_tac
  >> strip_tac
  >> simp_tac list_ss [Once matchFn_def]
  >> every_case_tac
  >> rw[] >> fs[] >> rfs[] >> rw []
    >- rw [IN_Contig_Lang,arb_label_recd_def]
    >- (fs[map_snd_fieldFn]
        >> ‘Contig_Lang theta' (arb_label_recd (MAP SND l ⧺ MAP SND t)) =
            Contig_Lang theta' (arb_label_recd (Recd l::MAP SND t))’
            by (rw [arb_label_recd_def,Recd_flat,EXTENSION]
                  >> AP_TERM_TAC
                  >> match_mp_tac field_names_ignored
                  >> rw[map_snd_lem])
        >> metis_tac[])
    >- (fs[map_snd_indexFn]
        >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘evalExp (theta',valFn) e = SOME x’ by metis_tac [evalExp_submap]
        >> ‘Contig_Lang theta' (arb_label_recd (Array c e::MAP SND t)) =
            Contig_Lang theta' (arb_label_recd (REPLICATE x c ⧺ MAP SND t))’
           by rw [EXTENSION,GSYM Recd_Array_flat]
        >> metis_tac [map_snd_indexFn])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘evalBexp (theta',valFn) b = SOME T’ by metis_tac [evalBexp_submap]
        >> rw [Recd_Alt_flatA])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘evalBexp (theta',valFn) b = SOME F’ by metis_tac [evalBexp_submap]
        >> rw [Recd_Alt_flatB])
    >- (qexists_tac ‘q' ++ prefix’
        >> rw [IN_Contig_Lang,arb_label_recd_def,PULL_EXISTS]
           >- (imp_res_tac take_drop_thm >> fs [])
           >- (imp_res_tac take_drop_thm
                >> fs [IN_Contig_Lang,arb_label_recd_def,PULL_EXISTS,map_snd_lem]
                >> rw[]
                >> metis_tac[]))
    >- (fs[map_snd_fieldFn]
        >> ‘Contig_Lang theta' (arb_label_recd (MAP SND l ⧺ MAP SND t)) =
            Contig_Lang theta' (arb_label_recd (Recd l::MAP SND t))’
            by (rw [arb_label_recd_def,Recd_flat,EXTENSION]
                  >> AP_TERM_TAC
                  >> match_mp_tac field_names_ignored
                  >> rw[map_snd_lem])
        >> metis_tac[])
    >- (fs[map_snd_indexFn]
        >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘evalExp (theta',valFn) e = SOME x’ by metis_tac [evalExp_submap]
        >> ‘Contig_Lang theta' (arb_label_recd (Array c e::MAP SND t)) =
            Contig_Lang theta' (arb_label_recd (REPLICATE x c ⧺ MAP SND t))’
           by rw [EXTENSION,GSYM Recd_Array_flat]
        >> pop_assum SUBST_ALL_TAC
        >> metis_tac [map_snd_indexFn])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘evalBexp (theta',valFn) b = SOME T’ by metis_tac [evalBexp_submap]
        >> rw [Recd_Alt_flatA])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘evalBexp (theta',valFn) b = SOME F’ by metis_tac [evalBexp_submap]
        >> rw [Recd_Alt_flatB])
QED

Theorem Contig_Degenerate_Recd :
 !s theta contig fName.
     s IN Contig_Lang theta (Recd [(fName,contig)])
      <=>
     s IN Contig_Lang theta contig
Proof
 rw [IN_Contig_Lang,PULL_EXISTS]
QED

Theorem matchFn_sound :
 !contig s theta.
   matchFn (atomWidth,valFn) ([(VarName"root",contig)],s,FEMPTY) = SOME ("", theta)
    ==>
   s IN Contig_Lang theta contig
Proof
  rw[]
  >> imp_res_tac (matchFn_wklist_sound |> SIMP_RULE std_ss [])
  >> rw []
  >> fs [arb_label_recd_def,Contig_Degenerate_Recd]
QED


val _ = export_theory();


(*
(*---------------------------------------------------------------------------*)
(* Invertibility for valFn/repFn                                             *)
(*---------------------------------------------------------------------------*)

val MAP_ORD_CHR = Q.prove
(`!list. EVERY ($> 256) list ==> (MAP (ORD o CHR) list = list)`,
 Induct >> rw_tac list_ss [ORD_CHR_RWT]);

val l2n_append_zeros = Q.prove
(`!n list. l2n 256 (list ++ GENLIST (K 0) n) = l2n 256 list`,
Induct
 >> rw_tac list_ss [GENLIST]
 >> metis_tac [APPEND_SNOC, qspec_arith `256` l2n_SNOC_0]);

val valFn_repFn = Q.store_thm
("valFn_repFn",
 `!n w. valFn (repFn w n) = n`,
 rw_tac list_ss [repFn_def, valFn_def,layout_def,MAP_MAP_o,
    PAD_RIGHT,n2l_BOUND,EVERY_GENLIST,MAP_ORD_CHR,l2n_append_zeros,l2n_n2l]);

Theorem REPLICATE_EQ_SELF :
 !L x. REPLICATE (LENGTH L) x = L <=> EVERY ($= x) L
Proof
 Induct >> rw_tac list_ss [REPLICATE]
QED

Theorem LAST_ADD_ELT :
 !P h L. ~(L=[]) ==> LAST L = LAST (h::L)
Proof
ntac 2 gen_tac
 >> Induct
 >> rw_tac list_ss []
QED

Theorem list_constant_suffix :
 !x L. ?l1 l2. L = l1 ++ l2 /\ EVERY ($= x) l2 /\ (l1 = [] \/ (~(l1=[]) /\ ~(LAST l1 = x)))
Proof
 gen_tac
   >> Induct
   >> rw_tac list_ss []
   >> Cases_on `h=x`
   >> rw_tac list_ss []
   >- (qexists_tac `[]` >> qexists_tac `h::l2` >> rw_tac list_ss [])
   >- (qexists_tac `[h]` >> qexists_tac `l2` >> rw_tac list_ss [])
   >- (qexists_tac `h::l1` >> qexists_tac `l2` >> rw_tac list_ss []
        >> metis_tac [LAST_ADD_ELT])
   >- (qexists_tac `h::l1` >> qexists_tac `l2` >> rw_tac list_ss []
        >> metis_tac [LAST_ADD_ELT])
QED

val split_zero_pad =
 list_constant_suffix
   |> Q.ISPEC `0n`
   |> Q.ISPEC `MAP ORD s`

Theorem repFn_valFn :
 !s. 0 < STRLEN s ==> repFn (STRLEN s) (valFn s) = s
Proof
rw_tac list_ss [repFn_def, valFn_def,layout_def]
 >> `1 < 256` by EVAL_TAC
 >> `EVERY ($> 256) (MAP ORD s)`
     by (rw_tac list_ss [EVERY_MAP, SIMP_RULE std_ss [GSYM GREATER_DEF] ORD_BOUND])
 >> rw_tac splat_ss [n2l_l2n,l2n_eq_0,EVERY_MAP,o_DEF, C_DEF]
 >- (rw_tac splat_ss [PAD_RIGHT,GSYM REPLICATE_GENLIST,map_replicate,GSYM REPLICATE]
     >> `SUC(STRLEN s - 1) = STRLEN s` by rw_tac list_ss [] >> pop_subst_tac
     >> rw_tac list_ss [REPLICATE_EQ_SELF]
     >> irule MONO_EVERY
     >> qexists_tac `\x. 0 = ORD x`
     >> rw_tac splat_ss [])
 >- (`EXISTS (\y. ~(0 = y)) (MAP ORD s)` by fs [NOT_EVERY,o_DEF,EXISTS_MAP]
     >> qpat_k_assum `~EVERY _ _`
     >> rw_tac splat_ss [LOG_l2n_dropWhile]
     >> strip_assume_tac split_zero_pad >> rw_tac splat_ss [] >> fs[] >> rw_tac splat_ss []
     >- (subst_all_tac (SYM (ETA_CONV ``\x. 0n = x``)) >> fs [] >> metis_tac [EVERY_NOT_EXISTS])
     >- (`EVERY ($= 0) (REVERSE l2)` by metis_tac [EVERY_REVERSE]
          >> rw_tac list_ss [dropWhile_APPEND_EVERY]
          >> `dropWhile ($= 0) (REVERSE l1) = REVERSE l1`
              by (Cases_on `REVERSE l1`
                >- full_simp_tac list_ss []
                >- (rw_tac list_ss [dropWhile_def]
                     >> `~(REVERSE l1 = [])` by rw_tac list_ss [REVERSE_EQ_NIL]
                     >> `HD (REVERSE l1) = LAST l1` by metis_tac [LAST_REVERSE, REVERSE_REVERSE]
                     >> metis_tac [HD]))
          >> pop_subst_tac
          >> pop_assum mp_tac
          >> rw_tac list_ss []
          >> `0 < LENGTH l1` by metis_tac [qdecide `~(x=0) <=> 0 < x`,LENGTH_NIL]
          >> `SUC (PRE (LENGTH l1)) = LENGTH l1` by metis_tac [SUC_PRE]
          >> pop_subst_tac
          >> rw_tac list_ss [TAKE_APPEND]
	  >> `STRLEN s = LENGTH l1 + LENGTH l2` by metis_tac [LENGTH_MAP,LENGTH_APPEND]
          >> rw_tac splat_ss [PAD_RIGHT,GSYM REPLICATE_GENLIST,map_replicate,GSYM REPLICATE]
          >> rw_tac list_ss [GSYM map_replicate]
          >> rw_tac std_ss [GSYM MAP_APPEND]
          >> `REPLICATE (LENGTH l2) 0 = l2` by metis_tac [REPLICATE_EQ_SELF]
          >> pop_subst_tac
          >> qpat_x_assum `MAP ORD s = _` (subst_all_tac o sym)
          >> rw_tac splat_ss [MAP_MAP_o, o_DEF]
        )
     >- (`EVERY ($= 0) (REVERSE l2)` by metis_tac [EVERY_REVERSE]
          >> rw_tac list_ss [dropWhile_APPEND_EVERY]
          >> `dropWhile ($= 0) (REVERSE l1) = REVERSE l1`
              by (Cases_on `REVERSE l1`
                >- full_simp_tac list_ss []
                >- (rw_tac list_ss [dropWhile_def]
                     >> `~(REVERSE l1 = [])` by rw_tac list_ss [REVERSE_EQ_NIL]
                     >> `HD (REVERSE l1) = LAST l1` by metis_tac [LAST_REVERSE, REVERSE_REVERSE]
                     >> metis_tac [HD]))
          >> pop_subst_tac
          >> pop_assum mp_tac
          >> rw_tac list_ss []
          >> `0 < LENGTH l1` by metis_tac [qdecide `~(x=0) <=> 0 < x`,LENGTH_NIL]
          >> `SUC (PRE (LENGTH l1)) = LENGTH l1` by metis_tac [SUC_PRE]
          >> pop_subst_tac
          >> rw_tac list_ss [TAKE_APPEND]
	  >> `STRLEN s = LENGTH l1 + LENGTH l2` by metis_tac [LENGTH_MAP,LENGTH_APPEND]
          >> rw_tac splat_ss [PAD_RIGHT,GSYM REPLICATE_GENLIST,map_replicate,GSYM REPLICATE]
          >> rw_tac list_ss [GSYM map_replicate]
          >> rw_tac std_ss [GSYM MAP_APPEND]
          >> `REPLICATE (LENGTH l2) 0 = l2` by metis_tac [REPLICATE_EQ_SELF]
          >> pop_subst_tac
          >> qpat_x_assum `MAP ORD s = _` (subst_all_tac o sym)
          >> rw_tac splat_ss [MAP_MAP_o, o_DEF]
        )
    )
QED
*)
