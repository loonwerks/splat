open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib regexpLib ASCIInumbersLib;

open pairTheory arithmeticTheory listTheory rich_listTheory pred_setTheory
		stringTheory combinTheory optionTheory numposrepTheory FormalLangTheory;

open finite_mapTheory bagTheory;  (* For termination of predFn, need to use mlt_list *)
open concatPartialTheory;

(*---------------------------------------------------------------------------*)
(* Setup basic proof support                                                 *)
(*---------------------------------------------------------------------------*)

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
fun simpCases_on q = Cases_on q >> fs [] >> rw[];

Triviality IS_SOME_NEG :
 IS_SOME = \x. ~(x=NONE)
Proof
  rw [FUN_EQ_THM] >> metis_tac [NOT_IS_SOME_EQ_NONE]
QED

val _ = new_theory "abscontig";

(*---------------------------------------------------------------------------*)
(* The types of interest: lvals, arithmetic expressions over rvals, boolean  *)
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
       | U8
       | U16
       | U32
End

Datatype:
  contig = Basic atom
         | Void
         | Assert bexp
         | Recd ((string # contig) list)
         | Array contig exp
         | List contig
         | Alt bexp contig contig
End

val contig_size_def = fetch "-" "contig_size_def";

(*---------------------------------------------------------------------------*)
(* Expression evaluation. Looking up lvals is partial, which infects evalExp *)
(*---------------------------------------------------------------------------*)

(* LSB with padding to width *)
Definition layout_def :
 layout b n width = PAD_RIGHT 0n width (n2l b n)
End

Definition repFn_def :
  repFn w n = MAP CHR (layout 256 n w)
End

Definition valFn_def :
  valFn s = if s = "" then NONE else SOME (l2n 256 (MAP ORD s))
End

Definition evalExp_def :
 evalExp theta (Loc lval) =
   (case FLOOKUP theta lval
     of SOME s => valFn s
      | NONE => NONE) /\
 evalExp theta (numLit n)  = SOME n /\
 evalExp theta (Add e1 e2) =
   (case evalExp theta e1
     of NONE => NONE
      | SOME n1 =>
    case evalExp theta e2
     of NONE => NONE
      | SOME n2 => SOME (n1+n2))
End

(*---------------------------------------------------------------------------*)
(* Boolean expression evaluation. Also partial                               *)
(*---------------------------------------------------------------------------*)

Definition evalBexp_def :
 (evalBexp theta (boolLit b) = SOME b) /\
 (evalBexp theta (BLoc lval) =
    case FLOOKUP theta lval
     of NONE => NONE
      | SOME s =>
     case valFn s
      of NONE => NONE
      | SOME n => SOME (~(n = 0n))) /\
 (evalBexp theta (Bnot b) =
   case evalBexp theta b
     of NONE => NONE
      | SOME bval => SOME (~bval)) /\
 (evalBexp theta (Bor b1 b2) =
   case evalBexp theta b1
     of NONE => NONE
     |  SOME bv1 =>
    case evalBexp theta b2
     of NONE => NONE
      | SOME bv2 => SOME (bv1 \/ bv2)) /\
 (evalBexp theta (Band b1 b2) =
   case evalBexp theta b1
     of NONE => NONE
      | SOME bv1 =>
    case evalBexp theta b2
     of NONE => NONE
      | SOME bv2 => SOME (bv1 /\ bv2)) /\
 (evalBexp theta (Beq e1 e2) =
   case evalExp theta e1
     of NONE => NONE
      | SOME n1 =>
    case evalExp theta e2
     of NONE => NONE
      | SOME n2 => SOME (n1 = n2)) /\
 (evalBexp theta (Blt e1 e2) =
   case evalExp theta e1
     of NONE => NONE
      | SOME n1 =>
    case evalExp theta e2
     of NONE => NONE
      | SOME n2 => SOME (n1 < n2))
End


Definition atomWidth_def:
 atomWidth Bool = 1 /\
 atomWidth Char = 1 /\
 atomWidth U8   = 1 /\
 atomWidth U16  = 2 /\
 atomWidth U32  = 4
End

(*---------------------------------------------------------------------------*)
(* Size of a contig. The system-generated contig_size goes through a lot of  *)
(* other types, including field names, and those shouldn't be counted because*)
(* field name size shouldn't count in the size of the expression.            *)
(*---------------------------------------------------------------------------*)

Theorem contig_size_lem:
 !plist p. MEM p plist ==> contig_size (SND p) < contig1_size plist
Proof
 simp_tac list_ss [FORALL_PROD]
 >> Induct
 >> rw_tac list_ss [contig_size_def]
 >- rw_tac list_ss [contig_size_def]
 >- (‘contig_size p_2 < contig1_size plist’ by metis_tac[] >> decide_tac)
QED

val _ = DefnBase.add_cong list_size_cong;

Definition csize_def :
  (csize (Basic a)     = 0) /\
  (csize Void          = 0) /\
  (csize (Assert b)    = 0) /\
  (csize (Recd fields) = 1 + list_size (\(a,c). csize  c) fields) /\
  (csize (Array c dim) = 1 + csize c) /\
  (csize (List c)      = 1 + csize c) /\
  (csize (Alt b c1 c2) = 1 + csize c1 + csize c2)
Termination
  WF_REL_TAC `measure contig_size`
  >> rw_tac list_ss [contig_size_def]
  >- (Induct_on `fields`
      >> rw_tac list_ss [contig_size_def]
      >> full_simp_tac list_ss [contig_size_def])
End

(*---------------------------------------------------------------------------*)
(* Size of an lval. Needed in termination proof of substFn.                  *)
(*---------------------------------------------------------------------------*)

Definition lvsize_def :
  lvsize (VarName s) = 1 /\
  lvsize (RecdProj lv s) = 1 + lvsize lv /\
  lvsize (ArraySub lv e) = 1 + lvsize lv
End

Definition lvprefixes_def :
  lvprefixes (VarName s) = {VarName s} /\
  lvprefixes (RecdProj lv s) = (RecdProj lv s INSERT lvprefixes lv) /\
  lvprefixes (ArraySub lv e) = (ArraySub lv e INSERT lvprefixes lv)
End

Theorem lvprefixes_refl :
 ∀lval. lval IN lvprefixes lval
Proof
 Induct >> rw[lvprefixes_def]
QED

Theorem lvprefixes_Recd_downclosed :
  ∀x lval fld. RecdProj lval fld IN lvprefixes x ⇒ lval IN lvprefixes x
Proof
 Induct
  >> rw [lvprefixes_def]
  >> metis_tac [lvprefixes_refl]
QED

Theorem lvsize_lvprefixes :
 ∀lval lv. lv IN lvprefixes lval ⇒ lvsize lv < lvsize lval ∨ lv = lval
Proof
 Induct
   >> rw[lvprefixes_def,lvsize_def]
   >> res_tac
   >> rw[]
QED

Definition lvdescendants_def :
  lvdescendants theta lval = {path | path IN FDOM theta ∧ lval IN lvprefixes path}
End

Definition NilTag_def :
  NilTag = CHR 0
End

Definition ConsTag_def :
  ConsTag = CHR 1
End

(*---------------------------------------------------------------------------*)
(* Semantics (formal language style)                                         *)
(*---------------------------------------------------------------------------*)

Definition Contig_Lang_def:
  Contig_Lang theta (Basic a) = {s | LENGTH s = atomWidth a} /\
  Contig_Lang theta Void = {} /\
  Contig_Lang theta (Assert b) =
    (case evalBexp theta b
      of NONE => {}
       | SOME T => {""}
       | SOME F => {}) /\
  Contig_Lang theta (Recd fields) =
    {CONCAT slist
      | LIST_REL (\s contig. s IN Contig_Lang theta contig) slist (MAP SND fields)} /\
  Contig_Lang theta (Array c e) =
    (case evalExp theta e
      of NONE => {}
       | SOME n =>
     {CONCAT slist
       | (LENGTH slist = n) /\ EVERY (Contig_Lang theta c) slist}) /\
  Contig_Lang theta (List c) =
      (KSTAR ({[ConsTag]} dot (Contig_Lang theta c)) dot {[NilTag]}) /\
  Contig_Lang theta (Alt bexp c1 c2) =
    (case evalBexp theta bexp
      of NONE => {}
       | SOME T => Contig_Lang theta c1
       | SOME F => Contig_Lang theta c2)
Termination
  WF_REL_TAC ‘measure (contig_size o SND)’
  >> rw [contig_size_def,MEM_MAP]
  >> imp_res_tac contig_size_lem
  >> decide_tac
End

(*---------------------------------------------------------------------------*)
(* Assert derivable. Complicates termination proof for Contig_Lang, so       *)
(* expanded form used in Contig_Lang_def above.                              *)
(*---------------------------------------------------------------------------*)

Theorem Assert_Alt :
  Contig_Lang theta (Assert b) = Contig_Lang theta (Alt b (Recd []) Void)
Proof
  rw[Contig_Lang_def]
   >> every_case_tac
   >> rw[EXTENSION]
QED

Theorem IN_Contig_Lang :
  ∀s.
     (s IN Contig_Lang theta (Basic a) ⇔ LENGTH s = atomWidth a) ∧
     (s IN Contig_Lang theta Void ⇔ F) ∧
     (s IN Contig_Lang theta (Assert b) ⇔ (s = "" ∧ evalBexp theta b = SOME T)) ∧
     (s IN Contig_Lang theta (Recd fields) ⇔
        ∃slist. s = CONCAT slist ∧
                LIST_REL (\s contig. s IN Contig_Lang theta contig) slist (MAP SND fields)) /\
     (s IN Contig_Lang theta (Array c e) ⇔
        ∃slist.
            evalExp theta e = SOME (LENGTH slist) ∧
            s = CONCAT slist ∧
            EVERY (Contig_Lang theta c) slist) ∧
     (s IN Contig_Lang theta (List c) ⇔
       ∃slist.
            s = STRCAT (CONCAT slist) [NilTag] ∧
            EVERY (\plist. ∃elt. plist = ConsTag::elt ∧ elt IN Contig_Lang theta c) slist) ∧
     (s IN Contig_Lang theta (Alt bexp c1 c2) ⇔
         ∃b. evalBexp theta bexp = SOME b ∧
              if b then s IN Contig_Lang theta c1
                   else s IN Contig_Lang theta c2)
Proof
 rw [Contig_Lang_def,EXTENSION]
  >> every_case_tac
  >> rw [IN_dot,IN_KSTAR_LIST]
  >> metis_tac[]
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

Triviality list_size_append :
 !L1 L2 f. list_size f (L1 ++ L2) = (list_size f L1 + list_size f L2)
Proof
 Induct_on ‘L1’ >> rw_tac list_ss [list_size_def]
QED

Triviality strlen_eq_1 :
 !L. (STRLEN L = 1) ⇔ ∃n. n < 256 ∧ L = [CHR n]
Proof
 Cases_on ‘L’
 >> rw_tac list_ss [STRLEN_DEF,EQ_IMP_THM]
 >> metis_tac[CHR_ONTO]
QED

Theorem atomWidth_pos :
 !b. 0 < atomWidth b
Proof
 Cases >> rw [atomWidth_def]
QED

Definition choiceFn_def :
  choiceFn theta bexp =
    case evalBexp theta bexp
     of NONE => F
      | SOME bval => bval
End

Definition indexFn_def :
  indexFn lval c n = (ArraySub lval (numLit n),c)
End

Definition fieldFn_def :
  fieldFn lval (fName,c) = (RecdProj lval fName,c)
End


Definition ListRecd_def :
  ListRecd lval c =
    (lval,
     Alt (Beq (Loc (RecdProj lval "tag")) (numLit 0)) (Recd [])
     (Alt (Beq (Loc (RecdProj lval "tag"))  (numLit 1))
          (Recd [("hd",c); ("tl", List c)])
          Void))
End


(*---------------------------------------------------------------------------*)
(* contig-specified predicate on strings.                                    *)
(*---------------------------------------------------------------------------*)

Definition predFn_def :
 predFn (worklist,s,theta) =
  case worklist
   of [] => T
    | (lval,Basic a)::t =>
        (case take_drop (atomWidth a) s
           of NONE => F
            | SOME (segment,rst) =>
              predFn (t, rst, theta |+ (lval,segment)))
   | (lval,Void)::t => F
   | (lval,Assert b)::t =>
       (case evalBexp theta b
         of NONE   => F
          | SOME F => F
          | SOME T => predFn (t,s,theta))
   | (lval,Recd fields)::t =>
       predFn (MAP (fieldFn lval) fields ++ t,s,theta)
   | (lval,Array c exp)::t =>
       (case evalExp theta exp
         of NONE => F
          | SOME dim =>
            predFn (MAP (indexFn lval c) (COUNT_LIST dim) ++ t,s,theta))
   | (lval, List c)::t =>
      (case take_drop 1 s
           of NONE => F
            | SOME (segment,rst) =>
              predFn (ListRecd lval c::t, rst, theta |+ (RecdProj lval "tag",segment)))
   | (lval,Alt bexp c1 c2)::t =>
       case evalBexp theta bexp
        of NONE => F
         | SOME T => predFn ((lval,c1)::t,s,theta)
         | SOME F => predFn ((lval,c2)::t,s,theta)
Termination
 WF_REL_TAC ‘inv_image
              (measure LENGTH
               LEX
               mlt_list (measure (csize o SND)))
              (\(b,c,d). (c,b))’
   >> rw [APPEND_EQ_SELF]
   >> rw [csize_def]
   >> fs [MEM_MAP,MEM_SPLIT]
   >- (imp_res_tac take_drop_thm >> rw [] >> metis_tac [atomWidth_pos])
   >- (imp_res_tac take_drop_thm >> rw [] >> metis_tac [atomWidth_pos])
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,fieldFn_def])
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,indexFn_def])
End

(*---------------------------------------------------------------------------*)
(* Worklist-based matcher. When it comes to add a new (lval |-> string)      *)
(* element to theta, it first checks that lval is not in FDOM(theta).        *)
(*---------------------------------------------------------------------------*)

Definition matchFn_def :
 matchFn (worklist,s,theta) =
 case worklist
  of [] => SOME (s,theta)
   | (lval,Basic a)::t =>
       (case take_drop (atomWidth a) s
         of NONE => NONE
          | SOME (segment,rst) =>
        if lval IN FDOM theta then
            NONE
        else matchFn (t, rst, theta |+ (lval,segment)))
   | (lval,Void)::t => NONE
   | (lval,Assert b)::t =>
       (case evalBexp theta b
         of NONE   => NONE
          | SOME F => NONE
          | SOME T => matchFn (t,s,theta))
   | (lval,Recd fields)::t =>
        matchFn (MAP (fieldFn lval) fields ++ t,s,theta)
   | (lval,Array c exp)::t =>
       (case evalExp theta exp
         of NONE => NONE
          | SOME dim =>
             matchFn (MAP (indexFn lval c) (COUNT_LIST dim) ++ t,s,theta))
   | (lval, List c)::t =>
      (case take_drop 1 s
           of NONE => NONE
            | SOME (segment,rst) =>
              if RecdProj lval "tag" IN FDOM theta then
                 NONE
              else
              matchFn (ListRecd lval c::t, rst, theta |+ (RecdProj lval "tag",segment)))
   | (lval,Alt bexp c1 c2)::t =>
       case evalBexp theta bexp
        of NONE => NONE
         | SOME T => matchFn ((lval,c1)::t,s,theta)
         | SOME F => matchFn ((lval,c2)::t,s,theta)
Termination
 WF_REL_TAC ‘inv_image
              (measure LENGTH
               LEX
               mlt_list (measure (csize o SND)))
              (\(b,c,d). (c,b))’
   >> rw [APPEND_EQ_SELF]
   >> rw [csize_def]
   >> fs [MEM_MAP,MEM_SPLIT]
   >- (imp_res_tac take_drop_thm >> rw [] >> metis_tac [atomWidth_pos])
   >- (imp_res_tac take_drop_thm >> rw [] >> metis_tac [atomWidth_pos])
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,fieldFn_def])
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,indexFn_def])
End

(*---------------------------------------------------------------------------*)
(* Apply a substitution to a contig.                                         *)
(*---------------------------------------------------------------------------*)

Definition remaining_lvals_def :
  remaining_lvals(theta,lval) = CARD(lvdescendants theta lval)
End

Definition substFn_def :
 substFn theta (lval,contig) =
  case contig
   of Basic _ => FLOOKUP theta lval
    | Void  => NONE
    | Assert b =>
       (case evalBexp theta b
         of NONE   => NONE
          | SOME F => NONE
          | SOME T => SOME "")
    | Recd fields =>
       concatPartial
         (MAP (\(fName,c). substFn theta (RecdProj lval fName,c)) fields)
    | Array c exp =>
       (case evalExp theta exp
         of NONE => NONE
          | SOME dim =>
            concatPartial
               (MAP (\i. substFn theta (ArraySub lval (numLit i), c))
                    (COUNT_LIST dim)))
    | List c =>
       (case FLOOKUP theta (RecdProj lval "tag")
         of NONE => NONE
          | SOME segment =>
            if segment = [NilTag] then
               SOME [NilTag]
            else
            if segment = [ConsTag] then
             concatPartial
                 [SOME [ConsTag];
                  substFn theta (RecdProj lval "hd",c);
                  substFn theta (RecdProj lval "tl",List c)]
             else NONE)
    | Alt bexp c1 c2 =>
       (case evalBexp theta bexp
         of NONE => NONE
          | SOME T => substFn theta (lval,c1)
          | SOME F => substFn theta (lval,c2))
Termination
 WF_REL_TAC ‘inv_image
              (measure csize LEX measure remaining_lvals)
              (\(b,c,d). (d,(b,c)))’
  >> rw [csize_def]
  >- (fs [remaining_lvals_def,ConsTag_def, NilTag_def]
        >> rw[]
        >> irule CARD_PSUBSET >> conj_tac
        >- (rw [lvdescendants_def]
              >> irule SUBSET_FINITE
              >> qexists_tac ‘FDOM theta’
              >> rw[SUBSET_DEF])
        >- (rw[PSUBSET_MEMBER,SUBSET_DEF,lvdescendants_def]
              >- metis_tac [lvprefixes_Recd_downclosed]
              >- (qexists_tac ‘RecdProj lval "tag"’
                  >> rw[]
                  >- metis_tac [flookup_thm]
                  >- rw [lvprefixes_def,lvprefixes_refl]
                  >- (disj2_tac >> disch_tac
                       >> imp_res_tac lvsize_lvprefixes
                       >> fs [lvsize_def]))))
  >- (disj1_tac >> Induct_on `fields` >> rw[list_size_def] >> rw[] >> fs[])
End


(*---------------------------------------------------------------------------*)
(* Successful evaluation is stable.                                          *)
(*---------------------------------------------------------------------------*)

Theorem evalExp_submap :
 ∀e theta1 theta2 v.
   theta1 SUBMAP theta2 ∧
   evalExp theta1 e = SOME v
   ⇒
   evalExp theta2 e = SOME v
Proof
Induct
 >> rw [evalExp_def]
 >> every_case_tac >> fs []
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11]
QED

Theorem evalBexp_submap :
 ∀bexp theta1 theta2 v.
   theta1 SUBMAP theta2 ∧
   evalBexp theta1 bexp = SOME v
   ⇒
   evalBexp theta2 bexp = SOME v
Proof
Induct
 >> rw [evalBexp_def]
 >> every_case_tac
 >> fs []
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11,evalExp_submap]
QED

(*---------------------------------------------------------------------------*)
(* The matcher only adds new bindings to theta.                              *)
(*---------------------------------------------------------------------------*)

Theorem match_submap :
 !wklist s theta s2 theta'.
    matchFn (wklist,s,theta) = SOME (s2, theta')
    ==>
   finite_map$SUBMAP theta theta'
Proof
 recInduct matchFn_ind
  >> rpt gen_tac >> strip_tac
  >> rw_tac list_ss [Once matchFn_def]
  >> every_case_tac
  >> rw[]
  >> fs [SUBMAP_FUPDATE]
  >> rfs[]
  >> rw[]
  >> metis_tac [SUBMAP_DOMSUB_gen,DOMSUB_NOT_IN_DOM]
QED

(*---------------------------------------------------------------------------*)
(* Apply a substitution to a worklist                                        *)
(*---------------------------------------------------------------------------*)

Definition substWk_def :
  substWk theta wklist = concatPartial (MAP (substFn theta) wklist)
End

(*---------------------------------------------------------------------------*)
(* The substitution computed by matchFn is correctly applied by substWk      *)
(*---------------------------------------------------------------------------*)

Theorem match_lem :
!wklist (s:string) theta s2 theta'.
   matchFn (wklist,s,theta) = SOME (s2, theta')
   ==>
   ?s1. substWk theta' wklist = SOME s1 /\  s1 ++ s2 = s
Proof
 simp_tac list_ss [substWk_def]
 >> recInduct matchFn_ind
 >> rpt gen_tac
 >> strip_tac
 >> rw_tac list_ss [Once matchFn_def]
 >> simpCases_on ‘worklist’
 >> TRY (Cases_on ‘h’ >> simpCases_on ‘r’)
 >- rw[concatPartial_thm]
 >- (simpCases_on ‘take_drop (atomWidth a) s’
     >> simpCases_on ‘x’
     >> qexists_tac ‘q' ++ s1’
     >> ‘s = STRCAT q' (STRCAT s1 s2)’ by metis_tac [take_drop_thm]
     >> rw []
     >> rw [Once substFn_def]
     >> ‘(theta |+ (q,q')) SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘FLOOKUP (theta |+ (q,q')) q = SOME q'’ by metis_tac [FLOOKUP_UPDATE]
     >> ‘FLOOKUP theta' q = SOME q'’ by metis_tac [FLOOKUP_SUBMAP]
     >> rw[]
     >> fs [concatPartial_thm])
 >- (simpCases_on ‘evalBexp theta b’
     >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘evalBexp theta' b = SOME T’ by metis_tac [evalBexp_submap]
     >> rw[Once substFn_def]
     >> fs [concatPartial_thm])
 >- (rw[Once substFn_def]
     >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,fieldFn_def,LAMBDA_PROD,IS_SOME_NEG]
     >> rw []
     >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
     >> metis_tac [NOT_EXISTS])
 >- (simpCases_on ‘evalExp theta e’
     >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘evalExp theta' e = SOME x’ by metis_tac [evalExp_submap]
     >> rw[Once substFn_def]
     >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,indexFn_def,LAMBDA_PROD,IS_SOME_NEG]
     >> rw []
     >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
     >> metis_tac [NOT_EXISTS])
 >- (simpCases_on ‘take_drop 1 s’
     >> simpCases_on ‘x’
     >> ‘∃tag lval. q' = tag ∧ q = lval’ by metis_tac[] >> ntac 2 (pop_subst_tac)
     >> qexists_tac ‘tag ++ s1’
     >> ‘s = STRCAT tag (STRCAT s1 s2)’ by metis_tac [take_drop_thm]
     >> ‘(theta |+ (RecdProj lval "tag", tag)) SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘FLOOKUP (theta |+ (RecdProj lval "tag",tag))
                 (RecdProj lval "tag") = SOME tag’ by metis_tac [FLOOKUP_UPDATE]
     >> ‘FLOOKUP theta' (RecdProj lval "tag") = SOME tag’ by metis_tac [FLOOKUP_SUBMAP]
     >> pop_assum (fn th => popk_tac >> assume_tac th)
     >> rw[Once substFn_def]
     >- (fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,LAMBDA_PROD,IS_SOME_NEG]
         >> rw []
         >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
         >> rw [Once substFn_def,ListRecd_def,evalBexp_def,evalExp_def,NilTag_def,valFn_def]
         >> rw [Once substFn_def,concatPartial_nil])
     >- (fs [ConsTag_def, NilTag_def] >> rw[]
         >> qpat_x_assum ‘matchFn _ = _’ kall_tac
         >> qpat_x_assum ‘take_drop _ _ = _’ kall_tac
         >> qpat_x_assum ‘~(_ IN _)’ kall_tac
         >> qpat_x_assum ‘_ SUBMAP _’ kall_tac
         >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,LAMBDA_PROD,IS_SOME_NEG]
         >> rw []
         >> qpat_x_assum ‘EVERY _ _’ kall_tac
         >> qpat_x_assum ‘~(substFn _ _ = NONE)’
               (mp_tac o SIMP_RULE (srw_ss()) [Once substFn_def,ListRecd_def])
         >> rw [evalBexp_def,evalExp_def,NilTag_def,ConsTag_def,valFn_def]
         >> qpat_x_assum ‘~(substFn _ _ = NONE)’
               (mp_tac o SIMP_RULE (srw_ss()) [Once substFn_def])
         >> rw [evalBexp_def,evalExp_def,NilTag_def,ConsTag_def,valFn_def]
         >> qpat_x_assum ‘~(substFn _ _ = NONE)’
               (mp_tac o SIMP_RULE (srw_ss()) [Once substFn_def])
         >> rw [concatPartial_thm]
         (* last clause *)
         >> rw [SimpRHS, Once substFn_def,ListRecd_def]
         >> rw [evalBexp_def,evalExp_def,NilTag_def,ConsTag_def,valFn_def]
         >> rw [SimpRHS, Once substFn_def]
         >> rw [evalBexp_def,evalExp_def,NilTag_def,ConsTag_def,valFn_def]
         >> rw [SimpRHS, Once substFn_def]
         >> rw [concatPartial_thm])
     >- (qpat_x_assum ‘concatPartial _ = _ ’ mp_tac
         >> rw [Once substFn_def,ListRecd_def,evalBexp_def,evalExp_def,NilTag_def]
         >> ‘∃n. valFn tag = SOME n ∧ ~(n=0) ∧ ~(n=1)’
            by (‘STRLEN tag = 1’ by metis_tac [take_drop_thm]
                  >> fs [strlen_eq_1,NilTag_def,ConsTag_def]
                  >> rw[]
                  >> ntac 2 (pop_assum mp_tac)
                  >> rw [CHR_11]
                  >> qexists_tac ‘n’
                  >> rw[valFn_def,l2n_def])
         >> full_case_tac >> fs[] >> rw[] >> rfs[]
         >> rw [concatPartial_thm]
         >> pop_assum mp_tac
         >> rw [Once substFn_def,ListRecd_def,evalBexp_def,evalExp_def,ConsTag_def]
         >> rw [Once substFn_def,concatPartial_thm]))
 >- (simpCases_on ‘evalBexp theta b’
     >> simpCases_on ‘x’
     >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
     >> rw[]
     >- (‘evalBexp theta' b = SOME T’ by metis_tac [evalBexp_submap]
          >> rw[Once substFn_def]
          >> every_case_tac
          >> rw [])
     >- (‘evalBexp theta' b = SOME F’ by metis_tac [evalBexp_submap]
         >> rw[Once substFn_def]
         >> every_case_tac
         >> rw []))
QED


Theorem match_subst_thm :
 !vFn wklist (s:string) theta s2 theta'.
    matchFn (wklist,s,theta) = SOME (s2, theta')
    ==>
    THE (substWk theta' wklist) ++ s2 = s
Proof
 metis_tac [match_lem,optionTheory.THE_DEF]
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
  evalExp theta e = SOME n
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
  evalBexp theta b = SOME T
   ==>
   (s IN Contig_Lang theta (arb_label_recd (Alt b c1 c2::clist))
    <=>
    s IN Contig_Lang theta (arb_label_recd (c1::clist)))
Proof
 rw[IN_Contig_Lang,arb_label_recd_def,EQ_IMP_THM,PULL_EXISTS]
QED

Theorem Recd_Alt_flatB :
 ∀s b c1 c2 clist theta.
  evalBexp theta b = SOME F
   ==>
   (s IN Contig_Lang theta (arb_label_recd (Alt b c1 c2::clist))
    <=>
    s IN Contig_Lang theta (arb_label_recd (c2::clist)))
Proof
 rw[IN_Contig_Lang,arb_label_recd_def,EQ_IMP_THM,PULL_EXISTS]
QED

Theorem Contig_Singleton_Recd :
 !s theta contig fName.
     s IN Contig_Lang theta (Recd [(fName,contig)])
      <=>
     s IN Contig_Lang theta contig
Proof
 rw [IN_Contig_Lang,PULL_EXISTS]
QED


Theorem matchFn_wklist_sound :
 !wklist s fmap suffix theta.
   matchFn (wklist,s,fmap) = SOME (suffix, theta)
    ==>
   ∃prefix. (s = prefix ++ suffix) ∧
             prefix IN Contig_Lang theta (arb_label_recd (MAP SND wklist))
Proof
 recInduct matchFn_ind
  >> simp_tac list_ss []
  >> rpt gen_tac
  >> strip_tac
  >> simp_tac list_ss [Once matchFn_def]
  >> simpCases_on ‘worklist’
  >> TRY (Cases_on ‘h’ >> simpCases_on ‘r’)
  >- rw [IN_Contig_Lang,arb_label_recd_def]
  >- (simpCases_on ‘take_drop (atomWidth a) s’
      >> simpCases_on ‘x’
      >> qexists_tac ‘q' ++ prefix’
      >> rw [IN_Contig_Lang,arb_label_recd_def,PULL_EXISTS]
         >- (imp_res_tac take_drop_thm >> fs [])
         >- (imp_res_tac take_drop_thm
             >> fs [IN_Contig_Lang,arb_label_recd_def,PULL_EXISTS,map_snd_lem]
             >> rw[]
             >> metis_tac[]))
  >- (simpCases_on ‘evalBexp theta b’
      >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
      >> ‘evalBexp theta' b = SOME T’ by metis_tac [evalBexp_submap]
      >> fs[IN_Contig_Lang,arb_label_recd_def,PULL_EXISTS,map_snd_lem]
      >> metis_tac[])
  >- (fs[map_snd_fieldFn]
      >> ‘Contig_Lang theta' (arb_label_recd (MAP SND l ⧺ MAP SND t)) =
          Contig_Lang theta' (arb_label_recd (Recd l::MAP SND t))’
          by (rw [arb_label_recd_def,Recd_flat,EXTENSION]
              >> AP_TERM_TAC
              >> match_mp_tac field_names_ignored
              >> rw[map_snd_lem])
      >> metis_tac[])
  >- (simpCases_on ‘evalExp theta e’
      >> fs[map_snd_indexFn]
      >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
      >> ‘evalExp theta' e = SOME x’ by metis_tac [evalExp_submap]
      >> ‘Contig_Lang theta' (arb_label_recd (Array c e::MAP SND t)) =
          Contig_Lang theta' (arb_label_recd (REPLICATE x c ⧺ MAP SND t))’
          by rw [EXTENSION,GSYM Recd_Array_flat]
      >> metis_tac [map_snd_indexFn])
 >- (simpCases_on ‘take_drop 1 s’
     >> simpCases_on ‘x’
     >> ‘∃tag lval. q' = tag ∧ q = lval’ by metis_tac[] >> ntac 2 (pop_subst_tac)
     >> qexists_tac ‘tag ++ prefix’
     >> ‘s = STRCAT tag (STRCAT prefix suffix)’ by metis_tac [take_drop_thm]
     >> rw[]
     >> ‘(theta |+ (RecdProj lval "tag", tag)) SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘FLOOKUP (theta |+ (RecdProj lval "tag",tag))
                 (RecdProj lval "tag") = SOME tag’ by metis_tac [FLOOKUP_UPDATE]
     >> ‘FLOOKUP theta' (RecdProj lval "tag") = SOME tag’ by metis_tac [FLOOKUP_SUBMAP]
     >> pop_assum (fn th => popk_tac >> assume_tac th)
     >> qpat_x_assum ‘matchFn _ = _’ kall_tac
     >> ‘STRLEN tag = 1’ by metis_tac [take_drop_thm]
     >> qpat_x_assum ‘take_drop _ _ = _’ kall_tac
     >> qpat_x_assum ‘~(_ IN _)’ kall_tac
     >> qpat_x_assum ‘_ SUBMAP _’ kall_tac
     >> qpat_x_assum ‘prefix IN Contig_Lang _ _’
          (strip_assume_tac o SIMP_RULE (srw_ss())
           [IN_Contig_Lang,arb_label_recd_def,ListRecd_def,PULL_EXISTS,map_snd_lem,
            evalExp_def, evalBexp_def])
     >> rw[] >> rfs[option_case_eq] >> fs [] >> rw[]
     >> simpCases_on ‘n1’
     >- (‘tag = [NilTag]’
           by (fs [strlen_eq_1,NilTag_def]
                >> rw[]
                >> fs[valFn_def,l2n_def]
                >> qpat_x_assum ‘_ = 0’ mp_tac
                >> rw [ORD_CHR_RWT])
         >> rw [IN_Contig_Lang,arb_label_recd_def,PULL_EXISTS,map_snd_lem]
         >> qexists_tac ‘xs’
         >> qexists_tac ‘[]’
         >> rw [])
     >- (‘tag = [ConsTag]’
           by (fs [strlen_eq_1,ConsTag_def]
                >> rw[]
                >> fs[valFn_def,l2n_def]
                >> qpat_x_assum ‘_ = 1’ mp_tac
                >> rw [ORD_CHR_RWT])
          >> qpat_x_assum ‘valFn tag = _’ kall_tac
          >> qpat_x_assum ‘valFn tag = _’ kall_tac
          >> qpat_x_assum ‘STRLEN tag = _’ kall_tac
          >> rw [IN_Contig_Lang,arb_label_recd_def,PULL_EXISTS,map_snd_lem]
          >> qexists_tac ‘xs’
          >> qexists_tac ‘STRCAT [ConsTag] s' :: slist'’
          >> rpt conj_tac
          >- rw []
          >- rw []
          >- metis_tac[]))
 >- (simpCases_on ‘evalBexp theta b’
     >> simpCases_on ‘x’
     >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
     >- (‘evalBexp theta' b = SOME T’ by metis_tac [evalBexp_submap]
          >> rw [Recd_Alt_flatA])
     >- (‘evalBexp theta' b = SOME F’ by metis_tac [evalBexp_submap]
         >> rw [Recd_Alt_flatB]))
QED

Theorem matchFn_sound :
 !contig s theta.
   matchFn ([(VarName"root",contig)],s,FEMPTY) = SOME ("", theta)
    ==>
   s IN Contig_Lang theta contig
Proof
  rw[]
  >> imp_res_tac (matchFn_wklist_sound |> SIMP_RULE std_ss [])
  >> rw []
  >> fs [arb_label_recd_def,Contig_Singleton_Recd]
QED


val _ = export_theory();
