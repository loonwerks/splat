gopen HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib ASCIInumbersLib;

open pairTheory arithmeticTheory listTheory rich_listTheory pred_setTheory
     stringTheory combinTheory optionTheory numposrepTheory FormalLangTheory;

(* For termination of predFn, need to use mlt_list from containerTheory *)
open finite_mapTheory bagTheory containerTheory;
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

Theorem SKOLEM_SUBSET :
  ∀P Q.
    (∀x. P x ⇒ ∃y. Q x y) ⇔ ∃f. ∀x. P x ⇒ Q x (f x)
Proof
 metis_tac[]
QED

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
val lval_mutual_ind = fetch "-" "lval_induction";
val contig_size_def = fetch "-" "contig_size_def";

val lval_ind =
  lval_mutual_ind
     |> Q.SPEC ‘P’
     |> Q.SPEC ‘K T’
     |> SIMP_RULE (srw_ss()) []
     |> Q.GEN ‘P’;


(*---------------------------------------------------------------------------*)
(* No duplicate record fields.                                               *)
(*---------------------------------------------------------------------------*)

Definition wf_contig_def :
  wf_contig c =
   case c
    of Basic _     => T
     | Void        => T
     | Assert _    => T
     | Array c e   => wf_contig c
     | List c      => wf_contig c
     | Alt b c1 c2 => (wf_contig c1 ∧ wf_contig c2)
     | Recd fields => ALL_DISTINCT (MAP FST fields) ∧
                      EVERY wf_contig (MAP SND fields)
Termination
 WF_REL_TAC ‘measure contig_size’
 >> Induct
 >> rw [contig_size_def]
 >- (Cases_on ‘h’ >> rw [contig_size_def])
 >- (RES_THEN mp_tac >> decide_tac)
End

(*---------------------------------------------------------------------------*)
(* Expression evaluation. Looking up lvals is partial, which infects evalExp *)
(* For now we hard-wire valFn and repFn                                      *)
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
     of SOME (a,s) => valFn s
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
      | SOME (a,s) =>
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
     ⇔
     (acc' ++ suf = REVERSE acc ++ list) /\
     (LENGTH acc' = n + LENGTH acc)
Proof
 recInduct tdrop_ind
 >> rw [tdrop_def,EQ_IMP_THM]
 >- metis_tac [LENGTH_REVERSE]
 >- fs [APPEND_11_LENGTH]
 >- fs [APPEND_11_LENGTH]
 >- (‘LENGTH (acc' ++ suf) = LENGTH acc’ by metis_tac[LENGTH_REVERSE] >>  fs[])
QED

Definition take_drop_def :
  take_drop n list = tdrop n list []
End

Theorem take_drop_thm :
  ∀n list.
      take_drop n list = SOME (pref,suf) ⇔ pref ++ suf = list /\ (n = LENGTH pref)
Proof
   rw_tac list_ss [take_drop_def,tdrop_thm] >> metis_tac[]
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
           | SOME (segment,rst) => predFn (t,rst,theta |+ (lval,(a,segment))))
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
      (case take_drop (atomWidth U8) s
        of NONE => F
         | SOME (segment,rst) =>
              predFn (ListRecd lval c::t, rst,
                      theta |+ (RecdProj lval "tag",(U8,segment))))
   | (lval,Alt bexp c1 c2)::t =>
       case evalBexp theta bexp
        of NONE => F
         | SOME T => predFn ((lval,c1)::t,s,theta)
         | SOME F => predFn ((lval,c2)::t,s,theta)
Termination
 WF_REL_TAC
    ‘inv_image
        (measure LENGTH LEX mlt_list (measure (csize o SND)))
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
        else matchFn (t, rst, theta |+ (lval,(a,segment))))
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
      (case take_drop (atomWidth U8) s
           of NONE => NONE
            | SOME (segment,rst) =>
              if RecdProj lval "tag" IN FDOM theta then
                 NONE
              else
              matchFn (ListRecd lval c::t, rst,
                       theta |+ (RecdProj lval "tag",(U8,segment))))
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
   >> fs [MEM_MAP,MEM_SPLIT,take_drop_thm]
   >> rw[]
   >- metis_tac [atomWidth_pos]
   >- EVAL_TAC
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,fieldFn_def])
   >- (Cases_on `y` >> fs[list_size_append,list_size_def,indexFn_def])
End

(*---------------------------------------------------------------------------*)
(* Apply a substitution to a contig.                                         *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Strings indexed by lvals are right size. Every lval in a theta maps to a  *)
(* (atom,string), and atomWidth(atom) needs to agree with strlen string.     *)
(* This is enforced by construction in matchFn, but we also have situations  *)
(* where we have to consider arbitrary well-sized thetas.                    *)
(*---------------------------------------------------------------------------*)

Definition remaining_lvals_def :
  remaining_lvals(theta,lval) = CARD(lvdescendants theta lval)
End

Definition substFn_def :
 substFn theta (lval,contig) =
  case contig
   of Basic _ =>
        (case FLOOKUP theta lval
          of NONE => NONE
           | SOME(a,segment) => SOME segment)
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
          | SOME (a,segment) =>
            if a = U8 ∧ segment = [NilTag] then
               SOME segment
            else
            if a = U8 ∧ segment = [ConsTag] then
             concatPartial
                 [SOME segment;
                  substFn theta (RecdProj lval "hd",c);
                  substFn theta (RecdProj lval "tl",List c)]
            else NONE
       )
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
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11,FST,SND,PAIR_EQ]
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
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11,
              FST,SND,PAIR_EQ,evalExp_submap]
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
   ?s1. substWk theta' wklist = SOME s1 /\ s1 ++ s2 = s
Proof
 simp_tac list_ss [substWk_def]
 >> recInduct matchFn_ind
 >> rpt gen_tac
 >> strip_tac
 >> rw_tac list_ss [Once matchFn_def]
 >> simpCases_on ‘worklist’
 >> TRY (Cases_on ‘h’ >> simpCases_on ‘r’)
 >- rw[concatPartial_thm]
 >- (rename1 ‘lval IN FDOM theta’
     >> simpCases_on ‘take_drop (atomWidth a) s’
     >> simpCases_on ‘x’
     >> qexists_tac ‘q ++ s1’
     >> gvs[take_drop_thm]
     >> rw [Once substFn_def,AllCaseEqs()]
     >> ‘(theta |+ (lval,a,q)) SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘FLOOKUP (theta |+ (lval,a,q)) lval = SOME (a,q)’ by metis_tac [FLOOKUP_UPDATE]
     >> ‘FLOOKUP theta' lval = SOME (a,q)’ by metis_tac [FLOOKUP_SUBMAP]
     >> rw[]
     >> fs [concatPartial_thm,take_drop_thm])
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
 >- (fs[atomWidth_def]
     >> simpCases_on ‘take_drop 1 s’
     >> simpCases_on ‘x’
     >> rename1 ‘(RecdProj lval "tag",(U8,tag))’
     >> qexists_tac ‘tag ++ s1’
     >> ‘s = STRCAT tag (STRCAT s1 s2)’ by metis_tac [take_drop_thm]
     >> ‘(theta |+ (RecdProj lval "tag", (U8,tag))) SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘FLOOKUP (theta |+ (RecdProj lval "tag",(U8,tag)))
                 (RecdProj lval "tag") = SOME (U8,tag)’ by metis_tac [FLOOKUP_UPDATE]
     >> ‘FLOOKUP theta' (RecdProj lval "tag") = SOME (U8,tag)’ by metis_tac [FLOOKUP_SUBMAP]
     >> pop_assum (fn th => popk_tac >> assume_tac th)
     >> rw[Once substFn_def]
     >- (fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,LAMBDA_PROD,IS_SOME_NEG]
         >> rw []
         >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
         >> rw [Once substFn_def,ListRecd_def,evalBexp_def,evalExp_def,NilTag_def,valFn_def]
         >> fs [l2n_def]
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
         >> fs [l2n_def]
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
 !wklist (s:string) theta s2 theta'.
    matchFn (wklist,s,theta) = SOME (s2, theta')
    ==>
    THE (substWk theta' wklist) ++ s2 = s
Proof
 metis_tac [match_lem,optionTheory.THE_DEF]
QED

Definition arb_labels_def:
  arb_labels clist = Recd (MAP (\c. (ARB, c)) clist)
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

(*---------------------------------------------------------------------------*)
(* Various Contig_Lang equivalences (ad hoc list).                           *)
(*---------------------------------------------------------------------------*)

Theorem Recd_flat :
 ∀s plist1 plist2 theta fName.
   s IN Contig_Lang theta (Recd ((fName,Recd plist1)::plist2)) <=>
   s IN Contig_Lang theta (Recd (plist1 ++ plist2))
Proof
 rw[Contig_Lang_def, EQ_IMP_THM]
 >- (qexists_tac ‘slist' ++ xs’ >> rw[] >> metis_tac [LIST_REL_APPEND_suff])
 >- (fs [LIST_REL_SPLIT2] >> rw[PULL_EXISTS] >> metis_tac [])
QED

Theorem Array_flat :
 ∀s e n c clist theta.
  evalExp theta e = SOME n
   ==>
   (s IN Contig_Lang theta (arb_labels(Array c e::clist))
    <=>
    s IN Contig_Lang theta (arb_labels(REPLICATE n c ⧺ clist)))
Proof
 rw[IN_Contig_Lang,arb_labels_def,EQ_IMP_THM,PULL_EXISTS]
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

Theorem Alt_flatA :
 ∀s b c1 c2 clist theta.
  evalBexp theta b = SOME T
   ==>
   (s IN Contig_Lang theta (arb_labels(Alt b c1 c2::clist))
    <=>
    s IN Contig_Lang theta (arb_labels(c1::clist)))
Proof
 rw[IN_Contig_Lang,arb_labels_def,EQ_IMP_THM,PULL_EXISTS]
QED

Theorem Alt_flatB :
 ∀s b c1 c2 clist theta.
  evalBexp theta b = SOME F
   ==>
   (s IN Contig_Lang theta (arb_labels(Alt b c1 c2::clist))
    <=>
    s IN Contig_Lang theta (arb_labels(c2::clist)))
Proof
 rw[IN_Contig_Lang,arb_labels_def,EQ_IMP_THM,PULL_EXISTS]
QED

Theorem Singleton_Recd :
 !s theta contig fName.
     s IN Contig_Lang theta (Recd [(fName,contig)])
      <=>
     s IN Contig_Lang theta contig
Proof
 rw [IN_Contig_Lang,PULL_EXISTS]
QED

(*---------------------------------------------------------------------------*)
(* Generalized soundness                                                     *)
(*---------------------------------------------------------------------------*)

Theorem matchFn_wklist_sound :
 !wklist s fmap suffix theta.
   matchFn (wklist,s,fmap) = SOME (suffix, theta)
    ==>
   ∃prefix. (s = prefix ++ suffix) ∧
             prefix IN Contig_Lang theta (arb_labels(MAP SND wklist))
Proof
 recInduct matchFn_ind
  >> simp_tac list_ss []
  >> rpt gen_tac
  >> strip_tac
  >> simp_tac list_ss [Once matchFn_def]
  >> simpCases_on ‘worklist’
  >> TRY (Cases_on ‘h’ >> simpCases_on ‘r’)
  >- rw [IN_Contig_Lang,arb_labels_def]
  >- (simpCases_on ‘take_drop (atomWidth a) s’
      >> simpCases_on ‘x’
      >> rename1 ‘(lval,(a,slice))’
      >> qexists_tac ‘slice ++ prefix’
      >> rw [IN_Contig_Lang,arb_labels_def,PULL_EXISTS]
         >- (imp_res_tac take_drop_thm >> fs [])
         >- (imp_res_tac take_drop_thm
             >> fs [IN_Contig_Lang,arb_labels_def,PULL_EXISTS,map_snd_lem]
             >> rw[]
             >> metis_tac[]))
  >- (simpCases_on ‘evalBexp theta b’
      >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
      >> ‘evalBexp theta' b = SOME T’ by metis_tac [evalBexp_submap]
      >> fs[IN_Contig_Lang,arb_labels_def,PULL_EXISTS,map_snd_lem]
      >> metis_tac[])
  >- (fs[map_snd_fieldFn]
      >> ‘Contig_Lang theta' (arb_labels(MAP SND l ⧺ MAP SND t)) =
          Contig_Lang theta' (arb_labels(Recd l::MAP SND t))’
          by (rw [arb_labels_def,Recd_flat,EXTENSION]
              >> AP_TERM_TAC
              >> match_mp_tac field_names_ignored
              >> rw[map_snd_lem])
      >> metis_tac[])
  >- (simpCases_on ‘evalExp theta e’
      >> fs[map_snd_indexFn]
      >> ‘theta SUBMAP theta'’ by metis_tac [match_submap]
      >> ‘evalExp theta' e = SOME x’ by metis_tac [evalExp_submap]
      >> ‘Contig_Lang theta' (arb_labels(Array c e::MAP SND t)) =
          Contig_Lang theta' (arb_labels(REPLICATE x c ⧺ MAP SND t))’
          by rw [EXTENSION,GSYM Array_flat]
      >> metis_tac [map_snd_indexFn])
 >- (fs[atomWidth_def]
     >> simpCases_on ‘take_drop 1 s’
     >> simpCases_on ‘x’
     >> rename1 ‘(RecdProj lval "tag",(U8,tag))’
     >> qexists_tac ‘tag ++ prefix’
     >> ‘s = STRCAT tag (STRCAT prefix suffix)’ by metis_tac [take_drop_thm]
     >> rw[]
     >> ‘(theta |+ (RecdProj lval "tag", (U8,tag))) SUBMAP theta'’ by metis_tac [match_submap]
     >> ‘FLOOKUP (theta |+ (RecdProj lval "tag",(U8,tag)))
                 (RecdProj lval "tag") = SOME (U8,tag)’ by metis_tac [FLOOKUP_UPDATE]
     >> ‘FLOOKUP theta' (RecdProj lval "tag") = SOME (U8,tag)’ by metis_tac [FLOOKUP_SUBMAP]
     >> pop_assum (fn th => popk_tac >> assume_tac th)
     >> qpat_x_assum ‘matchFn _ = _’ kall_tac
     >> ‘STRLEN tag = 1’ by metis_tac [take_drop_thm]
     >> qpat_x_assum ‘take_drop _ _ = _’ kall_tac
     >> qpat_x_assum ‘~(_ IN _)’ kall_tac
     >> qpat_x_assum ‘_ SUBMAP _’ kall_tac
     >> qpat_x_assum ‘prefix IN Contig_Lang _ _’
          (strip_assume_tac o SIMP_RULE (srw_ss())
           [IN_Contig_Lang,arb_labels_def,ListRecd_def,PULL_EXISTS,map_snd_lem,
            evalExp_def, evalBexp_def])
     >> rw[] >> rfs[option_case_eq] >> fs [] >> rw[]
     >> simpCases_on ‘n1’
     >- (‘tag = [NilTag]’
           by (fs [strlen_eq_1,NilTag_def]
                >> rw[]
                >> fs[valFn_def,l2n_def]
                >> qpat_x_assum ‘_ = 0’ mp_tac
                >> rw [ORD_CHR_RWT])
         >> rw [IN_Contig_Lang,arb_labels_def,PULL_EXISTS,map_snd_lem]
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
          >> rw [IN_Contig_Lang,arb_labels_def,PULL_EXISTS,map_snd_lem]
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
          >> rw [Alt_flatA])
     >- (‘evalBexp theta' b = SOME F’ by metis_tac [evalBexp_submap]
         >> rw [Alt_flatB]))
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
  >> fs [arb_labels_def,Singleton_Recd]
QED

Theorem matchFn_sound :
 !contig s theta lval.
   matchFn ([(lval,contig)],s,FEMPTY) = SOME ("", theta)
    ==>
   s IN Contig_Lang theta contig
Proof
  rw[]
  >> imp_res_tac (matchFn_wklist_sound |> SIMP_RULE std_ss [])
  >> rw []
  >> fs [arb_labels_def,Singleton_Recd]
QED


(*---------------------------------------------------------------------------*)
(* What's the right idea of language for contig types. One view is           *)
(* Contig_lang theta contig, the other is substFn theta contig. Let's try to *)
(* prove them co-extensive.                                                  *)
(*---------------------------------------------------------------------------*)

Definition well_sized_def :
  well_sized theta <=>
    ∀lval. lval IN FDOM theta
           ==>
           STRLEN (SND(theta ' lval)) = atomWidth (FST (theta ' lval))
End

Theorem well_sized_lookup :
  ∀theta lval.
     well_sized theta ∧
     FLOOKUP theta lval = SOME (a,s)
    ==>
     STRLEN s = atomWidth a
Proof
 rw [well_sized_def,flookup_thm] >> metis_tac [FST,SND]
QED

Definition lval_append_def :
 lval_append path (VarName s) = RecdProj path s ∧
 lval_append path (RecdProj lval fname) = RecdProj (lval_append path lval) fname ∧
 lval_append path (ArraySub lval dim) = ArraySub (lval_append path lval) dim
End

Definition path_size_def :
  path_size (VarName _) = 1 ∧
  path_size (RecdProj p s) = 1 + path_size p ∧
  path_size (ArraySub p e) = 1 + path_size p
End

Theorem path_size_subterm :
  ∀lv p. path_size p < path_size (lval_append p lv)
Proof
Induct \\ rw[path_size_def, lval_append_def]
 \\ pop_assum (mp_tac o Q.ID_SPEC) \\ decide_tac
QED

Theorem lval_append_acyclic :
  ∀lv path. lval_append path lv ≠ path
Proof
  rw[] \\ disch_then (mp_tac o Q.AP_TERM ‘path_size’)
  \\ metis_tac[path_size_subterm,decide “x < y ⇒ x ≠ y”]
QED

Theorem lval_append_11 :
  ∀p1 p2 lval. lval_append lval p1 = lval_append lval p2 ==> p1 = p2
Proof
 recInduct lval_ind \\ rw [] \\ Cases_on ‘p2’ \\
 gvs[lval_append_def,lval_append_acyclic] \\ metis_tac[]
QED

Theorem inj_lval_append :
  ∀lval s1 s2.  INJ (lval_append lval) s1 UNIV
Proof
  simp[INJ_DEF] \\ metis_tac [lval_append_11]
QED

Theorem inj_lval_append_univs :
  ∀lval.  INJ (lval_append lval) UNIV UNIV
Proof
  simp[INJ_DEF] \\ metis_tac [lval_append_11]
QED


Theorem Equiv1:
  ∀theta lval c s.
     well_sized theta ∧
     substFn theta (lval,c) = SOME s
    ==>
     s IN Contig_Lang theta c
Proof
  recInduct substFn_ind
  >> Cases_on ‘contig’
  >> rw []
  >> pop_assum mp_tac
  >> rw[Once IN_Contig_Lang,Once substFn_def,concatPartial_SOME,AllCaseEqs()]
  >- metis_tac [well_sized_lookup]
  >- (qexists_tac
          ‘MAP THE (MAP (\(fName,c). substFn theta (RecdProj lval fName,c)) l)’
      >> rw[]
      >> rw [LIST_REL_EVERY_ZIP,MAP_MAP_o,EVERY_MEM,FORALL_PROD]
      >> first_assum irule
      >> gvs [MEM_ZIP,EVERY_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
      >> qexists_tac ‘EL n (MAP FST l)’
      >> rw [EL_MAP,MEM_EL] THENL[all_tac,metis_tac[]]
      >> ‘∃f c. EL n l = (f,c)’ by metis_tac [ABS_PAIR_THM]
      >> ‘MEM (f,c) l’ by metis_tac [MEM_EL]
      >> gvs[]
      >> ‘IS_SOME (substFn theta (RecdProj lval f,c))’ by metis_tac[]
      >> fs [IS_SOME_EXISTS])
  >- (qexists_tac
          ‘(MAP THE
               (MAP (λi. substFn theta (ArraySub lval (numLit i),c))
                  (COUNT_LIST dim)))’
      >> rw[LENGTH_COUNT_LIST]
      >> rw [MAP_MAP_o,EVERY_MEM,FORALL_PROD]
      >> rename1 ‘Contig_Lang theta c s’
      >> fs[MEM_COUNT_LIST]
      >> qpat_x_assum ‘$∀ M’ (irule o SIMP_RULE std_ss [IN_DEF])
      >> fs [MEM_MAP,MEM_COUNT_LIST]
      >> qexists_tac ‘y’
      >> fs [EVERY_MAP,every_count_list,IS_SOME_EXISTS]
      >> res_tac
      >> rw[])
  >- (qexists_tac ‘[]’ >> gvs[])
  >- (fs[IS_SOME_EXISTS]
       >> res_tac
       >> rename1 ‘h IN Contig_Lang theta c’
       >> rename1 ‘t IN Contig_Lang theta (List c)’
       >> rpt (WEAKEN_TAC is_forall)
       >> fs [IN_Contig_Lang]
       >> qexists_tac ‘STRING ConsTag h :: slist’
       >> rw[])
  >- metis_tac[]
  >- metis_tac[]
QED

Theorem Equiv2 :
  ∀theta c path s.
    s IN Contig_Lang theta c ==> ∃sigma. substFn sigma (path,c) = SOME s
Proof
 recInduct Contig_Lang_ind >> rpt conj_tac
  >- (rw[IN_Contig_Lang,substFn_def,AllCaseEqs()]
      >> qexists_tac ‘FEMPTY |+ (path, s)’ >> EVAL_TAC)
  >- rw[IN_Contig_Lang,substFn_def]
  >- (rw[IN_Contig_Lang,substFn_def,AllCaseEqs()] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      rw[IN_Contig_Lang,Once substFn_def,AllCaseEqs(),concatPartial_SOME]
      >> qpat_x_assum ‘∀s. _’ (mp_tac o Q.SPECL [‘s’,‘[s]’])
      >> rw[]
      >> fs [GSYM EVERY_MEM,EVERY_MAP,LAMBDA_PROD]
      >> ‘∃sigmas. EVERY (\n. substFn (EL n sigmas)
                               (path,SND (EL n fields)) = SOME (EL n slist))
                         (COUNT_LIST (LENGTH fields))’
       by  (* byA *)
       (rw[every_count_list] >>
        qexists_tac
          ‘GENLIST (\n. @sigma. substFn sigma (path,SND(EL n fields)) = SOME (EL n slist))
                   (LENGTH fields)’
        >> rw []
        >> SELECT_ELIM_TAC >> rw[]
        >> ‘∃fname c. EL n fields = (fname,c)’ by metis_tac [ABS_PAIR_THM]
        >> ‘MEM (fname,c) fields’ by metis_tac [EL_MEM]
        >> fs [EVERY_MEM]
        >> res_tac
        >> pop_assum mp_tac
        >> simp_tac std_ss []
        >> disch_then (mp_tac o Q.ID_SPEC)
        >> ‘LENGTH slist = LENGTH fields’ by metis_tac [LIST_REL_LENGTH,LENGTH_MAP]
        >> ‘MEM (EL n slist) slist’ by metis_tac [EL_MEM]
        >> fs [LIST_REL_EL_EQN]
        >> ‘EL n (MAP SND fields) = c’ by metis_tac[EL_MAP,SND]
        >> ‘EL n slist IN Contig_Lang theta c’ by metis_tac[]
        >> fs [FORALL_PROD]
       )
       >> qexists_tac ‘FEMPTY
            |++ MAP2 (\(fname,c) sigma.
                          (RecdProj path fname, THE (substFn sigma (path,c))))
                     fields sigmas’
       >> rw[EVERY_MEM,FORALL_PROD]
       >- (fs [every_count_list,IS_SOME_EXISTS]
           >> rename1 ‘MEM (fname,contig) fields’
           >> fs [MEM_EL,LIST_REL_EL_EQN]
           >> ‘EL n (MAP SND fields) = contig’ by metis_tac[EL_MAP,SND]
           >> rfs [FORALL_PROD,EL_MAP]
           >> ‘substFn (EL n sigmas) (path,contig) = SOME (EL n slist)’ by metis_tac[]
           >> qexists_tac ‘EL n slist’
           >>

QED
(*
Theorem Equiv2 :
  ∀theta c s.
    s IN Contig_Lang theta c ==> ∃theta lval. substFn theta (lval,c) = SOME s
Proof
 recInduct Contig_Lang_ind >> rpt conj_tac
  >- (rw[IN_Contig_Lang,substFn_def,AllCaseEqs()]
      >> qexists_tac ‘FEMPTY |+ (VarName "root", s)’
      >> EVAL_TAC
      >> metis_tac[])
  >- rw[IN_Contig_Lang,substFn_def]
  >- (rw[IN_Contig_Lang,substFn_def,AllCaseEqs()] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      rw[IN_Contig_Lang,Once substFn_def,AllCaseEqs(),concatPartial_SOME] >>
      qexists_tac ‘theta’ >>
      qpat_x_assum ‘∀s. _’ (mp_tac o Q.SPECL [‘s’,‘[s]’]) >> rw[]

QED
*)

Theorem Equiv :
  ∀c.
    {s | ∃theta. s IN Contig_Lang theta c}
    =
    {s | ∃theta. substFn theta (VarName"root",c) = SOME s}
Proof
 simp [EXTENSION]
  >> CONV_TAC (RENAME_VARS_CONV ["c","s"])
  >> recInduct Contig_Lang_ind
  >- (rw[IN_Contig_Lang,substFn_def,EQ_IMP_THM]
      >- (qexists_tac ‘FEMPTY |+ (VarName "root", s)’ >> EVAL_TAC >> metis_tac[])
      >- fs[AllCaseEqs()])
  >- rw[IN_Contig_Lang,substFn_def,EQ_IMP_THM]
  >- (rw[IN_Contig_Lang,substFn_def,EQ_IMP_THM,AllCaseEqs()] >> metis_tac[])
  >- rw[IN_Contig_Lang,substFn_def,EQ_IMP_THM,AllCaseEqs()]

 >> metis_tac[])
QED

(*---------------------------------------------------------------------------*)
(* Completeness                                                              *)
(*---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*)
(* Path extension is used to relate the satisfying theta from the assumption *)
(*                                                                           *)
(*  s IN Contig_Lang theta contig                                            *)
(*                                                                           *)
(* with the lval seeding the call to running matchFn:                        *)
(*                                                                           *)
(*  matchFn ([(lval,contig)],s,extend_paths lval theta)                      *)
(*                                                                           *)
(* The rationale is that the matcher is working relative to a give path.     *)
(* Initially this will be VarName "root", or some such, but could be anything*)
(* Since the domain of theta has no such "offset", each elt in fdom(theta)   *)
(* is extended by lval in the call to matchFn.                               *)
(*---------------------------------------------------------------------------*)

Definition extend_paths_def :
  extend_paths path theta = MAP_KEYS (lval_append path) theta
End

Definition extend_exp_locs_def :
  extend_exp_locs path (Loc lval) = Loc (lval_append path lval) ∧
  extend_exp_locs path (numLit n) = numLit n ∧
  extend_exp_locs path (Add e1 e2) =
      Add (extend_exp_locs path e1) (extend_exp_locs path e2)
End

Definition extend_bexp_locs_def :
  extend_bexp_locs path (boolLit b) = boolLit b ∧
  extend_bexp_locs path (BLoc lval) = BLoc (lval_append path lval) ∧
  extend_bexp_locs path (Bnot b) = Bnot (extend_bexp_locs path b) ∧
  extend_bexp_locs path (Bor b1 b2) =
      Bor (extend_bexp_locs path b1) (extend_bexp_locs path b2) ∧
  extend_bexp_locs path (Band b1 b2) =
      Band (extend_bexp_locs path b1) (extend_bexp_locs path b2) ∧
  extend_bexp_locs path (Beq e1 e2) =
      Beq (extend_exp_locs path e1) (extend_exp_locs path e2) ∧
  extend_bexp_locs path (Blt e1 e2) =
      Blt (extend_exp_locs path e1) (extend_exp_locs path e2)
End

val map_keys =   (* unused? *)
  MAP_KEYS_def
   |> Q.ISPEC ‘lval_append lval’
   |> Q.SPEC ‘theta’
   |> SIMP_RULE (srw_ss()) [inj_lval_append]
;

val map_keys_thm =
 FLOOKUP_MAP_KEYS_MAPPED
  |> C MATCH_MP (SPEC_ALL inj_lval_append_univs)


Theorem extend_exp_locs :
  ∀exp lval theta.
     evalExp (extend_paths lval theta) (extend_exp_locs lval exp) = evalExp theta exp
Proof
 simp[extend_paths_def] \\ Induct \\ rw[evalExp_def,extend_exp_locs_def,map_keys_thm]
QED

Theorem extend_bexp_locs :
  ∀bexp lval theta.
     evalBexp (extend_paths lval theta) (extend_bexp_locs lval bexp) = evalBexp theta bexp
Proof
 simp[extend_paths_def] \\ Induct \\
 rw[evalBexp_def,extend_bexp_locs_def,extend_exp_locs,map_keys_thm] \\
 rw[GSYM extend_paths_def,extend_exp_locs]
QED

Definition extend_contig_locs_def :
  extend_contig_locs path (Basic a) = Basic a ∧
  extend_contig_locs path Void      = Void ∧
  extend_contig_locs path (Assert b) =
       Assert (extend_bexp_locs path b) ∧
  extend_contig_locs path (Recd fields) =
       Recd (MAP (\(fName,c). (fName, extend_contig_locs path c)) fields) ∧
  extend_contig_locs path (Array c e) =
       Array (extend_contig_locs path c)
             (extend_exp_locs path e) ∧
  extend_contig_locs path (List c) =
       List (extend_contig_locs path c) ∧
  extend_contig_locs path (Alt b c1 c2) =
       Alt (extend_bexp_locs path b)
           (extend_contig_locs path c1)
           (extend_contig_locs path c2)
Termination
 WF_REL_TAC ‘measure (contig_size o SND)’ \\
 rw [contig_size_def,MEM_MAP] \\
 imp_res_tac contig_size_lem \\ decide_tac
End

Triviality null_lem :
 ∀list. list = [] ∨ ∃e. MEM e list
Proof
 Cases \\ rw[] >> metis_tac []
QED

Theorem comp_lem1 :
 !theta contig lval s.
    s IN Contig_Lang theta contig
   ==>
    ∃sigma.
      matchFn ([(lval,extend_contig_locs lval contig)],s,extend_paths lval theta)
      =
      SOME ("", sigma) ∧
      SUBMAP theta sigma
Proof
 recInduct Contig_Lang_ind \\ rpt conj_tac
 >- (rw[IN_Contig_Lang,Once matchFn_def,extend_contig_locs_def,
        AllCaseEqs(),EXISTS_PROD,take_drop_thm]
     \\ CONV_TAC (RESORT_EXISTS_CONV
                   (K [“p_1:string”, “p_2:string”, “sigma:lval |-> atom # string”]))
     \\ qexists_tac ‘s’ \\ qexists_tac ‘""’ \\ rw[]
     \\ rw[RIGHT_EXISTS_AND_THM]
     >- (rw[extend_paths_def,MAP_KEYS_def] \\ metis_tac[lval_append_acyclic])
     >- rw[matchFn_def])

 >- rw[IN_Contig_Lang,matchFn_def,AllCaseEqs(),EXISTS_PROD,
        extend_paths_def,take_drop_thm,MAP_KEYS_def]
 >- (rw[IN_Contig_Lang,Once matchFn_def,AllCaseEqs(),EXISTS_PROD,
        take_drop_thm,extend_bexp_locs,extend_contig_locs_def]
     \\ rw[matchFn_def])
 >- (rpt gen_tac \\ strip_tac \\
     rw[IN_Contig_Lang,Once matchFn_def,AllCaseEqs(),EXISTS_PROD,
        take_drop_thm,extend_bexp_locs,extend_contig_locs_def] \\
     rw[MAP_MAP_o,fieldFn_def] \\ gvs[LIST_REL_EL_EQN] \\
     mp_tac (null_lem |> Q.ISPEC ‘slist:string list’) \\ rw[]
     >- (gvs[] >> rw [matchFn_def])
     >- (‘∃sigmas. EVERY (\n. substFn (EL n sigmas)
                               (path,SND (EL n fields)) = SOME (EL n slist))
                         (COUNT_LIST (LENGTH fields))’

gvs [MEM_EL] \\
         ‘EL n slist IN Contig_Lang theta (EL n (MAP SND fields))’ by metis_tac[] \\
         qpat_x_assum ‘∀n. _ ==> _’ kall_tac  \\
         first_x_assum (mp_tac o
           Q.SPECL [‘EL n slist’, ‘slist’,
                    ‘EL n (MAP SND (fields:(string#contig)list))’]) \\
         rw[PULL_EXISTS] \\ first_x_assum drule >> rw[] \\
         first_x_assum drule >> rw[] \\
         first_x_assum drule >> rw[] \\

MEM_EL and SUBSET_SKOLEM

         ‘MEM (EL k slist) slist ∧ MEM (EL k ’

LIST_REL_CONJ
LIST_REL_EL_EQN
LIST_REL_MAP2

     \\ rw[matchFn_def])

QED



val _ = export_theory();
