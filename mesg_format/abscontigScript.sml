open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib regexpLib ASCIInumbersLib;

open pairTheory arithmeticTheory listTheory rich_listTheory
     stringTheory combinTheory optionTheory ASCIInumbersTheory
     numposrepTheory FormalLangTheory;

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
(* Some support definitions                                                  *)
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


Definition concatPartial_def :
  concatPartial optlist =
    case concatPartial_acc optlist []
     of NONE => NONE
      | SOME list => SOME (FLAT (REVERSE list))
End

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
       | Signed num
       | Unsigned num
End

Datatype:
  contig = Basic atom
         | Recd ((string # contig) list)
         | Array contig exp
         | Alt bexp contig contig
End

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
(* Location completion                                                       *)
(*---------------------------------------------------------------------------*)

Definition lval_append_def :
  lval_append path (VarName s) = RecdProj path s /\
  lval_append path (RecdProj q s) = RecdProj (lval_append path q) s /\
  lval_append path (ArraySub q dim) = ArraySub (lval_append path q) dim
End

Definition path_prefixes_def :
  path_prefixes (VarName s) = [VarName s] /\
  path_prefixes (RecdProj p s) = (RecdProj p s) :: path_prefixes p /\
  path_prefixes (ArraySub (VarName s) dim) = [ArraySub (VarName s) dim] /\
  path_prefixes (ArraySub (RecdProj p s) dim) = ArraySub (RecdProj p s) dim :: path_prefixes p /\
  path_prefixes (ArraySub arr dim) = ArraySub arr dim :: path_prefixes arr
End

(*---------------------------------------------------------------------------*)
(* Attempt to extend a partial lval to something in the lvalMap.             *)
(*---------------------------------------------------------------------------*)

Definition resolve_lval_def :
 resolve_lval lvalMap path lval =
   let prefixes = path_prefixes path ;
       prospects = MAP (combin$C lval_append lval) prefixes ++ [lval] ;
   in optFirst (\p. FLOOKUP lvalMap p) prospects
End

Definition resolveExp_def:
 resolveExp lvmap p (numLit n) = SOME (numLit n) /\
 resolveExp lvmap p (Loc lval) =
    (case resolve_lval lvmap p lval
      of NONE => NONE
       | SOME full_lv => SOME (Loc full_lv)) /\
 resolveExp lvmap p (Add e1 e2) =
    (case resolveExp lvmap p e1
      of NONE => NONE
       | SOME e1' =>
     case resolveExp lvmap p e2
      of NONE => NONE
       | SOME e2' => SOME (Add e1' e2'))
End

Definition resolveBexp_def :
 resolveBexp lvmap p (boolLit b) = SOME (boolLit b) /\
 resolveBexp lvmap p (BLoc lval) =
    (case resolve_lval lvmap p lval
      of NONE => NONE
       | SOME lval' => SOME (BLoc lval')) /\
 resolveBexp lvmap p (Bnot b)    =
    (case resolveBexp lvmap p b
      of NONE => NONE
       | SOME b' =>  SOME (Bnot b')) /\
 resolveBexp lvmap p (Bor b1 b2) =
    (case resolveBexp lvmap p b1
      of NONE => NONE
       | SOME b1' =>
     case resolveBexp lvmap p b2
      of NONE => NONE
       | SOME b2' => SOME (Bor b1' b2')) /\
 resolveBexp lvmap p (Band b1 b2) =
    (case resolveBexp lvmap p b1
      of NONE => NONE
       | SOME b1' =>
     case resolveBexp lvmap p b2
      of NONE => NONE
       | SOME b2' => SOME (Band b1' b2')) /\
 resolveBexp lvmap p (Beq e1 e2) =
    (case resolveExp lvmap p e1
      of NONE => NONE
       | SOME e1' =>
     case resolveExp lvmap p e2
      of NONE => NONE
       | SOME e2' => SOME (Beq e1' e2')) /\
 resolveBexp lvmap p (Blt e1 e2) =
    (case resolveExp lvmap p e1
      of NONE => NONE
       | SOME e1' =>
     case resolveExp lvmap p e2
      of NONE => NONE
       | SOME e2' => SOME (Blt e1' e2'))
End

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
     tdrop n list acc = SOME (acc',suf) ⇒ acc' ++ suf = REVERSE acc ++ list
Proof
 recInduct tdrop_ind >> rw [tdrop_def]
QED

Definition take_drop_def :
  take_drop n list = tdrop n list []
End

Theorem take_drop_thm :
  ∀n list.
      take_drop n list = SOME (pref,suf) ⇒ pref ++ suf = list
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

(*---------------------------------------------------------------------------*)
(* Size of a contig. The system-generated contig_size goes through a lot of  *)
(* other types, including field names, and those shouldn't be counted because*)
(* field name size shouldn't count in the size of the expression.            *)
(*---------------------------------------------------------------------------*)

val contig_size_def = fetch "-" "contig_size_def";

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
 predFn (atomWidths,valFn) (worklist,s,theta) =
  case worklist
   of [] => T
    | (lval,Basic a)::t =>
        (case take_drop (atomWidths a) s
           of NONE => F
            | SOME (segment,rst) =>
              predFn (atomWidths,valFn) (t, rst, theta |+ (lval,segment)))
   | (lval,Recd fields)::t =>
       predFn (atomWidths,valFn) (MAP (fieldFn lval) fields ++ t,s,theta)
   | (lval,Array c exp)::t =>
       (case evalExp (theta,valFn) exp
         of NONE => F
          | SOME dim =>
            predFn (atomWidths,valFn)
                   (MAP (indexFn lval c) (upto 0 (dim - 1)) ++ t,s,theta))
   | (lval,Alt bexp c1 c2)::t =>
       case evalBexp (theta,valFn) bexp
        of NONE => F
         | SOME T => predFn (atomWidths,valFn) ((lval,c1)::t,s,theta)
         | SOME F => predFn (atomWidths,valFn) ((lval,c2)::t,s,theta)
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
 matchFn (atomicWidths,valFn) (worklist,s,theta) =
 case worklist
  of [] => SOME (s,theta)
   | (lval,Basic a)::t =>
       (case take_drop (atomicWidths a) s
         of NONE => NONE
          | SOME (segment,rst) =>
        if lval IN FDOM theta then
            NONE
        else matchFn (atomicWidths,valFn) (t, rst, theta |+ (lval,segment)))
   | (lval,Recd fields)::t =>
        matchFn (atomicWidths,valFn)
                (MAP (fieldFn lval) fields ++ t,s,theta)
   | (lval,Array c exp)::t =>
       (case evalExp (theta,valFn) exp
         of NONE => NONE
          | SOME dim =>
             matchFn (atomicWidths,valFn)
                     (MAP (indexFn lval c) (upto 0 (dim - 1)) ++ t,s,theta))
   | (lval,Alt bexp c1 c2)::t =>
       case evalBexp (theta,valFn) bexp
        of NONE => NONE
         | SOME T => matchFn (atomicWidths,valFn) ((lval,c1)::t,s,theta)
         | SOME F => matchFn (atomicWidths,valFn) ((lval,c2)::t,s,theta)
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
 substFn valFn theta (lval,contig) =
  case contig
   of Basic _  => FLOOKUP theta lval
    | Recd fields =>
       concatPartial
         (MAP (\(fName,c). substFn valFn theta (RecdProj lval fName,c)) fields)
    | Array c exp =>
       (case evalExp (theta,valFn) exp
         of NONE => NONE
          | SOME dim =>
            concatPartial
               (MAP (\i. substFn valFn theta (ArraySub lval (numLit i), c))
                    (upto 0 (dim - 1))))
    | Alt bexp c1 c2 =>
       (case evalBexp (theta,valFn) bexp
         of NONE => NONE
          | SOME T => substFn valFn theta (lval,c1)
          | SOME F => substFn valFn theta (lval,c2))
Termination
 WF_REL_TAC `measure (csize o SND o SND o SND)`
   >> rw [csize_def]
   >- (Induct_on `fields`  >> rw[list_size_def] >> rw[] >> fs[])
End

Definition substWk_def :
 substWk valFn theta wklist = concatPartial (MAP (substFn valFn theta) wklist)
End

Theorem match_submap :
  !atomicWidths valFn wklist s theta s2 theta'.
   matchFn (atomicWidths,valFn) (wklist,s,theta) = SOME (s2, theta')
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
 ∀e valFn theta1 theta2 v.
   theta1 SUBMAP theta2 ∧
   evalExp(theta1,valFn) e = SOME v
   ⇒
   evalExp(theta2,valFn) e = SOME v
Proof
Induct
 >> rw [evalExp_def]
 >> every_case_tac >> fs []
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11]
QED

Theorem evalBexp_submap :
 ∀bexp valFn theta1 theta2 v.
   theta1 SUBMAP theta2 ∧
   evalBexp(theta1,valFn) bexp = SOME v
   ⇒
   evalBexp(theta2,valFn) bexp = SOME v
Proof
Induct
 >> rw [evalBexp_def]
 >> every_case_tac
 >> fs []
 >> metis_tac[FLOOKUP_SUBMAP,NOT_SOME_NONE,SOME_11,evalExp_submap]
QED


Theorem match_lem :
!atomicWidths valFn wklist (s:string) theta s2 theta'.
   matchFn (atomicWidths,valFn) (wklist,s,theta) = SOME (s2, theta')
   ==>
   ?s1. substWk valFn theta' wklist = SOME s1 /\  s1 ++ s2 = s
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
   >- (‘theta SUBMAP theta'’ by metis_tac [match_submap] >>
       ‘evalExp (theta',valFn) e = SOME x’ by metis_tac [evalExp_submap]
       >> rw[Once substFn_def]
       >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,indexFn_def,LAMBDA_PROD,IS_SOME_NEG]
       >> rw []
       >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
       >> metis_tac [NOT_EXISTS])
   >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
       >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
       >> rw[]
       >> ‘evalBexp (theta',valFn) b = SOME T’ by metis_tac [evalBexp_submap]
       >> rw[Once substFn_def]
       >> every_case_tac
       >> rw [])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
        >> rw[]
        >> ‘evalBexp (theta',valFn) b = SOME F’ by metis_tac [evalBexp_submap]
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
        ‘evalExp (theta',valFn) e = SOME x’ by metis_tac [evalExp_submap]
        >> rw[Once substFn_def]
        >> fs [concatPartial_thm,MAP_MAP_o, combinTheory.o_DEF,indexFn_def,LAMBDA_PROD,IS_SOME_NEG]
        >> rw []
        >> fs [GSYM (SIMP_RULE std_ss [o_DEF] NOT_EXISTS)]
        >> metis_tac [NOT_EXISTS])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
        >> rw[]
        >> ‘evalBexp (theta',valFn) b = SOME T’ by metis_tac [evalBexp_submap]
        >> rw[Once substFn_def]
        >> every_case_tac
        >> rw [])
    >- (‘theta SUBMAP theta'’ by metis_tac [match_submap]
        >> ‘∃lval bexp. lval = q ∧ bexp = q'’ by metis_tac[]
        >> rw[]
        >> ‘evalBexp (theta',valFn) b = SOME F’ by metis_tac [evalBexp_submap]
        >> rw[Once substFn_def]
        >> every_case_tac
        >> rw [])
QED

Theorem match_sound :
!atomicWidths valFn wklist (s:string) theta s2 theta'.
   matchFn (atomicWidths,valFn) (wklist,s,theta) = SOME (s2, theta')
   ==>
     THE (substWk valFn theta' wklist) ++ s2 = s
Proof
 metis_tac [match_lem,optionTheory.THE_DEF]
QED

val _ = export_theory();
