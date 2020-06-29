open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib regexpLib ASCIInumbersLib;

open arithmeticTheory listTheory rich_listTheory
     stringTheory combinTheory ASCIInumbersTheory
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

Definition optFirst_def :
  optFirst f [] = NONE /\
  optFirst f (h::t) =
    case f h
     of NONE => optFirst f t
      | SOME x => SOME h
End

Definition concatOpt_def :
 concatOpt optlist  =
    if EXISTS (\x. x=NONE) optlist
       then NONE
    else SOME (CONCAT (MAP THE optlist))
End

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
      | Mult exp exp
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
  contig = Void
         | Basic atom
         | Recd ((string # contig) list)
         | Array contig exp
         | Union ((bexp # contig) list)
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
     |  SOME n1 =>
    case evalExp E e2
     of NONE => NONE
      | SOME n2 => SOME (n1+n2)) /\
 evalExp E (Mult e1 e2) =
   (case evalExp E e1
     of NONE => NONE
      | SOME n1 =>
    case evalExp E e2
     of NONE => NONE
      | SOME n2 => SOME (n1 * n2))
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
       | SOME e2' => SOME (Add e1' e2')) /\
 resolveExp lvmap p (Mult e1 e2) =
    (case resolveExp lvmap p e1
      of NONE => NONE
       | SOME e1' =>
     case resolveExp lvmap p e2
      of NONE => NONE
       | SOME e2' => SOME (Mult e1' e2'))
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
  (csize Void            = 0) /\
  (csize (Basic a)       = 0) /\
  (csize (Recd fields)   = 1 + list_size (\(a,c). csize  c) fields) /\
  (csize (Array c dim)   = 1 + csize c) /\
  (csize (Union choices) = 1 + list_size (\(b,c). csize c) choices)
Termination
  WF_REL_TAC `measure contig_size`
  >> rw_tac list_ss [contig_size_def]
  >- (Induct_on `choices`
        >> rw_tac list_ss [contig_size_def]
        >> full_simp_tac list_ss [contig_size_def])
  >- (Induct_on `fields`
        >> rw_tac list_ss [contig_size_def]
        >> full_simp_tac list_ss [contig_size_def])
End

Triviality list_size_append :
 !L1 L2 f. list_size f (L1 ++ L2) = (list_size f L1 + list_size f L2)
Proof
 Induct_on ‘L1’ >> rw_tac list_ss [list_size_def]
QED

(*---------------------------------------------------------------------------*)
(* contig-specified predicate on strings.                                    *)
(*---------------------------------------------------------------------------*)

Definition predFn_def :
 predFn (atomWidths,valFn) (worklist,s,theta) =
  case worklist
   of [] => T
    | (path,Void)::t => F
    | (path,Basic a)::t =>
        (case take_drop (atomWidths a) s
           of NONE => F
            | SOME (segment,rst) =>
              predFn (atomWidths,valFn) (t, rst, theta |+ (path,segment)))
   | (path,Recd fields)::t =>
      let fieldFn (fName,c) = (RecdProj path fName,c)
      in predFn (atomWidths,valFn)
                (MAP fieldFn fields ++ t,s,theta)
   | (path,Array c exp)::t =>
      (case resolveExp theta path exp
        of NONE => F
         | SOME exp' =>
       let dim  = THE (evalExp (theta,valFn) exp');
           indexFn n = (ArraySub path (numLit n),c)
       in predFn (atomWidths,valFn)
                 (MAP indexFn (upto 0 (dim - 1)) ++ t,s,theta))
   | (path,Union choices)::t =>
       let choiceFn (bexp,c) =
            (case resolveBexp theta path bexp
              of NONE => F
               | SOME bexp' => THE (evalBexp (theta,valFn) bexp'))
       in case FILTER choiceFn choices
           of [(_,c)] => predFn (atomWidths,valFn) ((path,c)::t,s,theta)
            | otherwise => F
Termination
 WF_REL_TAC `inv_image (mlt_list (measure (csize o SND))) (FST o SND)`
   >> rw [APPEND_EQ_SELF]
   >> rw [csize_def]
   >> fs [MEM_MAP,MEM_SPLIT]
   >- (Cases_on `y` >> fs[list_size_append,list_size_def])
   >- fs [FILTER_EQ_CONS,list_size_append,list_size_def]
End

(*
fun wellformed E contig s = predFn E ([(VarName"root",contig)],s,empty_lvalMap);
*)

(*---------------------------------------------------------------------------*)
(* Apply a substitution to a contig.                                         *)
(*---------------------------------------------------------------------------*)

Definition substFn_def :
 substFn valFn theta path contig =
  case contig
   of Void     => NONE
    | Basic _  => FLOOKUP theta path
    | Recd fields =>
       concatOpt
         (MAP (\(fName,c). substFn valFn theta (RecdProj path fName) c)
              fields)
    | Array c exp =>
        (case resolveExp theta path exp
          of NONE => NONE
           | SOME exp' =>
         let dim = THE (evalExp (theta,valFn) exp')
         in concatOpt (MAP (\i. substFn valFn theta (ArraySub path (numLit i)) c)
                      (upto 0 (dim - 1))))
    | Union choices =>
       let choiceFn (bexp,c) =
            (case resolveBexp theta path bexp
              of NONE => F
               | SOME bexp' => THE (evalBexp (theta,valFn) bexp'))
        in
           case FILTER choiceFn choices
            of [(_,c)] => substFn valFn theta path c
             |  otherwise => NONE
Termination
 WF_REL_TAC `measure (csize o SND o SND o SND)`
   >> rw [csize_def]
   >- (Induct_on `choices` >> rw[list_size_def] >> fs[])
   >- (Induct_on `fields` >> rw[list_size_def] >> rw[] >> fs[])
End


Definition matchFn_def :
 matchFn (atomicWidths,valFn) (worklist,s,theta) =
 case worklist
  of [] => SOME (s,theta)
   | (_,Void)::_ => NONE
   | (path,Basic a)::t =>
       (case take_drop (atomicWidths a) s
         of NONE => NONE
          | SOME (segment,rst) =>
              matchFn (atomicWidths,valFn) (t, rst, theta |+ (path,segment)))
   | (path,Recd fields)::t =>
       (let fieldFn (fName,c) = (RecdProj path fName,c)
        in matchFn (atomicWidths,valFn)
                   (MAP fieldFn fields ++ t,s,theta))
   | (path,Array c exp)::t =>
       (let indexFn n = (ArraySub path (numLit n),c)
        in case resolveExp theta path exp
            of NONE => NONE
             | SOME exp' =>
           let dim = THE (evalExp (theta,valFn) exp')
           in matchFn (atomicWidths,valFn)
                      (MAP indexFn (upto 0 (dim - 1)) ++ t,s,theta))
   | (path,Union choices)::t =>
       (let choiceFn (bexp,c) =
            case resolveBexp theta path bexp
             of NONE => F
              | SOME bexp' => THE (evalBexp (theta,valFn) bexp')
        in case FILTER choiceFn choices
            of [(_,c)] => matchFn (atomicWidths,valFn) ((path,c)::t,s,theta)
             | otherwise => NONE)
Termination
 WF_REL_TAC `inv_image (mlt_list (measure (csize o SND))) (FST o SND)`
   >> rw [APPEND_EQ_SELF]
   >> rw [csize_def]
   >> fs [MEM_MAP,MEM_SPLIT]
   >- (Cases_on `y` >> fs[list_size_append,list_size_def])
   >- fs [FILTER_EQ_CONS,list_size_append,list_size_def]
End


(* match E contig s = matchFn E ([(VarName"root",contig)],s,empty_lvalMap); *)

g `!atomicWidths valFn wklist s theta path contig s2 theta'.
   (wklist = [(path,contig)]) ==>
   matchFn (atomicWidths,valFn) (wklist,s,theta) = SOME (s2, theta')
   ==>
   THE (substFn valFn theta' path contig) ++ s2 = s`

  recInduct matchFn_ind >> rpt gen_tac >> strip_tac >>
  rw_tac list_ss [Once matchFn_def] >>
  every_case_tac >> rw[]
  >- (full_simp_tac list_ss [matchFn_def,Once substFn_def] >>
      rw[] >>
      fs[FLOOKUP_UPDATE] >>
      metis_tac [take_drop_thm])
  >- (Induct_on ‘l’  >> rw[]
      >- (full_simp_tac list_ss [matchFn_def,Once substFn_def]
          rw[concatOpt_def])
      >- (namedCases_on ‘h’ ["fName c"] >>
          full_simp_tac list_ss [] >>
          full_simp_tac list_ss [Once matchFn_def,Once substFn_def] >>
          rw[])
;



(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* Set up lval-map support                                                    *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val empty_lvMap = “mlmap$empty lval_compare”;

val _ = export_theory();
