(* A theory about parse trees *)
open HolKernel boolLib bossLib Parse Defn

open stringTheory grammarDefTheory regexpTheory listTheory pairTheory
optionTheory

open listLemmasTheory

val _ = new_theory "parseTree";

val _ = Hol_datatype 
`ptree = Leaf of string | Node of string => ptree list`;

val ptree2Sym = Define 
`(ptree2Sym (Node nt ptl) = NTS nt) /\
(ptree2Sym (Leaf tm) = TS tm)`

val isNode = Define `(isNode (Node _ _) = T) /\
(isNode (Leaf _) = F)`

val isLeaf = Define `(isLeaf (Node _ _) = F) /\
(isLeaf (Leaf _) = T)`

val ptsize_def = Define`  (ptsize (Leaf tmnl) = 1) 
/\  (ptsize (Node nt ptlist) = 1 + ptsizel ptlist) 
/\  (ptsizel [] = 0) 
/\     (ptsizel (h::t) = ptsize h + ptsizel t) `
val _ = BasicProvers.export_rewrites ["ptsize_def"]

val ptheight_def = Define`  (ptheight (Leaf tmnl) = 0) 
/\  (ptheight (Node nt ptlist) = 1 + ptheightl ptlist) 
/\  (ptheightl [] = 0) 
/\     (ptheightl (h::t) = ptheight h + ptheightl t) `

val ptsize_better = prove(
  ``ptsize (Node nt ptlist) = 1 + SUM (MAP ptsize ptlist)``,
  SRW_TAC [][] THEN Induct_on `ptlist` THEN
  SRW_TAC [][]);

val ptsizel_append = store_thm ("ptsizel_append",
``ptsizel (l1++l2) = ptsizel l1 + ptsizel l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [ptsize_def] THEN
DECIDE_TAC)


val size_nonzero = prove(
  ``!pt. ptsize pt > 0``,
  Induct THENL [
    SRW_TAC [][ptsize_def],
    SRW_TAC [numSimps.ARITH_ss][ptsize_def]
  ]);

(* <<HOL warning: Type.mk_type: more than one possibility>>
<<HOL message: Defined type: "option">> *)

(* fun parseTreeToRule :: ptree => rule *)

(* ptreeToRule :: ptree => [symbol, [symbol]] *)

(* try checking the rules while recursing over the tree + using sets
in HOL rather than converting to list *)

val getSymbols = Define `(getSymbols [] = []) /\ 
(getSymbols [Leaf tmnl] = [TS tmnl]) /\ 
(getSymbols [Node nt ptlist] = [NTS nt]) /\ 
(getSymbols ((Leaf tmnl)::t) = 
(TS tmnl) :: (getSymbols t)) /\ 
(getSymbols ((Node nt ptlist)::t) = 
(NTS nt) :: (getSymbols t))`;

val ptreeToRules = 
Define `(ptreeToRules (Leaf tmnl) = []) /\
(ptreeToRules (Node nt ptlist) = 
(rule nt (getSymbols ptlist)) :: (ptreeToRules2 ptlist)) /\ 
(ptreeToRules2 [] = []) /\ 
(ptreeToRules2 (h::t) = (ptreeToRules h) ++ (ptreeToRules2 t))`;


(* This should be checking against an actual rule format rather than a string format!!!! *)
val checkRules = Define `(checkRules [] rls = T) /\ 
(checkRules (h::t) rls = (MEM h rls) /\ checkRules t rls)`;

(* val validptree = Define `(validptree pt g = (checkRules (ptreeToRules pt) (rules g)))`;*)

val ptreeNodeSym = Define 
`(ptreeNodeSym (Node  nt tl) = NTS nt) /\
(ptreeNodeSym (Leaf tm) = TS tm)`

val ptreeSubtSyms = Define 
`(ptreeSubtSyms (Node nt tl) = MAP ptreeNodeSym tl) /\
(ptreeSubtSyms (Leaf  tm) = [])`

val ptreeSubtree = Define 
`(ptreeSubtree (Node x l) = l) /\
(ptreeSubtree (Leaf tm) = [])`

val validptree_defn = Hol_defn "validptree_defn" 
    `(validptree g (Node n ptl) =
      MEM (rule n (getSymbols ptl)) (rules g) /\
      (!e.MEM e ptl ==> isNode e ==> validptree g e)) /\
(validptree g (Leaf tm) = F)`

val (validptree, validptree_ind) = tprove (validptree_defn,
WF_REL_TAC (`measure (\(g,e).ptsize e)`) THEN
SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ptsizel_append] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [ptsize_def] THEN
DECIDE_TAC)

val _ = save_thm ("validptree",validptree)
val _ = save_thm ("validptree_ind",validptree_ind)


val leaves_def = Define 
`(leaves (Leaf tmnl) = [TS tmnl]) /\ 
(leaves (Node nt ptlist) =  cleaves ptlist) /\ 
(cleaves [] = []) /\ (cleaves (h::t) = leaves h ++ cleaves t)`;


val flat_leaves = store_thm("flat_leaves", 
``!l.(leaves (Node n l)) = FLAT (MAP leaves l)``,
Induct_on `l` THEN SRW_TAC [] [leaves_def, MAP, FLAT] THEN
METIS_TAC [leaves_def])

val getSyms_append = store_thm ("getSyms_append", 
``getSymbols (l1++l2) = getSymbols l1 ++ getSymbols l2``,
Induct_on `l1` THEN SRW_TAC [] [getSymbols] THEN
Cases_on `h` THEN SRW_TAC [] [getSymbols] THEN
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [getSymbols]
)

val getSymsEqptree2sym = store_thm ("getSymsEqptree2Sym", 
``getSymbols l = MAP (ptree2Sym) l``,
Induct_on `l` THEN SRW_TAC [] [getSymbols] THEN
`getSymbols (h::l) = getSymbols [h] ++ getSymbols l` by METIS_TAC [getSyms_append, APPEND] THEN
Cases_on `h` THEN Cases_on `l` THEN 
METIS_TAC [ptree2Sym, getSymbols]
)

val mapSymsptree = store_thm ("mapSymsptree",
``MAP (ptree2Sym o SND) p = getSymbols (MAP SND p)``,
Induct_on `p` THEN SRW_TAC [] [getSymbols] THEN
Cases_on `h` THEN Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [getSymbols, ptree2Sym, SND] THEN
Induct_on `MAP SND p` THEN 
METIS_TAC [getSyms_append, getSymsEqptree2sym, getSymbols])


val getSyms_len = store_thm ("getSyms_len",
``!l.LENGTH l = LENGTH (getSymbols l)``,
Induct_on `l` THEN SRW_TAC [] [getSymbols, LENGTH] THEN
Cases_on `h` THEN Induct_on `l` THEN 
SRW_TAC [] [getSymbols, LENGTH])

val take1_getSyms = store_thm ("take1_getSyms",
``!l n.(LENGTH l >= n) ==> 
(take1 n (getSymbols l) = getSymbols (take1 n l))``,
Induct_on `n` THEN Induct_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [take1, getSymbols] THENL[

Cases_on `h` THEN 
Induct_on `l` THEN FULL_SIMP_TAC (srw_ss()) [take1, getSymbols],
FULL_SIMP_TAC (arith_ss) [],
`LENGTH l >= n` by FULL_SIMP_TAC (arith_ss) [] THEN
RES_TAC THEN
`getSymbols (h::l) = getSymbols [h] ++ getSymbols l` by METIS_TAC [APPEND, getSyms_append] THEN
SRW_TAC [] [] THEN

Cases_on `h` THEN
FULL_SIMP_TAC (arith_ss) [take1, getSymbols] THENL[

`take1 (SUC n) ([(TS (tmnlToStr t))]++ getSymbols l) = 
take1 (SUC n) (TS (tmnlToStr t) :: getSymbols l)` by METIS_TAC [APPEND] THEN
SRW_TAC [] [take1] THEN
Induct_on `take1 n l` THEN METIS_TAC [getSymbols, take1, APPEND],

`take1 (SUC n) ([(NTS (nonTmnlToStr n'))]++ getSymbols l) = 
take1 (SUC n) (NTS (nonTmnlToStr n') :: getSymbols l)` by METIS_TAC [APPEND] THEN
SRW_TAC [] [take1] THEN
Induct_on `take1 n l` THEN METIS_TAC [getSymbols, take1, APPEND]
]])


val take_getSyms = store_thm ("take_getSyms",
``!n l.(take n (MAP SND l) = SOME x) ==> 
(THE (take n  (getSymbols (MAP SND l))) = getSymbols (THE (take n (MAP SND l))))``,
Induct_on `l` THEN SRW_TAC [] [] THENL[
Induct_on `n` THEN FULL_SIMP_TAC (srw_ss()) [take_def, getSymbols] THENL[
METIS_TAC [getSymbols, take10],
SRW_TAC [] [] THEN FULL_SIMP_TAC (arith_ss) [take10]],
`LENGTH (SND h::MAP SND l) >= n` by METIS_TAC [take_len, NOT_SOME_NONE] THEN
Cases_on `n` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (arith_ss) [] THEN METIS_TAC [take0, THE_DEF, take10],
FULL_SIMP_TAC (srw_ss()) [take_def] THEN
`LENGTH (getSymbols (SND h::MAP SND l)) = LENGTH (SND h::MAP SND l)` by 
METIS_TAC [getSyms_len] THEN
`LENGTH l = LENGTH (MAP SND l)` by METIS_TAC [LENGTH_MAP] THEN
`SUC (LENGTH l) = LENGTH (SND h::MAP SND l)` by METIS_TAC [LENGTH] THEN
`LENGTH (getSymbols (SND h::MAP SND l)) >= SUC n'` by METIS_TAC [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [take1_getSyms]]])


val checkRules_append = store_thm("checkRules_append", 
``checkRules (l1++l2) rs = checkRules l1 rs /\ checkRules l2 rs``,
SRW_TAC [] [EQ_IMP_THM] THENL[
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [checkRules],
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [checkRules],
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [checkRules]]
)

val ptreeToRules_append = store_thm ("ptreeToRules_append", 
``ptreeToRules2 (l1++l2) = ptreeToRules2 l1 ++ ptreeToRules2 l2``,
Induct_on `l1` THEN SRW_TAC [] [ptreeToRules]
)


val getSyms_nil = store_thm ("getSyms_nil", 
``(getSymbols l = []) ==> (l=[])``,
Induct_on `l` THEN SRW_TAC [] [getSymbols] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getSymbols] THEN
Induct_on `l` THEN
METIS_TAC [NULL, getSymbols])

val getSyms_rev = store_thm ("getSyms_rev",
``getSymbols (REVERSE x) = REVERSE (getSymbols x)``,
Induct_on `x` THEN SRW_TAC [] [REVERSE_DEF, getSymbols] THEN
FULL_SIMP_TAC (srw_ss()) [getSyms_append] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols] THEN
Induct_on `x` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols]
)

val mlDir = ref ("./theoryML/");

val _ =
 let open EmitML
 in emitML (!mlDir)
   ("parseTree",
OPEN ["num", "regexp"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: DATATYPE `ptree = Leaf of string | Node of string => ptree list`
    :: DEFN ptree2Sym
    :: [])
 end;

val _ = export_theory ();

