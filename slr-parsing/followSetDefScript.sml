open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory

open regexpTheory grammarDefTheory listLemmasTheory firstSetDefTheory

val _ = new_theory "followSetDef"

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w)

val _ = set_trace "Unicode" 1;

val _ = Globals.linewidth := 60



val followSet = Define 
`followSet g sym = 
{ TS ts | ∃s.MEM s (MAP ruleRhs (rules g)) ∧ 
          ∃pfx sfx.RTC (derives g) s (pfx++[sym]++[TS ts]++sfx) }`

val followRuleML_defn = Hol_defn "followRuleML_defn"
`(followRuleML g sn sym (rule l []) = {}) ∧
(followRuleML g sn sym (rule l (h::t)) = 
if (~(MEM sym sn) ∧ sym ∈ (allSyms g)) then
    if ((NTS l) IN (nonTerminalsML g)) then
	if (h=sym) then
	      LIST_TO_SET (firstSet1 g [] t) ∪ 
              followRuleML g sn sym (rule l t) ∪
	     (if nullableML g [] t then 
		BIGUNION (LIST_TO_SET 
	            (MAP (followRuleML g (sym::sn) (NTS l)) 
                      (rules g))) 
              else {})
	else followRuleML g sn sym (rule l t)
    else {}
else {})`


val (followRuleML,followRuleML_ind) = 
tprove (followRuleML_defn,
WF_REL_TAC (`inv_image  (((measure (\(g,sn). CARD ((allSyms g) DIFF (LIST_TO_SET sn))))) LEX (measure (\r.LENGTH (ruleRhs r)))) (\(g,sn,sym,r).(g,sn),r)`) THEN
SRW_TAC [] [] THEN
`FINITE (allSyms g)` 
    by METIS_TAC [FINITE_LIST_TO_SET,finiteAllSyms] THEN
SRW_TAC [] [FINITE_INSERT,FINITE_LIST_TO_SET] 
THENL[

      `sym ∈ allSyms g` by METIS_TAC [symInGr] THEN
      `((allSyms g) ∩ (sym INSERT set sn)) 
         = ((sym INSERT set sn) ∩ (allSyms g))` 
	  by METIS_TAC [INTER_COMM] THEN
      ASM_REWRITE_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
      SRW_TAC [] [ADD1] THEN
      `(allSyms g) ∩ set sn = (set sn) ∩ (allSyms g)` 
	  by METIS_TAC [INTER_COMM] THEN
      ASM_REWRITE_TAC [] THEN
      DECIDE_TAC,

      `sym IN allSyms g` by METIS_TAC [symInGr] THEN
      `~(sym ∈ set sn)` by FULL_SIMP_TAC list_ss [] THEN
      `~(sym ∈ ((allSyms g) ∩ (set sn)))` 
	  by METIS_TAC [IN_INTER] THEN
      `~(allSyms g = set sn)` by METIS_TAC [] THEN
      `CARD (allSyms g) - CARD (allSyms g ∩ set sn) 
         = CARD ((allSyms g) DIFF (set sn))` 
	  by METIS_TAC [CARD_DIFF,FINITE_LIST_TO_SET,
			FINITE_INSERT] THEN
      ASM_REWRITE_TAC [] THEN
      `sym ∈ (allSyms g DIFF set sn)` 
	  by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN 
	      METIS_TAC []) THEN
      `~((allSyms g DIFF set sn)={})` 
	  by METIS_TAC [MEMBER_NOT_EMPTY] THEN
      `~(CARD (allSyms g DIFF set sn)=0)` 
	  by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
      DECIDE_TAC])


val followSetML = Define `followSetML g sym = 
BIGUNION (LIST_TO_SET (MAP (followRuleML g [] sym) (rules g)))`

val fruleMLIsTmnl = store_thm 
("fruleMLIsTmnl",
``s IN followRuleML g sn e r ==> isTmnlSym s``,
MAGIC)

val followRuleEq1 = mk_thm ([], 
``!g sn sym r.((s IN (followRuleML g sn sym r))) ==> (s IN (followSet g sym))``)

val _ = save_thm ("followRuleEq1", followRuleEq1)

(*DOES NOT WORK WITH THE NEW HOL VERSION. FIX IT SO THAT IT DOES! *)

(*
val followRuleEq1 = store_thm ("followRuleEq1",
``∀g sn sym r.
     s ∈ (followRuleML g sn sym r) ==> MEM r (rules g)
        ==>
       s ∈ (followSet g sym)``,
HO_MATCH_MP_TAC followRuleML_ind THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [followRuleML],

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [followRuleML, LET_THM] THEN
Cases_on `~MEM sym sn ∧ sym IN allSyms g` THEN 
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
Cases_on `NTS l ∈ nonTerminalsML g` THEN 
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
Cases_on `h=sym` THEN 
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
Cases_on `nullableML g [] t` THEN 
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
SRW_TAC [][] THENL[

  FULL_SIMP_TAC (srw_ss()) [firstSetML_def] THEN
  `s IN (firstSetList g t)` 
      by METIS_TAC [firstSet1Eq1, firstSetML_def] THEN
  FULL_SIMP_TAC (srw_ss()) [firstSetList_def, followSet] THEN
  SRW_TAC [][] THEN
  `MEM (h::t) (MAP (ruleRhs) (rules g))` by (SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN 
  METIS_TAC []) THEN
  Q.EXISTS_TAC `(h::t)` THEN SRW_TAC [] [] THEN  
  `RTC (derives g) (h::t) ([h]++[TS fst]++rst)` 
      by METIS_TAC [APPEND, APPEND_ASSOC, 
		    rtc_derives_same_append_left] THEN
  METIS_TAC [APPEND, APPEND_ASSOC],

  FULL_SIMP_TAC (srw_ss()) [firstSetML_def] THEN
  `s IN (firstSetList g t)` 
      by METIS_TAC [firstSet1Eq1, firstSetML_def] THEN
  FULL_SIMP_TAC (srw_ss()) [firstSetList_def, followSet] THEN
  Q.EXISTS_TAC `(h::t)` THEN
  `RTC (derives g) (h::t) ([h]++[TS fst]++rst)` 
      by METIS_TAC [APPEND, APPEND_ASSOC, 
		    rtc_derives_same_append_left] THEN
  `MEM (h::t) (MAP (ruleRhs) (rules g))` 
      by (SRW_TAC [] [] THEN
	  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN 
	  METIS_TAC []) THEN
  METIS_TAC [APPEND, APPEND_ASSOC],

  `MEM (h::t) (MAP (ruleRhs) (rules g))` 
      by (SRW_TAC [] [] THEN
	  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN 
	  METIS_TAC []) THEN
  SRW_TAC [] [followSet] THEN
  `isTmnlSym s` by METIS_TAC [fruleMLIsTmnl] THEN
  Cases_on `s` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
  SRW_TAC [][] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []THEN
  FULL_SIMP_TAC (srw_ss()) [followRuleML]


Cases_on `~MEM (NTS l) sn` THEN FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
Cases_on `~(NTS l = sym)` THEN FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
`s IN followRuleML g (NTS l::sn) (NTS l) a` by METIS_TAC [] THEN
RES_TAC THEN
SRW_TAC [] [followSet] THEN
`nullable g t` by METIS_TAC [nullableEq1] THEN
FULL_SIMP_TAC (srw_ss()) [nullable_def, followSet] THEN
Q.EXISTS_TAC `s'` THEN
`RTC (derives g) [NTS l] ([h]++t)` by METIS_TAC [res1, RTC_MONOTONE, APPEND, CONS, RTC_RULES] THEN
`RTC (derives g) ([h]++t) [h]` by 
METIS_TAC [APPEND, APPEND_NIL, rtc_derives_same_append_left] THEN
`RTC (derives g) [NTS l] [h]` by METIS_TAC [RTC_RTC] THEN
METIS_TAC [rtc_derives_same_append_left, rtc_derives_same_append_right, APPEND_ASSOC, RTC_RTC]
]])

*)
val followSetEq1 = store_thm ("followSetEq1",
``!g sym.s IN (followSetML g sym) ==> s IN (followSet g sym)``,
FULL_SIMP_TAC (srw_ss()) [followSetML] THEN SRW_TAC [] [] THEN
METIS_TAC [followRuleEq1, MEM_MAP]
)


val followSetMem = store_thm ("followSetMem", 
``!u v.RTC (derives g) u v ==> (u=[NTS N]) ==> 
(v=(pfx++[NTS N']++[TS ts]++sfx)) ==> 
((TS ts) IN followSet g (NTS N'))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] 
THENL[

      `LENGTH [NTS N] = LENGTH (pfx ++ [NTS N'] ++ [TS ts] ++ sfx)` 
			       by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (arith_ss) [],

      FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq, followSet] THEN
      Q.EXISTS_TAC `u'` THEN
      SRW_TAC [] [] 
	      THENL[
		    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN
		    METIS_TAC [],
			  
		    METIS_TAC []]])




val mlDir = ref ("./theoryML/");


(*
val _ =
 let open EmitML
 in emitML (!mlDir)
   ("followSet",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "whileLemmas", "set","num", "parseTree", "firstSet"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: DATATYPE `item = item of string => symbol list # symbol list`
    :: DEFN firstSet1
    :: DEFN followRuleML
    :: DEFN followSetML
    :: [])
 end;
*)

val _ = export_theory ();