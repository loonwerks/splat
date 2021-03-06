open HolKernel boolLib bossLib Parse BasicProvers Defn
open listTheory containerTheory pred_setTheory arithmeticTheory relationTheory markerTheory
open regexpTheory grammarDefTheory listLemmasTheory

val _ = new_theory "firstSetDef"

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w)

val _ = set_trace "Unicode" 1;

val _ = Globals.linewidth := 60

val firstSet = Define
`firstSet g sym =
{ (TS fst) | ∃rst.RTC (derives g) [sym] ([TS fst]++rst) }`


val firstSet1_defn = Hol_defn "firstSet1_defn" `
  (firstSet1 g sn [] = []) ∧
  (firstSet1 g sn (TS ts :: rest) = [TS ts]) ∧
  (firstSet1 g sn (NTS nt :: rest) =
     rmDupes 
     (if MEM (NTS nt) sn then [] 
      else let
	      r = getRhs nt (rules g)
	  in
	      FLAT (MAP (firstSet1 g (NTS nt::sn)) r))
     ++ (if nullableML g [] [NTS nt] then 
	    firstSet1 g sn rest
	 else []))`


val (firstSet1,firstSet1_ind) = tprove (
  firstSet1_defn,
  WF_REL_TAC
   `inv_image (measure (λ(g,sn). CARD (nonTerminals g DIFF LIST_TO_SET sn))
                 LEX
               measure (λ(syms).LENGTH syms))
              (λ(g,sn,syms).((g,sn),syms))` THEN
  SRW_TAC [] [] THEN
  `FINITE (nonTerminals g)` by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
  `FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
  `FINITE (NTS A INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
  SRW_TAC [] [CARD_DIFF] THENL[
    SRW_TAC [] [CARD_INSERT,FINITE_LIST_TO_SET] THEN
    `~(getRhs nt (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `(NTS nt) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
    `(nonTerminals g ∩ (NTS nt INSERT set sn)) =
       (NTS nt INSERT set sn) ∩ nonTerminals g` by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
    SRW_TAC [] [ADD1] THEN
    `(nonTerminals g ∩ set sn) = (set sn ∩ nonTerminals g)`
       by METIS_TAC [INTER_COMM] THEN
    ASM_REWRITE_TAC [] THEN
    DECIDE_TAC,

    `~(getRhs nt (rules g) = [])` by METIS_TAC [listNotEmpty] THEN
    `(NTS nt) IN (nonTerminals g)` by METIS_TAC [ntsInGr] THEN
    `~((NTS nt) IN set sn)` by FULL_SIMP_TAC (srw_ss()) [MEM,LIST_TO_SET] THEN
    `~(NTS nt IN (nonTerminals g INTER set sn))` by METIS_TAC [IN_INTER] THEN
    `~(nonTerminals g = set sn)` by METIS_TAC [] THEN
    `FINITE (nonTerminals g)`
       by METIS_TAC [finiteNtsList,FINITE_LIST_TO_SET] THEN
    `FINITE (set sn)` by METIS_TAC [FINITE_LIST_TO_SET] THEN
    `FINITE (NTS nt INSERT set sn)` by METIS_TAC [FINITE_INSERT] THEN
    `CARD (nonTerminals g) - CARD (nonTerminals g ∩ set sn) =
       CARD (nonTerminals g DIFF set sn)`
       by METIS_TAC [CARD_DIFF] THEN
    ASM_REWRITE_TAC [] THEN
    `NTS nt ∈ (nonTerminals g DIFF set sn)` by
       (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF] THEN METIS_TAC []) THEN
    `~((nonTerminals g DIFF set sn)={})` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
    `~(CARD (nonTerminals g DIFF set sn)=0)`
       by METIS_TAC [CARD_EQ_0,FINITE_DIFF] THEN
    DECIDE_TAC
  ]);

val firstSetML = Define `firstSetML g sym = firstSet1 g [] [sym]`

val getRhsNilMem = store_thm ("getRhsNilMem",
``(getRhs nt (rules g) =[]) = ~(?r.MEM (rule nt r) (rules g))``,
SRW_TAC [] [EQ_IMP_THM] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN
Induct_on `l` THEN
SRW_TAC [] [getRhs_def] THEN
SRW_TAC [] [] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getRhs_def] THEN
Cases_on `nt=s` THEN
SRW_TAC [] [] THEN
METIS_TAC [getRhsDistrib,APPEND,APPEND_eq_NIL])

val getRhsNilRtc = store_thm ("getRhsNilRtc",
``(getRhs nt (rules g) = []) ==>
      (!l.RTC (derives g) [NTS nt] l ==> (l=[NTS nt]))``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq,getRhsNilMem] THEN
METIS_TAC [])


val MEM_getRhs = store_thm(
  "MEM_getRhs",
  ``MEM r (getRhs N l) = MEM (rule N r) l``,
  Induct_on `l` THEN SRW_TAC [][getRhs_def] THEN
  Cases_on `h` THEN SRW_TAC [][getRhs_def] THEN SRW_TAC [][]);


val firstSetList = Define
`firstSetList g l =
      {TS fst | ?rst. RTC (derives g) l ([TS fst] ++ rst)}`

val firstSet1Eq1 = store_thm ("firstSet1Eq1",
  ``∀g sn l. MEM s (firstSet1 g sn l) ==> s ∈ firstSetList g l``,
  HO_MATCH_MP_TAC firstSet1_ind THEN 
  SRW_TAC [] [firstSet1, rmd_mem_list] THENL[
    SIMP_TAC (srw_ss()) [firstSetList] THEN METIS_TAC [RTC_RULES],

    FULL_SIMP_TAC (srw_ss()) [firstSet1, firstSetList, LET_THM,
                              rmd_mem_list] THEN
    SRW_TAC [][] THEN
    METIS_TAC [nullableEq,nullable_def,APPEND_NIL,
	       derives_append,APPEND],


    FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
    `∃e. MEM e (MAP (\a.firstSet1 g (NTS nt::sn) a)
               (getRhs nt (rules g))) /\ (MEM s e)`
        by METIS_TAC [flat_map_mem] THEN
    `∃l. MEM l (getRhs nt (rules g)) ∧ 
          MEM s (firstSet1 g (NTS nt::sn) l)`
       by METIS_TAC [MEM_MAP] THEN
    RES_TAC THEN
    SRW_TAC [][] THEN
    `MEM (rule nt l') (rules g)` by METIS_TAC [MEM_getRhs] THEN
    SRW_TAC [] [firstSetList] THEN
    `derives g (NTS nt :: l) (l' ++ l)`
        by METIS_TAC [derives_same_append_right, APPEND, res1] THEN
    FULL_SIMP_TAC (srw_ss()) [firstSetList] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `rst ++ l` THEN
    `(derives g)^* (l' ++ l) ((TS fst :: rst) ++ l)`
       by METIS_TAC [rtc_derives_same_append_right] THEN
    METIS_TAC [RTC_RULES, APPEND, APPEND_ASSOC],

    FULL_SIMP_TAC (srw_ss()) [firstSetList] THEN
    SRW_TAC [][] THEN
    METIS_TAC [nullableEq,nullable_def,APPEND_NIL,
	       derives_append,APPEND],

    FULL_SIMP_TAC (srw_ss()) [LET_THM,firstSetList] THEN
    `∃e. MEM e (MAP (\a.firstSet1 g (NTS nt::sn) a)
               (getRhs nt (rules g))) /\ (MEM s e)`
        by METIS_TAC [flat_map_mem] THEN
    `∃l. MEM l (getRhs nt (rules g)) ∧ 
       MEM s (firstSet1 g (NTS nt::sn) l)`
       by METIS_TAC [MEM_MAP] THEN
    RES_TAC THEN
    SRW_TAC [][] THEN
    `MEM (rule nt l') (rules g)` by METIS_TAC [MEM_getRhs] THEN
    SRW_TAC [] [firstSetList] THEN
    `derives g (NTS nt :: l) (l' ++ l)`
        by METIS_TAC [derives_same_append_right, APPEND, res1] THEN
    FULL_SIMP_TAC (srw_ss()) [firstSetList] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `rst ++ l` THEN
    `(derives g)^* (l' ++ l) ((TS fst :: rst) ++ l)`
       by METIS_TAC [rtc_derives_same_append_right] THEN
    METIS_TAC [RTC_RULES, APPEND, APPEND_ASSOC]
    ])

open rich_listTheory


val ntderive_def = Define`
  (ntderive g tok [] = F) ∧ 
  (ntderive g tok [N] = 
     ∃pfx sfx rhs. 
        MEM (rule N rhs) (rules g) ∧
        (rhs = pfx ++ [TS tok] ++ sfx) ∧
        nullable g pfx) ∧
  (ntderive g tok (N1 :: N2 :: Ns) = 
     ∃pfx sfx rhs.
        MEM (rule N1 rhs) (rules g) ∧
        (rhs = pfx ++ [NTS N2] ++ sfx) ∧
        nullable g pfx ∧
        ntderive g tok (N2 :: Ns))
`;
val _ = export_rewrites ["ntderive_def"]

val ntderive_APPEND = store_thm(
  "ntderive_APPEND",
  ``∀l1 l2. ntderive g tok (l1 ++ l2) ∧ ¬(l2 = []) ==>
            ntderive g tok l2``,
  Induct THEN1 SRW_TAC [][] THEN 
  Cases_on `l1` THEN SRW_TAC [][] THENL [
    Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [APPEND]
  ])

val MEM_FLAT = prove(
  ``MEM e (FLAT l) = ∃l0. MEM l0 l ∧ MEM e l0``,
  Induct_on `l` THEN SRW_TAC [][] THEN METIS_TAC []);

val nullable_TS = prove(
  ``nullable g (TS s :: rest) = F``,
  SRW_TAC [][nullable_def] THEN 
  METIS_TAC [notTlRtcDerives])

val firstset1_nullable_append = prove(
  ``MEM t (firstSet1 g sn sfx) ∧ nullable g pfx ⇒
    MEM t (firstSet1 g sn (pfx ++ sfx))``,
  Induct_on `pfx` THEN SRW_TAC [][] THEN 
  `nullable g [h] ∧ nullable g pfx` 
     by METIS_TAC [nullable_APPEND, APPEND] THEN 
  `∃N. h = NTS N`
     by (Cases_on `h` THEN 
	 FULL_SIMP_TAC (srw_ss()) [nullable_TS]) THEN 
  SRW_TAC [][firstSet1, rmd_mem_list, GSYM nullableEq]);
  
val firstset1_cons_I = prove(
  ``MEM tok (firstSet1 g sn [h]) ⇒ 
    MEM tok (firstSet1 g sn (h :: t))``,
  Cases_on `h` THEN SRW_TAC [][firstSet1]);


val ntderive_firstset1 = prove(
  ``∀sn. ntderive g tok ns ∧ ALL_DISTINCT ns ∧
         (IMAGE NTS (set ns) ∩ set sn = {}) ⇒ 
         MEM (TS tok) (firstSet1 g sn [NTS (HD ns)])``,
  Induct_on `ns` THEN 
  SRW_TAC [][firstSet1, rmDupes, LET_THM, rmd_mem_list] THENL [
    DISJ2_TAC THEN DISJ2_TAC THEN 
    SRW_TAC [boolSimps.DNF_ss][EXTENSION],
    
    Cases_on `ns` THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      SRW_TAC [boolSimps.DNF_ss][MEM_FLAT, MEM_MAP] THEN 
      Q.EXISTS_TAC `pfx ++ [TS tok] ++ sfx` THEN 
      SRW_TAC [][MEM_getRhs] THEN 
      `MEM (TS tok) (firstSet1 g (NTS h::sn) ([TS tok] ++ sfx))`
         by SRW_TAC [][firstSet1] THEN 
      METIS_TAC [APPEND_ASSOC, firstset1_nullable_append],

      FULL_SIMP_TAC (srw_ss()) [] THEN 
      SRW_TAC [boolSimps.DNF_ss][MEM_FLAT, MEM_MAP] THEN 
      Q.EXISTS_TAC `pfx ++ [NTS h'] ++ sfx` THEN 
      SRW_TAC [][MEM_getRhs] THEN 
      ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN 
      MATCH_MP_TAC firstset1_nullable_append THEN 
      SRW_TAC [][] THEN MATCH_MP_TAC firstset1_cons_I THEN 
      FIRST_X_ASSUM MATCH_MP_TAC THEN 
      SRW_TAC [][] THEN 
      POP_ASSUM MP_TAC THEN 
      SRW_TAC [][EXTENSION] THEN 
      METIS_TAC [symbol_11]
    ]
  ])

val nullable_NIL = store_thm(
  "nullable_NIL",
  ``nullable g []``,
  SRW_TAC [][nullable_def])
val _ = export_rewrites ["nullable_NIL"]
      
val split_killer = prove(
  ``∀y p s. 
    (x ++ y = p ++ [E] ++ s) = 
    (∃x2. (x = p ++ [E] ++ x2) ∧ (s = x2 ++ y)) ∨
    (∃y1. (p = x ++ y1) ∧ (y = y1 ++ [E] ++ s))``,
  Induct_on `x` THEN SRW_TAC [][] THEN 
  Cases_on `p` THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN 
  METIS_TAC []);

val isolate_last = prove(
  ``∀l e. MEM e l ==>
          ∃pfx sfx. (l = pfx ++ [e] ++ sfx) ∧
                    ¬MEM e sfx``,
  Induct THEN SRW_TAC [][] THEN METIS_TAC [APPEND])

val ALL_DISTINCT_APPEND = prove(
  ``ALL_DISTINCT (l1 ++ l2) ==> ALL_DISTINCT l1 ∧ ALL_DISTINCT l2``,
  Induct_on `l1` THEN SRW_TAC [][]);

val ntderive_list_exists = prove(
  ``∀sf1 sf2.
       (derives g)^* sf1 sf2 ⇒
       ∀tok rest. (sf2 = TS tok :: rest) ∧
                  (∀pfx sfx. nullable g pfx ⇒ 
                             ¬(sf1 = pfx ++ [TS tok] ++ sfx))
                 ==> 
                  ∃nlist pfx sfx. 
                     (sf1 = pfx ++ [NTS (HD nlist)] ++ sfx) ∧
                     nullable g pfx ∧
                     ntderive g tok nlist ∧ 
                     ALL_DISTINCT nlist``,      
  HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
    (POP_ASSUM (Q.SPEC_THEN `[]` MP_TAC) THEN 
		SRW_TAC [][]) THEN 
  `∃N rhs pfx sfx. 
      MEM (rule N rhs) (rules g) ∧
      (sf1 = pfx ++ [NTS N] ++ sfx) ∧
      (sf1' = pfx ++ rhs ++ sfx)`
     by METIS_TAC [derives_def] THEN 
  SRW_TAC [][] THEN 
  Cases_on `∀p s. nullable g p ==> 
                  ¬(pfx ++ rhs ++ sfx = p ++ [TS tok] ++ s)`
  THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN
    REPEAT (Q.PAT_ASSUM `!x. P x` (K ALL_TAC)) THEN 
    RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [split_killer]) THEN 
    FULL_SIMP_TAC (srw_ss()) [] THENL [
      SRW_TAC [][] THEN METIS_TAC [APPEND_ASSOC],
      SRW_TAC [][] THEN 
      Cases_on `MEM N nlist` THENL [
        `∃n0 nsfx. (nlist = n0 ++ [N] ++ nsfx) ∧
                   ¬ MEM N nsfx`
           by METIS_TAC [isolate_last] THEN 
        SRW_TAC [][] THEN 
        MAP_EVERY Q.EXISTS_TAC 
                  [`N :: nsfx`, `pfx`, `sfx`] THEN
        SRW_TAC [][] THENL [
          FULL_SIMP_TAC (srw_ss()) [nullable_APPEND],
          METIS_TAC [ntderive_APPEND, APPEND_ASSOC, APPEND,
                     NOT_CONS_NIL],
          METIS_TAC [ALL_DISTINCT_APPEND]
        ],

	MAP_EVERY Q.EXISTS_TAC 
                  [`N :: nlist`, `pfx`, `sfx`] THEN
        SRW_TAC [][] THENL [
          FULL_SIMP_TAC (srw_ss()) [nullable_APPEND],
	  Cases_on `nlist` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	  METIS_TAC [nullable_APPEND]
        ]
      ],

      SRW_TAC [][] THEN 
      MAP_EVERY Q.EXISTS_TAC 
		[`nlist`, `pfx ++ [NTS N] ++ y1`, `sfx'`] THEN 
      SRW_TAC [][] THEN 
      METIS_TAC [nullable_APPEND, nullable_def, res1,
		 RTC_RULES]
    ],

    FULL_SIMP_TAC (srw_ss()) [] THEN 
    POP_ASSUM (MP_TAC o SIMP_RULE (srw_ss()) [split_killer]) THEN 
    STRIP_TAC THEN SRW_TAC [][] THENL [
      METIS_TAC [APPEND_ASSOC],
      MAP_EVERY Q.EXISTS_TAC [`[N]`, `pfx`, `sfx`] THEN 
      SRW_TAC [][] THEN METIS_TAC [nullable_APPEND],
      `nullable g [NTS N]`
         by METIS_TAC [nullable_APPEND, RTC_RULES, res1,
		       nullable_def] THEN 
      FULL_SIMP_TAC (srw_ss()) [nullable_APPEND] THEN 
      FIRST_X_ASSUM (Q.SPECL_THEN [`pfx ++ [NTS N] ++ y1`, `sfx'`]
				  MP_TAC) THEN 
      SRW_TAC [][nullable_APPEND]
    ]
  ])

val lemma =  SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) [] 
		       ntderive_list_exists 
val first_first1 = prove(
  ``TS t ∈ firstSetList g sf ⇒ TS t ∈ set (firstSet1 g [] sf)``,
  SRW_TAC [][firstSetList] THEN 
  Cases_on `∀p s. nullable g p ==> ¬(sf = p ++ [TS t] ++ s)` THENL[
    `∃nlist pfx sfx. 
        (sf = pfx ++ [NTS (HD nlist)] ++ sfx) ∧
        nullable g pfx ∧ ntderive g t nlist ∧
        ALL_DISTINCT nlist`
      by METIS_TAC [lemma] THEN 
    SRW_TAC [][] THEN 
    ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN 
    MATCH_MP_TAC firstset1_nullable_append THEN 
    SRW_TAC [][] THEN 
    MATCH_MP_TAC firstset1_cons_I THEN 
    MATCH_MP_TAC ntderive_firstset1 THEN 
    SRW_TAC [][],
    
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN 
    ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN 
    MATCH_MP_TAC firstset1_nullable_append THEN 
    SRW_TAC [][firstSet1]
  ]);



val firstSet1Eq = store_thm ("firstSet1Eq",
``∀g l.((MEM s (firstSet1 g [] l)) = 
             (s ∈ (firstSetList g l)))``,
SRW_TAC [] [EQ_IMP_THM] 
THENL[
      METIS_TAC [firstSet1Eq1],
      
      `∃ts.s=TS ts` 
	  by (Cases_on `s` THEN 
	      FULL_SIMP_TAC (srw_ss()) [firstSetList]) THEN
      SRW_TAC [][] THEN
      METIS_TAC [first_first1,containerLemmasTheory.mem_in]	
      ])
		


val _ = save_thm ("firstSet1",firstSet1)
val _ = save_thm ("firstSet1_ind",firstSet1_ind)



val _ = save_thm ("firstSet1",firstSet1)
val _ = save_thm ("firstSet1_ind",firstSet1_ind)


val mlDir = "./theoryML/"
(* local open parseTreeTheory in end
val _ =
 let open EmitML
 in emitML mlDir
   ("firstSet",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "set","num", "parseTree"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: DATATYPE `item = item of string => symbol list # symbol list`
    :: DEFN firstSet1
    :: DEFN firstSetML
    :: [])
 end;
*)


val _ = export_theory ();

