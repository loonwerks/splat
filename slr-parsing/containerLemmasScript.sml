open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory

val _ = new_theory "containerLemmas";


val mem_in = store_thm ("mem_in",
``!e l. MEM e l <=> e IN LIST_TO_SET l``,
SRW_TAC [] [EQ_IMP_THM])


val mem_subset = store_thm ("mem_subset",
``!l1 l2.
    (!e. MEM e l1 ==> MEM e l2)
    ==>
   (LIST_TO_SET l1) SUBSET (LIST_TO_SET l2)``,
SRW_TAC [] [] THEN
`!e. e IN LIST_TO_SET l1 ==> e IN LIST_TO_SET l2` by
FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST, FINITE_LIST_TO_SET] THEN
METIS_TAC [SUBSET_DEF])



val len_card = store_thm ("len_card",
``!l. LENGTH l >= CARD (LIST_TO_SET l)``,
Induct_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (arith_ss) []
)


val filter_seteq = store_thm ("filter_seteq" ,
``!p l. LIST_TO_SET (FILTER p l) = {x | p x /\ MEM x l}``,
SRW_TAC [] [EXTENSION,EQ_IMP_THM] THEN
METIS_TAC [MEM_FILTER])


val _ = export_theory ();
