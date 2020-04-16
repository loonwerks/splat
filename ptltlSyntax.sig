signature ptltlSyntax =
sig

include Abbrev

(*---------------------------------------------------------------------------*)
(* Formulas                                                                  *)
(*---------------------------------------------------------------------------*)

val formula : hol_type

val mk_Eid   : term -> term
val mk_Prim  : term -> term
val mk_Not   : term -> term
val mk_Imp   : term * term -> term
val mk_Equiv : term * term -> term
val mk_Or    : term * term -> term
val mk_Xor   : term * term -> term
val mk_And   : term * term -> term
val mk_Prev  : term -> term
val mk_Once  : term -> term
val mk_Since : term * term -> term
val mk_Histor : term -> term
val mk_Start : term -> term
val mk_End   : term -> term

val dest_And    : term -> term * term
val dest_Eid    : term -> term
val dest_End    : term -> term
val dest_Equiv  : term -> term * term
val dest_Histor : term -> term
val dest_Imp    : term -> term * term
val dest_Not    : term -> term
val dest_Once   : term -> term
val dest_Or     : term -> term * term
val dest_Prev   : term -> term
val dest_Prim   : term -> term
val dest_Since  : term -> term * term
val dest_Start  : term -> term
val dest_Xor    : term -> term * term

val is_And    : term -> bool
val is_Eid    : term -> bool
val is_End    : term -> bool
val is_Equiv  : term -> bool
val is_Histor : term -> bool
val is_Imp    : term -> bool
val is_Not    : term -> bool
val is_Once   : term -> bool
val is_Or     : term -> bool
val is_Prev   : term -> bool
val is_Prim   : term -> bool
val is_Since  : term -> bool
val is_Start  : term -> bool
val is_Xor    : term -> bool

(* From the AADL primitives *)

val mk_Trigger : term * term -> term
val mk_Yester  : term -> term
val mk_Zyester : term -> term

val dest_Trigger : term -> term * term
val dest_Yester  : term -> term
val dest_Zyester : term -> term

val is_Trigger : term -> bool
val is_Yester  : term -> bool
val is_Zyester : term -> bool


(*---------------------------------------------------------------------------*)
(* Evaluation                                                                *)
(*---------------------------------------------------------------------------*)

val empty_state : term
val other_elm : term

val mk_bigstep : term * term -> term
val mk_smallstep : term * term -> term
val mk_smallstep1 : term -> term
val mk_subforms : term -> term
val mk_decide_formula_start : term * term * term -> term
val mk_decide_formula : term * term * term * term -> term
val mk_transition_start : term * term -> term
val mk_transition : term * term * term -> term
val mk_dfa_loop : term * term * term * term -> term
val mk_power_list : term -> term
val mk_extract_ids : term -> term
val mk_find_reachable_edges : term * term * term * term * term * term -> term
val mk_relational_data : term * term -> term
val mk_table_data : term * term * term * term * term -> term
val mk_table_data1 : term -> term
val mk_table_transition : term * term * term -> term

val dest_bigstep : term -> term * term
val dest_smallstep : term -> term * term
val dest_mk_subforms : term -> term
val dest_decide_formula_start : term -> term * term * term
val dest_decide_formula :  term -> term * term * term * term
val dest_transition_start : term -> term * term
val dest_transition : term -> term * term * term
val dest_dfa_loop : term -> term * term * term * term
val dest_mk_power_list : term -> term
val dest_extract_ids : term -> term
val dest_find_reachable_edges : term -> term * term * term * term * term * term
val dest_mk_relational_data : term -> term * term
val dest_mk_table_data : term -> term * term * term * term * term
val dest_table_transition : term -> term * term * term

val is_bigstep : term -> bool
val is_smallstep : term -> bool
val is_mk_subforms : term -> bool
val is_decide_formula_start : term -> bool
val is_decide_formula : term -> bool
val is_transition_start : term -> bool
val is_transition : term -> bool
val is_dfa_loop : term -> bool
val is_mk_power_list : term -> bool
val is_extract_ids : term -> bool
val is_find_reachable_edges : term -> bool
val is_mk_relational_data : term -> bool
val is_mk_table_data : term -> bool
val is_table_transition : term -> bool

val bool2pltl : term -> term
val mk_pltl_cond : term * term * term -> term

end
