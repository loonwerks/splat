structure ptltlSyntax :> ptltlSyntax =
struct

open Feedback Lib HolKernel boolLib ptltlTheory;

val ERR = mk_HOL_ERR "ptltlSyntax";

val formula = mk_thy_type{Tyop="formula",Thy="ptltl",Args = []};

fun ptltl_const s = prim_mk_const{Thy = "ptltl", Name = s};

val const_Eid   = ptltl_const"Eid";
val const_Prim  = ptltl_const"Prim";
val const_Not   = ptltl_const"Not";
val const_Imp   = ptltl_const"Imp";
val const_Equiv = ptltl_const"Equiv";
val const_Or    = ptltl_const"Or";
val const_Xor   = ptltl_const"Xor";
val const_And   = ptltl_const"And";
val const_Since = ptltl_const"Since";
val const_Histor = ptltl_const"Histor";
val const_Once  = ptltl_const"Once";
val const_Prev  = ptltl_const"Prev";
val const_Start = ptltl_const"Start";
val const_End   = ptltl_const"End";

val const_Trigger = ptltl_const"Trigger";
val const_Yester  = ptltl_const"Yester";
val const_Zyester = ptltl_const"Zyester";


fun mk_Eid t  = mk_comb(const_Eid,t);
fun mk_Prim t = mk_comb(const_Prim,t);
fun mk_Not t  = mk_comb(const_Not,t);
fun mk_Imp(t1,t2) = list_mk_comb (const_Imp,[t1,t2]);
fun mk_Equiv(t1,t2) = list_mk_comb (const_Equiv,[t1,t2]);
fun mk_Or(t1,t2) = list_mk_comb (const_Or,[t1,t2]);
fun mk_Xor(t1,t2) = list_mk_comb (const_Xor,[t1,t2]);
fun mk_And(t1,t2) = list_mk_comb (const_And,[t1,t2]);
fun mk_Since(t1,t2) = list_mk_comb (const_Since,[t1,t2]);
fun mk_Histor t = mk_comb(const_Histor,t);
fun mk_Once t = mk_comb(const_Once,t);
fun mk_Prev t = mk_comb(const_Prev,t);
fun mk_Start t = mk_comb(const_Start,t);
fun mk_End t = mk_comb(const_End,t);

fun mk_Trigger(t1,t2) = list_mk_comb (const_Trigger,[t1,t2])
fun mk_Yester t = mk_comb (const_Yester,t)
fun mk_Zyester t = mk_comb (const_Zyester,t)
;

val dest_Eid   = dest_monop const_Eid    (ERR "dest_Eid" "")
val dest_Prim  = dest_monop const_Prim   (ERR "dest_Prim" "")
val dest_Not   = dest_monop const_Not    (ERR "dest_Not" "")
val dest_Imp   = dest_binop const_Imp    (ERR "dest_Imp" "")
val dest_Equiv = dest_binop const_Equiv  (ERR "dest_Equiv" "")
val dest_Or    = dest_binop const_Or     (ERR "dest_Or" "")
val dest_Xor   = dest_binop const_Xor    (ERR "dest_Xor" "")
val dest_And   = dest_binop const_And    (ERR "dest_And" "")
val dest_Since = dest_binop const_Since  (ERR "dest_Since" "")
val dest_Histor = dest_monop const_Histor (ERR "dest_Histor" "")
val dest_Once  = dest_monop const_Once   (ERR "dest_Once" "")
val dest_Prev  = dest_monop const_Prev   (ERR "dest_Prev" "")
val dest_Start = dest_monop const_Start  (ERR "dest_Start" "")
val dest_End   = dest_monop const_End    (ERR "dest_End" "")
;
val dest_Trigger = dest_binop const_Trigger (ERR "dest_Trigger" "")
val dest_Yester  = dest_monop const_Yester  (ERR "dest_Yester" "")
val dest_Zyester = dest_monop const_Zyester (ERR "dest_Zyester" "")
;
val is_Eid = Lib.can dest_Eid
val is_Prim = Lib.can dest_Prim
val is_Not  = Lib.can dest_Not
val is_Imp = Lib.can dest_Imp
val is_Equiv = Lib.can dest_Equiv
val is_Or = Lib.can dest_Or
val is_Xor = Lib.can dest_Xor
val is_And = Lib.can dest_And
val is_Since = Lib.can dest_Since
val is_Histor = Lib.can dest_Histor
val is_Once = Lib.can dest_Once
val is_Prev = Lib.can dest_Prev
val is_Start = Lib.can dest_Start
val is_End = Lib.can dest_End
;
val is_Trigger = Lib.can dest_Trigger
val is_Yester = Lib.can dest_Yester
val is_Zyester = Lib.can dest_Zyester
;

val other_elm                  = ptltl_const"other_elm";
val empty_state                = ptltl_const"empty_state";
val const_smallstep            = ptltl_const"smallstep";
val const_bigstep              = ptltl_const"bigstep";
val const_smallstep            = ptltl_const"smallstep";
val const_mk_subforms          = ptltl_const"mk_subforms";
val const_decide_formula_start = ptltl_const"decide_formula_start";
val const_decide_formula       = ptltl_const"decide_formula";
val const_transition_start     = ptltl_const"transition_start";
val const_transition           = ptltl_const"transition";
val const_dfa_loop             = ptltl_const"dfa_loop";
val const_mk_power_list        = ptltl_const"mk_power_list";
val const_extract_ids          = ptltl_const"extract_ids";
val const_find_reachable_edges = ptltl_const"find_reachable_edges";
val const_mk_relational_data   = ptltl_const"mk_relational_data";
val const_mk_table_data        = ptltl_const"mk_table_data";
val const_table_transition     = ptltl_const"table_transition";

fun mk_bigstep(t1,t2) = list_mk_comb(const_bigstep,[t1,t2])
fun mk_smallstep(t1,t2) = list_mk_comb(const_smallstep,[t1,t2])
fun mk_smallstep1 t = mk_comb(const_smallstep,t)
fun mk_subforms t = mk_comb(const_mk_subforms, t)
fun mk_decide_formula_start (t1,t2,t3) =
    list_mk_comb(const_decide_formula_start,[t1,t2,t3])
fun mk_decide_formula(t1,t2,t3,t4) =
    list_mk_comb(const_decide_formula,[t1,t2,t3,t4])
fun mk_transition_start(t1,t2) =
    list_mk_comb(const_transition_start,[t1,t2])
fun mk_transition (t1,t2,t3) =
    list_mk_comb(const_transition,[t1,t2,t3])
fun mk_dfa_loop(t1,t2,t3,t4) =
    list_mk_comb(const_dfa_loop,[t1,t2,t3,t4])
fun mk_power_list t = mk_comb(const_mk_power_list,t)
fun mk_extract_ids t = mk_comb(const_extract_ids,t)
fun mk_find_reachable_edges(t1,t2,t3,t4,t5,t6) =
    list_mk_comb(const_find_reachable_edges,[t1,t2,t3,t4,t5,t6])
fun mk_relational_data (t1,t2) =
    list_mk_comb(const_mk_relational_data,[t1,t2])
fun mk_table_data (t1,t2,t3,t4,t5) =
    list_mk_comb(const_mk_table_data,[t1,t2,t3,t4,t5])
fun mk_table_data1 t = mk_icomb (const_mk_table_data,t)
fun mk_table_transition (t1,t2,t3) =
    list_mk_comb(const_table_transition,[t1,t2,t3])

val dest_bigstep   = dest_binop const_bigstep (ERR "dest_bigstep" "")
val dest_smallstep = dest_binop const_smallstep (ERR "dest_smallstep" "")
val dest_mk_subforms  = dest_monop const_mk_subforms (ERR "dest_subforms" "")
val dest_decide_formula_start =
    dest_triop const_decide_formula_start (ERR "dest_decide_formula_start" "")

fun ndest c n e t =
  case total dest_comb t
   of NONE => raise e
   |  SOME(d,a) =>
       if same_const c d then
        let val (k,args) = strip_comb a
        in if length args = n-1 then
              k::args
           else raise e
        end
       else raise e;

fun dest_decide_formula t =
 let val err = ERR "dest_decide_formula" ""
 in case ndest const_decide_formula 4 err t
     of [a,b,c,d] => (a,b,c,d)
      | otherwise  => raise err
 end

val dest_transition_start =
    dest_binop const_transition_start (ERR "dest_transition_start" "")
val dest_transition = dest_triop const_transition (ERR "dest_transition" "")

fun dest_dfa_loop t =
 let val [t1,t2,t3,t4] = ndest const_dfa_loop 4 (ERR "dest_dfa_loop" "") t
 in (t1,t2,t3,t4)
 end

val dest_mk_power_list = dest_monop const_mk_power_list (ERR "dest_mk_power_list" "")
val dest_extract_ids = dest_monop const_extract_ids (ERR "dest_extract_ids" "")

fun dest_find_reachable_edges t =
 let val [t1,t2,t3,t4,t5,t6] =
      ndest const_find_reachable_edges 6 (ERR "dest_find_reachable_edges" "") t
 in (t1,t2,t3,t4,t5,t6)
 end

val dest_mk_relational_data =
     dest_binop const_mk_relational_data (ERR "dest_relational_data" "")

fun dest_mk_table_data t =
 let val [t1,t2,t3,t4,t5] =
      ndest const_mk_table_data 5 (ERR "dest_mk_table_data" "") t
 in (t1,t2,t3,t4,t5)
 end

val dest_table_transition =
     dest_triop const_table_transition (ERR "dest_table_transition" "")


val is_smallstep            = Lib.can dest_smallstep;
val is_bigstep              = Lib.can dest_bigstep;
val is_smallstep            = Lib.can dest_smallstep;
val is_mk_subforms          = Lib.can dest_mk_subforms;
val is_decide_formula_start = Lib.can dest_decide_formula_start;
val is_decide_formula       = Lib.can dest_decide_formula;
val is_transition_start     = Lib.can dest_transition_start;
val is_transition           = Lib.can dest_transition
val is_dfa_loop             = Lib.can dest_dfa_loop
val is_mk_power_list        = Lib.can dest_mk_power_list;
val is_extract_ids          = Lib.can dest_extract_ids;
val is_find_reachable_edges = Lib.can dest_find_reachable_edges;
val is_mk_relational_data   = Lib.can dest_mk_relational_data;
val is_mk_table_data        = Lib.can dest_mk_table_data;
val is_table_transition     = Lib.can dest_table_transition;

end
