open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib intLib stringLib regexpLib;

open arithmeticTheory listTheory rich_listTheory
     stringTheory combinTheory ASCIInumbersTheory
     numposrepTheory ASCIInumbersLib integerTheory;

val int_ss = intLib.int_ss;

val _ = numLib.prefer_num();

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

val _ = new_theory "contig";

(*---------------------------------------------------------------------------*)
(* The types of interest: lvals, arithmetic expressions over lvals, boolean  *)
(* expressions, atomic types, and contiguity types.                          *)
(*---------------------------------------------------------------------------*)

Datatype:
  lval = VarName string
       | RecdProj lval string
       | ArraySub lval exp ;

  exp = Loc lval
      | numLit num
      | ConstName string
      | Add exp exp
      | Mult exp exp
End

Datatype:
  bexp = boolLit bool
       | Bnot bexp
       | Bor  bexp bexp
       | Band bexp bexp
       | Beq  exp exp
       | Blt  exp exp
       | Bgtr exp exp
       | Bleq exp exp
       | Bgeq exp exp
End

Datatype:
  atom = Bool
       | Char
       | Float
       | Double
       | Signed num
       | Unsigned num
       | Enum string
End

Datatype:
  contig = Basic atom
         | Recd ((string # contig) list)
         | Array contig exp
         | Union ((bexp # contig) list)
End


(*---------------------------------------------------------------------------*)
(* NB: there are other constructors we want to add to the contig datatype    *)
(* (see contig.sml) but we will wait until the proofs get sorted for the     *)
(* initial version.                                                          *)
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

Definiton evalExp_def :
  evalExp (lvalMap,valueFn) exp =
 case exp
  of Loc lval =>
       (case Redblackmap.peek(lvalMap,lval)
         of SOME s => valueFn s
          | NONE => raise ERR "evalExp" "Lval binding failure")
   | numLit n => n
   | Add(e1,e2) => evalExp E e1 + evalExp E e2
   | Mult(e1,e2) => evalExp E e1 * evalExp E e2
;


val _ = export_theory();
