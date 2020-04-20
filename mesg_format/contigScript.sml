open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib regexpLib ASCIInumbersLib;

open arithmeticTheory listTheory rich_listTheory
     stringTheory combinTheory ASCIInumbersTheory
     numposrepTheory FormalLangTheory;


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
       | BLoc lval
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
       | Blob
       | Scanned
End

Datatype:
  contig = FAIL
         | Basic atom
         | Recd ((string # contig) list)
         | Array contig exp
         | Union ((bexp # contig) list)
End


(*---------------------------------------------------------------------------*)
(* comparison functions on lvals and exps                                    *)
(*---------------------------------------------------------------------------*)

Definition lval_compare_def :
 (lval_compare (VarName s1) (VarName s2) = string_compare s1 s2) /\
 (lval_compare (VarName _)  ____         = Less)      /\
 (lval_compare (RecdProj _ _) (VarName _)  = Greater) /\
 (lval_compare (RecdProj e1 s1) (RecdProj e2 s2) =
     (case lval_compare e1 e2
       of Equal => string_compare s1 s2
        | other => other))                            /\
 (lval_compare (RecdProj _ _) ____ = Less)            /\
 (lval_compare (ArraySub a b) (ArraySub c d) =
     (case lval_compare a c
       of Equal => exp_compare b d
        | other => other))                            /\
 (lval_compare (ArraySub _ _) ____ = Greater)
 /\
 (exp_compare (Loc lv1) (Loc lv2)   = lval_compare lv1 lv2)  /\
 (exp_compare (Loc lv1) ____        = Less)                  /\
 (exp_compare (numLit _) (Loc _)    = Greater)               /\
 (exp_compare (numLit m) (numLit n) = num_compare m n)       /\
 (exp_compare (numLit _)  ____      = Less)                  /\
 (exp_compare (Add _ _) (Mult _ _)      = Less)              /\
 (exp_compare (Add a b) (Add c d)   =
    (case exp_compare a c
      of Equal => exp_compare b d
       | other => other))                                    /\
 (exp_compare (Add _ _) ____          = Greater)             /\
 (exp_compare (Mult a b) (Mult c d) =
    (case exp_compare a c
      of Equal => exp_compare b d
       | other => other))                                    /\
 (exp_compare (Mult _ _) _____        = Greater)
End

(*---------------------------------------------------------------------------*)
(* Expression evaluation                                                     *)
(*---------------------------------------------------------------------------*)

Definition evalExp_def :
 evalExp (lvalMap,valueFn) (Loc lval) =
   (case lookup lval_compare lval lvalMap
     of SOME s => valueFn s
      | NONE => ARB) /\
 evalExp E (numLit n) = n /\
 evalExp E (Add e1 e2) = (evalExp E e1 + evalExp E e2) /\
 evalExp E (Mult e1 e2) = (evalExp E e1 * evalExp E e2)
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



val _ = export_theory();
