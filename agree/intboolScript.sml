open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory;

val _ = intLib.prefer_int();

val _ = new_theory "intbool";

val _ = TeX_notation {hol = "(|", TeX = ("\\HOLTokenWhiteParenLeft", 1)}
val _ = TeX_notation {hol = "|)", TeX = ("\\HOLTokenWhiteParenRight", 1)};

val _ = TeX_notation {hol = UTF8.chr 0x2987, TeX = ("\\HOLTokenWhiteParenLeft", 1)}
val _ = TeX_notation {hol = UTF8.chr 0x2988, TeX = ("\\HOLTokenWhiteParenRight", 1)}

val _ = TeX_notation {hol = "|->",           TeX = ("\\HOLTokenMapto", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x21A6, TeX = ("\\HOLTokenMapto", 1)}


(*---------------------------------------------------------------------------*)
(* Arithmetic and boolean expressions. Conventional, except that we have     *)
(* Lustre operators "pre" and "fby" as well as a temporal operator HistExpr  *)
(* ("Historically").                                                         *)
(*---------------------------------------------------------------------------*)

Datatype:
  expr = IntVar string
       | IntLit int
       | AddExpr expr expr
       | SubExpr expr expr
       | MultExpr expr expr
       | DivExpr expr expr
       | ModExpr expr expr
       | PreExpr expr
       | FbyExpr expr expr
       | CondExpr bexpr expr expr
   ;
 bexpr = BoolVar string
       | BoolLit bool
       | NotExpr bexpr
       | OrExpr  bexpr bexpr
       | AndExpr bexpr bexpr
       | ImpExpr bexpr bexpr
       | IffExpr bexpr bexpr
       | EqExpr  expr expr
       | LtExpr  expr expr
       | LeqExpr expr expr
       | HistExpr bexpr
End

Definition List_Conj_def :
   List_Conj blist = FOLDR AndExpr (BoolLit T) blist
End

(*---------------------------------------------------------------------------*)
(* Variable definitions (‘eq’ statements)                                    *)
(*---------------------------------------------------------------------------*)

Datatype:
  stmt = IntStmt string expr
       | BoolStmt string bexpr
End

(*---------------------------------------------------------------------------*)
(* A component = (I,V,O,A,G) comprises                                       *)
(*                                                                           *)
(*   - A list of input ports          I = [p1; ...; pi]                      *)
(*   - A list of variable definitions V = [v1 = e1; ...; vn = en]            *)
(*   - A list of output definitions   O = [o1 = e(n+1); ...; ok = e(n+k)]    *)
(*   - A list of assumptions          A = [a1,...,ai]                        *)
(*   - A list of guarantees           G = [g1,...,gj]                        *)
(*---------------------------------------------------------------------------*)

Datatype:
  component = <| inports     : string list;
                 var_defs    : stmt list;
                 out_defs    : stmt list;
                 assumptions : bexpr list;
                 guarantees  : bexpr list |>
End

(*---------------------------------------------------------------------------*)
(* Type of expression values                                                 *)
(*---------------------------------------------------------------------------*)

Datatype:
  value = BoolValue bool
        | IntValue int
End

Definition bool_of_def :
  bool_of (BoolValue b) = b
End

Definition int_of_def :
  int_of (IntValue i) = i
End

(* -------------------------------------------------------------------------- *)
(* An environment is a finite map from port names to value streams            *)
(* -------------------------------------------------------------------------- *)

Type env = “:'a |-> (num -> value)”

Definition updateEnv_def :
 updateEnv (fmap: 'a env) name value t =
   let strm = fmap ' name;
       strm' = strm (| t |-> value |)
   in
     fmap |+ (name,strm')
End


(*---------------------------------------------------------------------------*)
(* Value of expression in given environments                                 *)
(*---------------------------------------------------------------------------*)

Definition exprVal_def :
  exprVal E (IntVar s) (t:num) = int_of ((E ' s) t) /\
  exprVal E (IntLit i) t  = i /\
  exprVal E (AddExpr e1 e2) t = exprVal E e1 t + exprVal E e2 t /\
  exprVal E (SubExpr e1 e2) t = exprVal E e1 t - exprVal E e2 t /\
  exprVal E (MultExpr e1 e2) t = exprVal E e1 t * exprVal E e2 t /\
  exprVal E (DivExpr e1 e2) t = exprVal E e1 t / exprVal E e2 t /\
  exprVal E (ModExpr e1 e2) t = exprVal E e1 t % exprVal E e2 t /\
  exprVal E (PreExpr e) t = (if t=0 then ARB else exprVal E e (t-1)) /\
  exprVal E (FbyExpr e1 e2) t =
     (if t = 0 then exprVal E e1 0 else exprVal E e2 t) /\
  exprVal E (CondExpr b e1 e2) t =
     (if bexprVal E b t then exprVal E e1 0 else exprVal E e2 t)
  /\
  bexprVal E (BoolVar s) t     = bool_of ((E ' s) t) /\
  bexprVal E (BoolLit b) t     = b /\
  bexprVal E (NotExpr b) t     = (~bexprVal E b t) /\
  bexprVal E (OrExpr b1 b2) t  = (bexprVal E b1 t \/ bexprVal E b2 t) /\
  bexprVal E (AndExpr b1 b2) t = (bexprVal E b1 t /\ bexprVal E b2 t) /\
  bexprVal E (ImpExpr b1 b2) t = (bexprVal E b1 t ⇒ bexprVal E b2 t) /\
  bexprVal E (IffExpr b1 b2) t = (bexprVal E b1 t = bexprVal E b2 t)  /\
  bexprVal E (EqExpr e1 e2) t  = (exprVal E e1 t = exprVal E e2 t)    /\
  bexprVal E (LtExpr e1 e2) t  = (exprVal E e1 t < exprVal E e2 t)    /\
  bexprVal E (LeqExpr e1 e2) t = (exprVal E e1 t <= exprVal E e2 t)   /\
  bexprVal E (HistExpr b) t    = (!n. n <= t ==> bexprVal E b n)
End


(*---------------------------------------------------------------------------*)
(* A statement updates a binding in environment E                            *)
(*---------------------------------------------------------------------------*)

Definition stmtFn_def :
 stmtFn t E (IntStmt s exp)   = updateEnv E s (IntValue(exprVal E exp t)) t ∧
 stmtFn t E (BoolStmt s bexp) = updateEnv E s (BoolValue(bexprVal E bexp t)) t
End

(*---------------------------------------------------------------------------*)
(* Sequential accumulation of variable updates.                              *)
(*---------------------------------------------------------------------------*)

Definition stmtListFn_def :
   stmtListFn E stmts t = FOLDL (stmtFn t) E stmts
End

Definition componentFn_def :
  componentFn E comp t = stmtListFn E (comp.var_defs ++ comp.out_defs) t
End

(*---------------------------------------------------------------------------*)
(* Correctness of component: the effects  of the component model its spec.   *)
(* We first define a function over t that iterates variable assignments of   *)
(* the component. Time 0 is when the ports get their first value, so we      *)
(* have to calculate componentFn there as well.                              *)
(*---------------------------------------------------------------------------*)

Definition iterateFn_def :
  iterateFn E comp 0 = componentFn E comp 0 ∧
  iterateFn E comp (SUC t) = componentFn (iterateFn E comp t) comp (SUC t)
End

(*---------------------------------------------------------------------------*)
(* Assumptions and guarantees. The use of HistExpr for assumptions means     *)
(* that, at time t, we can assume that the assumptions hold for all j ≤ t.   *)
(*---------------------------------------------------------------------------*)

Definition assumsVal_def:
   assumsVal E comp = bexprVal E (HistExpr (List_Conj comp.assumptions))
End

(*---------------------------------------------------------------------------*)
(* Evaluate the conjunction of guarantees of the component at time t         *)
(*---------------------------------------------------------------------------*)

Definition guarsVal_def:
   guarsVal E comp = bexprVal E (List_Conj comp.guarantees)
End

(*---------------------------------------------------------------------------*)
(* Support defs for well-formedness of component                             *)
(*---------------------------------------------------------------------------*)

Definition exprVarNames_def :
  exprVarNames (IntVar s) = {s} /\
  exprVarNames (IntLit i) = {} /\
  exprVarNames (AddExpr e1 e2)  = exprVarNames e1 UNION exprVarNames e2 /\
  exprVarNames (SubExpr e1 e2)  = exprVarNames e1 UNION exprVarNames e2 /\
  exprVarNames (MultExpr e1 e2) = exprVarNames e1 UNION exprVarNames e2 /\
  exprVarNames (DivExpr e1 e2)  = exprVarNames e1 UNION exprVarNames e2 /\
  exprVarNames (ModExpr e1 e2)  = exprVarNames e1 UNION exprVarNames e2 /\
  exprVarNames (PreExpr e)      = exprVarNames e /\
  exprVarNames (FbyExpr e1 e2)  = exprVarNames e1 UNION exprVarNames e2 /\
  exprVarNames (CondExpr b e1 e2) =
       (bexprVarNames b UNION exprVarNames e1 UNION exprVarNames e2)
  /\
  bexprVarNames (BoolVar s)     = {s} /\
  bexprVarNames (BoolLit b)     = {} /\
  bexprVarNames (NotExpr b)     = bexprVarNames b /\
  bexprVarNames (OrExpr b1 b2)  = (bexprVarNames b1 UNION bexprVarNames b2) /\
  bexprVarNames (AndExpr b1 b2) = (bexprVarNames b1 UNION bexprVarNames b2) /\
  bexprVarNames (ImpExpr b1 b2) = (bexprVarNames b1 UNION bexprVarNames b2) /\
  bexprVarNames (IffExpr b1 b2) = (bexprVarNames b1 UNION bexprVarNames b2) /\
  bexprVarNames (EqExpr e1 e2)  = (exprVarNames e1 UNION exprVarNames e2)   /\
  bexprVarNames (LtExpr e1 e2)  = (exprVarNames e1 UNION  exprVarNames e2)  /\
  bexprVarNames (LeqExpr e1 e2) = (exprVarNames e1 UNION exprVarNames e2)   /\
  bexprVarNames (HistExpr b)    = bexprVarNames b
End

(* -------------------------------------------------------------------------- *)
(* Variable name of a definition                                              *)
(* -------------------------------------------------------------------------- *)

Definition defName_def :
 defName (IntStmt s e) = s ∧
 defName (BoolStmt s b) = s
End

(* -------------------------------------------------------------------------- *)
(* Variable names in the body of a definition                                 *)
(* -------------------------------------------------------------------------- *)

Definition def_varNames_def :
  def_varNames (IntStmt s e) = exprVarNames e ∧
  def_varNames (BoolStmt s b) = bexprVarNames b
End

(* -------------------------------------------------------------------------- *)
(* Declared variables of a component                                          *)
(* -------------------------------------------------------------------------- *)

Definition varDecs_def :
  varDecs comp = comp.inports ++ MAP defName (comp.var_defs ++ comp.out_defs)
End

(* -------------------------------------------------------------------------- *)
(* Variable names in any rhs of a component's definitions                     *)
(* -------------------------------------------------------------------------- *)

Definition rhsNames_def:
 rhsNames comp =
   FOLDL (UNION) {} (MAP def_varNames (comp.var_defs ++ comp.out_defs))
End

(* -------------------------------------------------------------------------- *)
(* Variable names in rhs of defs and in assums + guarantees                   *)
(* -------------------------------------------------------------------------- *)

Definition compOccs_def:
 compOccs comp =
   FOLDL (UNION) (rhsNames comp)
         (MAP bexprVarNames (comp.assumptions ++ comp.guarantees))
End

(*---------------------------------------------------------------------------*)
(* A component C is wellformed if                                            *)
(*                                                                           *)
(*   (a) All the declared variables of C are distinct                        *)
(*   (b) There are no undeclared variables occurring in C                    *)
(*   (c) Output port variables (defined in C.out_defs) do not occur in the   *)
(*       rhs of any definition                                               *)
(*   (d) to add: if a var occurs before its defining eqn, it must be under   *)
(*       a pre.                                                              *)
(*   (e) to add: in every pre(e) expression, e is a variable                 *)
(*---------------------------------------------------------------------------*)

Definition Wellformed_def:
 Wellformed comp <=>
    ALL_DISTINCT (varDecs comp) /\
    (compOccs comp SUBSET set(varDecs comp)) /\
    (DISJOINT (set (MAP defName comp.out_defs)) (rhsNames comp))
End

(*---------------------------------------------------------------------------*)
(* "Supports E comp": each declared variable of C is in the domain of E.     *)
(* This combines with (b) above to ensure that every variable in the program *)
(* has a value in E.                                                         *)
(*---------------------------------------------------------------------------*)

Definition Supports_def:
  Supports E comp <=> (set (varDecs comp) SUBSET FDOM E)
End


(*---------------------------------------------------------------------------*)
(* A component is correct if it is syntactically well-formed and its variable*)
(* assignments, when iterated t+1 times, make the guarantees true at t.      *)
(*---------------------------------------------------------------------------*)

Definition Component_Correct_def:
  Component_Correct comp
    ⇔
  Wellformed comp /\
  ∀E t.
     Supports E comp ∧ assumsVal E comp t
       ==>
     guarsVal (iterateFn E comp t) comp t
End

(*---------------------------------------------------------------------------*)
(* A sequence of proofs that end up showing that a wellformed component      *)
(* never overwrites the input variables of the component. A kind of frame    *)
(* condition.                                                                *)
(*---------------------------------------------------------------------------*)

Theorem Comp_Vars_Disjoint:
 ∀comp.
    Wellformed comp ⇒
     DISJOINT (set (comp.inports)) (set (MAP defName comp.var_defs)) ∧
     DISJOINT (set (MAP defName comp.var_defs)) (set (MAP defName comp.out_defs)) ∧
     DISJOINT (set (MAP defName comp.out_defs)) (set (comp.inports))
Proof
 rw [Wellformed_def,varDecs_def,ALL_DISTINCT_APPEND,IN_DISJOINT]
 >> metis_tac[]
QED

Theorem stmtFn_Stable:
  ∀E stmt s.
     Wellformed comp ∧
     s IN set (comp.inports) ∧
     MEM stmt (comp.var_defs ++ comp.out_defs)
     ⇒
    ∀t. (stmtFn t E stmt ' s) = (E ' s)
Proof
  rw_tac std_ss []
  >> ‘DISJOINT (set (comp.inports)) (set (MAP defName comp.var_defs)) ∧
      DISJOINT (set (comp.inports)) (set (MAP defName comp.out_defs))’
       by metis_tac [DISJOINT_SYM,Comp_Vars_Disjoint]
  >> Cases_on ‘stmt’
  >> EVAL_TAC
  >> rw[]
  >> fs [IN_DISJOINT,MEM_MAP]
  >> metis_tac[defName_def]
QED

Theorem stmtFn_foldl[local]:
  ∀comp list E s.
     Wellformed comp ∧
     s IN set (comp.inports) ∧
     (set list SUBSET set (comp.var_defs ++ comp.out_defs))
     ⇒
    (FOLDL (stmtFn t) E list ' s) = (E ' s)
Proof
 gen_tac
  >> Induct
  >> rw[] >> EVAL_TAC >> rw[]
  >> metis_tac [stmtFn_Stable,MEM_APPEND]
QED

Theorem componentFn_Stable:
  ∀comp E t s.
     Wellformed comp ∧
     s IN set (comp.inports)
     ⇒
    (componentFn E comp t ' s) = (E ' s)
Proof
 rw[componentFn_def, stmtListFn_def] >> metis_tac [stmtFn_foldl,SUBSET_REFL]
QED

Theorem Inputs_Stable:
  ∀E comp s.
     Wellformed comp ∧ s IN set (comp.inports)
     ⇒
    ∀t. (iterateFn E comp t ' s) = (E ' s)
Proof
 rpt gen_tac
  >> strip_tac
  >> Induct
  >> rw [iterateFn_def]
  >> metis_tac [componentFn_Stable]
QED

(*---------------------------------------------------------------------------*)
(* A sequence of proofs showing that iteration doesn't alter earlier values  *)
(* in the stream that it generates. Monotonicity?                            *)
(*---------------------------------------------------------------------------*)

Theorem stmtFn_timeframe :
 ∀E stmt t1 t2. ~(t1=t2) ⇒ ∀s. stmtFn t1 E stmt ' s t2 = E ' s t2
Proof
 Cases_on ‘stmt’ >> EVAL_TAC >> rw[] >> rw[combinTheory.APPLY_UPDATE_THM]
QED

Theorem stmtFn_foldl_timeframe[local]:
 ∀list E t1 t2 s. ~(t1=t2) ⇒ (FOLDL (stmtFn t2) E list ' s) t1 = (E ' s) t1
Proof
 Induct >> EVAL_TAC >> rw[stmtFn_timeframe]
QED

Theorem componentFn_timeframe:
 ∀comp E t1 t2. ~(t1=t2) ⇒ ∀s. (componentFn E comp t2 ' s) t1 = (E ' s) t1
Proof
 rw[componentFn_def,stmtListFn_def,stmtFn_foldl_timeframe]
QED

Theorem iterateFn_mono_lem[local] :
 !k m E comp s.
    (iterateFn E comp m ' s) m = (iterateFn E comp (m + k) ' s) m
Proof
 Induct
  >> simp_tac std_ss [ADD_CLAUSES]
  >> rw_tac std_ss [Once iterateFn_def]
  >> rw [componentFn_timeframe]
QED

Theorem iterateFn_timeframe :
 !E comp s m n.
   m ≤ n ⇒ ((iterateFn E comp n ' s) m = (iterateFn E comp m ' s) m)
Proof
 rpt strip_tac
  >> ‘∃k. n = m + k’ by intLib.ARITH_TAC
  >> rw[]
  >> metis_tac [ADD_SYM,iterateFn_mono_lem]
QED

val _ = export_theory();
