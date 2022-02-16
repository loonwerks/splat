open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory;

val _ = intLib.prefer_int();

val _ = new_theory "agree";

(*---------------------------------------------------------------------------*)
(* Arithmetic and boolean expressions. Conventional, except that we have     *)
(* Lustre operators "pre" and "fby" as well as a temporal operator HistExpr  *)
(* ("Historically"). The polymorphic operators equality, pre, fby, and cond  *)
(* are copied to cover both integers and booleans.                           *)
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
       | BoolPreExpr bexpr
       | BoolFbyExpr bexpr bexpr
       | BoolCondExpr bexpr bexpr bexpr
End

Definition List_Conj_def :
   List_Conj blist = FOLDR AndExpr (BoolLit T) blist
End

(*---------------------------------------------------------------------------*)
(* Variable definitions                                                      *)
(*---------------------------------------------------------------------------*)

Datatype:
  stmt = IntStmt string expr
       | BoolStmt string bexpr
End

(* -------------------------------------------------------------------------- *)
(* Variable name of a definition                                              *)
(* -------------------------------------------------------------------------- *)

Definition defName_def :
 defName (IntStmt s e) = s ∧
 defName (BoolStmt s b) = s
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

(* -------------------------------------------------------------------------- *)
(* Declared variables of a component                                          *)
(* -------------------------------------------------------------------------- *)

Definition varDecs_def :
  varDecs comp = comp.inports ++ MAP defName (comp.var_defs ++ comp.out_defs)
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
(* A stream environment is a finite map from port names to value streams      *)
(* -------------------------------------------------------------------------- *)

Type strm_env = “:string |-> (num -> value)”

Definition updateEnv_def :
 updateEnv (fmap:strm_env) name value t =
   let strm = fmap ' name;
       strm' = strm (| t |-> value |)
   in
     fmap |+ (name,strm')
End

Definition input_of_def :
 input_of comp env = DRESTRICT env (set comp.inports)
End

Definition state_of_def :
 state_of comp env = DRESTRICT env (set (MAP defName comp.var_defs))
End

Definition output_of_def :
 output_of comp env = DRESTRICT env (set (MAP defName comp.out_defs))
End

(*---------------------------------------------------------------------------*)
(* Value of expression in given environments                                 *)
(*---------------------------------------------------------------------------*)

Definition exprVal_def :
  exprVal E (IntVar s) (t:num) = int_of ((E ' s) t) /\
  exprVal E (IntLit i) t       = i /\
  exprVal E (AddExpr e1 e2) t  = exprVal E e1 t + exprVal E e2 t /\
  exprVal E (SubExpr e1 e2) t  = exprVal E e1 t - exprVal E e2 t /\
  exprVal E (MultExpr e1 e2) t = exprVal E e1 t * exprVal E e2 t /\
  exprVal E (DivExpr e1 e2) t = exprVal E e1 t / exprVal E e2 t /\
  exprVal E (ModExpr e1 e2) t = exprVal E e1 t % exprVal E e2 t /\
  exprVal E (PreExpr e) t = (if t=0 then ARB else exprVal E e (t-1)) /\
  exprVal E (FbyExpr e1 e2) t =
     (if t = 0 then exprVal E e1 0 else exprVal E e2 t) /\
  exprVal E (CondExpr b e1 e2) t =
     (if bexprVal E b t then exprVal E e1 t else exprVal E e2 t)
  /\
  bexprVal E (BoolVar s) t     = bool_of ((E ' s) t) /\
  bexprVal E (BoolLit b) t     = b /\
  bexprVal E (NotExpr b) t     = (~bexprVal E b t) /\
  bexprVal E (OrExpr b1 b2) t  = (bexprVal E b1 t \/ bexprVal E b2 t) /\
  bexprVal E (AndExpr b1 b2) t = (bexprVal E b1 t /\ bexprVal E b2 t) /\
  bexprVal E (ImpExpr b1 b2) t = (bexprVal E b1 t ⇒ bexprVal E b2 t) /\
  bexprVal E (IffExpr b1 b2) t = (bexprVal E b1 t = bexprVal E b2 t) /\
  bexprVal E (EqExpr e1 e2) t  = (exprVal E e1 t = exprVal E e2 t)   /\
  bexprVal E (LtExpr e1 e2) t  = (exprVal E e1 t < exprVal E e2 t)   /\
  bexprVal E (LeqExpr e1 e2) t = (exprVal E e1 t <= exprVal E e2 t)  /\
  bexprVal E (HistExpr b) t    = (!n. n <= t ==> bexprVal E b n)     ∧
  bexprVal E (BoolPreExpr b) t = (if t=0 then ARB else bexprVal E b (t-1)) /\
  bexprVal E (BoolFbyExpr b1 b2) t =
     (if t = 0 then bexprVal E b1 0 else bexprVal E b2 t) /\
  bexprVal E (BoolCondExpr b b1 b2) t =
     (if bexprVal E b t then bexprVal E b1 t else bexprVal E b2 t)
End


Definition prev_def :
 PrevExpr (x,y) = FbyExpr y (PreExpr x)
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

Definition strmStep_def :
  strmStep E comp t = stmtListFn E (comp.var_defs ++ comp.out_defs) t
End

(*---------------------------------------------------------------------------*)
(* Correctness of component: the effects  of the component model its spec.   *)
(* We first define a function over t that iterates variable assignments of   *)
(* the component up to and including time t. Time 0 is when the ports get    *)
(* their first value, so strmStep is calculated there as well.               *)
(*---------------------------------------------------------------------------*)

Definition strmSteps_def :
  strmSteps E comp 0 = strmStep E comp 0 ∧
  strmSteps E comp (SUC t) = strmStep (strmSteps E comp t) comp (SUC t)
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
  exprVarNames (FbyExpr e1 e2)  = (exprVarNames e1 UNION exprVarNames e2) /\
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
  bexprVarNames (LtExpr e1 e2)  = (exprVarNames e1 UNION exprVarNames e2)   /\
  bexprVarNames (LeqExpr e1 e2) = (exprVarNames e1 UNION exprVarNames e2)   /\
  bexprVarNames (HistExpr b)    = bexprVarNames b /\
  bexprVarNames (BoolPreExpr b) = bexprVarNames b /\
  bexprVarNames (BoolFbyExpr b1 b2) = (bexprVarNames b1 UNION bexprVarNames b2) /\
  bexprVarNames (BoolCondExpr b b1 b2) =
       (bexprVarNames b UNION bexprVarNames b1 UNION bexprVarNames b2)
End

(* -------------------------------------------------------------------------- *)
(* Variable names in the body of a definition                                 *)
(* -------------------------------------------------------------------------- *)

Definition def_rhsNames_def :
  def_rhsNames (IntStmt s e) = exprVarNames e ∧
  def_rhsNames (BoolStmt s b) = bexprVarNames b
End

(* -------------------------------------------------------------------------- *)
(* Variable names in any rhs of a component's definitions                     *)
(* -------------------------------------------------------------------------- *)

Definition rhsNames_def:
 rhsNames comp =
   FOLDL (UNION) {} (MAP def_rhsNames (comp.var_defs ++ comp.out_defs))
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
     guarsVal (strmSteps E comp t) comp t
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

Theorem strmStep_Stable:
  ∀comp E t s.
     Wellformed comp ∧
     s IN set (comp.inports)
     ⇒
    (strmStep E comp t ' s) = (E ' s)
Proof
 rw[strmStep_def, stmtListFn_def] >> metis_tac [stmtFn_foldl,SUBSET_REFL]
QED

Theorem Inputs_Stable:
  ∀E comp s.
     Wellformed comp ∧ s IN set (comp.inports)
     ⇒
    ∀t. (strmSteps E comp t ' s) = (E ' s)
Proof
 rpt gen_tac
  >> strip_tac
  >> Induct
  >> rw [strmSteps_def]
  >> metis_tac [strmStep_Stable]
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

Theorem strmStep_timeframe:
 ∀comp E t1 t2. ~(t1=t2) ⇒ ∀s. (strmStep E comp t2 ' s) t1 = (E ' s) t1
Proof
 rw[strmStep_def,stmtListFn_def,stmtFn_foldl_timeframe]
QED

Theorem strmSteps_mono_lem[local] :
 !k m E comp s.
    (strmSteps E comp m ' s) m = (strmSteps E comp (m + k) ' s) m
Proof
 Induct
  >> simp_tac std_ss [ADD_CLAUSES]
  >> rw_tac std_ss [Once strmSteps_def]
  >> rw [strmStep_timeframe]
QED

Theorem strmSteps_timeframe :
 !E comp s t u.
   t ≤ u ⇒ ((strmSteps E comp u ' s) t = (strmSteps E comp t ' s) t)
Proof
 rpt strip_tac
  >> ‘∃k. u = t + k’ by intLib.ARITH_TAC
  >> rw[]
  >> metis_tac [ADD_SYM,strmSteps_mono_lem]
QED

(*---------------------------------------------------------------------------*)
(* Stuff to help the Latex output look nicer                                 *)
(*---------------------------------------------------------------------------*)

val _ = TeX_notation {hol = "(|", TeX = ("\\HOLTokenWhiteParenLeft", 1)}
val _ = TeX_notation {hol = "|)", TeX = ("\\HOLTokenWhiteParenRight", 1)};

val _ = TeX_notation {hol = UTF8.chr 0x2987, TeX = ("\\HOLTokenWhiteParenLeft", 1)}
val _ = TeX_notation {hol = UTF8.chr 0x2988, TeX = ("\\HOLTokenWhiteParenRight", 1)}

val _ = TeX_notation {hol = "|->",           TeX = ("\\HOLTokenMapto", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x21A6, TeX = ("\\HOLTokenMapto", 1)}

val _ = TeX_notation {hol = "int_of", TeX = ("int\\_of", 6)};
val _ = TeX_notation {hol = "bool_of", TeX = ("bool\\_of", 7)};

val _ = TeX_notation {hol = "List_Conj", TeX = ("List\\_Conj", 9)};
val _ = TeX_notation {hol = "Component_Correct", TeX = ("Component\\_Correct", 17)};
val _ = TeX_notation {hol = "input_of", TeX = ("input\\_of", 8)};
val _ = TeX_notation {hol = "state_of", TeX = ("state\\_of", 8)};
val _ = TeX_notation {hol = "output_of", TeX = ("output\\_of", 9)};

val _ = export_theory();
