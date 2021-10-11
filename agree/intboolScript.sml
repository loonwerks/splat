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
  exprVal E (PreExpr e) t =
     (if t = 0 then ARB else exprVal E e (t-1)) /\
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
(* Value of statement in given environment                                   *)
(*---------------------------------------------------------------------------*)

Definition stmtVal_def :
 stmtVal E t (IntStmt s e) = (s, IntValue(exprVal E e t)) ∧
 stmtVal E t (BoolStmt s b) = (s, BoolValue(bexprVal E b t))
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
(* Evaluate the conjunction of assumptions of the component at time t. The   *)
(* use of HistExpr means that at time t we can assume that the assumptions   *)
(* hold for all j ≤ t.                                                       *)
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
(* Syntactic restrictions on components                                      *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Well-formedness of component                                              *)
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

Definition varDecs_def :
  varDecs comp = comp.inports ++ MAP defName (comp.var_defs ++ comp.out_defs)
End

(* -------------------------------------------------------------------------- *)
(* Variable names in any rhs of a component's definitions                     *)
(* -------------------------------------------------------------------------- *)

Definition defVars_def:
 defVars comp =
   FOLDL (UNION) {} (MAP def_varNames (comp.var_defs ++ comp.out_defs))
End

(* -------------------------------------------------------------------------- *)
(* Variable names in rhs of defs and in assums + guarantees                   *)
(* -------------------------------------------------------------------------- *)

Definition compVars_def:
 compVars comp =
   FOLDL (UNION) (defVars comp)
         (MAP bexprVarNames (comp.assumptions ++ comp.guarantees))
End

(*---------------------------------------------------------------------------*)
(* A (environment,component) pair (E,C) is wellformed if                     *)
(*                                                                           *)
(*   (a) All the declared variables of C are distinct                        *)
(*   (b) Each declared variable of C is in the domain of E                   *)
(*   (c) There are no undeclared variables occurring in C                    *)
(*   (d) Output port variables (defined in C.out_defs) do not occur in the   *)
(*       rhs of any definition                                               *)
(*---------------------------------------------------------------------------*)

Definition Wellformed_def:
 Wellformed E comp <=>
    ALL_DISTINCT (varDecs comp) /\
    (set (varDecs comp) SUBSET FDOM E) /\
    (compVars comp SUBSET set(varDecs comp)) /\
    (DISJOINT (set (MAP defName comp.out_defs)) (defVars comp))
End

(*---------------------------------------------------------------------------*)
(* A component is correct if its variable assignments, when iterated, make   *)
(* the guarantees true, for any time t.                                      *)
(*---------------------------------------------------------------------------*)

Definition Component_Correct_def:
  Component_Correct comp
    ⇔
  ∀E t.
     Wellformed E comp /\
     assumsVal E comp t
        ==>
      guarsVal (iterateFn E comp t) comp t
End


(*---------------------------------------------------------------------------*)
(* A sequence of proofs that end up showing that a wellformed (env,comp)     *)
(* pair never overwrites the input variables of the component.               *)
(*---------------------------------------------------------------------------*)

Theorem Comp_Vars_Disjoint:
 ∀E comp.
    Wellformed E comp ⇒
     DISJOINT (set (comp.inports)) (set (MAP defName comp.var_defs)) ∧
     DISJOINT (set (MAP defName comp.var_defs)) (set (MAP defName comp.out_defs)) ∧
     DISJOINT (set (MAP defName comp.out_defs)) (set (comp.inports))
Proof
 rw [Wellformed_def,varDecs_def,ALL_DISTINCT_APPEND,IN_DISJOINT]
 >> metis_tac[]
QED

Theorem stmtFn_fdom_stable:
  ∀E comp stmt t.
     set (varDecs comp) SUBSET FDOM E
     ⇒
     set (varDecs comp) SUBSET FDOM (stmtFn t E stmt)
Proof
 Cases_on ‘stmt’
   >> EVAL_TAC
   >> rw[]
   >> metis_tac [SUBSET_INSERT_RIGHT]
QED

Theorem stmtListFn_fdom_stable:
  ∀list E comp t.
     set (varDecs comp) SUBSET FDOM E
     ⇒
     set (varDecs comp) SUBSET FDOM (stmtListFn E list t)
Proof
 Induct
  >> fs [stmtListFn_def]
  >> metis_tac [stmtFn_fdom_stable]
QED

Theorem componentFn_fdom_stable:
  ∀E comp t.
     set (varDecs comp) SUBSET FDOM E
     ⇒
     set (varDecs comp) SUBSET FDOM (componentFn E comp t)
Proof
  metis_tac [componentFn_def,stmtListFn_fdom_stable]
QED

Theorem Wellformed_stmtFn:
  ∀E comp stmt t.
     Wellformed E comp ∧
     (MEM stmt comp.var_defs ∨ MEM stmt comp.out_defs)
     ⇒ Wellformed (stmtFn t E stmt) comp
Proof
 Cases_on ‘stmt’
 >> EVAL_TAC
 >> rw[]
 >> metis_tac [SUBSET_INSERT_RIGHT]
QED

Theorem Wellformed_componentFn:
  ∀E comp t.
     Wellformed E comp
     ⇒
    Wellformed (componentFn E comp t) comp
Proof
 rw[Wellformed_def] >> metis_tac [componentFn_fdom_stable]
QED

Theorem Wellformed_iterateFn:
  ∀E comp stmt.
     Wellformed E comp
     ⇒
     ∀t. Wellformed (iterateFn E comp t) comp
Proof
 rpt gen_tac
 >> strip_tac
 >> Induct
 >> rw [iterateFn_def]
 >> metis_tac [Wellformed_componentFn]
QED

Theorem stmtFn_Stable:
  ∀E stmt s.
     Wellformed E comp ∧ s IN set (comp.inports) ∧
     (MEM stmt comp.var_defs ∨ MEM stmt comp.out_defs)
     ⇒
    ∀t. (stmtFn t E stmt ' s) = (E ' s)
Proof
 rpt gen_tac >> strip_tac
  >> ‘DISJOINT (set (comp.inports)) (set (MAP defName comp.var_defs)) ∧
      DISJOINT (set (comp.inports)) (set (MAP defName comp.out_defs))’
       by metis_tac [DISJOINT_SYM,Comp_Vars_Disjoint]
  >> Cases_on ‘stmt’
  >> EVAL_TAC
  >> rw[]
  >> fs [IN_DISJOINT,MEM_MAP]
  >> metis_tac[defName_def]
QED

Theorem stmtFn_FOLDL_Stable:
  ∀list E s comp.
     Wellformed E comp ∧ s IN set (comp.inports) ∧
     (set list SUBSET (set comp.var_defs UNION set comp.out_defs))
     ⇒
    (FOLDL (stmtFn t) E list ' s) = (E ' s)
Proof
 Induct
  >> rw[]
  >> ‘DISJOINT (set (comp.inports)) (set (MAP defName comp.var_defs)) ∧
      DISJOINT (set (comp.inports)) (set (MAP defName comp.out_defs))’
       by metis_tac [DISJOINT_SYM,Comp_Vars_Disjoint]
  >> EVAL_TAC
  >> rw[]
  >> metis_tac [stmtFn_Stable,Wellformed_stmtFn]
QED

Theorem componentFn_Stable:
  ∀E comp t s.
     Wellformed E comp ∧ s IN set (comp.inports)
     ⇒
    (componentFn E comp t ' s) = (E ' s)
Proof
  rw [componentFn_def,stmtListFn_def]
  >> irule stmtFn_FOLDL_Stable
  >> fs[Wellformed_def]
  >> qexists_tac ‘comp’
  >> rw[]
QED

Theorem Inputs_Stable:
  ∀E comp s.
     Wellformed E comp ∧ s IN set (comp.inports)
     ⇒
    ∀t. (iterateFn E comp t ' s) = (E ' s)
Proof
 rpt gen_tac
  >> strip_tac
  >> Induct
  >> rw [iterateFn_def]
  >- metis_tac [componentFn_Stable]
  >- metis_tac [componentFn_Stable,Wellformed_iterateFn]
QED


val _ = export_theory();
