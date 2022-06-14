
open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory;

val _ = intLib.prefer_int();

val _ = new_theory "agree_full";


(*---------------------------------------------------------------------------*)
(* Ports                                                                     *)
(*---------------------------------------------------------------------------*)

Datatype:
 port = Data 'a
      | Event_Only 'a
      | Event_Data ('a option)
End

(*---------------------------------------------------------------------------*)
(* Expression values                                                         *)
(*---------------------------------------------------------------------------*)

Datatype:
 value = BoolValue bool
       | IntValue int
       | RecdValue ((string # value) list)
       | ArrayValue (value list)
       | PortValue (value port)
End

Definition intOf_def :
 intOf (IntValue i) = i
End

Definition boolOf_def :
 boolOf (BoolValue b) = b
End

Definition portOf_def :
  portOf (PortValue p) = p
End

Definition recdOf_def :
  recdOf (RecdValue r) = r
End

Definition arrayOf_def :
  arrayOf (ArrayValue a) = a
End

(*---------------------------------------------------------------------------*)
(* Port operations                                                           *)
(*---------------------------------------------------------------------------*)

Definition eventOf_def:
  eventOf (Data x) = F /\
  eventOf (Event_Only bv) = boolOf bv  /\
  eventOf (Event_Data NONE) = F  /\
  eventOf (Event_Data (SOME x)) = T
End

Definition dataOf_def:
  dataOf (Data x) = x /\
  dataOf (Event_Data (SOME x)) = x /\
  dataOf otherwise = ARB
End

(*---------------------------------------------------------------------------*)
(* Types (unused so far)                                                     *)
(*---------------------------------------------------------------------------*)

Datatype:
 ty = BoolTy
    | Signed int num
    | RecdTy ((string # ty) list)
    | ArrayTy ty num
End

(*---------------------------------------------------------------------------*)
(* Expressions                                                               *)
(*---------------------------------------------------------------------------*)

Datatype:
  expr = Var string
       | IntLit int
       | BoolLit bool
       | AddExpr expr expr
       | SubExpr expr expr
       | MultExpr expr expr
       | DivExpr expr expr
       | ModExpr expr expr
       | NotExpr expr
       | OrExpr expr expr
       | AndExpr expr expr
       | ImpExpr expr expr
       | IffExpr expr expr
       | EqExpr expr expr
       | LeqExpr expr expr
       | LtExpr expr expr
       | RecdExpr ((string # expr) list)
       | RecdProj expr string
       | ArrayExpr (expr list)
       | ArraySub expr expr
       | PortEvent expr
       | PortData expr
       | PreExpr expr
       | FbyExpr expr expr
       | CondExpr expr expr expr
       | HistExpr expr
End

(*---------------------------------------------------------------------------*)
(* Used solely for termination of fns over expr                              *)
(*---------------------------------------------------------------------------*)

Definition esize_def :
  esize (Var s) = 0n  /\
  esize (IntLit i) = 0  /\
  esize (BoolLit b) = 0  /\
  esize (AddExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (SubExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (MultExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (DivExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (ModExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (NotExpr e) = 1 + esize e  /\
  esize (OrExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (AndExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (ImpExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (IffExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (EqExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (LeqExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (LtExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (RecdExpr fields) = 1 + list_size (esize o SND) fields /\
  esize (RecdProj e s) = 1 + esize e /\
  esize (ArrayExpr elts) = 1 + list_size esize elts /\
  esize (ArraySub e1 e2) = 1 + esize e1 + esize e2  /\
  esize (PortEvent e) = 1 + esize e  /\
  esize (PortData e) = 1 + esize e  /\
  esize (PreExpr e) = 1 + esize e  /\
  esize (FbyExpr e1 e2) = 1 + esize e1 + esize e2  /\
  esize (CondExpr e1 e2 e3) = 1 + esize e1 + esize e2 + esize e3  /\
  esize (HistExpr e) = 1 + esize e
Termination
  WF_REL_TAC ‘measure expr_size’
End

(*---------------------------------------------------------------------------*)
(* Derived syntax                                                            *)
(*---------------------------------------------------------------------------*)

Definition prev_def :
 PrevExpr (x,y) = FbyExpr y (PreExpr x)
End

Definition List_Conj_def :
   List_Conj blist = FOLDR AndExpr (BoolLit T) blist
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

(*---------------------------------------------------------------------------*)
(* Value of expression in given environments                                 *)
(*---------------------------------------------------------------------------*)

Definition RecdProjValue_def:
  RecdProjValue fields s =
    case FIND ((=) s o FST) fields
     of SOME p => SND p
      | NONE => ARB
End

Definition ArraySubValue_def:
  ArraySubValue arr i = EL (Num i) arr
End

Definition exprVal_def :
  exprVal E (Var s) (t:num) = (E ' s) t /\
  exprVal E (IntLit i) t    = IntValue i /\
  exprVal E (BoolLit b) t   = BoolValue b /\
  exprVal E (AddExpr e1 e2) t =
        IntValue(intOf (exprVal E e1 t) + intOf (exprVal E e2 t)) /\
  exprVal E (SubExpr e1 e2) t =
        IntValue(intOf (exprVal E e1 t) - intOf(exprVal E e2 t)) /\
  exprVal E (MultExpr e1 e2) t =
        IntValue(intOf(exprVal E e1 t) * intOf(exprVal E e2 t)) /\
  exprVal E (DivExpr e1 e2) t =
        IntValue(intOf(exprVal E e1 t) / intOf(exprVal E e2 t)) /\
  exprVal E (ModExpr e1 e2) t =
        IntValue(intOf(exprVal E e1 t) % intOf(exprVal E e2 t)) /\
  exprVal E (NotExpr e) t =
        BoolValue (~boolOf(exprVal E e t)) /\
  exprVal E (OrExpr e1 e2) t =
        BoolValue(boolOf(exprVal E e1 t) \/ boolOf(exprVal E e2 t)) /\
  exprVal E (AndExpr e1 e2) t =
        BoolValue(boolOf(exprVal E e1 t) /\ boolOf(exprVal E e2 t)) /\
  exprVal E (ImpExpr e1 e2) t =
        BoolValue(boolOf(exprVal E e1 t) ==> boolOf(exprVal E e2 t)) /\
  exprVal E (IffExpr e1 e2) t =
        BoolValue(boolOf(exprVal E e1 t) <=> boolOf(exprVal E e2 t)) /\
  exprVal E (EqExpr e1 e2) t =
        BoolValue (exprVal E e1 t = exprVal E e2 t) /\
  exprVal E (LeqExpr e1 e2) t =
        BoolValue(intOf(exprVal E e1 t) <= intOf(exprVal E e2 t)) /\
  exprVal E (LtExpr e1 e2) t =
        BoolValue(intOf(exprVal E e1 t) < intOf(exprVal E e2 t)) /\
  exprVal E (RecdExpr fields) t =
        RecdValue (MAP (\p. (FST p, exprVal E (SND p) t)) fields) /\
  exprVal E (RecdProj e s) t =
        RecdProjValue (recdOf (exprVal E e t)) s /\
  exprVal E (ArrayExpr elist) t =
        ArrayValue (MAP (\e. exprVal E e t) elist)  /\
  exprVal E (ArraySub e1 e2) t =
        ArraySubValue (arrayOf(exprVal E e1 t)) (intOf(exprVal E e2 t)) /\
  exprVal E (PortEvent e) t =
        BoolValue(eventOf(portOf (exprVal E e t))) /\
  exprVal E (PortData e) t =
        dataOf(portOf(exprVal E e t)) /\
  exprVal E (PreExpr e) t = (if t=0 then ARB else exprVal E e (t-1)) /\
  exprVal E (FbyExpr e1 e2) t =
     (if t = 0 then exprVal E e1 0 else exprVal E e2 t) /\
  exprVal E (CondExpr b e1 e2) t =
     (if boolOf(exprVal E b t) then exprVal E e1 t else exprVal E e2 t) /\
  exprVal E (HistExpr e) t =
     BoolValue(!n:num. n ≤ t ==> boolOf(exprVal E e n))
Termination
  WF_REL_TAC ‘measure (esize o FST o SND)’ >> rw[esize_def]
  >- (Induct_on ‘elist’ >> rw[list_size_def] >> rw[] >> res_tac >> rw[])
  >- (Induct_on ‘fields’ >> rw[list_size_def] >> rw[] >> res_tac >> rw[])
End

(*---------------------------------------------------------------------------*)
(* State variable definitions                                                *)
(*---------------------------------------------------------------------------*)

Datatype:
  stmt = Stmt string expr
End

Definition varOf_def :
 varOf (Stmt s exp) = s
End

Definition bodyOf_def :
 bodyOf (Stmt s exp) = exp
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
                 assumptions : expr list;
                 guarantees  : expr list |>
End

Definition inputOf_def :
 inputOf comp env = DRESTRICT env (set comp.inports)
End

Definition stateOf_def :
 stateOf comp env = DRESTRICT env (set (MAP varOf comp.var_defs))
End

Definition outputOf_def :
 outputOf comp env = DRESTRICT env (set (MAP varOf comp.out_defs))
End

(*---------------------------------------------------------------------------*)
(* Assumptions and guarantees. The use of HistExpr for assumptions means     *)
(* that, at time t, we can assume that the assumptions hold for all j ≤ t.   *)
(*---------------------------------------------------------------------------*)

Definition assumsVal_def:
  assumsVal E comp = exprVal E (HistExpr (List_Conj comp.assumptions))
End

(*---------------------------------------------------------------------------*)
(* Evaluate the conjunction of guarantees of the component at time t         *)
(*---------------------------------------------------------------------------*)

Definition guarsVal_def:
  guarsVal E comp = exprVal E (List_Conj comp.guarantees)
End


(*---------------------------------------------------------------------------*)
(* A statement updates a binding in environment E                            *)
(*---------------------------------------------------------------------------*)

Definition stmtFn_def :
 stmtFn t E (Stmt s exp) = updateEnv E s (exprVal E exp t) t
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

(* -------------------------------------------------------------------------- *)
(* Declared variables of a component                                          *)
(* -------------------------------------------------------------------------- *)

Definition varDecs_def :
  varDecs comp = comp.inports ++ MAP varOf (comp.var_defs ++ comp.out_defs)
End

(*---------------------------------------------------------------------------*)
(* Support defs for well-formedness of component                             *)
(*---------------------------------------------------------------------------*)

Definition exprVars_def :
  exprVars (Var s) = {s} /\
  exprVars (IntLit i) = {} /\
  exprVars (BoolLit b) = {} /\
  exprVars (AddExpr e1 e2) = exprVars e1 UNION exprVars e2 /\
  exprVars (SubExpr e1 e2) = exprVars e1 UNION exprVars e2 /\
  exprVars (MultExpr e1 e2) = exprVars e1 UNION exprVars e2 /\
  exprVars (DivExpr e1 e2) = exprVars e1 UNION exprVars e2 /\
  exprVars (ModExpr e1 e2) = exprVars e1 UNION exprVars e2 /\
  exprVars (NotExpr b)     = exprVars b /\
  exprVars (OrExpr b1 b2)  = (exprVars b1 UNION exprVars b2) /\
  exprVars (AndExpr b1 b2) = (exprVars b1 UNION exprVars b2) /\
  exprVars (ImpExpr b1 b2) = (exprVars b1 UNION exprVars b2) /\
  exprVars (IffExpr b1 b2) = (exprVars b1 UNION exprVars b2) /\
  exprVars (EqExpr e1 e2)  = (exprVars e1 UNION exprVars e2) /\
  exprVars (LtExpr e1 e2)  = (exprVars e1 UNION exprVars e2) /\
  exprVars (LeqExpr e1 e2) = (exprVars e1 UNION exprVars e2) /\
  exprVars (HistExpr b)    = exprVars b /\
  exprVars (PreExpr e)     = exprVars e /\
  exprVars (FbyExpr e1 e2) = (exprVars e1 UNION exprVars e2) /\
  exprVars (CondExpr a b c) = (exprVars a UNION exprVars b UNION exprVars c)
End

(* -------------------------------------------------------------------------- *)
(* Variable names in any rhs of a component's definitions                     *)
(* -------------------------------------------------------------------------- *)

(*
Definition rhsNames_def:
 rhsNames comp =
   FOLDL (UNION) {}
      (MAP (exprVars o bodyOf) (comp.var_defs ++ comp.out_defs))
End

(* -------------------------------------------------------------------------- *)
(* Variable names in rhs of defs and in assums + guarantees                   *)
(* -------------------------------------------------------------------------- *)

Definition compBodyVars_def:
 compBodyVars comp =
   FOLDL (UNION) {}
         (MAP exprVars (comp.assumptions ++ comp.guarantees))
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
    (DISJOINT (set (MAP varOf comp.out_defs)) (rhsNames comp))
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
    <=>
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
     DISJOINT (set (comp.inports)) (set (MAP varOf comp.var_defs)) ∧
     DISJOINT (set (MAP varOf comp.var_defs)) (set (MAP varOf comp.out_defs)) ∧
     DISJOINT (set (MAP varOf comp.out_defs)) (set (comp.inports))
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
  >> ‘DISJOINT (set (comp.inports)) (set (MAP varOf comp.var_defs)) ∧
      DISJOINT (set (comp.inports)) (set (MAP varOf comp.out_defs))’
       by metis_tac [DISJOINT_SYM,Comp_Vars_Disjoint]
  >> Cases_on ‘stmt’
  >> EVAL_TAC
  >> rw[]
  >> fs [IN_DISJOINT,MEM_MAP]
  >> metis_tac[varOf_def]
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
(* There is a special stream---isInit---used by programs to tell if in the   *)
(* initial step or not. Defined as                                           *)
(*                                                                           *)
(*  isInit = T -> F                                                          *)
(*---------------------------------------------------------------------------*)

Definition isInit_Stream_def :
   isInit_Stream strm ⇔ ∀n. strm n = BoolValue (n = 0n)
End

Theorem isInit_Stable:
  ∀E comp t s.
    Wellformed comp ∧
    "isInit" IN set comp.inports ∧
    isInit_Stream (E ' "isInit")
     ⇒
    ∀t. isInit_Stream (strmSteps E comp t ' "isInit")
Proof
  metis_tac [Inputs_Stable]
QED

(*---------------------------------------------------------------------------*)
(* A sequence of proofs showing that iteration doesn't alter earlier values  *)
(* in the environment it generates.                                          *)
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
(* A sequence of proofs showing that evaluation doesn't change the domain    *)
(* of the environment.                                                       *)
(*---------------------------------------------------------------------------*)

Theorem stmtFn_fdom :
  ∀E stmt t. varOf stmt IN FDOM E ⇒ FDOM (stmtFn t E stmt) = FDOM E
Proof
  Cases_on ‘stmt’ >> EVAL_TAC >> rw[SUBSET_DEF]
QED

Theorem stmtFn_foldl_fdom[local]:
 ∀list E t. EVERY (\stmt. varOf stmt IN FDOM E) list
             ⇒
            FDOM(FOLDL (stmtFn t) E list) = FDOM E
Proof
  Induct
    >> rw []
    >> ‘FDOM (stmtFn t E h) = FDOM E’ by metis_tac[stmtFn_fdom]
    >> ‘EVERY (\stmt. varOf stmt IN FDOM (stmtFn t E h)) list’ by rw[]
    >> metis_tac[]
QED

Theorem EVERY_SUBSET :
  ∀P l. EVERY P l <=> set l SUBSET P
Proof
  simp [EVERY_MEM,SUBSET_DEF,IN_DEF]
QED

Theorem strmStep_fdom:
 ∀comp E t. Supports E comp ⇒ FDOM(strmStep E comp t) = FDOM E
Proof
 rw[strmStep_def,stmtListFn_def,Supports_def,varDecs_def]
 >> irule stmtFn_foldl_fdom
 >> fs[LIST_TO_SET_MAP,EVERY_SUBSET]
 >> fs [SUBSET_DEF]
 >> metis_tac[]
QED

Theorem strmSteps_fdom :
 ∀comp E t. Supports E comp ⇒ FDOM(strmSteps E comp t) = FDOM E
Proof
 Induct_on ‘t’
  >> rw [strmSteps_def]
  >> metis_tac [strmStep_fdom,Supports_def]
QED

Theorem Supports_strmSteps:
  ∀E comp. Supports E comp ==> ∀t. Supports (strmSteps E comp t) comp
Proof
  rpt strip_tac
  >> drule strmSteps_fdom
  >> fs [Supports_def]
QED

Theorem input_of_stable:
  ∀E comp t.
     Wellformed comp ∧ Supports E comp ⇒ input_of comp E = input_of comp (strmSteps E comp t)
Proof
 rw [input_of_def,fmap_EXT,FDOM_DRESTRICT]
  >- rw [strmSteps_fdom]
  >- (rw [DRESTRICT_DEF]
      >- metis_tac [Inputs_Stable]
      >- metis_tac [strmSteps_fdom])
QED
*)

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
