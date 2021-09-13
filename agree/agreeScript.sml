open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory;

val _ = intLib.prefer_int();

val _ = new_theory "agree";

val _ = TeX_notation {hol = "(|", TeX = ("\\HOLTokenWhiteParenLeft", 1)}
val _ = TeX_notation {hol = "|)", TeX = ("\\HOLTokenWhiteParenRight", 1)};

val _ = TeX_notation {hol = UTF8.chr 0x2987, TeX = ("\\HOLTokenWhiteParenLeft", 1)}
val _ = TeX_notation {hol = UTF8.chr 0x2988, TeX = ("\\HOLTokenWhiteParenRight", 1)}

val _ = TeX_notation {hol = "|->",           TeX = ("\\HOLTokenMapto", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x21A6, TeX = ("\\HOLTokenMapto", 1)}


(*---------------------------------------------------------------------------*)
(* Arithmetic expressions. Conventional, except that there are two kinds of  *)
(* variable: one normal and one for input ports. This allows us to get the   *)
(* values for input ports from a separate environment than that used to get  *)
(* the values for variables introduced by ‘eq’ statements.                   *)
(*                                                                           *)
(* Also we have Lustre operators "pre" and "fby" as well as a temporal       *)
(* operator HistExpr ("Historically").                                       *)
(*---------------------------------------------------------------------------*)

Datatype:
  expr = PortVar string
       | ProgVar string
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
 bexpr = BoolLit bool
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

(*---------------------------------------------------------------------------*)
(* Value of expression in given environments                                 *)
(*---------------------------------------------------------------------------*)

Definition exprVal_def :
  exprVal (portEnv,varEnv) (PortVar s) (t:num) = (portEnv ' s) t /\
  exprVal (portEnv,varEnv) (ProgVar s) t  = (varEnv ' s) t /\
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
(* Variable definitions (‘eq’ statements)                                    *)
(*---------------------------------------------------------------------------*)

Datatype:
  stmt = NumStmt string expr
End

(*---------------------------------------------------------------------------*)
(* Value of statement in given environments                                  *)
(*---------------------------------------------------------------------------*)

Definition stmtVal_def :
 stmtVal (portEnv,varEnv) t (NumStmt varName e) =
      (varName, exprVal (portEnv,varEnv) e t)
End

(*---------------------------------------------------------------------------*)
(* Environments are finite maps from names to streams                        *)
(*---------------------------------------------------------------------------*)

Definition updateEnv_def :
 updateEnv (fmap: 'a |-> (num -> 'b)) name value t =
   let strm = fmap ' name;
       strm' = strm (| t |-> value |)
   in
     fmap |+ (name,strm')
End

(*---------------------------------------------------------------------------*)
(* A statement updates a binding in varEnv                                   *)
(*---------------------------------------------------------------------------*)

Definition stmtEffect_def :
 stmtEffect t (portEnv,varEnv) (NumStmt varName e) =
    let i = exprVal (portEnv,varEnv) e t
    in (portEnv,updateEnv varEnv varName i t)
End

(*---------------------------------------------------------------------------*)
(* Sequential accumulation of variable updates                               *)
(*---------------------------------------------------------------------------*)

Definition stmtListEffect_def :
  stmtListEffect (portEnv,varEnv) stmts t =
     FOLDL (stmtEffect t) (portEnv,varEnv) stmts
End

(*---------------------------------------------------------------------------*)
(* Accumulation of parallel updates                                          *)
(*---------------------------------------------------------------------------*)

Definition insertBinding_def:
  insertBinding t (s,i) varEnv = updateEnv varEnv s i t
End

Definition stmtListParEffect_def :
 stmtListParEffect (portEnv,varEnv) stmts t =
   let outBindings = MAP (stmtVal (portEnv,varEnv) t) stmts;
       varEnv' = FOLDR (insertBinding t) varEnv outBindings
   in (portEnv,varEnv')
End

(*---------------------------------------------------------------------------*)
(* A component = (V,O,A,G) comprises                                         *)
(*                                                                           *)
(*   - A list of variable definitions V = [v1 = e1; ...; vn = en]            *)
(*   - A list of output definitions   O = [o1 = e(n+1); ...; ok = e(n+k)]    *)
(*   - A list of assumptions          A = [a1,...,ai]                        *)
(*   - A list of guarantees           G = [g1,...,gj]                        *)
(*---------------------------------------------------------------------------*)

Datatype:
  component = <| var_defs    : stmt list;
                 out_defs    : stmt list;
                 assumptions : bexpr list;
                 guarantees  : bexpr list |>
End

(*---------------------------------------------------------------------------*)
(* The "effect" of the component is the environment obtained by running the  *)
(* variable assignments given the input port values. The variable definitions*)
(* are run in sequence, and then the output definitions are evaluated in     *)
(* parallel (ensuring that no output can depend on any other output), and    *)
(* added to the bindings obtained in the first stage.                        *)
(*---------------------------------------------------------------------------*)

Definition componentEffect_def :
  componentEffect (portEnv,varEnv) comp t =
  let (portEnv,varEnv') = stmtListEffect (portEnv,varEnv) comp.var_defs t;
      (portEnv,varEnv'') = stmtListParEffect (portEnv,varEnv') comp.out_defs t
  in varEnv''
End

(*---------------------------------------------------------------------------*)
(* Evaluate the conjunction of guarantees of the component at time t         *)
(*---------------------------------------------------------------------------*)

Definition guarsVal_def:
   guarsVal E comp = bexprVal E (FOLDR AndExpr (BoolLit T) comp.guarantees)
End

(*---------------------------------------------------------------------------*)
(* Evaluate the conjunction of assumptions of the component at time t. Only  *)
(* the input port values can be accessed. At a time t we can assume that the *)
(* assumptions hold for all j ≤ t.                                           *)
(*---------------------------------------------------------------------------*)

Definition assumsVal_def:
   assumsVal portEnv comp =
        bexprVal (portEnv,FEMPTY)
             (HistExpr (FOLDR AndExpr (BoolLit T) comp.assumptions))
End

(*---------------------------------------------------------------------------*)
(* Correctness of component: the effects  of the component model its spec.   *)
(* We first define a function over t that iterates variable assignments of   *)
(* the component. Time 0 is when the ports get their first value, so we      *)
(* have to calculate componentEffect there as well.                          *)
(*---------------------------------------------------------------------------*)

Definition Iterate_Effect_def :
  Iterate_Effect portEnv comp 0 = componentEffect (portEnv,ARB) comp 0 ∧
  Iterate_Effect portEnv comp (SUC t) =
    componentEffect (portEnv,Iterate_Effect portEnv comp t) comp (SUC t)
End

(*---------------------------------------------------------------------------*)
(* A component is correct if its variable assignments, when iterated, make   *)
(* the guarantees true, for any time t.                                      *)
(*---------------------------------------------------------------------------*)

Definition Component_Correct_def:
  Component_Correct comp
    ⇔
  ∀portEnv t.
      assumsVal portEnv comp t
        ==>
      guarsVal (portEnv, Iterate_Effect portEnv comp t) comp t
End

(*---------------------------------------------------------------------------*)
(* Trivial beginning example                                                 *)
(*  A = []                                                                   *)
(*  V = []                                                                   *)
(*  O = [output = input]                                                     *)
(*  G = [output ≤ input]                                                     *)
(*---------------------------------------------------------------------------*)

Theorem example_1 :
  Component_Correct
     <|   var_defs := [];
          out_defs := [NumStmt "output" (PortVar "input")];
       assumptions := [];
        guarantees := [NotExpr (LtExpr (ProgVar "output") (PortVar "input"))]
     |>
Proof
 EVAL_TAC >> Cases_on ‘t’ >> EVAL_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Simple use of variable assignments                                        *)
(*  V = [v = input + 1]                                                      *)
(*  O = [output = v]                                                         *)
(*  A = []                                                                   *)
(*  G = [input < output]                                                     *)
(*---------------------------------------------------------------------------*)

Theorem example_2 :
  Component_Correct
     <| var_defs := [NumStmt "v" (AddExpr (PortVar "input") (IntLit 1))];
        out_defs := [NumStmt "output" (ProgVar "v")];
       assumptions := [];
      guarantees := [LtExpr (PortVar "input") (ProgVar "output")]
     |>
Proof
 EVAL_TAC >> Cases_on ‘t’ >> EVAL_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Trivial use of Hist                                                       *)
(*  A = []                                                                   *)
(*  V = []                                                                   *)
(*  O = [output = 42]                                                        *)
(*  G = [Hist(output = 42)]                                                  *)
(*---------------------------------------------------------------------------*)

Theorem example_3 :
  Component_Correct
     <| var_defs := [];
        out_defs := [NumStmt "output" (IntLit 42)];
       assumptions := [];
      guarantees := [HistExpr (EqExpr (ProgVar "output") (IntLit 42))]
     |>
Proof
  EVAL_TAC >> Induct_on ‘t’ >> EVAL_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Fby and Pre                                                               *)
(*  A = []                                                                   *)
(*  V = [steps = 1 -> 1 + pre steps]                                         *)
(*  O = [output = steps]                                                     *)
(*  G = [0 < output]                                                         *)
(*                                                                           *)
(* Needs some lemmas in order to do the proof                                *)
(*---------------------------------------------------------------------------*)

Definition comp4_def:
   comp4 =
       <| var_defs :=
              [NumStmt "steps"
                 (FbyExpr (IntLit 1)
                    (AddExpr (IntLit 1) (PreExpr (ProgVar "steps"))))];
          out_defs := [NumStmt "output" (ProgVar "steps")];
       assumptions := [];
        guarantees := [LtExpr (IntLit 0) (ProgVar "output")]|>
End

Triviality output_effect :
 ∀t portEnv varEnv.
     componentEffect (portEnv,varEnv) comp4 t ' "output" t =
       (if t = 0 then 1 else 1 + varEnv ' "steps" (t − 1))
Proof
 rpt gen_tac >> EVAL_TAC >> fs[]
QED

Triviality steps_effect :
 ∀t portEnv varEnv.
     componentEffect (portEnv,varEnv) comp4 t ' "steps" t =
       (if t = 0 then 1 else 1 + varEnv ' "steps" (t − 1))
Proof
 rpt gen_tac >> EVAL_TAC >> fs[]
QED

Theorem Vars_Eq :
   ∀t portEnv. Iterate_Effect portEnv comp4 t ' "output" t =
                Iterate_Effect portEnv comp4 t ' "steps" t
Proof
  Induct >> rw [Iterate_Effect_def,output_effect,steps_effect]
QED

Theorem example_4 :
  Component_Correct comp4
Proof
 rw [Component_Correct_def,comp4_def,assumsVal_def,guarsVal_def,exprVal_def]
  >> simp_tac std_ss [GSYM comp4_def]
  >> Induct_on ‘t’
  >> EVAL_TAC
  >> fs [GSYM comp4_def,Vars_Eq]
QED

(*---------------------------------------------------------------------------*)
(* Iterative factorial is implemented by the rewrite system                  *)
(*                                                                           *)
(*   (n,fact) --> (n+1,fact * (n+1))                                         *)
(*                                                                           *)
(*  A = []                                                                   *)
(*  V = [n    = 0 -> 1 + pre n;                                              *)
(*       fact = 1 -> pre fact * n]                                           *)
(*  O = [output = fact]                                                      *)
(*  G = [0 < fact]                                                           *)
(*                                                                           *)
(* We can take the iteration of this transition system into HOL and show     *)
(* that it implements the usual recursion equation for factorial.            *)
(*---------------------------------------------------------------------------*)

Definition itFact_def:
   itFact =
     <| var_defs :=
          [NumStmt "n"
             (FbyExpr (IntLit 0) (AddExpr (IntLit 1) (PreExpr (ProgVar "n"))));
           NumStmt "fact"
                 (FbyExpr (IntLit 1)
                    (MultExpr (PreExpr (ProgVar "fact")) (ProgVar "n")))];
        out_defs := [NumStmt "output" (ProgVar "fact")];
        assumptions := [];
        guarantees := [LtExpr (IntLit 0) (ProgVar "output")]|>
End

val output_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) itFact t ' "output" t”);

val n_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) itFact t ' "n" t”);

val fact_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) itFact t ' "fact" t”);

Theorem Vars_Eq :
   ∀t portEnv. Iterate_Effect portEnv itFact t ' "output" t =
                Iterate_Effect portEnv itFact t ' "fact" t
Proof
  Induct >> rw [Iterate_Effect_def,output_effect,fact_effect]
QED

Theorem n_is_N:
  ∀t portEnv. Iterate_Effect portEnv itFact t ' "n" t = &t
Proof
  Induct
   >> rw [Iterate_Effect_def,n_effect,integerTheory.int_of_num,integerTheory.INT_1]
   >> pop_assum kall_tac
   >> intLib.ARITH_TAC
QED

Theorem itFact_Meets_Spec :
  Component_Correct itFact
Proof
 rw [Component_Correct_def,itFact_def,guarsVal_def,assumsVal_def,exprVal_def]
  >> simp_tac std_ss [GSYM itFact_def]
  >> Induct_on ‘t’
  >> EVAL_TAC
  >> fs [GSYM itFact_def]
  >> fs[Vars_Eq,n_is_N]
  >> pop_assum mp_tac
  >> qspec_tac (‘Iterate_Effect portEnv itFact t ' "fact" t’,‘i’)
  >> rpt strip_tac
  >> match_mp_tac int_arithTheory.positive_product_implication
  >> intLib.ARITH_TAC
QED

(*---------------------------------------------------------------------------*)
(* Iterative factorial is equal to recursive factorial (arithmeticTheory.FACT*)
(*---------------------------------------------------------------------------*)

val num_mult_int = CONJUNCT1 integerTheory.INT_MUL_CALCULATE;

Theorem itFact_eq_FACT :
 ∀t portEnv. Iterate_Effect portEnv itFact t ' "fact" t = &(FACT t)
Proof
 rw [Component_Correct_def,itFact_def,guarsVal_def,assumsVal_def,exprVal_def]
  >> simp_tac std_ss [GSYM itFact_def]
  >> Induct_on ‘t’
  >> EVAL_TAC
  >> fs [GSYM itFact_def]
  >> fs[Vars_Eq,n_is_N]
  >> rw_tac std_ss [arithmeticTheory.FACT,Once (GSYM num_mult_int)]
  >> rw_tac std_ss [integerTheory.int_of_num,integerTheory.INT_1]
  >> intLib.ARITH_TAC
QED

(*---------------------------------------------------------------------------*)
(* Iterative Fibonacci is implemented by the rewrite system                  *)
(*                                                                           *)
(*       (x,y) --> (y,x+y)                                                   *)
(*                                                                           *)
(*  A = []                                                                   *)
(*  V = [x = 0 -> pre y;                                                     *)
(*       y = 1 -> pre x + pre y]                                             *)
(*  O = [output = y]                                                         *)
(*  G = [0 <= x and 0 < output]                                              *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition itFib_def:
   itFib =
      <| var_defs :=
             [NumStmt "x"
               (FbyExpr (IntLit 0) (PreExpr (ProgVar "y")));
              NumStmt "y"
                 (FbyExpr (IntLit 1)
                    (AddExpr (PreExpr (ProgVar "x")) (PreExpr (ProgVar "y"))))];
         out_defs := [NumStmt "output" (ProgVar "y")];
       assumptions := [];
       guarantees := [AndExpr (NotExpr (LtExpr (ProgVar "x") (IntLit 0)))
                              (LtExpr (IntLit 0) (ProgVar "output"))]
      |>
End

val output_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) itFib t ' "output" t”);

val x_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) itFib t ' "x" t”);

val y_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) itFib t ' "y" t”);

Theorem Vars_Eq :
   ∀t portEnv. Iterate_Effect portEnv itFib t ' "output" t =
                Iterate_Effect portEnv itFib t ' "y" t
Proof
  Induct >> rw [Iterate_Effect_def,output_effect,y_effect]
QED

Theorem itFib_Meets_Spec :
  Component_Correct itFib
Proof
 simp [Component_Correct_def,itFib_def,guarsVal_def,assumsVal_def,exprVal_def]
  >> simp_tac std_ss [GSYM itFib_def]
  >> Induct_on ‘t’
  >- (EVAL_TAC >> rw[])
  >- (simp [Iterate_Effect_def]
       >> EVAL_TAC
       >> simp_tac arith_ss [GSYM itFib_def]
       >> fs[Vars_Eq]
       >> gen_tac
       >> pop_assum (mp_tac o Q.SPEC ‘portEnv’)
       >> qspec_tac (‘Iterate_Effect portEnv itFib t ' "x" t’,‘i’)
       >> qspec_tac (‘Iterate_Effect portEnv itFib t ' "y" t’,‘j’)
       >> intLib.ARITH_TAC)
QED

(*---------------------------------------------------------------------------*)
(* Monitor an input stream for sortedness (w/o boolean vars)                 *)
(*                                                                           *)
(*  A = []                                                                   *)
(*  V = [diff  = 0 -> input - pre input]                                     *)
(*  O = [alert = 0 -> if diff < 0 then 1 else pre alert]                     *)
(*  G = [alert = 0 iff Hist (0 <= diff)]                                     *)
(*---------------------------------------------------------------------------*)

Definition sorted_def:
   sorted =
      <| var_defs :=
             [NumStmt "diff"
               (FbyExpr (IntLit 0)
                        (SubExpr (PortVar "input")
                                 (PreExpr (PortVar "input"))))] ;
         out_defs :=
             [NumStmt "alert"
                (FbyExpr (IntLit 0)
                         (CondExpr (LtExpr (ProgVar "diff") (IntLit 0))
                                   (IntLit 1)
                                   (PreExpr (ProgVar "alert"))))] ;
       assumptions := [];
       guarantees := [IffExpr (EqExpr (ProgVar "alert") (IntLit 0))
                              (HistExpr (LeqExpr (IntLit 0) (ProgVar "diff")))]
      |>
End

Triviality int_lem :
  i < 0i <=> ~(0i <= i)
Proof
  intLib.ARITH_TAC
QED

Theorem sorted_Meets_Spec :
  Component_Correct sorted
Proof
 simp [Component_Correct_def,sorted_def,guarsVal_def,assumsVal_def,exprVal_def]
  >> simp_tac std_ss [GSYM sorted_def]
  >> gen_tac
  >> Induct_on ‘t’
  >- (EVAL_TAC >> rw[])
  >- (simp [Iterate_Effect_def]
       >> EVAL_TAC
       >> simp_tac arith_ss [GSYM sorted_def]
       >> rw[]
       >- (qexists_tac ‘SUC t’ >> rw[] >> metis_tac [int_lem])
       >- (rw[EQ_IMP_THM]
           >- (rw[] >> fs [int_lem])
           >- (‘n <= SUC t /\ ~(SUC t = n)’ by decide_tac >> metis_tac[])))
QED


(*---------------------------------------------------------------------------*)
(* A division node implementing summation of pointwise division of stream    *)
(* i1 by i2                                                                  *)
(*                                                                           *)
(*  A = [0 ≤ i1, 0 < i2]                                                     *)
(*  V = [divsum = (i1 / i2) -> pre divsum + (i1/i2)]                         *)
(*  O = [output = divsum]                                                    *)
(*  G = [0 ≤ output]                                                         *)
(*                                                                           *)
(* Subtlety: one might think that we could have written                      *)
(*                                                                           *)
(*  V = []                                                                   *)
(*  O = [output = (i1 / i2) -> pre output + (i1/i2)]                         *)
(*                                                                           *)
(* but output variables aren't allowed to be state-holding                   *)
(*---------------------------------------------------------------------------*)

Definition divsum_def:
  divsum =
     <| var_defs :=
          [NumStmt "divsum"
               (FbyExpr (DivExpr (PortVar "i1") (PortVar "i2"))
                        (AddExpr (PreExpr (ProgVar "divsum"))
                                 (DivExpr (PortVar "i1") (PortVar "i2"))))];
         out_defs := [NumStmt "output" (ProgVar "divsum")];
      assumptions := [LtExpr (IntLit 0) (PortVar"i2");
                      LeqExpr (IntLit 0) (PortVar"i1")];
       guarantees := [LeqExpr (IntLit 0) (ProgVar"output")]
      |>
End

val divsum_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) divsum t ' "divsum" t”);

val output_effect = SIMP_RULE (srw_ss()) []
  (EVAL “componentEffect (portEnv,varEnv) divsum t ' "output" t”);

Theorem Vars_Eq :
   ∀t portEnv. Iterate_Effect portEnv divsum t ' "output" t =
                Iterate_Effect portEnv divsum t ' "divsum" t
Proof
  Induct >> rw [Iterate_Effect_def,output_effect,divsum_effect]
QED

Theorem divsum_Meets_Spec :
  Component_Correct divsum
Proof
EVAL_TAC
  >> rw [GSYM divsum_def,Vars_Eq]
  >> Induct_on ‘t’
  >> strip_tac
    >- (EVAL_TAC
        >> pop_assum (mp_tac o Q.SPEC ‘0n’) >> rw[]
        >> rpt (pop_assum mp_tac)
        >> qspec_tac(‘portEnv ' "i2" 0’,‘j’)
        >> qspec_tac(‘portEnv ' "i1" 0’,‘i’)
        >> rpt gen_tac
        >> rw []
        >> ‘~(j=0)’ by intLib.ARITH_TAC
        >> rw [integerTheory.int_div])
    >- (simp_tac std_ss [Iterate_Effect_def,divsum_effect]
        >> rw[]
        >> ‘t ≤ SUC t’ by rw[]
        >> ‘0 ≤ Iterate_Effect portEnv divsum t ' "divsum" t’ by fs[]
        >> irule integerTheory.INT_LE_ADD
        >> conj_tac
        >- metis_tac[]
        >- (‘0 < portEnv ' "i2" (SUC t) ∧ 0 ≤ portEnv ' "i1" (SUC t)’ by fs[]
            >> ntac 2 (pop_assum mp_tac)
            >> rpt (pop_assum kall_tac)
            >> qspec_tac(‘portEnv ' "i2" (SUC t)’,‘j’)
            >> qspec_tac(‘portEnv ' "i1" (SUC t)’,‘i’)
            >> rpt gen_tac
            >> rw []
            >> ‘~(j=0)’ by intLib.ARITH_TAC
            >> rw [integerTheory.int_div]))
QED

val _ = export_theory();
