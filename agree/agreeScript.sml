open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory;

val _ = intLib.prefer_int();

val _ = new_theory "agree";

(*---------------------------------------------------------------------------*)
(* Arithmetic expressions. Conventional, except that there are two kinds of  *)
(* variable: one normal and one for input ports. This allows us to get the   *)
(* values for input ports from a separate environment than that used to get  *)
(* the values for variables introduced by ‘eq’ statements.                   *)
(*                                                                           *)
(* Also we have Lustre operators "pre" and "fby"                             *)
(*---------------------------------------------------------------------------*)

Datatype:
  expr = PortExpr string
       | VarExpr string
       | IntLit int
       | AddExpr expr expr
       | SubExpr expr expr
       | MultExpr expr expr
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
       | LteExpr expr expr
       | HistExpr bexpr
End

(*---------------------------------------------------------------------------*)
(* Value of expression in given environments                                 *)
(*---------------------------------------------------------------------------*)

Definition exprVal_def :
  exprVal (portEnv,varEnv) (PortExpr s) (t:num) = (portEnv ' s) t /\
  exprVal (portEnv,varEnv) (VarExpr s) t  = (varEnv ' s) t /\
  exprVal E (IntLit i) t  = i /\
  exprVal E (AddExpr e1 e2) t = exprVal E e1 t + exprVal E e2 t /\
  exprVal E (SubExpr e1 e2) t = exprVal E e1 t - exprVal E e2 t /\
  exprVal E (MultExpr e1 e2) t = exprVal E e1 t * exprVal E e2 t /\
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
  bexprVal E (LteExpr e1 e2) t = (exprVal E e1 t <= exprVal E e2 t)   /\
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
(* A component = (V,O,G) comprises                                           *)
(*                                                                           *)
(*   - A list of variable definitions V = [v1 = e1; ...; vn = en]            *)
(*   - A list of output definitions   O = [o1 = e(n+1); ...; ok = e(n+k)]    *)
(*   - A list of guarantees           G = [g1,...,gi]                        *)
(*---------------------------------------------------------------------------*)

Datatype:
  component = <| var_defs : stmt list;
                 out_defs : stmt list;
                 guarantees : bexpr list |>
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
   guarsVal E comp t = EVERY (\g. bexprVal E g t) comp.guarantees
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
      guarsVal (portEnv, Iterate_Effect portEnv comp t) comp t
End

(*---------------------------------------------------------------------------*)
(* Trivial beginning example                                                 *)
(*  V = []                                                                   *)
(*  O = [output = input]                                                     *)
(*  G = [output ≤ input]                                                     *)
(*---------------------------------------------------------------------------*)

Theorem example_1 :
  Component_Correct
     <| var_defs := [];
        out_defs := [NumStmt "output" (PortExpr "input")];
      guarantees := [NotExpr (LtExpr (VarExpr "output") (PortExpr "input"))]
     |>
Proof
 EVAL_TAC >> Cases_on ‘t’ >> EVAL_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Simple use of variable assignments                                        *)
(*  V = [v = input + 1]                                                      *)
(*  O = [output = v]                                                         *)
(*  G = [input < output]                                                     *)
(*---------------------------------------------------------------------------*)

Theorem example_2 :
  Component_Correct
     <| var_defs := [NumStmt "v" (AddExpr (PortExpr "input") (IntLit 1))];
        out_defs := [NumStmt "output" (VarExpr "v")];
      guarantees := [LtExpr (PortExpr "input") (VarExpr "output")]
     |>
Proof
 EVAL_TAC >> Cases_on ‘t’ >> EVAL_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Trivial use of Hist                                                       *)
(*  V = []                                                                   *)
(*  O = [output = 42]                                                        *)
(*  G = [Hist(output = 42)]                                                  *)
(*---------------------------------------------------------------------------*)

Theorem example_3 :
  Component_Correct
     <| var_defs := [];
        out_defs := [NumStmt "output" (IntLit 42)];
      guarantees := [HistExpr (EqExpr (VarExpr "output") (IntLit 42))]
     |>
Proof
  EVAL_TAC >> Induct_on ‘t’ >> EVAL_TAC >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Fby and Pre                                                               *)
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
                    (AddExpr (IntLit 1) (PreExpr (VarExpr "steps"))))];
          out_defs := [NumStmt "output" (VarExpr "steps")];
        guarantees := [LtExpr (IntLit 0) (VarExpr "output")]|>
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
 rw [Component_Correct_def,comp4_def,guarsVal_def,exprVal_def]
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
(*  V = [n = 0 -> 1 + pre n;                                                 *)
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
             (FbyExpr (IntLit 0) (AddExpr (IntLit 1) (PreExpr (VarExpr "n"))));
           NumStmt "fact"
                 (FbyExpr (IntLit 1)
                    (MultExpr (PreExpr (VarExpr "fact")) (VarExpr "n")))];
        out_defs := [NumStmt "output" (VarExpr "fact")];
        guarantees := [LtExpr (IntLit 0) (VarExpr "output")]|>
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
 rw [Component_Correct_def,itFact_def,guarsVal_def,exprVal_def]
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
 rw [Component_Correct_def,itFact_def,guarsVal_def,exprVal_def]
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
               (FbyExpr (IntLit 0) (PreExpr (VarExpr "y")));
              NumStmt "y"
                 (FbyExpr (IntLit 1)
                    (AddExpr (PreExpr (VarExpr "x")) (PreExpr (VarExpr "y"))))];
         out_defs := [NumStmt "output" (VarExpr "y")];
       guarantees := [AndExpr (NotExpr (LtExpr (VarExpr "x") (IntLit 0)))
                              (LtExpr (IntLit 0) (VarExpr "output"))]
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
 simp [Component_Correct_def,itFib_def,guarsVal_def,exprVal_def]
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
(*  V = [diff  = 0 -> input - pre input]                                     *)
(*  O = [alert = 0 -> if diff < 0 then 1 else pre alert]                     *)
(*  G = [alert = 0 iff Hist (0 <= diff)]                                     *)
(*---------------------------------------------------------------------------*)

Definition sorted_def:
   sorted =
      <| var_defs :=
             [NumStmt "diff"
               (FbyExpr (IntLit 0)
                        (SubExpr (PortExpr "input")
                                 (PreExpr (PortExpr "input"))))] ;
         out_defs :=
             [NumStmt "alert"
                (FbyExpr (IntLit 0)
                         (CondExpr (LtExpr (VarExpr "diff") (IntLit 0))
                                   (IntLit 1)
                                   (PreExpr (VarExpr "alert"))))] ;
       guarantees := [IffExpr (EqExpr (VarExpr "alert") (IntLit 0))
                              (HistExpr (LteExpr (IntLit 0) (VarExpr "diff")))]
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
 simp [Component_Correct_def,sorted_def,guarsVal_def,exprVal_def]
  >> simp_tac std_ss [GSYM sorted_def]
  >> gen_tac
  >> Induct_on ‘t’
  >- (EVAL_TAC >> rw[])
  >- (simp [Iterate_Effect_def]
       >> EVAL_TAC
       >> simp_tac arith_ss [GSYM sorted_def]
       >> rw[]
       >- (qexists_tac ‘SUC t’ >> rw[] >>
           metis_tac [int_lem])
       >- (rw[EQ_IMP_THM]
           >- (rw[] >> fs [int_lem])
           >- (‘n <= SUC t /\ ~(SUC t = n)’ by decide_tac >> metis_tac[])))
QED


val _ = export_theory();
