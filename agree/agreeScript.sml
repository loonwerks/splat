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
       | PreExpr expr
       | FbyExpr expr expr
End

(*---------------------------------------------------------------------------*)
(* Boolean expressions                                                       *)
(*---------------------------------------------------------------------------*)

Datatype:
  bexpr = BoolLit bool
        | NotExpr bexpr
        | OrExpr  bexpr bexpr
        | AndExpr bexpr bexpr
        | EqExpr  expr expr
        | LtExpr  expr expr
End

(*---------------------------------------------------------------------------*)
(* So-called ‘eq’ statements                                                 *)
(*---------------------------------------------------------------------------*)

Datatype:
  stmt = NumStmt string expr
(*       | BoolStmt string bexpr  *)

End

(*---------------------------------------------------------------------------*)
(* Value of arithmetic expressions in given environments                     *)
(*---------------------------------------------------------------------------*)

Definition exprVal_def :
  exprVal (portEnv,varEnv) (PortExpr s) (t:num) = (portEnv ' s) t /\
  exprVal (portEnv,varEnv) (VarExpr s) t  = (varEnv ' s) t /\
  exprVal E (IntLit i) t  = i /\
  exprVal E (AddExpr e1 e2) t = exprVal E e1 t + exprVal E e2 t /\
  exprVal E (PreExpr e) t =
     (if t = 0 then ARB else exprVal E e (t-1)) /\
  exprVal E (FbyExpr e1 e2) t =
     (if t = 0 then exprVal E e1 0 else exprVal E e2 t)
End

(*---------------------------------------------------------------------------*)
(* Value of boolean expressions in given environments                        *)
(*---------------------------------------------------------------------------*)

Definition bexprVal_def :
  bexprVal E (BoolLit b) t     = b /\
  bexprVal E (NotExpr b) t     = (~bexprVal E b t) /\
  bexprVal E (OrExpr b1 b2) t  = (bexprVal E b1 t \/ bexprVal E b2 t) /\
  bexprVal E (AndExpr b1 b2) t = (bexprVal E b1 t /\ bexprVal E b2 t) /\
  bexprVal E (EqExpr e1 e2) t  = (exprVal E e1 t = exprVal E e2 t) /\
  bexprVal E (LtExpr e1 e2) t  = (exprVal E e1 t < exprVal E e2 t)
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

Definition updateEnv :
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
(*   - A list of guarantees           G = [g_1,...,gi]                       *)
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
(* parallel (so that no output can depend on any other output), and added to *)
(* the bindings obtained in the first stage.                                 *)
(*---------------------------------------------------------------------------*)

Definition Comp_Effect_def :
  Comp_Effect (portEnv,varEnv) comp t =
  let (portEnv,varEnv') = stmtListEffect (portEnv,varEnv) comp.var_defs t;
      (portEnv,varEnv'') = stmtListParEffect (portEnv,varEnv') comp.out_defs t
  in varEnv''
End

(*---------------------------------------------------------------------------*)
(* The streams in E make the guarantees of the component true at time t      *)
(*---------------------------------------------------------------------------*)

Definition guarsVal_def:
   guarsVal E comp t = EVERY (\g. bexprVal E g t) comp.guarantees
End

(*---------------------------------------------------------------------------*)
(* Notion of guarsVal holding for all t. Not sure if this is right yet.      *)
(*---------------------------------------------------------------------------*)

Definition Comp_Spec_def:
   Comp_Spec comp E = ∀t. guarsVal E comp t
End

(*---------------------------------------------------------------------------*)
(* Correctness of component: the effects  of the component meet its spec.    *)
(* We first define a function over t that iterates variable assignments of   *)
(* the component. Time 0 is when the ports get their first value, so we      *)
(* have to calculate Comp_Effect there as well.                              *)
(*---------------------------------------------------------------------------*)

Definition Iterate_Effect_def :
  Iterate_Effect portEnv comp 0 = Comp_Effect (portEnv,ARB) comp 0 ∧
  Iterate_Effect portEnv comp (SUC t) =
    Comp_Effect (portEnv,Iterate_Effect portEnv comp t) comp (SUC t)
End

(*---------------------------------------------------------------------------*)
(* A component is correct if its variable assignments, when iterated, make   *)
(* the Comp_Spec true, for any time t.                                       *)
(*---------------------------------------------------------------------------*)

Definition Comp_Correct_def:
  Comp_Correct comp
    ⇔
  ∀portEnv t. Comp_Spec comp (portEnv, Iterate_Effect portEnv comp t)
End


val _ = export_theory();
