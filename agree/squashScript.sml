open agreeTheory ASCIInumbersLib;

val _ = intLib.prefer_int();

val _ = new_theory "squash";

Definition newAux_def :
  newAux n = STRCAT "aux" (num_to_dec_string n)
End

(*---------------------------------------------------------------------------*)
(* Temporal Squashing of all pre-expressions                                 *)
(*---------------------------------------------------------------------------*)

Definition exprSquash_def :
    exprSquash A M (IntVar s)       = (A, M, IntVar s)
  ∧ exprSquash A M (IntLit i)       = (A, M, IntLit i)
  ∧ exprSquash A M (PreExpr e)      =
     (if e ∈ FDOM M then
       (A, M, M ' e)
     else
       (let
          (A', M', e') = exprSquash A M e;  
          s = newAux (LENGTH A');
        in
          ((IntStmt s e')::A', M' |+ (e, (IntVar s)), IntVar s)))
  ∧ exprSquash A M (AddExpr e1 e2)  =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', AddExpr e1' e2'))
  ∧ exprSquash A M (SubExpr e1 e2)  =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', SubExpr e1' e2'))
  ∧ exprSquash A M (MultExpr e1 e2) =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', MultExpr e1' e2'))
  ∧ exprSquash A M (DivExpr e1 e2)  =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', DivExpr e1' e2'))
  ∧
  exprSquash A M (ModExpr e1 e2)  =
  (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', ModExpr e1' e2'))
  ∧ exprSquash A M (FbyExpr e1 e2)  =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', CondExpr (BoolVar "init") e1' e2'))
  ∧ exprSquash A M (CondExpr b e1 e2) =
    (let
       (A1, M1, b') = bexprSquash A M b;
       (A', M', e1') = exprSquash A1 M1 e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', CondExpr b' e1' e2'))
  ∧
    bexprSquash A M (BoolVar s) = (A,M,BoolVar s)
  ∧ bexprSquash A M (BoolLit b) = (A,M,BoolLit b)
  ∧ bexprSquash A M (NotExpr b) =
    (let (A', M', b') = bexprSquash A M b
     in (A',M',NotExpr b'))
  ∧ bexprSquash A M (OrExpr b1 b2)  =
    (let
       (A', M', b1') = bexprSquash A M b1;
       (A'', M'', b2') = bexprSquash A' M' b2;
     in
       (A'', M'', OrExpr b1' b2'))
  ∧ bexprSquash A M (AndExpr b1 b2)  =
    (let
       (A', M', b1') = bexprSquash A M b1;
       (A'', M'', b2') = bexprSquash A' M' b2;
     in
       (A'', M'', AndExpr b1' b2'))
  ∧ bexprSquash A M (ImpExpr b1 b2)  =
    (let
       (A', M', b1') = bexprSquash A M b1;
       (A'', M'', b2') = bexprSquash A' M' b2;
     in
       (A'', M'', ImpExpr b1' b2'))
  ∧ bexprSquash A M (IffExpr b1 b2)  =
    (let
       (A', M', b1') = bexprSquash A M b1;
       (A'', M'', b2') = bexprSquash A' M' b2;
     in
       (A'', M'', IffExpr b1' b2'))
  ∧ bexprSquash A M (EqExpr e1 e2) =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', EqExpr e1' e2'))
  ∧ bexprSquash A M (LtExpr e1 e2) =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', LtExpr e1' e2'))
  ∧ bexprSquash A M (LeqExpr e1 e2) =
    (let
       (A', M', e1') = exprSquash A M e1;
       (A'', M'', e2') = exprSquash A' M' e2;
     in
       (A'', M'', LeqExpr e1' e2'))
  ∧ bexprSquash A M (HistExpr b) =
    (let
       (A', M', b') = bexprSquash A M b
     in
       (A', M', HistExpr b'))
  ∧ bexprSquash A M (BoolFbyExpr b1 b2) =
    (let
       (A', M', b1') = bexprSquash A M b1;
       (A'', M'', b2') = bexprSquash A' M' b2;
     in
       (A'', M'', BoolFbyExpr b1' b2'))
  ∧ bexprSquash A M (BoolCondExpr b1 b2 b3) =
    (let
       (A1, M1, b1') = bexprSquash A M b1;
       (A2, M2, b2') = bexprSquash A1 M1 b2;
       (A3, M3, b3') = bexprSquash A2 M2 b3;
     in
       (A3, M3, BoolCondExpr b1' b2' b3))
End

(* Following left out because it fails on a type clash:

  ∧ exprSquash A M (BoolPreExpr b) =
    (let
       (A', M', b') = bexprSquash A M b;
       s = newAux (LENGTH A');
       A'' = A' ++ [(BoolStmt s b')];
       M'' = M' |+ (b', (BoolVar s));
     in
       if b' ∈ FDOM M then
         (A', M', M' ' b')
       else
         (A'', M'', (BoolVar s)))
*)

Definition squashStmt_def :
  squashStmt (IntStmt s e) (S,A,M) =
    let (A',M',e') = exprSquash A M e
     in (IntStmt s e'::S, A', M')
End

(* NOTE: there is going to be a typing issue at some point because the stmnt   *)
(* needs the type of the aux for the varible reference.                        *)
Definition squashOutputStmt_def :
  squashOutputStmt (IntStmt s e) (S,A,M) =
  let (A',M',e') = exprSquash A M e;
      s' = newAux (LENGTH A')
  in if e = e' then
       (IntStmt s e'::S, A', M')
     else
       (IntStmt s (IntVar s')::S, IntStmt s' e'::A', M')  
End

Definition squashStmts_def :
  squashStmts fn (S,A,M) stmts = FOLDR fn (S,A,M) stmts
End

Definition squash_comp_def :
  squash_comp comp =
  let
    (out_defs,aux_defs,M) = squashStmts squashOutputStmt ([],[],FEMPTY) comp.out_defs;
    (var_defs,aux_defs',M')  = squashStmts squashStmt ([],aux_defs,M) comp.var_defs;
  in
    <| inports  := comp.inports;
       var_defs := var_defs ++ aux_defs';
       out_defs  := out_defs;
       assumptions := comp.assumptions;
       guarantees := comp.guarantees |>
End

(* Squash guarantees as well
   
Definition squashExpr1_def :
  squashExpr1 (A,M,elist) e =
    let (A',M',e') = exprSquash A M e
     in (A', M',e'::elist)
End


Definition squashExprs_def :
  squashExprs (A,M) elist = FOLDL squashExpr1 (A,M,[]) elist
End

Definition squash_comp_def :
  squash_comp comp =
  let (var_defs',M) = squashStmts ([],FEMPTY) comp.var_defs;
      (out_defs',M') = squashStmts([],M) comp.out_defs;
      (guar_defs,M'',guars') = squashExprs ([],M') comp.guarantees
  in
    <| inports  := comp.inports;
       var_defs := var_defs' ++ guar_defs;
       out_defs  := out_defs';
       assumptions := comp.assumptions;
       guarantees := guars' |>
End
 *)


(*---------------------------------------------------------------------------*)
(* Version with lookback to depths one and two.                              *)
(*                                                                           *)
(*  inports = [input]                                                        *)
(*       N = 0 -> 1 + pre N                                                  *)
(*  isProg = if N ≤ 1 then                                                   *)
(*              T                                                            *)
(*           else                                                            *)
(*              pre isProg and                                               *)
(*                  (input - pre input = pre input - pre(pre input))         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition arithprog_def:
  arithprog =
    <| inports  := ["input"];
       var_defs :=
          [IntStmt "N" (FbyExpr (IntLit 0)
                                (AddExpr (PreExpr (IntVar "N")) (IntLit 1)));
           BoolStmt "isProg"
            (BoolCondExpr
                 (LeqExpr (IntVar "N") (IntLit 1))
                 (BoolLit T)
                 (AndExpr
                    (EqExpr (SubExpr (IntVar "input") (PreExpr (IntVar "input")))
                            (SubExpr (PreExpr (IntVar "input"))
                                     (PreExpr (PreExpr(IntVar "input")))))
                    (BoolPreExpr (BoolVar "isProg"))))];
         out_defs := [BoolStmt "out" (BoolVar "isProg")];
      assumptions := [];
      guarantees  := []
      |>
End

(*---------------------------------------------------------------------------*)
(* Nesting of "pre" in order to look both 1 and 2 steps back in the          *)
(* computation. Simulates a recursive Fibonacci                              *)
(*                                                                           *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [fib = 1 -> pre(1 -> fib + pre fib)]                                 *)
(*  O = [output = fib]                                                       *)
(*  G = [0 ≤ output]                                                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition recFib_def:
  recFib =
     <| inports := [];
        var_defs :=
          [IntStmt "recFib"
             (FbyExpr (IntLit 1)
                (PreExpr (FbyExpr (IntLit 1)
                         (AddExpr (IntVar "recFib") (PreExpr (IntVar "recFib"))))))];
         out_defs := [IntStmt "output" (IntVar "recFib")];
      assumptions := [];
       guarantees := [LeqExpr (IntLit 0) (IntVar"output")]
      |>
End

(*---------------------------------------------------------------------------*)
(* Deeper Nesting of "pre" in order to look further back and add more        *)
(* comman sub-expressions.                                                   *)
(*                                                                           *)
(*  I = []                                                                   *)
(*  A = []                                                                   *)
(*  V = [fib = 1 -> pre(1 -> fib + pre fib)                                  *)
(*       x = 0 -> pre(1 -> pre(1 -> fib + pre fib))                          *)
(*       y = x -> pre(x -> pre(x) - pre(pre(x)))]                            *)
(*  O = [output = fib]                                                       *)
(*  G = [0 ≤ output]                                                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition testInput_def:
  testInput =
     <| inports := [input];
        var_defs :=
          [IntStmt "recFib"
             (FbyExpr (IntLit 1)
                (PreExpr (FbyExpr (IntLit 1)
                          (AddExpr (IntVar "recFib") (PreExpr (IntVar "recFib"))))));
           IntStmt "x"
                   (FbyExpr (IntLit 0)
                    (PreExpr (FbyExpr (IntLit 1)
                              (PreExpr (FbyExpr (IntLit 1)
                                                (AddExpr (IntVar "recFib") (PreExpr (IntVar "recFib"))))))));
           IntStmt "y"
             (FbyExpr (IntVar "x")
                (PreExpr (FbyExpr (IntVar "x")
                                  (SubExpr (PreExpr (IntVar "x")) (PreExpr (PreExpr (IntVar "recFib")))))))];
                          
        out_defs := [IntStmt "output" (IntVar "recFib")];
      assumptions := [];
       guarantees := [LeqExpr (IntLit 0) (IntVar"output")]
      |>
End

(*---------------------------------------------------------------------------*)
(* Compute the output directly without using variable declarations.          *)
(*                                                                           *)
(*  I = [input]                                                              *)
(*  A = []                                                                   *)
(*  V = []                                                                   *)
(*  O = [output = 1 -> pre(1 -> input + pre input)]                          *)
(*  G = [0 ≤ output]                                                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

Definition outputFib_def:
  outputFib =
     <| inports := [];
        var_defs := [];
        out_defs := [
                 IntStmt "output"
                 (FbyExpr (IntLit 1)
                  (PreExpr (FbyExpr (IntLit 1)
                            (AddExpr (IntVar "input") (PreExpr (IntVar "input"))))))];
      assumptions := [];
       guarantees := [LeqExpr (IntLit 0) (IntVar"output")]
      |>
End

(* bexpr is not yet defined, so arithprog does _not_ work yet *)
(* EVAL “squash_comp arithprog”;                              *)

EVAL “squash_comp recFib”;
EVAL “squash_comp testInput”;
EVAL “squash_comp outputFib”;

val _ = export_theory();

(*---------------------------------------------------------------------------*)
(* Algorithm Explanation with two examples that follow                       *)
(*---------------------------------------------------------------------------*)

(*
   Re-write the program so that next-state deponds only on current
   state.

   Requires: no cycles!
   Ensures: no pre-operators!

   A: stmt List
   M: expr -> (BoolVar | IntVar)

   Recursively visit the definition list building a new list on the way out.

   Post-order on a pre-expression (pre e):

     if (e ∈ M) then
       A' = A
       M' = M
       e' = M e
     else
       a' = newAuxilliary e
       A' = A ++ (Stmt a' e)
       M' = M |+ (e, (Var a'))

     (A', M', e')

   Concatenation on A is not really correct. A needs to be such that any use
   of an auxilliary on the right is before _before_ its definition.

   Post-order on statements: add the statement to the new variable definitions list

   Example 1:

         N = if init then 1 else pre(N)
    isProg = if (N ≤ 1) then
               T
             else
               pre(isProg) ∧
               (input - pre(input) = pre(input) - pre(pre(input)))

     A = []
     M = []

     Visit(N): V = [N = if init then 1 else a_0]
               A = [a_0 = N]
               M = [(N, a_0)]

     Visit(isProg): V = [     N = if init then 1 else a_0
                         isProg = if (N ≤ 1) then
                                    T
                                  else
                                    a_1 ∧
                                    (input - a_2 = a_2 - a_3)
                        ]
                    A = [a_0 = N,
                         a_1 = isProg
                         a_3 = a_2
                         a_2 = input
                        ]
                    M = [(N, a_0)
                         (isProg, a_1)
                         (input, a_2)
                         (a_2, a_3)
                        ]


   Example 2: Fibonacci Sequence

   V = [fib = if init then
                1
              else
                pre(if init then 1 else fib + pre fib)
       ]
   A = []
   M = []

   Visit(fib):

   V = [fib = if init then
                1
              else
                a_1
       ]
   A = [a_1 = if init then 1 else fib + a_0
        a_0 = fib
       ]
   M = []

   t   | 0 | 1 | 2 | 3 | 4 | 5
   ---------------------------------------------
   fib | 1 | 1 | 2 | 3 | 5 | 8
   a_1 | 1 | 2 | 3 | 5 | 8 | 13
   a_0 | 1 | 1 | 2 | 3 | 5 | 8

 *)
