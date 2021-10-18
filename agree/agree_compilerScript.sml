open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory;

val _ = intLib.prefer_int();

val _ = new_theory "agree_compiler";



(* ========================================================================== *)
(* Compilation of a component into a "step" function. The step function       *)
(* is similar to the semantic componentFn, except that its state              *)
(* variables are values, not value streams. If                                *)
(*                                                                            *)
(*    stepFn = compile comp                                                   *)
(*                                                                            *)
(* then it should be the case that the latest values of the streams           *)
(* computed by iterateFn will be the current values for the state             *)
(* variables of the stepFn. Roughly:                                          *)
(*                                                                            *)
(*  !v. v IN varDecs comp                                                     *)
(*        ==>                                                                 *)
(*      !t. (iterateFn E comp t ' v) t =                                      *)
(*          FUNPOW stepFn t (init_state E) ' v                                *)
(*                                                                            *)
(* Some complicating factors:                                                 *)
(*                                                                            *)
(*  1. The component needs to be in "pre normal form" so that the state-      *)
(*     holding variables can be straightforwardly dealt with. The normal form *)
(*     enforces that the componentFn accesses variable values at most one     *)
(*     time step back in the stream.                                          *)
(*                                                                            *)
(*  2. State variables and output variables are treated the same in E, but    *)
(*     need to be distinguished in stepFn                                     *)
(* ========================================================================== *)

val _ = export_theory();
