(*
  Compile appraiser program the nice-and-slow way by evaluating
  the CakeML compiler in-logic.
 *)
open bossLib preamble ml_progLib ml_translatorLib;
open appraiserTheory;
open compilationLib;


val _ = new_theory "appraiserEvalCompile";

val _ = translation_extends "appraiser";

(* Convert the list of declarations comprising the appraiser from SNOC list to CONS list.
   Save in a def becase compile_x64 expects a thm where the rhs is the prog in question *)
Definition appraiser_prog_def:
  appraiser_prog = ^(get_ml_prog_state() |> get_prog |> EVAL |> concl |> rhs)
End

(* Compile, export the resulting ELF template to a file,
   and produce a theorem certifying that the machine code therein is the
   compiler output *)
val compile_thm = compile_x64 1000 1000 "eval_appraiser" appraiser_prog_def

(* In terminal:

 > gcc eval_appraiser.S $CAKEMLDIR/basis/basis_ffi.c -o appraiser

 *)

val _ = export_theory();
