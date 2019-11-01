(*
  Compile appraiser program the quick-and-dirty way with the
  unverified S-expression bootstrap. Assumes a cake binary on
  your $PATH
 *)
open bossLib preamble ml_progLib ml_translatorLib;
open appraiserTheory fromSexpTheory;
open astToSexprLib;


val _ = new_theory "appraiserCompile";

val _ = translation_extends "appraiser";

(* Convert the list of declarations comprising the appraiser from SNOC list to CONS list *)
val appraiser_prog = get_ml_prog_state() |> get_prog |> EVAL |> concl |> rhs;

(* Pretty-print aforementioned CONS list as an s-expression *)
val _ = write_ast_to_file "appraiser.sexp" appraiser_prog;

(* In terminal:

 > cake --skip_type_inference=true --sexp=true < appraiser.sexp > appraiser.S

  To link:

 > gcc appraiser.S $CAKEMLDIR/basis/basis_ffi.c -o appraiser

 *)

val _ = export_theory();
