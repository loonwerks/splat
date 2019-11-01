open HolKernel boolLib Parse bossLib;
open stringLib;
open finite_mapLib;

open preamble
open ml_translatorTheory;
open ml_translatorLib ml_progLib;
open basisFunctionsLib;
open basisProgTheory;
open wordsTheory;
open comparisonTheory;

val _ = new_theory "copland";

(*---------------------------------------------------------------------------*)
(* Terms                                                                     *)
(*---------------------------------------------------------------------------*)
val res = type_abbrev ("place",``:word32``);
val res = type_abbrev ("mid",  ``:num``);
val res = type_abbrev("pi", ``:bool # bool``); (* provisional *)

(* Explicitly typed w2n to word32 to avoid running into problems with dimindex/the 'itself' constructor *)
val w322n_def = Define `w322n (w:word32) = w2n w`;

val place_cmp_def = Define
  `place_cmp (p1 : place) (p2 : place) = num_cmp (w322n p1) (w322n p2)`;

val res = translate num_cmp_def;
val res = translate w322n_def;
val res = translate place_cmp_def;

val _ = Hol_datatype
  `term = USM of mid => string list  (* User space measurement *)
        | KIM of mid => place => string list (* Kernel integrity measurement *)
	      | SIG
	      | HSH
	      | CPY
	      | NONCE
        | AT of place => term
        | LN of term => term
        | BRS of pi => term => term
        | BRP of pi => term => term`;

val _ = Hol_datatype
  `evidence (* akin to values in a PL *) (* more like types. They're abstract versions of the concrete evidence below *)
       = Mt
       | U of place => evidence  (* User space measurement evidence *)
       | K of place => place => evidence
       | G of evidence => place
       | H of evidence => place
       | N of place => evidence
       | SS of evidence => evidence
       | PP of evidence => evidence`;


(*---------------------------------------------------------------------------*)
(* Concrete Evidence                                                         *)
(*---------------------------------------------------------------------------*)

val res = type_abbrev ("args",``:string list``);
val res = type_abbrev ("bits", ``:string``); (* base64 (or 16 now?) encoded string *)

val _ = Hol_datatype
  `concrete
       = MT
       | CUSM of place => mid => args => bits => concrete  (* User space measurement concrete *)
       | CKSM of place => place => mid => args => bits => concrete
       | CSIG of place => concrete => bits
       | CHASH of place => bits
       | CNONCE of place => bits => concrete
       | CSEQ of concrete => concrete
       | CPAR of concrete => concrete`;

(*---------------------------------------------------------------------------*)
(* Messages                                                                  *)
(*---------------------------------------------------------------------------*)

val res = type_abbrev ("address",``:num``);

val _ = Hol_datatype
   `request = <| toPlace : place ;
                 fromPlace : place ;
		             reqNameMap : place |-> address ;
		             reqTerm : term ;
		             reqEv : concrete |>`;


val _ = Hol_datatype
  `response = <| respToPlace : place ;
                 respFromPlace : place ;
		             respEv : concrete |>`;

val _ = export_theory();
