open HolKernel Parse boolLib bossLib;
open preamble semanticPrimitivesTheory;
open ml_translatorTheory;
open ml_translatorLib;
open ml_monad_translator_interfaceLib;
open ml_progLib;
open MapProgTheory;
open basisFunctionsLib;
open basisProgTheory;

open balanced_mapTheory;
open coplandTheory;
open comparisonTheory;
open wordsTheory;

val _ = new_theory "appraiser";
val _ = numLib.prefer_num ();

val sel4AM_def     = Define `sel4AM = 1w : place`;
val platformAM_def = Define `platformAM = 2w : place`;
val userAM_def     = Define `userAM = 3w : place`;

val usm11_def = Define `usm11 = 11`;
val kim11_def = Define `kim21 = 21`;

val attestation_cmd_def = Define
    `attestation_cmd = LN (AT platformAM (LN (AT sel4AM (LN (KIM kim21 platformAM [])
                                                            SIG))
                                             (LN (KIM kim21 userAM []) SIG)))
                          (LN (USM usm11 []) SIG)`;

val expected_bs1_def = Define `expected_bs1 = "1234"`;
val expected_bs2_def = Define `expected_bs2 = "2234"`;
val expected_bs3_def = Define `expected_bs3 = "3234"`;
val expected_bs4_def = Define `expected_bs4 = "4234"`;
val expected_bs5_def = Define `expected_bs5 = "5234"`;
val expected_bs6_def = Define `expected_bs6 = "6234"`;

val appraise_def = Define
    `(appraise (CSIG uAM (CUSM uAM2 u [] b5
                   (CSIG pAM (CKSM pAM2 uAM3 k1 [] b3
                       (CSIG sAM (CKSM sAM2 pAM3 k2 [] b1 MT) b2))
                       b4))
                   b6)
       = ((b6 = expected_bs6) /\ (b5 = expected_bs5) /\
          (b4 = expected_bs4) /\ (b3 = expected_bs3) /\
          (b2 = expected_bs2) /\ (b1 = expected_bs1) /\
          (uAM = userAM)      /\ (uAM2 = userAM)     /\ (uAM3 = userAM)     /\
          (pAM = platformAM)  /\ (pAM2 = platformAM) /\ (pAM3 = platformAM) /\
          (sAM = sel4AM)      /\ (sAM2 = sel4AM)     /\ (u = usm11)         /\
          (k1 = kim21)        /\ (k2 = kim21)))      /\

     (appraise _  = F)`;


val _ = type_abbrev ("cache",``:(place, bool # num # bool) balanced_map``);

val is_accepted_def = Define
    `is_accepted c p = case (balanced_map$lookup place_cmp p c)
                        of NONE => F
                         | SOME (a,_,_) => a`;

val is_time_expired_def = Define
    `is_time_expired c p curr_time =
         case (balanced_map$lookup place_cmp p c)
          of NONE => F
           | SOME (_,t,_) => curr_time < t`;

val is_waiting_def = Define
    `is_waiting c p = case (balanced_map$lookup place_cmp p c)
                       of NONE => F
                        | SOME (_,_,w) => w`;

val check_cache_before_req_def = Define
    `check_cache_before_req c p curr_t =
         is_accepted c p /\ is_time_expired c p curr_t /\ ~(is_waiting c p)`;

val update_cache_def = Define
    `update_cache c p curr_t a w =
          balanced_map$insert place_cmp p (a,curr_t + 1800,w) c`;

val _ = Hol_datatype `
    state_references = <| cache_ref : cache |>`;

val config = global_state_config |> with_state ``:state_references``
                                 |> with_refs [("cache_ref", ``balanced_map$empty : cache``)];

val check_cache_or_request_def = Define `
    check_cache_or_request msg time =
        let place = userAM;
        in do
            c <- get_cache_ref;
            if (check_cache_before_req c place time)
            then return T
            else (do set_cache_ref (update_cache c place time F T); return F od)
           od`;

val response_and_appraise_def = Define `
    response_and_appraise msg time attn_res =
        let place = userAM;
            acc = appraise attn_res
           in do
               c <- get_cache_ref;
               if is_waiting c place then set_cache_ref (update_cache c place time acc F) else set_cache_ref c;
               return (acc /\ is_waiting c place)
              od`;

(* val _ = translation_extends "basisProg"; *)
val res = translate empty_def;
val res = start_translation config;

val res = translate num_cmp_def;
val res = translate w322n_def;
val res = translate place_cmp_def;

(* translated in basis library as well, but unable to merge a.t.m. *)
val res = translate lookup_def;
val res = translate delta_def;
val res = translate singleton_def;
val res = translate ratio_def;
val res = translate size_def;
val res = translate balanceL_def;
val res = translate balanceR_def;
val res = translate insert_def;

val res = ml_prog_update (open_module "Appraiser");

val res = translate sel4AM_def;
val res = translate platformAM_def;
val res = translate userAM_def;

val res = translate usm11_def;
val res = translate kim11_def;

val res = translate expected_bs1_def;
val res = translate expected_bs2_def;
val res = translate expected_bs3_def;
val res = translate expected_bs4_def;
val res = translate expected_bs5_def;
val res = translate expected_bs6_def;

val res = translate appraise_def;
val res = translate attestation_cmd_def;

val res = translate is_accepted_def;
val res = translate is_time_expired_def;
val res = translate is_waiting_def;

val res = translate check_cache_before_req_def;
val res = translate update_cache_def;

val res = m_translate check_cache_or_request_def;
val res = m_translate response_and_appraise_def;

val res = ml_prog_update (close_module NONE)

val _ = export_theory();
