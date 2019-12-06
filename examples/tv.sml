open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory listTheory rich_listTheory stringTheory
     FormalLangTheory charsetTheory regexpTheory Regexp_Numerics numposrepTheory
     splatTheory pred_setLib intLib regexpLib splatLib;

(*---------------------------------------------------------------------------*)
(* Boilerplate prelude stuff                                                 *)
(*---------------------------------------------------------------------------*)

val ERR = mk_HOL_ERR "TV";

val mesg_ss = list_ss
             ++ intSimps.INT_REDUCE_ss
             ++ intSimps.INT_RWTS_ss
             ++ intLib.INT_ARITH_ss
             ++ PRED_SET_ss
             ++ rewrites [ord_mod_256,CHR_ORD];

val _ = numLib.prefer_num();

overload_on ("++",``list$APPEND``);

infix byA;
val op byA = BasicProvers.byA;

val var_eq_tac = rpt BasicProvers.VAR_EQ_TAC;
val decide = bossLib.DECIDE;
val qdecide = decide o Parse.Term;

val sym = SYM;
val subst_all_tac = SUBST_ALL_TAC;
val popk_tac = pop_assum kall_tac;
val pop_subst_tac = pop_assum subst_all_tac;
val pop_sym_subst_tac = pop_assum (subst_all_tac o sym);
val qpat_k_assum = C qpat_x_assum kall_tac;

fun qspec q th = th |> Q.SPEC q
fun qspec_arith q th = qspec q th |> SIMP_RULE mesg_ss [];

(*---------------------------------------------------------------------------*)
(* Stuff about regexps and twos_complement encoding                          *)
(*---------------------------------------------------------------------------*)

val regexp_lang_cat = el 2 (CONJUNCTS regexp_lang_def);
val regexp_lang_or = last (CONJUNCTS regexp_lang_def);

val (enci_bytes_1 :: enci_bytes_2 :: _) = CONJUNCTS enci_bytes;
val (enc_bytes_1 :: enc_bytes_2 :: _) = CONJUNCTS enc_bytes;
val (enci_limits_1 :: enci_limits_2 :: _) = CONJUNCTS enci_limits;

(*---------------------------------------------------------------------------*)
(* Declare simple record and define wellformedness                           *)
(*---------------------------------------------------------------------------*)

val _ =
 Hol_datatype
   `gps = <| lat:  int ;
             lon : int ;
             alt : int |>`;

val good_gps_def =
  Define
    `good_gps recd <=>
          -90 <= recd.lat /\ recd.lat <= 90 /\
         -180 <= recd.lon /\ recd.lon <= 180 /\
            0 <= recd.alt /\ recd.alt <= 17999`;

(*---------------------------------------------------------------------------*)
(* Regexp expressing the interval constraints                                *)
(*---------------------------------------------------------------------------*)

val gps_regexp =
    Regexp_Match.normalize
        (Regexp_Type.fromQuote `\i{~90,90}\i{~180,180}\i{0,17999}`);

val gps_regexp_term = regexpSyntax.regexp_to_term gps_regexp;

(*---------------------------------------------------------------------------*)
(* "The" translation validation theorem.                                     *)
(*---------------------------------------------------------------------------*)

Theorem tv_thm :
  !s. s IN regexp_lang ^gps_regexp_term
      <=>
      s IN ({enci 1 i | -90 <= i /\ i <= 90} dot
            {enci 2 i | -180 <= i /\ i <= 180} dot
            {enci 2 i | 0 <= i /\ i <= 17999})
Proof
rw_tac (mesg_ss ++ in_charset_conv_ss)
       [regexp_lang_cat,regexp_lang_or,IN_dot, LIST_UNION_def,PULL_EXISTS]
>> eq_tac
>- (rpt (DISCH_THEN (CHOOSE_THEN MP_TAC))
     >> DISCH_THEN (fn th =>
        qexists_tac `deci 1 u`
        >> qexists_tac `deci 2 u'`
        >> qexists_tac `deci 2 v'`
        >> mp_tac th)
     >> rw_tac mesg_ss []
     >> `0 < STRLEN u /\
         0 < STRLEN (STRCAT u'' v) /\
         0 < STRLEN (STRCAT u''' v'')` by rw_tac mesg_ss []
     >> imp_res_tac enci_deci
     >> rfs[]
     >> ntac 6 popk_tac
     >> `?c1 c2 c3 c4 c5.
           u = [c1] /\ u'' = [c2] /\ v = [c3] /\ u''' = [c4] /\ v'' = [c5]`
         by metis_tac [strlen_eq]
     >> var_eq_tac
     >> assume_tac (qspec_arith `[c2;c3]` dec_bound)
     >> assume_tac (qspec_arith `[c4;c5]` dec_bound)
     >> full_simp_tac mesg_ss [deci_def,n2i_def,dec_char,dec_rec]
   )
>- (rpt (disch_then (CHOOSE_THEN MP_TAC))
     >> disch_then (fn th =>
             qexists_tac `enci 1 i`
          >> qexists_tac `enci 2 i'`
          >> qexists_tac `enci 2 i''`
          >> mp_tac th)
    >> rw_tac mesg_ss []
    >- (`?a. enci 1 i = [a]` by rw_tac mesg_ss [enci_bytes_1] >> rw_tac mesg_ss [])
    >- (`representable 8 i` by rw_tac mesg_ss [representable_def]
         >> rw_tac mesg_ss [enci_def,i2n_def,dec_enc]
         >> intLib.ARITH_TAC)
    >- (`representable 16 i'` by rw_tac mesg_ss [representable_def]
         >> rw_tac mesg_ss [enci_def,i2n_def]
         >- (disj2_tac
              >> `Num i' <= 180 ` by intLib.ARITH_TAC
              >> rw_tac mesg_ss [enc_bytes_2]
              >> qexists_tac `[CHR (Num i')]`
              >> qexists_tac `[CHR ((Num i' DIV 256) MOD 256)]`
              >> rw_tac mesg_ss [dec_rec,ORD_CHR_RWT] >> intLib.ARITH_TAC)
         >- (disj1_tac
              >> `0 < Num (ABS i')` by intLib.ARITH_TAC
              >> rw_tac mesg_ss [enc_bytes_2]
              >> qexists_tac `[CHR ((65536 − Num (ABS i')) MOD 256)]`
              >> qexists_tac `[CHR (((65536 − Num (ABS i')) DIV 256) MOD 256)]`
              >> rw_tac mesg_ss [dec_rec,ORD_CHR_RWT] >> intLib.ARITH_TAC))
    >- (`representable 16 i''` by rw_tac mesg_ss [representable_def]
         >> rw_tac mesg_ss [enci_def,i2n_def]
         >> `0i <= i'' /\ i'' < 256i \/
             256 <= i'' /\ i'' < 17920 \/
             17920 <= i'' /\ i'' < 18000` by intLib.ARITH_TAC
         >- (disj2_tac >> disj1_tac
              >> `Num i'' < 256 ` by intLib.ARITH_TAC
              >> rw_tac mesg_ss [enc_bytes_2]
              >> qexists_tac `[CHR (Num i'')]`
              >> qexists_tac `[CHR ((Num i'' DIV 256) MOD 256)]`
              >> rw_tac mesg_ss [dec_rec,ORD_CHR_RWT] >> intLib.ARITH_TAC)
         >- (disj2_tac >> disj2_tac
              >> `Num i'' < 17920` by intLib.ARITH_TAC
              >> rw_tac mesg_ss [enc_bytes_2]
              >> qexists_tac `[CHR (Num i'' MOD 256)]`
              >> qexists_tac `[CHR ((Num i'' DIV 256) MOD 256)]`
              >> rw_tac mesg_ss [dec_rec,ORD_CHR_RWT] >> intLib.ARITH_TAC)
         >- (disj1_tac
              >> `Num i'' < 18000` by intLib.ARITH_TAC
              >> rw_tac mesg_ss [enc_bytes_2]
              >> qexists_tac `[CHR (Num i'' MOD 256)]`
              >> qexists_tac `[CHR ((Num i'' DIV 256) MOD 256)]`
              >> rw_tac mesg_ss [dec_rec,ORD_CHR_RWT] >> intLib.ARITH_TAC)
       )
   )
QED

(*
val lemB =
 qdecide `!a b c k1 k2 k3.
            k1 <= (a:num) /\ k2 <= b /\ k3 <= c /\
            (a+b+c = k1+k2+k3)
            ==> (a=k1) /\ (b=k2) /\ (c=k3)`
   |> qspec `LENGTH (enci 1n (m.lat:int))`
   |> qspec `LENGTH (enci 2n (m.lon:int))`
   |> qspec `LENGTH (enci 2n (m.alt:int))`
   |> qspec `1n`
   |> qspec `2n`
   |> qspec `2n`
   |> SIMP_RULE arith_ss [lower_enci];



val manifest =
 [(``recd.lat``,
   Interval
     {span = (IntInf.fromInt ~90,IntInf.fromInt 90),
      encoding = Regexp_Numerics.Twos_comp,
      endian   = Regexp_Numerics.LSB,
      width    = BYTEWIDTH 1,
      encoder  = fn _ => raise ERR "filter_info" "null SML encoder",
      decoder  = fn _ => raise ERR "filter_info" "null SML decoder",
      regexp   = Regexp_Type.fromQuote `\i{~90,90}`}),
  (``recd.lon``,
   Interval
     {span = (IntInf.fromInt ~180,IntInf.fromInt 180),
      encoding = Regexp_Numerics.Twos_comp,
      endian   = Regexp_Numerics.LSB,
      width    = BYTEWIDTH 2,
      encoder  = fn _ => raise ERR "filter_info" "null SML encoder",
      decoder  = fn _ => raise ERR "filter_info" "null SML decoder",
      regexp   = Regexp_Type.fromQuote `\i{~180,180}`}),
  (``recd.alt``,
   Interval
     {span = (IntInf.fromInt 0,IntInf.fromInt 17999),
      encoding = Regexp_Numerics.Twos_comp,
      endian   = Regexp_Numerics.LSB,
      width    = BYTEWIDTH 2,
      encoder  = fn _ => raise ERR "filter_info" "null SML encoder",
      decoder  = fn _ => raise ERR "filter_info" "null SML decoder",
      regexp   = Regexp_Type.fromQuote `\i{0,17999}`})];

Theorem mem_last_alt :
 !L. ~(L = []) ==> MEM (LAST L) L
Proof
 Cases >> rw_tac list_ss [MEM_LAST]
QED


Theorem append_cons :
 !L1 h L2. L1 ++ (h::L2) = (L1 ++ [h]) ++ L2
Proof
 Induct >> metis_tac [APPEND]
QED

Theorem l2n_append :
 !n b list. 0 < b ==> l2n b (list ++ REPLICATE n 0) = l2n b list
Proof
 Induct
  >> rw_tac list_ss [REPLICATE,SNOC_APPEND]
  >> metis_tac [l2n_SNOC_0,SNOC_APPEND,append_cons]
QED
*)
