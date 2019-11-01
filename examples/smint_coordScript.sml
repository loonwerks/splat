open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory stringTheory pred_setLib intLib
     FormalLangTheory charsetTheory regexpTheory regexpLib
     numposrepTheory splatTheory splatLib Regexp_Numerics;

val int_ss = intSimps.int_ss;

(*---------------------------------------------------------------------------*)
(* Boilerplate prelude stuff                                                 *)
(*---------------------------------------------------------------------------*)

val _ = numLib.prefer_num();

overload_on ("++",``list$APPEND``);

infix byA;
val op byA = BasicProvers.byA;

val qpat_k_assum = Lib.C qpat_x_assum kall_tac;
val allhyp_mp_tac = rpt (pop_assum mp_tac);
val allhyp_kill_tac = rpt (pop_assum kall_tac);
fun qpat_keeponly_assum qpat = qpat_x_assum qpat mp_tac >> allhyp_kill_tac

fun qspec q th = th |> Q.SPEC q
fun qspec_arith q th = qspec q th |> SIMP_RULE arith_ss [];

val var_eq_tac = rpt BasicProvers.VAR_EQ_TAC;

val decide = bossLib.DECIDE;
val qdecide = decide o Parse.Term;

val ERR = mk_HOL_ERR "SMINT";

val regexp_lang_cat = el 2 (CONJUNCTS regexp_lang_def);
val regexp_lang_or = last (CONJUNCTS regexp_lang_def);


(*---------------------------------------------------------------------------*)
(* Declare simple record and define wellformedness                           *)
(*---------------------------------------------------------------------------*)

val _ = new_theory "smint_coord";

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

val filter_info = 
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


(*---------------------------------------------------------------------------*)
(* Encode/decode gps elts                                                    *)
(*---------------------------------------------------------------------------*)

val encode_def =
    Define
    `encode recd =
       CONCAT [enci 1 recd.lat;
               enci 2 recd.lon;
               enci 2 recd.alt]`;

(*---------------------------------------------------------------------------*)
(* Note that this decoder operates under the assumption that decZ is total.  *)
(*---------------------------------------------------------------------------*)

val decode_def =
 Define
  `decode s =
    case s
     of [a;b;c;d;e] =>
        SOME <| lat := deci 1 [a];
                lon := deci 2 [b;c];
                alt := deci 2 [d;e] |>
      | otherwise => NONE`;

(*---------------------------------------------------------------------------*)
(* Examples                                                                  *)
(*---------------------------------------------------------------------------*)

val GPS  =    ``<| lat := 0i; lon := 135i; alt := 6578 |>``;
val GPS1 =    ``<| lat := ~90; lon := ~135i; alt := 15999 |>``;
val NON_GPS = ``<| lat := ~91; lon := ~135i; alt := 16000 |>``;

EVAL ``decode (encode ^GPS) = SOME ^GPS``;
EVAL ``decode (encode ^GPS1) = SOME ^GPS1``;
EVAL ``decode (encode ^GPS1) = SOME ^GPS1``;
EVAL ``good_gps ^NON_GPS``;
EVAL ``good_gps ^NON_GPS ==> decode (encode ^NON_GPS) = NONE``;

val (enci_bytes_1 :: enci_bytes_2 :: _) = CONJUNCTS enci_bytes;
val (enci_limits_1 :: enci_limits_2 :: _) = CONJUNCTS enci_limits;


GROSS ... 
val NO_PAD_RIGHT = Q.prove
(`!x n L1 L2. n = LENGTH L2 ==> ((PAD_RIGHT x n L1 = L2) = (L1 = L2))`,
 rw_tac list_ss [PAD_RIGHT]
   >> `(n - LENGTH L1) = 0` by rw_tac arith_ss []
   >> rw_tac list_ss []
);
val NO_PAD_RIGHT = Q.prove
(`!x n L1 L2. n <= LENGTH L2 ==> ((PAD_RIGHT x n L1 = L2) = (L1 = L2))`,
 rw_tac list_ss [PAD_RIGHT]
   >> `(n - LENGTH L1) = 0` by rw_tac arith_ss []
   >> rw_tac list_ss []
);


Theorem decode_encode :
  !m. good_gps m ==> (decode (encode m) = SOME m)
Proof
 rw_tac list_ss [decode_def, encode_def, list_case_eq, PULL_EXISTS,
                 good_gps_def, fetch "-" "gps_component_equality"]
  >> `?p. enci 1 m.lat = [p]` 
        by (match_mp_tac (qspec `m.lat` enci_bytes_1) >>  intLib.ARITH_TAC)
  >> `?q r. enci 2 m.lon = [q;r]` 
        by (match_mp_tac (qspec `m.lon` enci_bytes_2) >>  intLib.ARITH_TAC)
  >> `?s t. enci 2 m.alt = [s;t]` 
        by (match_mp_tac (qspec `m.alt` enci_bytes_2) >>  intLib.ARITH_TAC)
  >> `deci 1 (enci 1 m.lat) = m.lat /\
      deci 2 (enci 2 m.lon) = m.lon /\
      deci 2 (enci 2 m.alt) = m.alt` 
       by (rpt conj_tac >> match_mp_tac deci_enci 
           >> rw[representable_def] >> intLib.ARITH_TAC)
  >> rw_tac (srw_ss()) []
  >> metis_tac []
QED

fun LENGTH_EQ_CONV tm = 
 let open listSyntax numSyntax
     val (l,r) = dest_eq tm
     val (len, [exp]) = strip_comb l 
     val _ = if same_const len length_tm then () else raise ERR "LENGTH_EQ_CONV" ""
     val ty = dest_list_type (type_of exp)
     val k = numSyntax.int_of_term r
     val vars = map (C (curry mk_var) ty)
                    (map (strcat "v" o Int.toString) (upto 1 k))
     val rhs_form = list_mk_exists(vars,mk_eq(exp,listSyntax.mk_list(vars,ty)))
  in 
    prove (mk_eq(tm,rhs_form),
    rw_tac list_ss [Ntimes listTheory.LENGTH_EQ_NUM_compute k] >> metis_tac[])
  end

(*---------------------------------------------------------------------------*)
(* Regexp expressing the interval constraints                                *)
(*---------------------------------------------------------------------------*)

val gps_regexp =
    Regexp_Match.normalize
        (Regexp_Type.fromQuote `\i{~90,90}\i{~180,180}\i{0,17999}`);

val gps_regexp_term = regexpSyntax.regexp_to_term gps_regexp;

val lem = qdecide `!a c b d. (a:num) <= c /\ b <= d /\ (c+d = a+b) ==> (a=c) /\ (b=d)`;
val lemA = qdecide `!a b c k1 k2 k3. k1 <= (a:num) /\ k2 <= b /\ k3 <= c /\ 
                  (a+b+c = k1+k2+k3) ==> (a=k1) /\ (b=k2) /\ (c=k3)`;

val lemB = 
 lemA
   |> qspec `LENGTH (enci 1n (m.lat:int))` 
   |> qspec `LENGTH (enci 2n (m.lon:int))`
   |> qspec `LENGTH (enci 2n (m.alt:int))`
   |> qspec `1n` 
   |> qspec `2n` 
   |> qspec `2n` 
   |> SIMP_RULE arith_ss [lower_enci];

val BOUNDED_FORALL_TAC = 
    rpt (CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL)) >> rw[]

  
Theorem AGREE_ENCODE_PROP :
  !m. good_gps m <=> encode(m) IN regexp_lang ^gps_regexp_term
Proof
 rw_tac list_ss [regexp_lang_cat,IN_dot,PULL_EXISTS,encode_def,EQ_IMP_THM]
 >- (rw_tac (list_ss ++ in_charset_conv_ss) 
       [regexp_lang_cat,regexp_lang_or,LIST_UNION_def,
        IN_dot,strlen_eq,PULL_EXISTS,dec_char]
     >> fs [good_gps_def]
     >> `?p. enci 1 m.lat = [p]` 
           by (match_mp_tac (qspec `m.lat` enci_bytes_1) >>  intLib.ARITH_TAC)
     >> `?q r. enci 2 m.lon = [q;r]` 
           by (match_mp_tac (qspec `m.lon` enci_bytes_2) >>  intLib.ARITH_TAC)
     >> `?s t. enci 2 m.alt = [s;t]` 
           by (match_mp_tac (qspec `m.alt` enci_bytes_2) >>  intLib.ARITH_TAC)
     >> qexists_tac `enci 2 m.lon`
     >> qexists_tac `enci 2 m.alt`
     >> qexists_tac `p`
     >> simp_tac bool_ss [GSYM STRCAT_ASSOC,STRCAT_11]
     >> rw []
     >> pop_assum (mp_tac o Q.AP_TERM `deci 2`)
     >> pop_assum (mp_tac o Q.AP_TERM `deci 2`)
     >> pop_assum (mp_tac o Q.AP_TERM `deci 1`)
     >> rw_tac (int_ss ++ intSimps.INT_ARITH_ss) [deci_enci,representable_def]
     >> ntac 3 (pop_assum SUBST_ALL_TAC)
        >- (ntac 4 (pop_assum kall_tac)
             >> rpt (pop_assum mp_tac)
             >> Cases_on `p` 
             >> asm_simp_tac list_ss [ORD_CHR_RWT]
             >> BasicProvers.NORM_TAC list_ss 
                  [deci_def,dec_def,ORD_CHR_RWT,l2n_def,n2i_def]
             >> rpt (pop_assum mp_tac)
             >> Q.ID_SPEC_TAC `n`
             >> BOUNDED_FORALL_TAC)
        >- (ntac 2 (pop_assum kall_tac)
             >> ntac 2 (pop_assum mp_tac)
             >> rpt (pop_assum kall_tac)
             >> Cases_on `q` 
             >> Cases_on `r` 
             >> asm_simp_tac list_ss [ORD_CHR_RWT]
             >> BasicProvers.NORM_TAC list_ss 
                  [deci_def,dec_def,ORD_CHR_RWT,l2n_def,n2i_def]
             >> rpt (pop_assum mp_tac)
             >> Q.ID_SPEC_TAC `n`
             >> BOUNDED_FORALL_TAC)
        >- (ntac 2 (pop_assum mp_tac)
             >> rpt (pop_assum kall_tac)
             >> Cases_on `s` 
             >> Cases_on `t` 
             >> asm_simp_tac list_ss [ORD_CHR_RWT]
             >> BasicProvers.NORM_TAC list_ss 
                  [deci_def,dec_def,ORD_CHR_RWT,l2n_def,n2i_def]
             >> rpt (pop_assum mp_tac)
             >> Q.ID_SPEC_TAC `n`
             >> BOUNDED_FORALL_TAC)
    )

 (* second part *)
 >- (full_simp_tac (list_ss ++ in_charset_conv_ss) 
              [regexp_lang_cat,regexp_lang_or,LIST_UNION_def,
               IN_dot,strlen_eq,PULL_EXISTS,dec_char]
     >> rw_tac list_ss []
     >> full_simp_tac list_ss [dec_char,ORD_EQ]
     >> rw_tac list_ss []
     >> `STRLEN (enci 1 m.lat) = 1 /\ STRLEN (enci 2 m.lon) = 2 /\ STRLEN (enci 2 m.alt) = 2` 
         by (match_mp_tac lemB 
             >> qpat_assum `_ = _` (mp_tac o Q.AP_TERM `STRLEN`) >> rw[])
     >> fs [listTheory.LENGTH_EQ_NUM_compute] >> rw[] >> fs[] >> rw[]
     >> imp_res_tac enci_limits_1
     >> imp_res_tac enci_limits_2
FOO
     >> pop_assum (mp_tac o Q.AP_TERM `deci 2`)
     >> pop_assum (mp_tac o Q.AP_TERM `deci 2`)
     >> pop_assum (mp_tac o Q.AP_TERM `deci 1`)
     >> rw_tac (int_ss ++ intSimps.INT_ARITH_ss) [deci_enci]
   
     >> `?c c1 c2 c3 c4 c5 c6.
          (enci 1 m.lat = [c1]) /\ 
          (enci 2 m.lon = [c2;c3]) /\ 
          (enci 2 m.alt = [c4;c5])` by metis_tac [len_lem]
     >> full_simp_tac list_ss [encZ_def]
     >> BasicProvers.NORM_TAC list_ss [CHR_11]
     >> asm_simp_tac list_ss [good_gps_def]
     >> `(m.lat = decZ (encZ 1 m.lat)) /\
         (m.lon = decZ (encZ 1 m.lon)) /\
         (m.alt = decZ (encZ 1 m.alt))` by metis_tac [decz_encz]
     >> ntac 3 (pop_assum SUBST1_TAC)
     >> asm_simp_tac bool_ss [encZ_def]
     >> asm_simp_tac int_ss [decZ_eqns,dec_char,dec_enc]
     >> qpat_x_assum `enc 2 _ = _` (mp_tac o AP_TERM ``dec``)
     >> rw_tac list_ss [dec_enc, dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
    )
QED


 >- (rw_tac (list_ss ++ in_charset_conv_ss) []
     >> simp_tac bool_ss [GSYM STRCAT_ASSOC,STRCAT_11]
     >> full_simp_tac list_ss [good_gps_def]
     >> rpt conj_tac
        >- metis_tac [encZ_def]
        >- (ntac 4 (pop_assum kall_tac)
            >> Cases_on `m.lat < 0` THENL [disj2_tac, disj1_tac]
            >> `Num(ABS m.lat) < 256` by intLib.ARITH_TAC
            >> rw_tac int_ss [encZ_def,enc_bytes,ORD_CHR_RWT]
            >> intLib.ARITH_TAC)
        >- (ntac 2 (pop_assum kall_tac) 
            >> ntac 2 (pop_assum mp_tac) 
            >> ntac 2 (pop_assum kall_tac) 
            >> rpt strip_tac
            >> Cases_on `m.lon < 0` THENL [disj2_tac, disj1_tac]
            >> `Num(ABS m.lon) < 256` by intLib.ARITH_TAC
            >> rw_tac int_ss [encZ_def,enc_bytes,ORD_CHR_RWT]
            >> intLib.ARITH_TAC)
        >- EVAL_TAC
        >- (ntac 2 (pop_assum mp_tac) 
            >> rpt (pop_assum kall_tac) 
            >> rpt strip_tac
            >> `m.alt >= 256 * 70 \/ m.alt < 256 * 70` 
                  by intLib.ARITH_TAC 
            THENL [disj1_tac,disj2_tac]
            >- (`Num(ABS m.alt) < 65536` by intLib.ARITH_TAC
                >> rw_tac int_ss [enc_bytes,ORD_CHR_RWT]
                >> intLib.ARITH_TAC)
            >- (Cases_on `m.alt < 256` THENL [disj1_tac,disj2_tac]
                >- (`Num(ABS m.alt) < 256` by intLib.ARITH_TAC
                     >> rw_tac int_ss [enc_bytes,ORD_CHR_RWT]
                     >> intLib.ARITH_TAC)
                >- (`Num(ABS m.alt) < 65536` by intLib.ARITH_TAC
                     >> rw_tac int_ss [enc_bytes,ORD_CHR_RWT]
                     >> intLib.ARITH_TAC)))
    )

 
Theorem AGREE_DECODE_PROP :
 !s. s IN regexp_lang ^gps_regexp_term ==> good_gps (THE (decode s))
Proof
 rw_tac std_ss [AGREE_ENCODE_PROP]
  >> full_simp_tac (list_ss ++ in_charset_conv_ss) 
       [regexp_lang_cat,regexp_lang_or,LIST_UNION_def,IN_dot,strlen_eq,PULL_EXISTS,dec_char,ORD_EQ]
  >> rw_tac list_ss [decode_def,decZ_eqns,dec_char]
  >> rw_tac (srw_ss()) [encode_def]
  >- (qexists_tac `[#"+"; c']`
      >> qexists_tac `[#"+"; c'']`
      >> qexists_tac `[c;#"F"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"+"; c']`
      >> qexists_tac `[#"+"; c'']`
      >> qexists_tac `[c;#"\^@"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"+"; c']`
      >> qexists_tac `[#"+"; c'']`
      >> qexists_tac `[c;c''']`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- (rw_tac bool_ss [Once ADD_SYM,Once MULT_SYM]
              >> rw_tac list_ss [MOD_MULT,CHR_ORD])
         >- (rw_tac (srw_ss()) [ADD_DIV_RWT,LESS_DIV_EQ_ZERO]
              >> rw_tac bool_ss [Once MULT_SYM]
              >> rw_tac std_ss [MULT_DIV,ord_mod_256,CHR_ORD]))

  >- (qexists_tac `[#"+"; c']`
      >> qexists_tac `[#"-"; c'']`
      >> qexists_tac `[c;#"F"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"+"; c']`
      >> qexists_tac `[#"-"; c'']`
      >> qexists_tac `[c;#"\^@"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"+"; c']`
      >> qexists_tac `[#"-"; c'']`
      >> qexists_tac `[c;c''']`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- (rw_tac bool_ss [Once ADD_SYM,Once MULT_SYM]
              >> rw_tac list_ss [MOD_MULT,CHR_ORD])
         >- (rw_tac (srw_ss()) [ADD_DIV_RWT,LESS_DIV_EQ_ZERO]
              >> rw_tac bool_ss [Once MULT_SYM]
              >> rw_tac std_ss [MULT_DIV,ord_mod_256,CHR_ORD]))

  >- (qexists_tac `[#"-"; c']`
      >> qexists_tac `[#"+"; c'']`
      >> qexists_tac `[c;#"F"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"-"; c']`
      >> qexists_tac `[#"+"; c'']`
      >> qexists_tac `[c;#"\^@"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"-"; c']`
      >> qexists_tac `[#"+"; c'']`
      >> qexists_tac `[c;c''']`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- (rw_tac bool_ss [Once ADD_SYM,Once MULT_SYM]
              >> rw_tac list_ss [MOD_MULT,CHR_ORD])
         >- (rw_tac (srw_ss()) [ADD_DIV_RWT,LESS_DIV_EQ_ZERO]
              >> rw_tac bool_ss [Once MULT_SYM]
              >> rw_tac std_ss [MULT_DIV,ord_mod_256,CHR_ORD]))

  >- (qexists_tac `[#"-"; c']`
      >> qexists_tac `[#"-"; c'']`
      >> qexists_tac `[c;#"F"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"-"; c']`
      >> qexists_tac `[#"-"; c'']`
      >> qexists_tac `[c;#"\^@"]`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- rw_tac list_ss [Once (GSYM MOD_PLUS),CHR_ORD]
         >- rw_tac list_ss [ADD_DIV_RWT,LESS_DIV_EQ_ZERO])

  >- (qexists_tac `[#"-"; c']`
      >> qexists_tac `[#"-"; c'']`
      >> qexists_tac `[c;c''']`
      >> rw_tac int_ss [encZ_def,enc_bytes,CHR_ORD]
      >> rw_tac std_ss [STRCAT_EQNS]
      >> rw_tac list_ss [dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
      >> rw_tac int_ss [enc_bytes]
         >- (rw_tac bool_ss [Once ADD_SYM,Once MULT_SYM]
              >> rw_tac list_ss [MOD_MULT,CHR_ORD])
         >- (rw_tac (srw_ss()) [ADD_DIV_RWT,LESS_DIV_EQ_ZERO]
              >> rw_tac bool_ss [Once MULT_SYM]
              >> rw_tac std_ss [MULT_DIV,ord_mod_256,CHR_ORD]))
QED


Theorem back:
 `!recd. 
   (P1 (recd.lat) <=> encZ 1 recd.lat IN regexp_lang r1) /\
   (P2(recd.lon) <=> encZ 1 recd.lon IN regexp_lang r2) /\
   (P3(recd.alt) <=> encZ 2 recd.alt IN regexp_lang r3) 
==> 
   (P1 (recd.lat) /\ P2 (recd.lon) /\ P3 (recd.alt) <=>
     CONCAT [encZ 1 recd.lat; encZ 1 recd.lon; encZ 2 recd.alt] 
     IN regexp_lang (Cat r1 (Cat r2 r3)))`
Proof
rw_tac std_ss []
 >> rpt (pop_assum kall_tac)
 >> rw_tac list_ss [regexp_lang_cat,IN_dot,EQ_IMP_THM]
    >- metis_tac [STRCAT_ASSOC,STRCAT_11]
    >-
 >- (first_x_assum match_mp_tac
metis_tac []
QED

Theorem AGREE_ENCODE_PROP :
  !m. good_gps m <=> encode(m) IN regexp_lang ^gps_regexp_term
Proof

 rw_tac list_ss [regexp_lang_cat,IN_dot,PULL_EXISTS,encode_def,EQ_IMP_THM]
 >- (rw_tac (list_ss ++ in_charset_conv_ss) 
       [regexp_lang_cat,regexp_lang_or,LIST_UNION_def,IN_dot,strlen_eq,PULL_EXISTS,dec_char]
     >> qexists_tac `encZ 1 m.lat`
     >> qexists_tac `encZ 1 m.lon`
     >> qexists_tac `enc 2 (Num (ABS m.alt))`
     >> qexists_tac `#"+"`
     >> simp_tac bool_ss [GSYM STRCAT_ASSOC,STRCAT_11]
     >> full_simp_tac list_ss [good_gps_def]
     >> rpt conj_tac
        >- metis_tac [encZ_def]
        >- (ntac 4 (pop_assum kall_tac)
            >> Cases_on `m.lat < 0` THENL [disj2_tac, disj1_tac]
            >> `Num(ABS m.lat) < 256` by intLib.ARITH_TAC
            >> rw_tac int_ss [encZ_def,enc_bytes,ORD_CHR_RWT]
            >> intLib.ARITH_TAC)
        >- (ntac 2 (pop_assum kall_tac) 
            >> ntac 2 (pop_assum mp_tac) 
            >> ntac 2 (pop_assum kall_tac) 
            >> rpt strip_tac
            >> Cases_on `m.lon < 0` THENL [disj2_tac, disj1_tac]
            >> `Num(ABS m.lon) < 256` by intLib.ARITH_TAC
            >> rw_tac int_ss [encZ_def,enc_bytes,ORD_CHR_RWT]
            >> intLib.ARITH_TAC)
        >- EVAL_TAC
        >- (ntac 2 (pop_assum mp_tac) 
            >> rpt (pop_assum kall_tac) 
            >> rpt strip_tac
            >> `m.alt >= 256 * 70 \/ m.alt < 256 * 70` 
                  by intLib.ARITH_TAC 
            THENL [disj1_tac,disj2_tac]
            >- (`Num(ABS m.alt) < 65536` by intLib.ARITH_TAC
                >> rw_tac int_ss [enc_bytes,ORD_CHR_RWT]
                >> intLib.ARITH_TAC)
            >- (Cases_on `m.alt < 256` THENL [disj1_tac,disj2_tac]
                >- (`Num(ABS m.alt) < 256` by intLib.ARITH_TAC
                     >> rw_tac int_ss [enc_bytes,ORD_CHR_RWT]
                     >> intLib.ARITH_TAC)
                >- (`Num(ABS m.alt) < 65536` by intLib.ARITH_TAC
                     >> rw_tac int_ss [enc_bytes,ORD_CHR_RWT]
                     >> intLib.ARITH_TAC)))
    )
 (* second part *)
 >- (`2 <= LENGTH (encZ 1 m.lat) /\ 2 <= LENGTH (encZ 1 m.lon) /\ 3 <= LENGTH (encZ 2 m.alt)`
        byA (rw_tac list_ss [strlen_encZ]
             >> metis_tac [lower_enc, qdecide `2 = 1 + 1`, qdecide `3 = 2 + 1`,
                           arithmeticTheory.LE_ADD_RCANCEL])
     >> full_simp_tac (list_ss ++ in_charset_conv_ss) 
              [regexp_lang_cat,regexp_lang_or,LIST_UNION_def,
               IN_dot,strlen_eq,PULL_EXISTS,dec_char]
     >> rw_tac list_ss []
     >> full_simp_tac list_ss [dec_char,ORD_EQ]
     >> rw_tac list_ss []
     >> `?c c1 c2 c3 c4 c5 c6.
          (encZ 1 m.lat = [c;c1]) /\ (encZ 1 m.lon = [c2;c3]) /\ (encZ 2 m.alt = [c4;c5;c6])`
            by metis_tac [len_lem]
     >> full_simp_tac list_ss [encZ_def]
     >> BasicProvers.NORM_TAC list_ss [CHR_11]
     >> asm_simp_tac list_ss [good_gps_def]
     >> `(m.lat = decZ (encZ 1 m.lat)) /\
         (m.lon = decZ (encZ 1 m.lon)) /\
         (m.alt = decZ (encZ 1 m.alt))` by metis_tac [decz_encz]
     >> ntac 3 (pop_assum SUBST1_TAC)
     >> asm_simp_tac bool_ss [encZ_def]
     >> asm_simp_tac int_ss [decZ_eqns,dec_char,dec_enc]
     >> qpat_x_assum `enc 2 _ = _` (mp_tac o AP_TERM ``dec``)
     >> rw_tac list_ss [dec_enc, dec_def, l2n_def,ord_mod_256,ORD_CHR_RWT]
    )
QED

(*

val two_leq_length = Q.prove
(`!L. (2 <= LENGTH L) <=> ?a b t. L = a::b::t`,
  Cases_on `L` >> rw_tac list_ss [] >>
  Cases_on `t` >> rw_tac list_ss []);

val APPEND_EQ_CONS_ALT = Q.prove
(`!l1 l2 h t.
  ((l1 ++ l2 = h::t) <=> ((l1 = []) /\ (l2 = h::t)) \/ (∃lt. (l1 = h::lt) ∧ (t = lt ⧺ l2)))
  /\
  ((h::t = l1 ++ l2) <=> ((l1 = []) ∧ (l2 = h::t)) ∨ (∃lt. (l1 = h::lt) ∧ (t = lt ⧺ l2)))`,
 metis_tac [APPEND_EQ_CONS]);

val len_lem = Q.prove
(`!A B C.
   (2 <= LENGTH A) /\ (2 <= LENGTH B) /\ (3 <= LENGTH C) /\
   (A ++ B ++ C = [c1;c2;c3;c4;c5;c6;c7])
  ==>
  (A = [c1;c2]) /\ (B = [c3;c4]) /\ (C = [c5;c6;c7])`,
 rw_tac list_ss [APPEND_EQ_CONS_ALT,two_leq_length]
 >> full_simp_tac list_ss [APPEND_EQ_CONS_ALT]);
*)

val _ = export_theory();
