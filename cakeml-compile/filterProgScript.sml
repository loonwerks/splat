(*---------------------------------------------------------------------------*)
(* Skeleton for generating regexp compiler to CakeML and invoking the regexp *)
(* compiler on a given regexp. leaving a DFA function that expects a string. *)
(* I hope that the partial evaluation during compilation will work.          *)
(*---------------------------------------------------------------------------*)

open preamble basis MapProgTheory ml_translatorLib ml_progLib 
     basisFunctionsLib ml_translatorTheory cfTacticsBaseLib cfDivTheory cfDivLib
     charsetTheory regexpTheory regexp_compilerTheory;

val _ = new_theory "filterProg";

(*---------------------------------------------------------------------------*)
(* The regexp wrt. which we're filtering. This will be created by the splat  *)
(* frontend but is hardcoded for now.                                        *)
(*---------------------------------------------------------------------------*)

val the_regexp = Regexp_Type.fromQuote "foobar\^@";

val _ = translation_extends"MapProg";


val regexp_compilation_results as {certificate, aux, ...}
  = regexpLib.gen_dfa regexpLib.HOL the_regexp;

val matcher_certificate = save_thm
  ("matcher_certificate",
    certificate
      |> valOf
      |> CONV_RULE(QUANT_CONV(LHS_CONV (REWRITE_CONV [MAP])))
);

(*---------------------------------------------------------------------------*)
(* Define a named matcher function                                           *)
(*---------------------------------------------------------------------------*)

val matcher_def =
 Define `matcher ^(matcher_certificate |> concl |> dest_forall |> fst) =
                 ^(matcher_certificate |> concl |> dest_forall |> snd |> lhs)`

val match_string_def = Define `match_string s = matcher(explode s)`

val language_def =
 Define `language =
                 ^(matcher_certificate |> concl |> dest_forall |> snd |> rhs |> rator)`

val match_string_eq = Q.prove(`match_string = language o explode`,
  `!s. match_string s = (language o explode) s` suffices_by metis_tac[]
  >> rw[match_string_def,language_def,matcher_def,matcher_certificate]);

(*---------------------------------------------------------------------------*)
(* Translator setup boilerplate                                              *)
(*---------------------------------------------------------------------------*)

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end

val _ = find_def_for_const := def_of_const;

(* TODO: translate balanced_map module separately? *)

val _ = ml_translatorLib.pick_name :=
  let val default = !ml_translatorLib.pick_name in
    fn c =>
    if same_const c ``balanced_map$member`` then "balanced_map_member" else
    if same_const c ``balanced_map$empty`` then "balanced_map_empty" else
      default c
  end

val spec64 = INST_TYPE[alpha|->``:64``]

val _ = translate matcher_def

val mem_tolist = Q.prove(`MEM (toList l) (MAP toList ll) = MEM l ll`,
  Induct_on `ll` >> fs[]);

val length_tolist_cancel = Q.prove(
  `!n. n < LENGTH l ==> LENGTH (EL n (MAP mlvector$toList l)) = length (EL n l)`,
  Induct_on `l`
  >> fs[]
  >> rpt strip_tac
  >> Cases_on `n`
  >> fs[mlvectorTheory.length_toList]);

val EL_map_toList = Q.prove(`!n. n < LENGTH l ==> EL n' (EL n (MAP toList l)) = sub (EL n l) n'`,
  Induct_on `l`
  >> fs[]
  >> rpt strip_tac
  >> Cases_on `n`
  >> fs[mlvectorTheory.EL_toList]);

val exec_dfa_side_imp = Q.prove(
  `!finals table n s.
   good_vec (MAP toList (toList table)) (toList finals)
    /\ EVERY (λc. MEM (ORD c) ALPHABET) (EXPLODE s)
    /\ n < length finals
   ==> exec_dfa_side finals table n s`,
  Induct_on `s`
  >- fs[fetch "-" "exec_dfa_side_def"]
  >> PURE_ONCE_REWRITE_TAC [fetch "-" "exec_dfa_side_def"]
  >> fs[good_vec_def,mlvectorTheory.length_toList]
  >> rpt GEN_TAC
  >> Induct_on `table`
   >> rpt strip_tac
   >> fs[sub_def,length_def,mlvectorTheory.toList_thm]
   >> `MEM (toList (EL n l)) (MAP toList l)`
        by fs[EL_MEM,mem_tolist,mlvectorTheory.toList_thm]
   >- metis_tac[mlvectorTheory.length_toList]
   >> first_x_assum(MATCH_MP_TAC o Q.SPECL [`finals`,`Vector l`, `x1`])
    >> rpt strip_tac
    >> fs[mlvectorTheory.toList_thm, length_def, mem_tolist]
    >- metis_tac[]
    >> first_x_assum(ASSUME_TAC o Q.SPECL [`toList (EL n l)`,`ORD h`])
    >> first_x_assum(MATCH_MP_TAC o Q.SPECL [`n`,`ORD h`,`x1`])
    >> rfs[mlvectorTheory.length_toList,mem_tolist,EL_map_toList,length_tolist_cancel]);

val all_ord_string = Q.prove
(`EVERY (\c. MEM (ORD c) ALPHABET) s
   <=>
  EVERY (\c. ORD c < alphabet_size) s`,
 simp_tac list_ss [mem_alphabet_iff]);

val good_vec_thm =
 SIMP_RULE std_ss [dom_Brz_alt_equal]
    regexp_compilerTheory.compile_regexp_good_vec;

val matcher_side_lem = Q.prove(
  `!s. matcher_side s <=> T`,
  rw[fetch "-" "matcher_side_def"]
  >> match_mp_tac exec_dfa_side_imp
  >> rw_tac list_ss [mlvectorTheory.toList_thm]
    >- metis_tac [aux |> valOf,good_vec_thm]
    >- rw_tac list_ss [all_ord_string,ORD_BOUND,alphabet_size_def]
    >- EVAL_TAC)
 |>
 update_precondition;

val _ = translate match_string_def

(* val _ = translate(word_bit_test |> spec64); *)

(* TODO: this is largely copied from the bootstrap translation
         can it be properly abstracted out? *)
local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_WORD = find_equality_type_thm``WORD``
val no_closures_def = ml_translatorTheory.no_closures_def;
val LIST_TYPE_def = ml_translatorTheory.LIST_TYPE_def;
val EqualityType_def = ml_translatorTheory.EqualityType_def;
val types_match_def = ml_translatorTheory.types_match_def;
val ctor_same_type_def = semanticPrimitivesTheory.ctor_same_type_def;

Theorem tolist_fromlist_map_cancel:
  MAP mlvector$toList (MAP fromList ll) = ll
Proof
  Induct_on `ll` >> fs[]
QED

(*---------------------------------------------------------------------------*)
(* Auxiliary functions to deal with null termination.                        *)
(*---------------------------------------------------------------------------*)

val null_index_def = tDefine "null_index"
  `null_index s n =
    if n >= strlen s then NONE
    else if strsub s n = CHR 0 then SOME n
    else null_index s (SUC n)`
  (wf_rel_tac `inv_image (measure (λ(a,b). SUC a - b)) (strlen ## I)`);

val null_index_ind = fetch "-" "null_index_ind";

Theorem null_index_le_len:
  !s n m. null_index s n = SOME m ==> m < strlen s
Proof
  ho_match_mp_tac null_index_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_def])
  >> rw[]
QED

Theorem null_index_in_bound:
  !s n m. null_index s n = SOME m ==> n <= m
Proof
  ho_match_mp_tac null_index_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_def])
  >> rw[] >> fs[]
QED

Theorem null_index_null:
  !s n m. null_index s n = SOME m ==> strsub s m = CHR 0
Proof
  ho_match_mp_tac null_index_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_def])
  >> rw[] >> fs[]
QED

Theorem null_index_no_null:
  !s n m. null_index s n = SOME m ==> EVERY ($~ o $= (CHR 0)) (TAKE (m-n) (DROP n (explode s)))
Proof
  ho_match_mp_tac null_index_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_def])
  >> rw[]
  >> first_x_assum drule >> rpt(disch_then drule)
  >> strip_tac
  >> imp_res_tac null_index_le_len
  >> imp_res_tac null_index_in_bound
  >> qmatch_goalsub_abbrev_tac `EVERY _ (TAKE a1 a2)`
  >> Q.ISPECL_THEN [`a1`,`1`,`a2`] mp_tac take_drop_partition
  >> unabbrev_all_tac
  >> impl_tac >- intLib.COOPER_TAC
  >> disch_then(fn x => rw[GSYM x])
  >> fs[ADD1,DROP_DROP]
  >> `n < LENGTH(explode s)`
     by(fs[])
  >> drule TAKE1_DROP
  >> Cases_on `s` >> fs[mlstringTheory.strsub_def]
QED

Theorem null_index_no_null2:
  !s n. null_index s n = NONE ==> EVERY ($~ o $= (CHR 0)) (DROP n (explode s))
Proof
  ho_match_mp_tac null_index_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_def])
  >> rw[] >> Cases_on `n ≥ strlen s`
  >> Cases_on `s` >> fs[GREATER_EQ]
  >> imp_res_tac DROP_LENGTH_TOO_LONG >> fs[]
  >> `n < STRLEN s'` by fs[]
  >> imp_res_tac DROP_CONS_EL >> fs[]
QED

val cut_at_null_def = Define `cut_at_null s =
  case null_index s 0 of
      NONE => strcat s (str(CHR 0))
    | SOME n => substring s 0 (SUC n)`

Theorem cut_at_null_SPLITP:
  !s. cut_at_null s = implode(FST(SPLITP ($= (CHR 0)) (explode s)) ++ [CHR 0])
Proof
  Cases >> rw[cut_at_null_def] >> reverse(PURE_TOP_CASE_TAC >> rw[])
  >- (imp_res_tac null_index_le_len >> rw[mlstringTheory.substring_def]
      >> fs[mlstringTheory.strlen_def,mlstringTheory.implode_def]
      >> imp_res_tac null_index_no_null >> fs[]
      >> imp_res_tac null_index_null >> fs[]
      >> imp_res_tac SPLITP_TAKE_DROP >> rfs[]
      >> imp_res_tac (GSYM TAKE_SEG) >> fs[]
      >> fs[ADD1]
      >> Q.ISPECL_THEN [`s'`,`x`] assume_tac TAKE_EL_SNOC
      >> rfs[])
  >- (imp_res_tac null_index_no_null2
      >> fs[o_DEF] >> imp_res_tac SPLITP_EVERY
      >> fs[mlstringTheory.implode_def,mlstringTheory.strcat_thm])
QED

val _ = translate cut_at_null_def;

val null_index_side_lem = Q.prove(
  `!s n. null_index_side s n <=> T`,
  ho_match_mp_tac null_index_ind
  >> rw[]
  >> PURE_ONCE_REWRITE_TAC[fetch "-" "null_index_side_def"]
  >> fs[ADD1])
 |> update_precondition;

val cut_at_null_side_lem = Q.prove(`!s. cut_at_null_side s <=> T`,
  rw[fetch "-" "cut_at_null_side_def",null_index_side_lem]
  >> imp_res_tac null_index_le_len >> fs[])
 |> update_precondition;

val null_index_w_def = tDefine "null_index_w"
  `null_index_w s n =
    if n >= LENGTH s then NONE
    else if EL n s = 0w then SOME n
    else null_index_w s (SUC n)`
  (wf_rel_tac `inv_image (measure (λ(a,b). SUC a - b)) (LENGTH ## I)`);

val null_index_w_ind = fetch "-" "null_index_w_ind";

Theorem null_index_w_le_len:
  !s n m. null_index_w s n = SOME m ==> m < LENGTH s
Proof
  ho_match_mp_tac null_index_w_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index_w` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_w_def])
  >> rw[]
QED

Theorem null_index_w_in_bound:
  !s n m. null_index_w s n = SOME m ==> n <= m
Proof
  ho_match_mp_tac null_index_w_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index_w` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_w_def])
  >> rw[] >> fs[]
QED

Theorem null_index_w_null:
  !s n m. null_index_w s n = SOME m ==> EL m s = 0w
Proof
  ho_match_mp_tac null_index_w_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index_w` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_w_def])
  >> rw[] >> fs[]
QED

Theorem null_index_w_no_null:
  !s n m. null_index_w s n = SOME m ==> EVERY ($~ o $= 0w) (TAKE (m-n) (DROP n s))
Proof
  ho_match_mp_tac null_index_w_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index_w` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_w_def])
  >> rw[]
  >> first_x_assum drule >> rpt(disch_then drule)
  >> strip_tac
  >> imp_res_tac null_index_w_le_len
  >> imp_res_tac null_index_w_in_bound
  >> qmatch_goalsub_abbrev_tac `EVERY _ (TAKE a1 a2)`
  >> Q.ISPECL_THEN [`a1`,`1`,`a2`] mp_tac take_drop_partition
  >> unabbrev_all_tac
  >> impl_tac >- intLib.COOPER_TAC
  >> disch_then(fn x => rw[GSYM x])
  >> fs[ADD1,DROP_DROP]
  >> `n < LENGTH s`
     by(fs[])
  >> drule TAKE1_DROP >> fs[]
QED

Theorem null_index_w_no_null2:
  !s n. null_index_w s n = NONE ==> EVERY ($~ o $= 0w) (DROP n s)
Proof
  ho_match_mp_tac null_index_w_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index_w` (mp_tac o PURE_ONCE_REWRITE_RULE [null_index_w_def])
  >> rw[] >> Cases_on `n ≥ LENGTH s`
  >> fs[GREATER_EQ]
  >> imp_res_tac DROP_LENGTH_TOO_LONG >> fs[]
  >> `n < LENGTH s` by fs[]
  >> imp_res_tac DROP_CONS_EL >> fs[]
QED

val cut_at_null_w_def = Define `cut_at_null_w s =
  case null_index_w s 0 of
      NONE => s ++ [0w]
    | SOME n => SEG (SUC n) 0 s`

Theorem cut_at_null_w_SPLITP:
  !s. cut_at_null_w s = FST(SPLITP ($= 0w) s) ++ [0w]
Proof
  rw[cut_at_null_w_def] >> reverse(PURE_TOP_CASE_TAC >> rw[])
  >- (imp_res_tac null_index_w_le_len >> rw[mlstringTheory.substring_def]
      >> fs[mlstringTheory.strlen_def,mlstringTheory.implode_def]
      >> imp_res_tac null_index_w_no_null >> fs[]
      >> imp_res_tac null_index_w_null >> fs[]
      >> imp_res_tac SPLITP_TAKE_DROP >> rfs[]
      >> fs[GSYM TAKE_SEG,ADD1]
      >> Q.ISPECL_THEN [`s`,`x`] assume_tac TAKE_EL_SNOC
      >> rfs[])
  >- (imp_res_tac null_index_w_no_null2
      >> fs[o_DEF] >> imp_res_tac SPLITP_EVERY >> fs[])
QED

Theorem null_index_w_thm:
  ∀s n. null_index_w (s:word8 list) n = null_index (implode (MAP (CHR ∘ w2n) s)) n
Proof
  ho_match_mp_tac null_index_w_ind
  >> rpt strip_tac
  >> MAP_EVERY PURE_ONCE_REWRITE_TAC [[null_index_def],[null_index_w_def]] >> rw[]
  >> fs[mlstringTheory.implode_def]
  >> `n < LENGTH s` by fs[]
  >> rfs[EL_MAP]
  >> qspecl_then [`[EL n s]`,`[0w]`] assume_tac MAP_CHR_w2n_11
  >> fs[]
QED

Theorem cut_at_null_w_thm:
  ∀s. cut_at_null_w (s:word8 list) = MAP (n2w o ORD) (explode (cut_at_null (implode (MAP (CHR ∘ w2n) s))))
Proof
  rw[cut_at_null_w_def,cut_at_null_def,null_index_w_thm]
  >> PURE_TOP_CASE_TAC >> rw[MAP_MAP_o]
  >> fs[n2w_ORD_CHR_w2n]
  >> imp_res_tac null_index_le_len
  >> fs[mlstringTheory.implode_def,mlstringTheory.substring_def]
  >> MAP_EVERY PURE_ONCE_REWRITE_TAC [[null_index_def],[null_index_w_def]] >> rw[]
  >> fs[GSYM TAKE_SEG,MAP_TAKE,MAP_MAP_o,n2w_ORD_CHR_w2n]
QED

Theorem cut_at_null_thm:
  cut_at_null(strlit (MAP (CHR o w2n) l)) = strlit(MAP (CHR o w2n) (cut_at_null_w(l:word8 list)))
Proof
  rw[cut_at_null_w_thm,MAP_MAP_o,implode_def,CHR_w2n_n2w_ORD,REWRITE_RULE[implode_def] implode_explode]
QED

val null_terminated_def = Define `
  null_terminated s = ?m. null_index s 0 = SOME m`

val null_terminated_w_def = Define `
  null_terminated_w s = ?m. null_index_w s 0 = SOME m`

Theorem null_terminated_w_thm:
  !s. null_terminated_w (s:word8 list) = null_terminated(implode(MAP (CHR o w2n) s))
Proof
  rw[null_terminated_def,null_terminated_w_def,null_index_w_thm]
QED

Theorem null_index_strcat1:
  !s1 n s2 m. null_index s1 n = SOME m ==> null_index (strcat s1 s2) n = SOME m
Proof
  ho_match_mp_tac null_index_ind
  >> rpt strip_tac
  >> qhdtm_x_assum `null_index` mp_tac
  >> PURE_ONCE_REWRITE_TAC [null_index_def]
  >> rw[] >> fs[]
  >> MAP_EVERY Cases_on [`s1`,`s2`]
  >> fs[mlstringTheory.strsub_def,mlstringTheory.strcat_def,mlstringTheory.concat_def,EL_APPEND_EQN]
QED

Theorem null_terminated_cut_APPEND:
  !s1 s2. null_terminated s1 ==> cut_at_null(strcat s1 s2) = cut_at_null s1
Proof
  rw[null_terminated_def,cut_at_null_def] >> imp_res_tac null_index_strcat1
  >> fs[] >> imp_res_tac null_index_le_len
  >> MAP_EVERY Cases_on [`s1`,`s2`]
  >> fs[mlstringTheory.strsub_def,mlstringTheory.strcat_def,mlstringTheory.concat_def,
        mlstringTheory.substring_def]
  >> match_mp_tac SEG_APPEND1 >> fs[]
QED

Theorem null_terminated_cut_w_APPEND:
  !s1 s2. null_terminated_w(s1:word8 list) ==> cut_at_null_w(s1 ++ s2) = cut_at_null_w s1
Proof
  rw[null_terminated_w_thm,cut_at_null_w_thm]
  >> drule null_terminated_cut_APPEND
  >> disch_then(qspec_then `implode(MAP (CHR ∘ w2n) s2)` assume_tac)
  >> simp[mlstringTheory.implode_STRCAT]
QED

(*---------------------------------------------------------------------------*)
(* Loop processing input stream. Currently limited to strings <= 256 chars.  *)
(* This is not a HOL function so is not being pushed through translate.      *)
(*---------------------------------------------------------------------------*)

val dummyarr_e = ``(App Aw8alloc [Lit (IntLit 0); Lit (Word8 0w)])``
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = ``^st with refs := ^st.refs ++ [W8array (REPLICATE 0 0w)]``
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, dummyarr_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "dummyarr_loc" v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end

val dummyarr_loc_def = fetch "-" "dummyarr_loc_def";

val _ = ml_prog_update (add_Dlet eval_thm "dummyarr" []);

val forward_matching_lines = process_topdecs`
fun forward_loop inputarr =
    (#(accept_call) "" inputarr;
     let val ln = Word8Array.substring inputarr 0 256;
         val ln' = cut_at_null ln;
     in
       if match_string ln' then
         #(emit_string) ln' dummyarr
       else ()
     end;
     forward_loop inputarr);

fun forward_matching_lines u =
    let val inputarr = Word8Array.array 256 (Word8.fromInt 0);
    in
      forward_loop inputarr
    end`

val _ = append_prog forward_matching_lines;

val st = get_ml_prog_state();

val maincall =
  ``Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short "forward_matching_lines"); Con NONE []])``

val filter_ffi = Datatype `
  filter_ffi =
  <| input : word8 list llist
   |>`

val filter_oracle = Define `
  (filter_oracle:filter_ffi oracle) port st conf bytes =
  if port = "accept_call" then
    (if st.input = LNIL then Oracle_final FFI_diverged
     else if LENGTH bytes = 256 then
        Oracle_return (st with input := THE(LTL(st.input)))
                        (TAKE 256 (THE(LHD st.input)) ++ DROP (LENGTH(THE(LHD st.input))) bytes)
     else Oracle_final FFI_failed)
  else if port = "emit_string" then
    Oracle_return st bytes
  else Oracle_final FFI_failed
`

val encode_oracle_state_def = Define `
  encode_oracle_state st =
      (Fun
         (λffi.
            case ffi of
              iNum n =>
              (case LNTH n st.input of
                 SOME l => Str(MAP (CHR o w2n) l)
               | NONE => Num 0)
            | _ => ARB
         )
      )`

val filter_ffi_component_equality = fetch "-" "filter_ffi_component_equality"

val decode_oracle_state_def = Define `
  decode_oracle_state ffi =
     case destFun ffi of
       SOME instream =>
       <|input:= LUNFOLD (λn. OPTION_MAP ($, (SUC n) o MAP (n2w o ORD))
                              (destStr(instream (iNum n)))) 0|>`

val filter_cf_oracle = Define `
  filter_cf_oracle port conf bytes ffi =
  case filter_oracle port (decode_oracle_state ffi) conf bytes of
      Oracle_final FFI_failed => NONE
    | Oracle_final FFI_diverged => SOME FFIdiverge
    | Oracle_return st' bytes => SOME(FFIreturn bytes (encode_oracle_state st'))`

val seL4_IO_def = Define `
  seL4_IO input events =
  one(
    FFI_part
      (encode_oracle_state (<|input:=input|>))
      filter_cf_oracle
      ["accept_call";"emit_string"]
      events)`

Theorem decode_encode_oracle_state_11:
  !ffi_st. decode_oracle_state(encode_oracle_state ffi_st) = ffi_st
Proof
  rw[encode_oracle_state_def,decode_oracle_state_def,
                   filter_ffi_component_equality] >>
  rename1 `_ = ll` >>
  qho_match_abbrev_tac `a1 ll = _` >>
  PURE_ONCE_REWRITE_TAC[LLIST_BISIMULATION] >>
  qexists_tac `\x y. ?ll. x = a1 ll /\ y = ll` >>
  qunabbrev_tac `a1` >>
  rw[] >>
  simp[SimpL ``$=``, Once LUNFOLD] >>
  simp[LNTH] >>
  rename1 `LHD ll` >> Cases_on `ll` >> fs[MAP_MAP_o,n2w_ORD_CHR_w2n] >>
  simp[GSYM OPTION_MAP_COMPOSE] >>
  PURE_ONCE_REWRITE_TAC[LUNFOLD_BISIMULATION] >>
  qexists_tac `\x y. x = SUC y` >>
  rw[] >> metis_tac[option_CASES]
QED

Theorem every_LDROP:
  !i l ll1.
  every f ll1 /\
  LDROP i ll1 = SOME ll2
  ==> every f ll2
Proof
  Induct >> Cases_on `ll1` >> rw[] >> rw[] >> metis_tac[]
QED

val LLENGTH_NONE_LTAKE = Q.prove(
  `!n ll. LLENGTH ll = NONE ==> ?l. LTAKE n ll = SOME l`,
  Induct >> Cases_on `ll` >> rw[]);

val is_emit_def = Define
  `is_emit (IO_event s _ _) = (s = "emit_string")`

val output_event_of_def = Define
  `output_event_of s = IO_event "emit_string" s []`

val nth_arr_def = Define `nth_arr n ll =
 FST(FUNPOW (λ(l,ll).
 if ll = [||] then (l,[||])
 else (
   TAKE 256 (THE(LHD ll)) ++ DROP (LENGTH(THE(LHD ll))) l
      ,THE(LTL ll))) n
 (REPLICATE 256 (0w:word8),ll))`

Theorem nth_arr_infinite:
 !n ll.
 LLENGTH ll = NONE ==>
 nth_arr n ll =
 FST(FUNPOW (λ(l,ll).
 (TAKE 256 (THE(LHD ll)) ++ DROP (LENGTH(THE(LHD ll))) l,THE(LTL ll))) n
 (REPLICATE 256 (0w:word8),ll))
Proof
  simp[nth_arr_def] >>
  qabbrev_tac `a1 = REPLICATE 256 (0w:word8)` >>
  `LENGTH a1 = 256` by(unabbrev_all_tac >> simp[]) >>
  MAP_EVERY pop_assum [mp_tac,kall_tac] >>
  simp[PULL_FORALL] >> qid_spec_tac `a1` >>
  Induct_on `n` >> rw[FUNPOW] >>
  Cases_on `ll` >> fs[LENGTH_TAKE_EQ]
QED

Theorem nth_arr_SUC: !n ll.
  LLENGTH ll = NONE ==>
  nth_arr (SUC n) ll
  =
  TAKE 256 (THE(LNTH n ll)) ++ DROP (LENGTH(THE(LNTH n ll))) (nth_arr n ll)
Proof
  `∀n ll (l:word8 list).
       LLENGTH ll = NONE /\ LENGTH l = 256 ⇒
       (FUNPOW
            (λ(l,ll).
                 (TAKE 256 (THE (LHD ll)) ++ DROP (LENGTH (THE (LHD ll))) l,
                  THE (LTL ll))) (SUC n) (l,ll)) =
       (TAKE 256 (THE (LNTH n ll)) ++
       DROP (LENGTH (THE (LNTH n ll)))
         (FST
            (FUNPOW
               (λ(l,ll).
                    (TAKE 256 (THE (LHD ll)) ++
                     DROP (LENGTH (THE (LHD ll))) l,THE (LTL ll))) n
               (l,ll))),THE(LDROP (SUC n) ll))`
    suffices_by rw[nth_arr_infinite] >>
  Induct_on `n` >> rpt strip_tac >> fs[FUNPOW_SUC,LDROP1_THM,CONJUNCT1 LNTH] >>
  `~LFINITE ll` by simp[LFINITE_LLENGTH] >>
  imp_res_tac infinite_lnth_some >>
  first_x_assum(qspec_then `SUC n` strip_assume_tac) >>
  drule LNTH_LDROP >> simp[] >> disch_then kall_tac >>
  Cases_on `ll` >> fs[LDROP_SUC] >>
  rename1 `LDROP n ll` >>
  Cases_on `LDROP n ll` >> fs[] >>
  metis_tac[LDROP_NONE_LFINITE]
QED

Theorem nth_arr_LENGTH:
  every ($>= 256 ∘ LENGTH) ll
   ==> LENGTH(nth_arr n ll) = 256
Proof
  simp[nth_arr_def] >>
  qabbrev_tac `a1 = REPLICATE 256 (0w:word8)` >>
  `LENGTH a1 = 256` by(unabbrev_all_tac >> simp[]) >>
  MAP_EVERY pop_assum [mp_tac,kall_tac] >>
  qid_spec_tac `a1` >> qid_spec_tac `ll` >>
  Induct_on `n` >> rw[FUNPOW] >>
  Cases_on `ll` >> fs[LENGTH_TAKE_EQ]
QED

val next_filter_events = Define
  `next_filter_events filter_fun last_input input =
   let new_input = TAKE 256 input ++ DROP (LENGTH input) last_input
   in
    [IO_event "accept_call" [] (ZIP (last_input,new_input))] ++
    if filter_fun(cut_at_null_w input) then
      [IO_event "emit_string" (cut_at_null_w new_input) []]
    else
      []`

val nth_arr_init_def = Define `nth_arr_init n ll buff =
      FST(FUNPOW
             (λ(l,ll).
               if ll = [||] then (l,[||])
               else
                 (TAKE 256 (THE (LHD ll)) ++
                  DROP (LENGTH (THE (LHD ll))) l,THE (LTL ll))) n
             (buff:word8 list,ll))`

Theorem nth_arr_init_SUC: !h n ll init.
  nth_arr_init (SUC n) (h:::ll) init = nth_arr_init n ll (TAKE 256 h ++ DROP(LENGTH h) init)
Proof
  rw[nth_arr_init_def,FUNPOW]
QED

Theorem nth_arr_init_add: !n m ll init.
  LLENGTH ll = NONE ==>
  nth_arr_init (n + m) ll init = nth_arr_init n (THE(LDROP m ll)) (nth_arr_init m ll init)
Proof
  Induct_on `m` >- rw[nth_arr_init_def] >>
  rw[] >>
  PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC] >>
  Cases_on `ll` >> fs[] >>
  fs[nth_arr_init_SUC]
QED

Theorem LLENGTH_NONE_LDROP:
  !n ll ll'. LLENGTH ll = NONE /\ LDROP n ll = SOME ll' ==> LLENGTH ll' = NONE
Proof
  Induct >> Cases_on `ll` >> rw[] >> rw[LLENGTH_THM] >> metis_tac[]
QED

Theorem nth_arr_init_LENGTH:
  !n ll init. every ($>= 256 ∘ LENGTH) ll /\
  LENGTH init = 256 /\ LLENGTH ll = NONE
   ==> LENGTH(nth_arr_init n ll init) = 256
Proof
  Induct_on `n` >> Cases_on `ll` >> rw[nth_arr_init_SUC,TAKE_LENGTH_TOO_LONG] >>
  TRY(simp[nth_arr_init_def] >> NO_TAC)
QED

val filter_bisim_rel_infinite_def = Define `
  filter_bisim_rel_infinite =
  λl1 l2.
   (?inl buff.
     l1 = LFILTER is_emit (LFLATTEN
               (LGENLIST
                  (λx.
                       fromList
                         (next_filter_events (language ∘ MAP (CHR ∘ w2n))
                            (nth_arr_init x inl buff) (THE (LNTH x inl)))) NONE)) /\
     l2 = LMAP (output_event_of o cut_at_null_w) (LFILTER (language o MAP (CHR o w2n) o cut_at_null_w) inl) /\
     LLENGTH inl = NONE /\
     LENGTH buff = 256 /\
     every ($>= 256 ∘ LENGTH) inl /\
     every null_terminated_w inl)`

Theorem exists_LFLATTEN:
  !P ll. exists P (LFLATTEN ll) /\
    every LFINITE ll /\
    every ($<> [||]) ll==>
    exists (exists P) ll
Proof
  rw[exists_LNTH] >>
  rpt(pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`e`,`ll`,`n`] >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  Cases >> rw[LNTH] >-
    (Cases_on `ll` >> fs[] >>
     rename1 `[||] <> hd` >> Cases_on `hd` >> fs[] >>
     rveq >> qexists_tac `0` >> simp[] >> qexists_tac `0` >> simp[]) >-
    (qpat_x_assum `_ = OPTION_JOIN _` (assume_tac o GSYM) >>
     fs[OPTION_JOIN_EQ_SOME,OPTION_MAP_EQ_SOME] >>
     Cases_on `ll` >> fs[] >>
     rename1 `h:::ll` >>
     Cases_on `h` >> fs[] >>
     rename1 `(h:::l):::ll` >>
     imp_res_tac LFINITE_HAS_LENGTH >>
     rveq >> fs[LNTH_LAPPEND] >>
     PURE_FULL_CASE_TAC >-
       (fs[] >> qexists_tac `0` >> simp[] >>
        Q.REFINE_EXISTS_TAC `SUC _` >> simp[] >> metis_tac[]) >-
       (fs[] >> Q.REFINE_EXISTS_TAC `SUC _` >> simp[] >>
        rename1 `n0 < n` >>
        first_x_assum (match_mp_tac o MP_CANON) >>
        qexists_tac `n0 - n` >> simp[] >> metis_tac[]))
QED

val cut_at_null_simplify = Q.prove(`(?n' e'.
   SOME e' =
     LNTH n'
        (fromList
         (next_filter_events f
         iarr input)) ∧ is_emit e')
  = f(cut_at_null_w input)`,
  rw[EQ_IMP_THM,next_filter_events] >-
    (qexists_tac `SUC 0` >> fs[is_emit_def]) >-
    (rename1 `LNTH n` >> Cases_on `n` >> fs[] >> rveq >> fs[is_emit_def] >>
     CCONTR_TAC >> fs[] >> rveq >> fs[is_emit_def]));

val LFLATTEN_fromList_GENLIST =
    LFLATTEN_fromList |> Q.SPEC `GENLIST f n` |> SIMP_RULE std_ss [MAP_GENLIST,o_DEF]

val LFILTER_fromList = Q.prove(`
  !l. LFILTER f (fromList l) = fromList(FILTER f l)`,
  Induct >> rw[]);

Theorem forward_matching_lines_div_spec:
  !input output rv.
    limited_parts ["accept_call";"emit_string"] p /\
    LLENGTH input = NONE /\
    every (null_terminated_w) input /\
    every ($>= 256 o LENGTH) input
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "forward_matching_lines" st) [rv]
      (seL4_IO input [] * W8ARRAY dummyarr_loc [])
      (POSTd io. LFILTER is_emit io = LMAP (output_event_of o cut_at_null_w) (LFILTER (language o MAP (CHR o w2n) o cut_at_null_w) input))
Proof
  xcf "forward_matching_lines" st >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  unfold_cf_app >>
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "forward_loop" st >>
  rename1 `_ 0 inputarr` >>
  MAP_EVERY qexists_tac
    [`λn. W8ARRAY dummyarr_loc [] *
      W8ARRAY inputarr
              (nth_arr n input)`,
     `\n. if n = 0 then []
          else next_filter_events (language o MAP (CHR o w2n)) (nth_arr (n-1) input) (THE(LNTH (n-1) input))
     `,
     `K($= inputarr)`,
     `λn. encode_oracle_state
      <|input:=THE(LDROP n input)|>`,
     `filter_cf_oracle`
    ] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (xsimpl >>
     simp[seL4_IO_def,next_filter_events,nth_arr_def] >>
     simp[Once LUNFOLD] >>
     simp[toList,LAPPEND_NIL_2ND] >>
     xsimpl) >>
  simp[] >>
  conj_tac >-
    (strip_tac >>
     qmatch_goalsub_abbrev_tac `W8ARRAY inputarr inputbuff` >>
     `LENGTH inputbuff = 256`
       by(unabbrev_all_tac >> metis_tac[nth_arr_LENGTH]) >>
     xlet `(POSTv v. &UNIT_TYPE () v * W8ARRAY dummyarr_loc [] *
            W8ARRAY inputarr ((TAKE 256 (THE (LHD (THE (LDROP i input)))) ++
                              DROP (LENGTH (THE (LHD (THE (LDROP i input))))) inputbuff))  *
      one
        (FFI_part
           (encode_oracle_state
              <|input := THE (LDROP (SUC i) input)|>) filter_cf_oracle
           ["accept_call"; "emit_string"]
           [IO_event "accept_call" [] (ZIP(inputbuff,
                                          ((TAKE 256 (THE (LHD (THE (LDROP i input)))) ++
                              DROP (LENGTH (THE (LHD (THE (LDROP i input))))) inputbuff))))]
           ))` >-
       (xffi >> xsimpl >>
        qmatch_goalsub_abbrev_tac `one(FFI_part s u ns events)` >>
        MAP_EVERY qexists_tac [`W8ARRAY dummyarr_loc []`,`s`,`u`,`ns`,`events`] >>
        unabbrev_all_tac >> xsimpl >>
        simp[filter_cf_oracle,decode_encode_oracle_state_11,filter_oracle] >>
        `?i1 input'. LDROP i input = SOME(i1:::input')`
          by(qpat_x_assum `LLENGTH input = NONE` mp_tac >>
             qid_spec_tac `input` >> rpt(pop_assum kall_tac) >>
             Induct_on `i` >> fs[] >>
             Cases >> rw[]) >>
        simp[LDROP_SUC] >>
        xsimpl) >>
     xlet `(POSTv v. &UNIT_TYPE () v * W8ARRAY dummyarr_loc [] *
            W8ARRAY inputarr ((TAKE 256 (THE (LHD (THE (LDROP i input)))) ++
                              DROP (LENGTH (THE (LHD (THE (LDROP i input))))) inputbuff))  *
      one
        (FFI_part
           (encode_oracle_state
              <|input := THE (LDROP (SUC i) input)|>) filter_cf_oracle
           ["accept_call"; "emit_string"]
           (next_filter_events (language o MAP (CHR o w2n)) inputbuff (THE(LNTH i input)))))` >-
       (xlet_auto >-
          (xsimpl >>
           `?i1 input'. LDROP i input = SOME(i1:::input')`
             by(qpat_x_assum `LLENGTH input = NONE` mp_tac >>
                qid_spec_tac `input` >> rpt(pop_assum kall_tac) >>
                Induct_on `i` >> fs[] >>
                Cases >> rw[]) >>
           fs[] >>
           imp_res_tac every_LDROP >>
           fs[every_thm,LENGTH_TAKE_EQ]) >>
        xlet_auto >- xsimpl >>
        xlet_auto >- xsimpl >>
        reverse xif >-
          (xcon >> xsimpl >>
           `~LFINITE input` by rw[LFINITE_LLENGTH] >>
           `?i1. LNTH i input = SOME(i1)`
             by(CCONTR_TAC >> fs[LFINITE_LNTH_NONE] >> metis_tac[NOT_SOME_NONE,option_nchotomy]) >>
           fs[] >>
           simp[Abbr `inputbuff`,next_filter_events,nth_arr_SUC] >>
           drule_then(qspec_then `i` strip_assume_tac) (GEN_ALL nth_arr_LENGTH) >>
           drule_then strip_assume_tac LNTH_LDROP >> fs[] >>
           fs[match_string_eq] >> fs[cut_at_null_w_thm,MAP_MAP_o,CHR_w2n_n2w_ORD,implode_def] >>
           imp_res_tac every_LNTH >> fs[every_thm] >>
           fs[null_terminated_w_thm,implode_def] >>
           fs[null_terminated_cut_APPEND,TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
           fs[GSYM strlit_STRCAT,null_terminated_cut_APPEND] >>
           fs[DROP_LENGTH_TOO_LONG] >>
           xsimpl) >-
          (xffi >>
           fs[cut_at_null_thm,STRING_TYPE_def] >>
           qmatch_goalsub_abbrev_tac `MAP _ a1 = _` >>
           qexists_tac `a1` >> qunabbrev_tac `a1` >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `W8ARRAY inputarr ibuff` >>
           MAP_EVERY qexists_tac [`[]`,`W8ARRAY inputarr ibuff`] >>
           xsimpl >>
           qmatch_goalsub_abbrev_tac `FFI_part s u ns events` >>
           MAP_EVERY qexists_tac [`s`,`u`,`ns`,`events`] >>
           unabbrev_all_tac >> simp[filter_cf_oracle,filter_oracle] >>
           xsimpl >>
           `~LFINITE input` by rw[LFINITE_LLENGTH] >>
           `?i1. LNTH i input = SOME(i1)`
             by(CCONTR_TAC >> fs[LFINITE_LNTH_NONE] >> metis_tac[NOT_SOME_NONE,option_nchotomy]) >>
           fs[] >>
           simp[next_filter_events,nth_arr_SUC] >>
           drule_then(qspec_then `i` strip_assume_tac) (GEN_ALL nth_arr_LENGTH) >>
           drule_then strip_assume_tac LNTH_LDROP >> fs[] >>
           fs[match_string_eq] >> fs[cut_at_null_w_thm,MAP_MAP_o,CHR_w2n_n2w_ORD,implode_def] >>
           imp_res_tac every_LNTH >> fs[every_thm] >>
           fs[null_terminated_w_thm,implode_def] >>
           fs[null_terminated_cut_APPEND,TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
           fs[DROP_LENGTH_TOO_LONG] >>
           fs[GSYM strlit_STRCAT,null_terminated_cut_APPEND] >>
           simp[decode_encode_oracle_state_11] >>
           xsimpl)
       ) >>
       xvar >> xsimpl >>
       simp[nth_arr_SUC] >>
       `~LFINITE input` by rw[LFINITE_LLENGTH] >>
       `?i1. LNTH i input = SOME(i1)`
         by(CCONTR_TAC >> fs[LFINITE_LNTH_NONE] >> metis_tac[NOT_SOME_NONE,option_nchotomy]) >>
         fs[] >>
       drule_then strip_assume_tac LNTH_LDROP >> fs[]
    ) >>
  simp [Once(REWRITE_RULE [o_DEF] LGENLIST_NONE_UNFOLD)] >>
  match_mp_tac LLIST_BISIM_UPTO >>
  qexists_tac `filter_bisim_rel_infinite` >>
  conj_tac >-
    (simp[filter_bisim_rel_infinite_def,nth_arr_def,nth_arr_init_def] >>
     metis_tac[LENGTH_REPLICATE]) >>
  rpt(pop_assum kall_tac) >>
  rw[filter_bisim_rel_infinite_def] >>
  qmatch_goalsub_abbrev_tac `a1 /\ _ \/ _` >>
  Cases_on `a1` (* Are there incoming messages that will pass the filter? *) >>
  fs[markerTheory.Abbrev_def]
  >-
    (`LFILTER (language ∘ MAP (CHR ∘ w2n) ∘ cut_at_null_w) inl = [||]` suffices_by fs[] >>
     fs[LFILTER_EQ_NIL] >>
     rpt(pop_assum mp_tac) >>
     MAP_EVERY qid_spec_tac [`buff`,`inl`] >>
     SIMP_TAC pure_ss [AND_IMP_INTRO,LEFT_FORALL_IMP_THM] >>
     ho_match_mp_tac every_coind >>
     rpt gen_tac >> rpt(disch_then strip_assume_tac) >>
     fs[] >>
     pop_assum(assume_tac o PURE_ONCE_REWRITE_RULE[LGENLIST_NONE_UNFOLD]) >>
     pop_assum(mp_tac o PURE_REWRITE_RULE[Once next_filter_events]) >>
     rw[is_emit_def] >> fs[o_DEF] >>
     fs(map (REWRITE_RULE[ADD1]) [nth_arr_init_SUC,LNTH]) >>
     PURE_ONCE_REWRITE_TAC[CONJ_SYM] >> asm_exists_tac >>
     fs[LENGTH_TAKE_EQ]) >>
  fs[LFILTER_EQ_NIL,every_def] >>
  conj_tac >-
    (drule exists_LFLATTEN >>
     impl_tac >- rw[every_LNTH,LNTH_LGENLIST,next_filter_events,LFINITE_fromList] >>
     simp[SimpL ``$==>``,exists_LNTH,LNTH_LGENLIST] >>
     Ho_Rewrite.PURE_ONCE_REWRITE_TAC [cut_at_null_simplify] >>
     disch_then(strip_assume_tac o Ho_Rewrite.REWRITE_RULE[whileTheory.LEAST_EXISTS]) >>
     rename1 `LNTH n0` >>
     qmatch_goalsub_abbrev_tac `LGENLIST f` >>
     Q.ISPECL_THEN [`n0`,`f`] assume_tac (GEN_ALL LGENLIST_CHUNK_GENLIST) >>
     simp[] >>
     pop_assum kall_tac >>
     simp[LFLATTEN_LAPPEND_fromList] >>
     unabbrev_all_tac >>
     Ho_Rewrite.REWRITE_TAC[LFLATTEN_fromList_GENLIST] >>
     simp[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList] >>
     qmatch_goalsub_abbrev_tac `FILTER is_emit a1` >>
     `FILTER is_emit a1 = []`
       by(unabbrev_all_tac >>
          rw[FILTER_EQ_NIL,EVERY_FLAT,EVERY_GENLIST,next_filter_events,
             is_emit_def]) >>
     simp[] >> ntac 2 (pop_assum kall_tac) >>
     simp[Once LGENLIST_NONE_UNFOLD] >>
     simp[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList,
          next_filter_events,is_emit_def] >>
     `~LFINITE inl` by fs[LFINITE_LLENGTH] >>
     drule(CONJUNCT1 LTAKE_DROP) >>
     disch_then(qspec_then `n0` (fn thm => CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM thm])))) >>
     simp[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList] >>
     qmatch_goalsub_abbrev_tac `FILTER af al` >>
     `FILTER af al = []`
       by(unabbrev_all_tac >>
          drule_then(qspec_then `n0` strip_assume_tac) LLENGTH_NONE_LTAKE >>
          rw[FILTER_EQ_NIL,EVERY_FLAT,EVERY_GENLIST,next_filter_events,
             is_emit_def] >>
          rw[EVERY_EL] >>
          first_x_assum(qspec_then `n` mp_tac) >>
          impl_keep_tac >- metis_tac[LTAKE_LENGTH] >>
          drule_then drule LTAKE_LNTH_EL >> simp[]) >>
     unabbrev_all_tac >>
     `?i1 inl'. LDROP n0 inl = SOME(i1:::inl')`
          by(qpat_x_assum `LLENGTH inl = NONE` mp_tac >>
             qid_spec_tac `inl` >> rpt(pop_assum kall_tac) >>
             Induct_on `n0` >> fs[] >>
             Cases >> rw[]) >>
     fs[LNTH_HD_LDROP,output_event_of_def] >>
     fs[GSYM every_def] >>
     imp_res_tac every_LDROP >>
     fs[TAKE_LENGTH_TOO_LONG] >>
     fs[null_terminated_cut_w_APPEND]) >-
    (qmatch_goalsub_abbrev_tac `llist_upto REL` >>
     drule exists_LFLATTEN >>
     impl_tac >- rw[every_LNTH,LNTH_LGENLIST,next_filter_events,LFINITE_fromList] >>
     simp[SimpL ``$==>``,exists_LNTH,LNTH_LGENLIST] >>
     Ho_Rewrite.PURE_ONCE_REWRITE_TAC [cut_at_null_simplify] >>
     disch_then(strip_assume_tac o Ho_Rewrite.REWRITE_RULE[whileTheory.LEAST_EXISTS]) >>
     rename1 `LNTH n0` >>
     qmatch_goalsub_abbrev_tac `LGENLIST f` >>
     Q.ISPECL_THEN [`n0`,`f`] assume_tac (GEN_ALL LGENLIST_CHUNK_GENLIST) >>
     simp[] >>
     pop_assum kall_tac >>
     simp[LFLATTEN_LAPPEND_fromList] >>
     qunabbrev_tac `f` >>
     Ho_Rewrite.REWRITE_TAC[LFLATTEN_fromList_GENLIST] >>
     simp[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList] >>
     qmatch_goalsub_abbrev_tac `FILTER is_emit a1` >>
     `FILTER is_emit a1 = []`
       by(unabbrev_all_tac >>
          rw[FILTER_EQ_NIL,EVERY_FLAT,EVERY_GENLIST,next_filter_events,
             is_emit_def]) >>
     simp[] >> ntac 2 (pop_assum kall_tac) >>
     CONV_TAC(RATOR_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD]))) >>
     simp[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList,
          Once next_filter_events,is_emit_def] >>
     `~LFINITE inl` by fs[LFINITE_LLENGTH] >>
     drule(CONJUNCT1 LTAKE_DROP) >>
     disch_then(qspec_then `n0` (fn thm => CONV_TAC(RAND_CONV(PURE_ONCE_REWRITE_CONV [GSYM thm])))) >>
     simp[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList] >>
     fs[is_emit_def] >>
     qmatch_goalsub_abbrev_tac `llist$fromList(FILTER af al)` >>
     `FILTER af al = []`
       by(unabbrev_all_tac >>
          drule_then(qspec_then `n0` strip_assume_tac) LLENGTH_NONE_LTAKE >>
          rw[FILTER_EQ_NIL,EVERY_FLAT,EVERY_GENLIST,next_filter_events,
             is_emit_def] >>
          rw[EVERY_EL] >>
          first_x_assum(qspec_then `n` mp_tac) >>
          impl_keep_tac >- metis_tac[LTAKE_LENGTH] >>
          drule_then drule LTAKE_LNTH_EL >> simp[]) >>
     unabbrev_all_tac >>
     `?i1 inl'. LDROP n0 inl = SOME(i1:::inl')`
          by(qpat_x_assum `LLENGTH inl = NONE` mp_tac >>
             qid_spec_tac `inl` >> rpt(pop_assum kall_tac) >>
             Induct_on `n0` >> fs[] >>
             Cases >> rw[]) >>
     fs[LNTH_HD_LDROP,output_event_of_def] >>
     fs[GSYM every_def] >>
     imp_res_tac every_LDROP >>
     fs[TAKE_LENGTH_TOO_LONG] >>
     fs[null_terminated_cut_w_APPEND] >>
     match_mp_tac llist_upto_rel >>
     rw[o_DEF] >>
     qexists_tac `inl'` >> fs[o_DEF] >>
     qexists_tac `nth_arr_init (n0 + 1) inl buff` >>
     fs[] >>
     simp[REWRITE_RULE [o_DEF] nth_arr_init_LENGTH] >>
     PURE_ONCE_REWRITE_TAC[ADD_SYM] >>
     PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC] >>
     FULL_SIMP_TAC std_ss [nth_arr_init_add] >>
     PURE_ONCE_REWRITE_TAC[ADD_SYM] >>
     PURE_ONCE_REWRITE_TAC[GSYM ADD1] >>
     FULL_SIMP_TAC std_ss [Once LDROP_ADD] >>
     fs[REWRITE_RULE [ADD1] LDROP_SUC,LDROP_SUC] >>
     drule_all LLENGTH_NONE_LDROP >>
     rw[LLENGTH_THM])
QED

Theorem LTAKE_LLENGTH_SOME2:
  LLENGTH ll = SOME n
  ==> ?l. ll = fromList l /\ LENGTH l = n
Proof
  strip_tac >> imp_res_tac LTAKE_LLENGTH_SOME >>
  qexists_tac `l` >>
  imp_res_tac LTAKE_LENGTH >> simp[] >>
  `LFINITE ll` by simp[LFINITE_LLENGTH] >>
  drule to_fromList >>
  disch_then(fn thm => PURE_ONCE_REWRITE_TAC[GSYM thm]) >>
  simp[]
QED

Theorem STRING_TYPE_explode:
  !s u. STRING_TYPE s u ==> u = Litv(StrLit(explode s))
Proof
  Cases >> rw[STRING_TYPE_def]
QED

Theorem forward_matching_lines_ffidiv_spec:
  !input rv.
    limited_parts ["accept_call";"emit_string"] p /\
    LLENGTH input = SOME n /\
    every (null_terminated_w) input /\
    every ($>= 256 o LENGTH) input
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "forward_matching_lines" st) [rv]
      (seL4_IO input [] * W8ARRAY dummyarr_loc [])
      (POSTf s. λconf (bytes:word8 list).
         &(s = "accept_call" /\ conf = []) *
         W8ARRAY dummyarr_loc [] *
         SEP_EXISTS loc init. W8ARRAY loc init *
         SEP_EXISTS events.
         seL4_IO [||] events *
         cond(LFILTER is_emit (fromList events) =
              LMAP (output_event_of o cut_at_null_w)
                   (LFILTER (language o MAP (CHR o w2n) o cut_at_null_w)
                   input))
      )
Proof
  xcf "forward_matching_lines" st >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  unfold_cf_app >>
  imp_res_tac LTAKE_LLENGTH_SOME2 >> rveq >>
  qmatch_goalsub_abbrev_tac `W8ARRAY _ init` >>
  `LENGTH init = 256` by(qunabbrev_tac `init` >> simp[]) >>
  pop_assum mp_tac >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `seL4_IO _ events` >>
  `!newevents. seL4_IO [||] newevents = seL4_IO [||] (events ++ newevents)` by(unabbrev_all_tac >> simp[]) >>
  pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
  pop_assum kall_tac >>
  rpt(pop_assum mp_tac) >>
  SPEC_ALL_TAC >>
  Induct_on `l` >-
    (rw[] >>
     xcf "forward_loop" st >>
     xlet `(POSTf s. (λconf bytes.
             &(s = "accept_call" ∧ conf = []) *
                seL4_IO [||] events * W8ARRAY v' init *
                 W8ARRAY dummyarr_loc []))` >-
       (simp[cf_ffi_def] >>
        match_mp_tac local_elim >>
        hnf >>
        simp[app_ffi_def] >> reduce_tac >>
        reverse conj_tac >- (simp[SEP_IMPPOSTe_POSTf_left,SEP_IMPPOSTd_POSTf_left]) >>
        xsimpl >>
        simp[seL4_IO_def] >>
        qmatch_goalsub_abbrev_tac `one(FFI_part s u ns events)` >>
        MAP_EVERY qexists_tac [`W8ARRAY dummyarr_loc []`,`s`,`u`,`ns`,`events`] >>
        unabbrev_all_tac >> xsimpl >>
        simp[filter_cf_oracle,decode_encode_oracle_state_11,filter_oracle] >>
        xsimpl) >>
     xsimpl >> rename1 `W8ARRAY loc init` >>
     MAP_EVERY qexists_tac [`loc`,`init`,`[]`] >>
     simp[] >> xsimpl) >>
  rpt strip_tac >> fs[] >>
  xcf "forward_loop" st >>
  qabbrev_tac `newinit = TAKE 256 h ++ DROP (LENGTH h) init` >>
  xlet `POSTv v. &UNIT_TYPE () v *
        W8ARRAY v' newinit * W8ARRAY dummyarr_loc [] *
        seL4_IO (fromList l) (SNOC (IO_event "accept_call" [] (ZIP(init,newinit))) events)` >-
    (xffi >> xsimpl >>
     simp[seL4_IO_def,Abbr `newinit`] >>
     qmatch_goalsub_abbrev_tac `one(FFI_part s u ns events)` >>
     MAP_EVERY qexists_tac [`W8ARRAY dummyarr_loc []`,`s`,`u`,`ns`,`events`] >>
     unabbrev_all_tac >> simp[] >> xsimpl >>
     simp[filter_cf_oracle,decode_encode_oracle_state_11,filter_oracle] >>
     xsimpl >>
     simp[SNOC_APPEND,SEP_IMP_REFL]) >>
  xlet `(POSTv v. &UNIT_TYPE () v * W8ARRAY dummyarr_loc [] *
         W8ARRAY v' newinit *
         SEP_EXISTS events'.
         seL4_IO (fromList l) (events ++ events') *
         &(LFILTER is_emit (fromList events') =
           LMAP (output_event_of o cut_at_null_w)
           (if language (MAP(CHR o w2n) (cut_at_null_w h)) then
             [|h|]
            else [||])))` >-
    (xlet_auto >- (xsimpl >> simp[LENGTH_TAKE_EQ]) >>
     xlet_auto >- xsimpl >>
     xlet_auto >- xsimpl >>
     reverse xif >-
       (xcon >> xsimpl >>
        fs[match_string_eq] >>
        qunabbrev_tac `newinit` >>
        fs[null_terminated_w_thm,implode_def] >>
        rfs[null_terminated_cut_APPEND,TAKE_APPEND,TAKE_LENGTH_TOO_LONG,TAKE_TAKE_MIN] >>
        rfs[GSYM strlit_STRCAT,null_terminated_cut_APPEND] >>
        fs[cut_at_null_w_thm,MAP_MAP_o,CHR_w2n_n2w_ORD,implode_def] >>
        fs[DROP_APPEND1,DROP_LENGTH_TOO_LONG] >>
        simp[SNOC_APPEND,toList_THM] >> xsimpl >>
        PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND,SNOC_APPEND] >>
        xsimpl >>
        qmatch_goalsub_abbrev_tac `events ++ x` >>
        qexists_tac `x` >> simp[Abbr `x`] >>
        simp[is_emit_def] >> xsimpl
       ) >>
     xffi >> xsimpl >>
     simp[seL4_IO_def] >>
     imp_res_tac STRING_TYPE_explode >>
     rveq >> fs[] >>
     simp[cut_at_null_thm] >>
     qmatch_goalsub_abbrev_tac `one(FFI_part s u ns newevents)` >>
     MAP_EVERY qexists_tac [`cut_at_null_w(TAKE 256 newinit)`,`W8ARRAY v' newinit`,`s`,`u`,`ns`,`newevents`] >>
     unabbrev_all_tac >> simp[] >> xsimpl >>
     simp[filter_cf_oracle,decode_encode_oracle_state_11,filter_oracle] >>
     xsimpl >>
     fs[match_string_eq] >>
     fs[cut_at_null_w_thm,MAP_MAP_o,CHR_w2n_n2w_ORD,implode_def] >>
     fs[null_terminated_w_thm,implode_def] >>
     rfs[null_terminated_cut_APPEND,TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
     rfs[GSYM strlit_STRCAT,null_terminated_cut_APPEND] >>
     simp[toList_THM] >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND,SNOC_APPEND] >>
     xsimpl >>
     qmatch_goalsub_abbrev_tac `events ++ x` >>
     qexists_tac `x` >> simp[Abbr `x`] >>
     simp[is_emit_def] >> xsimpl >>
     simp[output_event_of_def,cut_at_null_w_thm,implode_def]
    ) >>
  xapp >>
  xsimpl >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac `events ++ events'` >>
  xsimpl >>
  unabbrev_all_tac >> simp[LENGTH_TAKE_EQ] >>
  asm_exists_tac >> rw[] >>
  rename1 `events ++ events' ++ events''` >>
  rename1 `W8ARRAY a1 a2` >>
  MAP_EVERY qexists_tac [`a1`,`a2`,`events' ++ events''`] >>
  fs[LFILTER_APPEND,LFINITE_fromList,GSYM LAPPEND_fromList] >>
  xsimpl
QED

val seL4_proj1_def = Define `
  seL4_proj1 = (λffi.
    FEMPTY |++ (mk_proj1 (encode_oracle_state,decode_oracle_state,
                          [("accept_call", filter_oracle "accept_call");
                           ("emit_string", filter_oracle "emit_string")]) ffi))`;

val seL4_proj2 = Define `seL4_proj2 =
  [(["accept_call";"emit_string"],filter_cf_oracle)]`

val filter_ffi_state_def = Define `filter_ffi input =
  <|oracle:=filter_oracle; ffi_state := input; io_events := []|>`;

Theorem limited_parts_proj:
  limited_parts ["accept_call";"emit_string"] (seL4_proj1,seL4_proj2)
Proof
  rw[limited_parts_def,seL4_proj2]
QED

Theorem parts_ok_filter:
  parts_ok (filter_ffi <|input:= input|>) (seL4_proj1,seL4_proj2)
Proof
  rw[cfStoreTheory.parts_ok_def,seL4_proj1_def,seL4_proj2,filter_ffi_state_def,
     cfStoreTheory.ffi_has_index_in_def,mk_proj1_def,FLOOKUP_UPDATE,
     FUPDATE_LIST_THM,FAPPLY_FUPDATE_THM,decode_encode_oracle_state_11,
     filter_oracle,filter_cf_oracle]
  >- metis_tac[NOT_SOME_NONE]
  >> rw[] >> fs[] >> rveq >> fs[]
  >> every_case_tac >> fs[] >> rveq >> fs[LENGTH_TAKE_EQ]
  >> rw[fmap_eq_flookup,FLOOKUP_UPDATE]
QED

Theorem forward_matching_lines_semantics:
 LLENGTH input = NONE /\ every null_terminated_w input /\
 every ($>= 256 ∘ LENGTH) input
 ==>
 ?events.
 semantics_prog (^(get_state st) with ffi := (filter_ffi <|input:=input|>)) ^(get_env st)
  [Dlet unknown_loc (Pcon NONE [])
           (App Opapp [Var (Short "forward_matching_lines"); Con NONE []])]
  (Diverge events) /\
 LFILTER is_emit events = LMAP (output_event_of o cut_at_null_w) (LFILTER (language o MAP (CHR o w2n) o cut_at_null_w) input)
Proof
  rpt strip_tac >>
  `nsLookup ^(get_env st).v (Short "forward_matching_lines") = SOME forward_matching_lines_v`
    by(unabbrev_all_tac >> EVAL_TAC) >>
  assume_tac limited_parts_proj >>
  drule_all forward_matching_lines_div_spec >>
  disch_then(qspec_then `ARB` mp_tac) >>
  disch_then(qspec_then `Conv NONE []` mp_tac) >>
  simp[app_def,app_basic_def] >>
  CONV_TAC(RATOR_CONV(RAND_CONV(RESORT_FORALL_CONV rev))) >>
  qmatch_goalsub_abbrev_tac `semantics_prog st` >>
  disch_then(qspec_then `st` mp_tac) >>
  unabbrev_all_tac >>
  simp[cfStoreTheory.st2heap_def,cfStoreTheory.store2heap_append,cfStoreTheory.ffi2heap_def,
       fetch "-" "filterProg_st_def",parts_ok_filter] >>
  qmatch_goalsub_abbrev_tac `FFI_split INSERT FFIset` >>
  `FFIset = {FFI_part (encode_oracle_state <|input:= input|>) filter_cf_oracle
                      ["accept_call"; "emit_string"] []}`
    by(unabbrev_all_tac >> rw[FUN_EQ_THM,EQ_IMP_THM] >-
        (pairarg_tac >> fs[seL4_proj2] >> rveq >>
         first_x_assum(qspec_then `"accept_call"` mp_tac) >>
         simp[seL4_proj1_def,mk_proj1_def] >>
         simp[FLOOKUP_UPDATE,FUPDATE_LIST_THM,filter_ffi_state_def]) >>
       Q.REFINE_EXISTS_TAC `(s,u,ns,ts)` >>
       rw[seL4_proj2,filter_ffi_state_def,seL4_proj1_def,mk_proj1_def,
          FLOOKUP_UPDATE,FUPDATE_LIST_THM,filter_ffi_state_def]) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  qmatch_goalsub_abbrev_tac `(Mem dummyarr _ INSERT junk) ∪ {_;FFIpart}` >>
  disch_then(qspecl_then [`FFI_split INSERT junk`,
                          `{Mem dummyarr (W8array []);FFIpart}`]
                         mp_tac) >>
  impl_tac >-
    (rw[SPLIT_def] >> unabbrev_all_tac >> simp[] >-
       (rw[FUN_EQ_THM,EQ_IMP_THM] >> rw[]) >-
       (simp[cfStoreTheory.FFI_part_NOT_IN_store2heap_aux,
             cfStoreTheory.store2heap_def]) >-
       (spose_not_then strip_assume_tac >>
        drule cfStoreTheory.store2heap_IN_LENGTH >> simp[])
    ) >>
  impl_tac >- (simp[STAR_def,seL4_IO_def,SPLIT_def,dummyarr_loc_def,
                    W8ARRAY_def] >>
               MAP_EVERY qexists_tac [`{FFIpart}`,`{Mem dummyarr (W8array [])}`] >>
               conj_tac >- (simp[FUN_EQ_THM,Abbr `FFIpart`] >> metis_tac[]) >>
               conj_tac >- simp[one_def] >>
               simp[SEP_EXISTS,cond_def,cell_def,one_def]) >>
  strip_tac >>
  Cases_on `r` >> fs[cond_def] >> rveq >>
  fs[evaluate_to_heap_def,semanticsTheory.semantics_prog_def] >>
  rename1 `lprefix_lub _ events` >>
  qexists_tac `events` >>
  rpt strip_tac >-
    (simp[semanticsTheory.evaluate_prog_with_clock_def,
          terminationTheory.evaluate_decs_def,
          astTheory.pat_bindings_def] >>
     simp[terminationTheory.evaluate_def] >>
     simp[semanticPrimitivesTheory.do_con_check_def,semanticPrimitivesTheory.build_conv_def] >>
     rw[evaluateTheory.dec_clock_def] >>
     fs[evaluate_ck_def] >>
     first_x_assum(qspec_then `k - 1` strip_assume_tac) >>
     fs[]) >>
  fs[] >>
  match_mp_tac(GEN_ALL lprefix_lub_subset) >>
  asm_exists_tac >> simp[] >> conj_tac >-
    (rw[IMAGE_DEF,SUBSET_DEF] >>
     qexists_tac `SUC ck` >>
     simp[semanticsTheory.evaluate_prog_with_clock_def,
          terminationTheory.evaluate_decs_def,
          astTheory.pat_bindings_def
         ] >>
     simp[terminationTheory.evaluate_def] >>
     simp[semanticPrimitivesTheory.do_con_check_def,semanticPrimitivesTheory.build_conv_def] >>
     rw[evaluateTheory.dec_clock_def] >>
     fs[evaluate_ck_def] >>
     rpt(PURE_TOP_CASE_TAC >> rveq >> fs[])) >>
  rw[PULL_EXISTS] >>
  simp[LPREFIX_fromList_fromList] >>
  simp[semanticsTheory.evaluate_prog_with_clock_def,
       terminationTheory.evaluate_decs_def,
       astTheory.pat_bindings_def
      ] >>
  simp[terminationTheory.evaluate_def] >>
  simp[semanticPrimitivesTheory.do_con_check_def,semanticPrimitivesTheory.build_conv_def] >>
  rw[evaluateTheory.dec_clock_def] >>
  fs[evaluate_ck_def] >>
  first_x_assum(qspec_then `k - 1` strip_assume_tac) >>
  fs[] >-
    (qexists_tac `ARB` >>
     qmatch_goalsub_abbrev_tac `evaluate st` >>
     Q.ISPEC_THEN `st` mp_tac
       (CONJUNCT1 evaluatePropsTheory.evaluate_io_events_mono
        |> SIMP_RULE std_ss [evaluatePropsTheory.io_events_mono_def]) >>
     simp[Abbr `st`]) >>
  qexists_tac `k - 1` >>
  every_case_tac >> fs[]
QED

Theorem forward_matching_lines_ffidiv_semantics:
 LLENGTH input = SOME n /\ every null_terminated_w input /\
 every ($>= 256 ∘ LENGTH) input
 ==>
 ?bytes events.
 semantics_prog (^(get_state st) with ffi := (filter_ffi <|input:=input|>)) ^(get_env st)
  [Dlet unknown_loc (Pcon NONE [])
           (App Opapp [Var (Short "forward_matching_lines"); Con NONE []])]
  (Terminate (FFI_outcome(Final_event "accept_call" [] bytes FFI_diverged))
             events) /\
 LFILTER is_emit (fromList events) = LMAP (output_event_of o cut_at_null_w) (LFILTER (language o MAP (CHR o w2n) o cut_at_null_w) input)
Proof
  rpt strip_tac >>
  `nsLookup ^(get_env st).v (Short "forward_matching_lines") = SOME forward_matching_lines_v`
    by(unabbrev_all_tac >> EVAL_TAC) >>
  assume_tac limited_parts_proj >>
  drule_all forward_matching_lines_ffidiv_spec >>
  disch_then(qspec_then `Conv NONE []` mp_tac) >>
  simp[app_def,app_basic_def] >>
  CONV_TAC(RATOR_CONV(RAND_CONV(RESORT_FORALL_CONV rev))) >>
  qmatch_goalsub_abbrev_tac `semantics_prog st` >>
  disch_then(qspec_then `st` mp_tac) >>
  unabbrev_all_tac >>
  simp[cfStoreTheory.st2heap_def,cfStoreTheory.store2heap_append,cfStoreTheory.ffi2heap_def,
       fetch "-" "filterProg_st_def",parts_ok_filter] >>
  qmatch_goalsub_abbrev_tac `FFI_split INSERT FFIset` >>
  `FFIset = {FFI_part (encode_oracle_state <|input:= input|>) filter_cf_oracle
                      ["accept_call"; "emit_string"] []}`
    by(unabbrev_all_tac >> rw[FUN_EQ_THM,EQ_IMP_THM] >-
        (pairarg_tac >> fs[seL4_proj2] >> rveq >>
         first_x_assum(qspec_then `"accept_call"` mp_tac) >>
         simp[seL4_proj1_def,mk_proj1_def] >>
         simp[FLOOKUP_UPDATE,FUPDATE_LIST_THM,filter_ffi_state_def]) >>
       Q.REFINE_EXISTS_TAC `(s,u,ns,ts)` >>
       rw[seL4_proj2,filter_ffi_state_def,seL4_proj1_def,mk_proj1_def,
          FLOOKUP_UPDATE,FUPDATE_LIST_THM,filter_ffi_state_def]) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  qmatch_goalsub_abbrev_tac `(Mem dummyarr _ INSERT junk) ∪ {_;FFIpart}` >>
  disch_then(qspecl_then [`FFI_split INSERT junk`,
                          `{Mem dummyarr (W8array []);FFIpart}`]
                         mp_tac) >>
  impl_tac >-
    (rw[SPLIT_def] >> unabbrev_all_tac >> simp[] >-
       (rw[FUN_EQ_THM,EQ_IMP_THM] >> rw[]) >-
       (simp[cfStoreTheory.FFI_part_NOT_IN_store2heap_aux,
             cfStoreTheory.store2heap_def]) >-
       (spose_not_then strip_assume_tac >>
        drule cfStoreTheory.store2heap_IN_LENGTH >> simp[])
    ) >>
  impl_tac >- (simp[STAR_def,seL4_IO_def,SPLIT_def,dummyarr_loc_def,
                    W8ARRAY_def] >>
               MAP_EVERY qexists_tac [`{FFIpart}`,`{Mem dummyarr (W8array [])}`] >>
               conj_tac >- (simp[FUN_EQ_THM,Abbr `FFIpart`] >> metis_tac[]) >>
               conj_tac >- simp[one_def] >>
               simp[SEP_EXISTS,cond_def,cell_def,one_def]) >>
  strip_tac >>
  Cases_on `r` >> fs[SEP_CLAUSES,SEP_F_def] >> rveq >>
  fs[STAR_def,SEP_EXISTS_THM,cond_def] >> rveq >>
  fs[SPLIT_def,SPLIT3_def,seL4_IO_def,one_def] >> rveq >>
  fs[evaluate_to_heap_def,semanticsTheory.semantics_prog_def] >>
  qmatch_asmsub_abbrev_tac `{ffipart}` >>
  `ffipart ∈ st2heap (seL4_proj1,seL4_proj2) st'`
    by(unabbrev_all_tac >> fs[]) >>
  unabbrev_all_tac >>
  drule_all limited_FFI_part_IN_st2heap_IMP >>
  strip_tac >> fs[] >>
  fs[evaluate_to_heap_def,semanticsTheory.semantics_prog_def] >>
  simp[semanticsTheory.evaluate_prog_with_clock_def,
          terminationTheory.evaluate_decs_def,
          astTheory.pat_bindings_def] >>
  simp[terminationTheory.evaluate_def] >>
  simp[semanticPrimitivesTheory.do_con_check_def,semanticPrimitivesTheory.build_conv_def] >>
  rw[evaluateTheory.dec_clock_def] >>
  PURE_ONCE_REWRITE_TAC[CONJ_SYM] >>
  asm_exists_tac >> simp[] >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac `SUC ck` >>
  fs[evaluate_ck_def]
QED

Theorem semantics_diverge_filter:
   every ($>= 256 o LENGTH) inl
   /\ every (null_terminated_w) inl
   /\ semantics_prog (^(get_state st) with ffi:=(filter_ffi <|input:=inl|>))
                     ^(get_env st) [^maincall] (Diverge events)
   ==> LFILTER is_emit events = LMAP (output_event_of o cut_at_null_w) (LFILTER (language o MAP (CHR o w2n) o cut_at_null_w) inl)
Proof
  rpt strip_tac
  >> `LLENGTH inl = NONE`
      by(CCONTR_TAC >> fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
         >> metis_tac[forward_matching_lines_ffidiv_semantics,ffiTheory.behaviour_distinct,
                      semanticsPropsTheory.semantics_prog_deterministic])
  >> imp_res_tac(GEN_ALL forward_matching_lines_semantics)
  >> first_x_assum(qspec_then `ffi` strip_assume_tac)
  >> dxrule semanticsPropsTheory.semantics_prog_deterministic
  >> disch_then dxrule >> simp[]
  >> metis_tac[]
QED

Theorem semantics_finite_filter:
   every ($>= 256 o LENGTH) inl
   /\ every (null_terminated_w) inl
   /\ semantics_prog (^(get_state st) with ffi:=(filter_ffi <|input:=inl|>))
                     ^(get_env st) [^maincall] (Terminate outcome events)
   ==> LFILTER is_emit (fromList events) =
       LMAP (output_event_of o cut_at_null_w)
         (LFILTER (language o MAP (CHR o w2n) o cut_at_null_w) inl)
Proof
  rpt strip_tac
  >> `?n. LLENGTH inl = SOME n`
      by(simp[GSYM IS_SOME_EXISTS] >> CCONTR_TAC
         >> fs[]
         >> metis_tac[forward_matching_lines_semantics,ffiTheory.behaviour_distinct,
                      semanticsPropsTheory.semantics_prog_deterministic])
  >> drule forward_matching_lines_ffidiv_semantics >> asm_rewrite_tac []
  >> disch_then (qspec_then `ffi` mp_tac) >> strip_tac
  >> dxrule(GEN_ALL semanticsPropsTheory.semantics_prog_deterministic)
  >> disch_then dxrule >> simp[]
  >> metis_tac[]
QED

(* S-expr generation handled by CMake build system
val _ = astToSexprLib.write_ast_to_file "../program.sexp" prog;
*)

val _ = export_theory ();
