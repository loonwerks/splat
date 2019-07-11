(*===========================================================================*)
(* Input format for a SPLAT system supporting network messages               *)
(*===========================================================================*)

structure splatLib :> splatLib =
struct

open HolKernel Parse boolLib bossLib MiscLib;

open regexpMisc regexpSyntax pred_setSyntax 
     arithmeticTheory listTheory stringTheory
     charsetTheory regexpTheory splatTheory
     pred_setLib numLib stringLib 
     Regexp_Type Regexp_Numerics regexpLib Enum_Encode;


fun listrel R [] [] = true
  | listrel R (a::t1) (b::t2) = R a b andalso listrel R t1 t2
  | listrel _ _ _ = false;

fun pairrel R1 R2 (x,y) (u,v) = R1 x u andalso R2 y v;

val ERR = Feedback.mk_HOL_ERR "splatLib";

type filter_info
   = {name : string,
      regexp : Regexp_Type.regexp,
      encode_def : thm, 
      decode_def : thm,
      inversion : term,
      correctness : term,
      receiver_correctness : term,
      implicit_constraints : thm option};

     
structure Finmap = Redblackmap;

type ('a, 'b) fmap = ('a, 'b) Finmap.dict;

(*---------------------------------------------------------------------------*)
(* Width of a message field, in bits or in word8s                            *)
(*---------------------------------------------------------------------------*)

datatype width = BITWIDTH of int | BYTEWIDTH of int;

val bits2bytes = 
 let fun roundup (q,r) = q + (if r > 0 then 1 else 0)
 in fn n => roundup(n div 8,n mod 8)
 end

fun width2bits (BYTEWIDTH n) = n*8
  | width2bits (BITWIDTH n) = n

fun width2bytes (BYTEWIDTH n) = n
  | width2bytes (BITWIDTH n) = 
     let fun roundup (q,r) = q + (if r > 0 then 1 else 0)
     in roundup(n div 8,n mod 8)
     end

(*---------------------------------------------------------------------------*)
(* A format contains enough information to bridge between a byte array and   *)
(* a higher-level which the byte array is a representation of.               *)
(*---------------------------------------------------------------------------*)

datatype atomic =
   Interval of 
     {span : IntInf.int * IntInf.int,
      encoding : encoding,
      endian : endian,
      width  : width,
      encoder : IntInf.int -> string,
      decoder : string -> IntInf.int,
      recog  : Regexp_Type.regexp}
  | Enumset of 
     {enum_type : hol_type,
      constr_codes : (term * int) list,
      logic : Enum_Encode.logic_info,
      recog : Regexp_Type.regexp}
  | StringLit of string
  | Raw of width
;

fun width_of atm =
 case atm
  of Interval{width,...} => width
   | Enumset _ => BYTEWIDTH 1
   | other => raise ERR "width_of" "";

fun recog_of atm =
 case atm
  of Interval{recog,...} => recog
   | Enumset{recog,...} => recog
   | other => raise ERR "recog_of" "";

(*---------------------------------------------------------------------------*)
(* Defaulting to LSB for the moment                                          *)
(*---------------------------------------------------------------------------*)

fun term_encoder(encoding,endian,width) =
 case encoding
  of Unsigned  => ``splat$enc ^(numSyntax.term_of_int (width2bytes width))``
   | Twos_comp => ``splat$enci ^(numSyntax.term_of_int (width2bytes width))``
   | Zigzag    => ``splat$encZigZag ^(numSyntax.term_of_int (width2bytes width))``
   | Sign_mag  => ``splat$encSignMag ^(numSyntax.term_of_int (width2bytes width))``

fun encoder_of atm =
 case atm
  of Interval{encoding,endian, width,...} => term_encoder(encoding,endian,width)
   | Enumset{logic,...} => #enc logic
   | other => raise ERR "encoder_of" "";

fun term_decoder(encoding,endian,width) =
 case encoding
  of Unsigned  => ``splat$dec``
   | Twos_comp => ``splat$deci ^(numSyntax.term_of_int (width2bytes width))``
   | Zigzag    => ``splat$decZigZag``
   | Sign_mag  => ``splat$decSignMag``

fun decoder_of atm =
 case atm
  of Interval{encoding,endian,width,...} => term_decoder(encoding,endian,width)
   | Enumset {logic,...} => #dec logic
   | other => raise ERR "decoder_of" "";


fun mk_interval enc dir (lo,hi) = 
 let open Regexp_Numerics
     val byte_width = interval_width enc (lo,hi)
 in Interval{span = (lo,hi),
             encoding = enc,
             endian = dir, 
             width = BYTEWIDTH byte_width,
             encoder = iint2string enc dir byte_width,
             decoder = string2iint enc dir,
             recog = interval_regexp enc dir byte_width (lo,hi)}
 end;

fun mk_enumset (ety,elts) = 
  case Finmap.peek (Enum_Encode.the_enumMap(),ety)
   of SOME (clist,logic) =>
        let val ilist = List.map (fn e => op_assoc aconv e clist) elts
            val chars = List.map Char.chr ilist
            val cset = Regexp_Type.charset_of chars
        in
          Enumset{enum_type = ety,
                  constr_codes = clist,
                  logic = logic,
                  recog = Chset cset}
        end
    | NONE => raise ERR "mk_enumset" 
                ("enumerated type "^Lib.quote (fst(dest_type ety))^" not registered")


(*---------------------------------------------------------------------------*)
(* Intended to be easily mapped to and from Robby's bitcodec representation  *)
(*---------------------------------------------------------------------------*)

datatype format
  = ATOM of atomic
  | CONCAT of format list
  | LIST of format
  | ARRAY of format * int
  | UNION of format * format
  | PACKED of format list * width
;


(*---------------------------------------------------------------------------*)
(* Translate formula coming from AGREE specs to regexp. Create encoder and   *)
(* decoder. Generate correctness formulas                                    *)
(*---------------------------------------------------------------------------*)

fun is_comparison tm =
 let val (opr,args) = strip_comb tm
  in op_mem same_const opr 
          [numSyntax.less_tm,numSyntax.leq_tm,numSyntax.greater_tm,
           numSyntax.geq_tm, intSyntax.less_tm,intSyntax.leq_tm,
           intSyntax.great_tm,intSyntax.geq_tm]
  end	

fun mk_set_lr list =
 let fun mk_set [] acc = rev acc
       | mk_set (h::t) acc =
         if op_mem aconv h acc then mk_set t acc else mk_set t (h::acc)
 in mk_set list []
 end

fun tdrop i list = (List.take(list,i),List.drop(list,i))

fun take_list [] [] = []
  | take_list [] _ = raise ERR "take_list" "non-empty list remains"
  | take_list (i::t) elts = 
    let val (h,elts') = tdrop i elts
    in h::take_list t elts'
    end
    handle _ => raise ERR "take_list" "";

(*---------------------------------------------------------------------------*)
(* Expand out all possible nested record projections from a variable of      *)
(* record type. The sequence of paths is the order in which fields will be   *)
(* written to the format.                                                    *)
(*---------------------------------------------------------------------------*)

fun all_paths recdvar =
 let val recdty = type_of recdvar
     val {Thy,Tyop=rtyname,Args} = dest_thy_type recdty
     fun projfn_of th = fst(strip_comb(lhs(snd(strip_forall (concl th)))))
     fun grow tm =
       let val ty = type_of tm
       in if TypeBase.is_record_type ty
	  then let val pfns = map projfn_of (TypeBase.accessors_of ty)
	       in map (Lib.C (curry mk_comb) tm) pfns
	       end
          else 
          if fcpSyntax.is_cart_type ty then
              let val (bty,dty) = fcpSyntax.dest_cart_type ty
		  val d = fcpSyntax.dest_int_numeric_type dty
                  val copies = map numSyntax.term_of_int (upto 0 (d-1))
                  fun Aproj n = fcpSyntax.mk_fcp_index(tm,n)
              in
                 map Aproj copies
              end
	  else [tm]
       end
     fun genpaths paths =
       let val paths' = flatten (map grow paths)
       in if listrel aconv paths' paths then 
               paths 
          else genpaths paths'
       end
 in
    genpaths [recdvar]
 end;

(*---------------------------------------------------------------------------*)
(* Takes the expanded wellformedness definition and extracts the per-field   *)
(* constraints on the underlying record type. The constraints are then       *)
(* translated to regular expressions. (Actually, one big one.) Also,         *)
(* encoders and decoders are created, along with a suite of theorems showing *)
(* the relationships between the encoder, decoder, and filter (generated     *)
(* from the big regular expression).                                         *) 
(*---------------------------------------------------------------------------*)

val ii2term = intSyntax.term_of_int o Arbint.fromLargeInt;

val default_int_bits = 31;

val SMAX_INT = twoE default_int_bits;  (* successor of maxint *)
val MIN_INT = IntInf.~SMAX_INT;
val SMAX_NUM = twoE (default_int_bits + 1); (* successor of maxnum *)

val smaxint_tm = ii2term SMAX_INT;
val minint_tm = ii2term MIN_INT;
val smaxnum_tm = numSyntax.mk_numeral (Arbnum.fromLargeInt SMAX_NUM);

fun max_const ty =
  if ty = numSyntax.num then smaxnum_tm else 
  if ty = intSyntax.int_ty then smaxint_tm 
  else raise ERR "max_const" "";

fun min_const ty =
  if ty = numSyntax.num then numSyntax.zero_tm else 
  if ty = intSyntax.int_ty then minint_tm 
  else raise ERR "min_const" "";

fun mk_lt ty = 
  if ty = numSyntax.num then numSyntax.less_tm else 
  if ty = intSyntax.int_ty then intSyntax.less_tm
  else raise ERR "mk_lt" "";
fun mk_le ty = 
  if ty = numSyntax.num then numSyntax.leq_tm else 
  if ty = intSyntax.int_ty then intSyntax.leq_tm
  else raise ERR "mk_le" "";


fun filter_correctness (fname,thm) =
 let val (wfpred_apps, expansion) = dest_eq(concl thm)
     val recdvar = 
        (case free_vars wfpred_apps
          of [x] => x
           | otherwise => raise ERR "filter_correctness" "expected 1 free var")
     val recdty = type_of recdvar
     val {Thy,Tyop=rtyname,Args} = dest_thy_type recdty
     val constraints = strip_conj expansion
     fun has_recd_var t = op_mem aconv recdvar (free_vars t)
     val allprojs = all_paths recdvar
     fun proj_of t =
       filter has_recd_var
	(if is_comparison t orelse is_eq t
        then snd (strip_comb t)
        else if is_disj t  (* disjunction of equalities *)
            then flatten (map (snd o strip_comb) (strip_disj t))
            else if type_of t = Type.bool then [t]
                 else raise ERR "proj_of" 
                   "expected a disjunction of equalities or an arithmetic inequality")
     val projs = mk_set_lr (flatten (map proj_of constraints))
     val omitted_projs = op_set_diff aconv allprojs projs
     fun in_group tmlist tm = (tm, filter (Lib.can (find_term (aconv tm))) tmlist)
     val allgroups = map (in_group constraints) allprojs 
     val groups = map (in_group constraints) projs 
     val groups' =  (* unconstrained fields get explicitly constrained *)
         if null omitted_projs
	 then groups
	 else
         let fun unconstrained proj = (* Done for integers and enums currently *)
              let val ty = type_of proj
                  open intSyntax 
              in if ty = int_ty
                    then [mk_leq(minint_tm,proj), mk_less(proj,smaxint_tm)]
	         else 
                 if ty = numSyntax.num 
                    then [numSyntax.mk_leq(numSyntax.zero_tm,proj),
                          numSyntax.mk_less(proj,smaxnum_tm)]
                 else case Finmap.peek (the_enumMap(),type_of proj)
                       of NONE => raise ERR "mk_correctness_goals" 
                                ("following field is not in the_enumMap(): "
                                 ^term_to_string proj)
		        | SOME (plist,_) => 
                            [list_mk_disj (map (curry mk_eq proj o fst) plist)]
              end
             fun supplement (proj,[]) = (proj,unconstrained proj)
               | supplement other = other
	 in 
            map supplement allgroups
         end

     (* Add implicit constraints to the wfpred *)

     val implicit_constraints = List.mapPartial (C (op_assoc1 aconv) groups') omitted_projs
     val (wfpred_apps',iconstraints_opt) = 
	 if null implicit_constraints
	 then (wfpred_apps,NONE)
	 else 
         let val implicit_constraints_tm =
                 list_mk_conj (map list_mk_conj implicit_constraints)
	     val iconstr_name = fname^"_implicit_constraints"
	     val iconstr_app = mk_comb(mk_var(iconstr_name,recdty --> Type.bool),recdvar)
	     val iconstr_def_tm = mk_eq(iconstr_app, implicit_constraints_tm)
	     val implicit_constraints_def = TotalDefn.Define `^iconstr_def_tm`
	     val implicit_constraints_const = 
                  mk_const(dest_var(fst(dest_comb iconstr_app)))
         in
            (mk_conj(wfpred_apps,mk_comb(implicit_constraints_const,recdvar)),
             SOME implicit_constraints_def)
         end

     (* map constraints to an interval. The (lo,hi) pair denotes the inclusive
        interval {i | lo <= i <= hi} so there is some fiddling to translate        all relations to <=.
     *)
     fun constraint_interval ctr =  (* elements of c expected to have form relop t1 t2 *)
      let val domtys = fst (strip_fun (type_of (fst (strip_comb (hd ctr)))))
          val _ = if Lib.all (fn ty => ty = numSyntax.num orelse ty = intSyntax.int_ty) domtys
                   then () else raise ERR "constraint_interval" "not a numeric constraint"
          fun elim_gtr tm = (* elim > and >= *)
            case strip_comb tm
	      of (rel,[a,b]) =>
                  if same_const rel numSyntax.greater_tm
		    then (numSyntax.less_tm,b,a) else 
                  if same_const rel numSyntax.geq_tm 
		    then (numSyntax.leq_tm,b,a) else 
                  if same_const rel intSyntax.great_tm
		    then (intSyntax.less_tm,b,a) else 
                  if same_const rel intSyntax.geq_tm 
		    then (intSyntax.leq_tm,b,a) else 
                  if op_mem same_const rel
                          [intSyntax.leq_tm,numSyntax.leq_tm,
                           intSyntax.less_tm,numSyntax.less_tm,boolSyntax.equality]
                     then (rel,a,b)
                  else raise ERR "constraint_interval" "unknown numeric relation"
	       | other => raise ERR "constraint_interval" "expected term of form `relop a b`"
          val ctr' = map elim_gtr ctr
          fun has_recdvar t = op_mem aconv recdvar (free_vars t)
          fun add_constraint [ctr as (rel,a,b)] = 
                 let val ty = type_of a
                 in if same_const boolSyntax.equality rel then
                       [ctr, (rel,b,a)]
                    else
                    if has_recdvar b then 
                         [ctr, (mk_lt ty, b,max_const ty)] else 
                    if has_recdvar a then
                         [(mk_le ty, min_const ty, a),ctr] 
                    else raise ERR "constraint_interval" "add_constraint"
                 end
            | add_constraint (x as [_,_]) = x
            | add_constraint other = raise ERR "constraint_interval" "add_constraint"
          val ctr'' = add_constraint ctr'
          fun sort [c1 as (_,a,b), c2 as (_,c,d)] = 
              let val fva = free_vars a
                  val fvb = free_vars b
                  val fvc = free_vars c
                  val fvd = free_vars d
              in 
                 if op_mem aconv recdvar fvb andalso op_mem aconv recdvar fvc andalso aconv b c
                   then (c1,c2)
	         else
	         if op_mem aconv recdvar fvd andalso op_mem aconv recdvar fva andalso aconv a d
                   then (c2,c1)
	         else raise ERR "constraint_interval(sort)" "unexpected format"
              end
            | sort otherwise = raise ERR "constraint_interval(sort)" "unexpected format"
          val ((rel1,lo_tm,_),(rel2,_,hi_tm)) = sort ctr''
	  fun dest_literal t = 
             (if type_of t = numSyntax.num
	        then Arbint.fromNat o numSyntax.dest_numeral
                else intSyntax.int_of_term) t
          val lo = dest_literal lo_tm
          val hi = dest_literal hi_tm
          val lo' = if op_mem same_const rel1 [numSyntax.less_tm,intSyntax.less_tm]
                      then Arbint.+(lo, Arbint.one) else lo
          val hi' = if op_mem same_const rel2 [numSyntax.less_tm,intSyntax.less_tm]
                      then Arbint.-(hi,Arbint.one) else hi
          val ctype = type_of lo_tm
	  val encoding = if ctype = numSyntax.num then Unsigned else Twos_comp
          val dir = LSB
      in  
        mk_interval encoding dir (Arbint.toLargeInt lo',Arbint.toLargeInt hi')
      end

     (*---------------------------------------------------------------------*)
     (* Expects (x = C1) \/ (x = C2) \/ ...                                 *)
     (* There are some special cases when the enumerated type is bool       *)
     (*---------------------------------------------------------------------*)

     fun constraint_enumset [ctr] =   (* Should be extended to finite sets of numbers *)
         let val eqns = 
              if not (is_disj ctr) then 
                  (if is_neg ctr then 
                     [mk_eq (dest_neg ctr,boolSyntax.F)] else
                     [mk_eq (ctr,boolSyntax.T)])
              else strip_disj ctr
             val constlike = null o free_vars
             fun elt_of eqn = 
                let val (l,r) = dest_eq eqn 
                in if constlike l then l else 
                   if constlike r then r else 
                   raise ERR "constraint_enumset (elt_of)" "expected a projection"
		end
	     val elts = map elt_of eqns
             val _ = if null elts then raise ERR "constraint_enumset" "no elements" else ()
	     val enumty = type_of (hd elts)
	     val etyname = fst(dest_type enumty)
             val _ = if 256 < length (TypeBase.constructors_of enumty) 
                       then raise ERR "constraint_enumset" 
                         ("enumerated type "^Lib.quote etyname
                          ^" has > 256 elements: too many") 
                       else ()
          in mk_enumset(enumty,elts)
	  end
       | constraint_enumset other = 
           raise ERR "constraint_enumset" "expected a disjunction of equations"

     fun mk_atomic x = 
        constraint_interval (snd x) 
         handle HOL_ERR _ => 
        constraint_enumset (snd x)

     val [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17] = groups';

     val atomics = map mk_atomic groups'

     (* Compute regexps for the fields *)

     val regexps = map recog_of atomics
     val the_regexp = Regexp_Match.normalize (catlist regexps)
     val the_regexp_tm = regexpSyntax.regexp_to_term the_regexp
     
     val codings = 
       List.map (fn atm => {enc = encoder_of atm, dec = decoder_of atm}) atomics

     (* Define encoder *)
     val encs = map #enc codings
     val encode_fields = map mk_comb (zip encs allprojs)
     val encode_fields_list = listSyntax.mk_list(encode_fields,stringLib.string_ty)
     val encodeFn_var = mk_var("encode_"^rtyname,recdty --> stringLib.string_ty)
     val encodeFn_lhs = mk_comb(encodeFn_var,recdvar)
     val encodeFn_rhs = listSyntax.mk_flat encode_fields_list
     val encodeFn_def_term = mk_eq(encodeFn_lhs,encodeFn_rhs)
     val encodeFn_def = TotalDefn.Define `^encodeFn_def_term`
     val encodeFn = mk_const(dest_var encodeFn_var)

     val regexp_lang_tm = 
       mk_thy_const{Name = "regexp_lang", Thy = "regexp", 
          Ty = regexpSyntax.regexp_ty --> stringSyntax.string_ty --> Type.bool}

     val correctness_goal = mk_forall(recdvar,
        mk_eq(wfpred_apps',
          pred_setSyntax.mk_in
            (mk_comb(encodeFn,recdvar),
	     mk_comb(regexp_lang_tm,the_regexp_tm))))

     (* Define decoder *)
     val decodeFn_name = "decode_"^rtyname
     val decodeFn_ty = stringSyntax.string_ty --> optionSyntax.mk_option recdty
     val decodeFn_var = mk_var(decodeFn_name,decodeFn_ty)
     val fvar = mk_var("s",stringSyntax.string_ty)
     val decodeFn_lhs = mk_comb(decodeFn_var, fvar)

     val fwidths = List.map (width2bytes o width_of) atomics
     val vars = map (fn i => mk_var("v"^Int.toString i, stringSyntax.char_ty))
                    (upto 0 (List.foldl (op+) 0 fwidths - 1))
     val decs = map #dec codings
     val chunked_vars = take_list fwidths vars
     fun enlist vlist = listSyntax.mk_list(vlist,stringSyntax.char_ty)
     val chunked_vars_tms = map enlist chunked_vars
     val rhs_info = zip allprojs (map mk_comb (zip decs chunked_vars_tms))
     fun rev_strip t b acc = 
         if is_var t then (rev acc, b) else
         if fcpSyntax.is_fcp_index t then 
          let val (A,i) = fcpSyntax.dest_fcp_index t
              val Aty = type_of A
              val Avar = mk_var("A",Aty)
              val indexOp = mk_abs(Avar,fcpSyntax.mk_fcp_index(Avar,i))
          in rev_strip A b (indexOp::acc)
	  end
         else 
         let val (M,N) = dest_comb t
	 in rev_strip N b (M::acc)
	 end
     fun booger (p,x) = rev_strip p x []
     val paths = map booger rhs_info

     fun parts [] = []
       | parts ((p as ([_],v))::t) = [p]::parts t
       | parts ((h as (segs1,_))::t) = 
	 let fun P (segs2,_) = 
                if null segs1 orelse null segs2 then false 
                else listrel aconv (tl segs1) (tl segs2)
             val (L1,L2) = Lib.partition P (h::t)
	 in L1 :: parts L2
	 end

     fun mk_recd_app rty args = 
       case TypeBase.constructors_of rty
        of [constr] => list_mk_comb (constr,args)
         | otherwise => raise ERR "mk_recd_app" "expected to find a record constructor"
     
     fun maybe_shrink [] = raise ERR "maybe_shrink" "empty partition"
       | maybe_shrink (partn as [([_],_)]) = partn  (* fully shrunk *)
       | maybe_shrink (partn as (apath::_)) = 
          let val segs = fst apath
              val args = map snd partn
              val ty = dom(type_of (hd segs))
          in if TypeBase.is_record_type ty then 
                let val fields = TypeBase.fields_of ty
                in if length fields = length args
                   then  [(tl segs,mk_recd_app ty args)]
                   else partn
                end
             else 
             if fcpSyntax.is_cart_type ty then 
                let open fcpSyntax
                    val (bty,dty) = dest_cart_type ty
                    val dim = dest_int_numeric_type dty
                in if dim = length args
                   then [(tl segs, mk_l2v(listSyntax.mk_list(args,type_of (hd args))))]
                   else raise ERR "maybe_shrink" 
                        ("expected to construct array of size "^Int.toString dim)
                end 
             else raise ERR "maybe_shrink" "expected record or array"
          end
       handle e => raise wrap_exn "splatLib" "maybe_shrink" e

     (* path : (term list * term) list *)
     val path_eq = listrel (pairrel (listrel aconv) aconv)
			    
     fun mk_recd paths =
      if Lib.all (equal 1 o length o fst) paths
         then mk_recd_app recdty (map snd paths)
      else 
      let val partns = parts paths
          val partns' = map maybe_shrink partns
	  val paths' = flatten partns'
      in
          if length paths' < length paths
	  then mk_recd paths'
	  else 
            if path_eq paths' paths (* paths' = paths *)
            then raise ERR "mk_recd" "irreducible path"
          else if length paths' = length paths
            then raise ERR "mk_recd" "length of paths not reduced"
            else raise ERR "mk_recd" "length of some path(s) increased"
      end

     val pat = listSyntax.mk_list(vars,stringSyntax.char_ty)
     val rhs_value = mk_recd paths
     val valid_rhs = optionSyntax.mk_some rhs_value
     val rules = [(pat,valid_rhs), (``otherwise:string``,optionSyntax.mk_none recdty)]
     val rhs = TypeBase.mk_pattern_fn rules
     val decodeFn_rhs = Term.beta_conv (mk_comb(rhs,fvar))
     val decodeFn_def = Define `^(mk_eq(decodeFn_lhs,decodeFn_rhs))`
     val decodeFn = mk_const(decodeFn_name,decodeFn_ty)

    (* Construct the formula of the receiver correctness theorem *)
    val svar = mk_var("s",stringSyntax.string_ty)
    val decoded_tm = optionSyntax.mk_the(mk_comb(decodeFn,svar))
    val wf_tm = if is_conj wfpred_apps
		then let val v = mk_var("vvv",type_of decoded_tm)
                     in pairSyntax.mk_anylet
                         ([(v,decoded_tm)],subst [recdvar |-> v] wfpred_apps)
                     end
                else subst [recdvar |-> decoded_tm] wfpred_apps
    val receiver_correctness_goal = mk_forall(svar,
        mk_imp
         (pred_setSyntax.mk_in
             (svar, mk_comb(regexp_lang_tm,the_regexp_tm)),wf_tm))
    (* Construct the formula of the inversion theorem *)
    val inversion_goal = mk_forall(recdvar,
        mk_imp(wfpred_apps',
               mk_eq(mk_comb(decodeFn,mk_comb(encodeFn,recdvar)),
                     optionSyntax.mk_some recdvar)))
 in
     {name        = fname,
      regexp      = the_regexp,
      encode_def  = encodeFn_def,
      decode_def  = decodeFn_def,
      inversion   = inversion_goal,
      correctness = correctness_goal,
      receiver_correctness = receiver_correctness_goal,
      implicit_constraints = iconstraints_opt}
 end
 handle e => raise wrap_exn "splatLib" "filter_correctness" e;

(*---------------------------------------------------------------------------*)
(* Proves goals of the form                                                  *)
(*                                                                           *)
(*   s IN regexp_lang (Chset (Charset a b c d))                              *)
(*     <=>                                                                   *)
(*   (LENGTH s = 1) /\ dec s <= K                                            *)
(*---------------------------------------------------------------------------*)

val IN_CHARSET_NUM_TAC =
 rw_tac (list_ss ++ regexpLib.charset_conv_ss) [EQ_IMP_THM,strlen_eq,LE_LT1]
  >> TRY EVAL_TAC 
  >> rule_assum_tac 
        (SIMP_RULE list_ss [dec_def, numposrepTheory.l2n_def, ord_mod_256])
  >> rpt (qpat_x_assum `_ < ORD c` mp_tac ORELSE qpat_x_assum `ORD c < _` mp_tac)
  >> Q.SPEC_TAC (`ORD c`, `n`)
  >> REPEAT (CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL))
  >> rw_tac bool_ss [];

end
