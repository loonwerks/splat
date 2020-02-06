(*===========================================================================*)
(* Input format for a SPLAT system supporting network messages               *)
(*===========================================================================*)

structure splatLib :> splatLib =
struct

open HolKernel Parse boolLib bossLib MiscLib;

open regexpMisc regexpSyntax pred_setSyntax
     arithmeticTheory listTheory stringTheory
     FormalLangTheory charsetTheory regexpTheory splatTheory
     pred_setLib numLib stringLib
     Regexp_Type Regexp_Numerics regexpLib Enum_Encode;

local open Json intLib in end;

type endian = Regexp_Numerics.endian
type encoding = Regexp_Numerics.encoding

val ERR = Feedback.mk_HOL_ERR "splatLib";

fun pp_ostrm ostrm pretty =
  let open Portable PP
      val writer = curry TextIO.output ostrm
  in
     PP.prettyPrint (writer,75) pretty
  end

structure Finmap = Redblackmap;

type ('a, 'b) fmap = ('a, 'b) Finmap.dict;

fun listrel R [] [] = true
  | listrel R (a::t1) (b::t2) = R a b andalso listrel R t1 t2
  | listrel _ _ _ = false;

fun pairrel R1 R2 (x,y) (u,v) = R1 x u andalso R2 y v;

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
(* Unconstrained ints in the input spec (those not given an interval in the  *)
(* wellformedness specification) need to be given a width in the message.    *)
(* Optimize i means that the width of an int field is computed to be the     *)
(* minimum width needed to represent the specified interval; if no interval  *)
(* is specified, then i bits is the width. Uniform i means that all int      *)
(* fields (constrained or not) are set to be of width i.                     *)
(*---------------------------------------------------------------------------*)

datatype shrink = Optimize of int | Uniform of int

fun shrinkVal (Optimize i) = i
  | shrinkVal (Uniform i) = i;


(*---------------------------------------------------------------------------*)
(* A format contains enough information to bridge between a byte array and   *)
(* a higher-level which the byte array is a representation of.               *)
(*---------------------------------------------------------------------------*)

datatype fieldrep =
   Interval of
     {span : IntInf.int * IntInf.int,
      encoding : encoding,
      endian : endian,
      width  : width,
      encoder : IntInf.int -> string,
      decoder : string -> IntInf.int,
      regexp  : Regexp_Type.regexp,
      constraint : term}
  | Enumset of
     {enum_type : hol_type,
      constr_codes : (term * int) list,
      elts : term list,
      codec : Enum_Encode.enum_codec,
      regexp : Regexp_Type.regexp,
      constraint : term}
  | StringLit of
     {strlit : string,
      regexp : Regexp_Type.regexp,
      constraint : term}
  | Raw of
     {width : width,
      regexp : Regexp_Type.regexp,
      constraint : term}
;

fun encoding2string Unsigned  = "Unsigned"
  | encoding2string Twos_comp = "Twos_comp"
  | encoding2string Zigzag    = "Zigzag"
  | encoding2string Sign_mag  = "Sign_mag";

fun endian2string LSB  = "LSB"
  | endian2string MSB  = "MSB";

fun fieldrep2json frep =
 let open Json
 in
   case frep
    of Interval{span,encoding,endian,width,encoder,decoder,regexp,constraint} =>
       AList [("kind", String "Interval"),
              ("span",
                AList [("lbound",Number(Int(Int.fromLarge(fst span)))),
                       ("rbound",Number(Int(Int.fromLarge(snd span))))]),
              ("encoding", String (encoding2string encoding)),
              ("endian", String(endian2string endian)),
              ("width", Number(Int(width2bits width)))]
     | Enumset{enum_type,constr_codes,elts,codec,regexp,constraint} =>
       AList [("kind", String "Enumset"),
              ("enum_type",
               let val {Tyop,Thy,Args} = dest_thy_type enum_type
                in AList [("Tyop", String Tyop), ("Thy",String Thy)]
               end),
              ("constr_codes",
                List (map (fn (constr,code) => AList
                              [("constr", String (fst(dest_const constr))),
                               ("code", Number(Int code))]) constr_codes)),
              ("elts", List (map (fn e => String (fst(dest_const e))) elts)),
              ("width", Number(Int 8))]
     | StringLit{strlit,regexp,constraint} =>
       AList [("kind", String "StringLit"),
              ("contents",  String strlit),
              ("width", Number(Int (String.size strlit * 8)))]
    | Raw {width,regexp,constraint} =>
        raise ERR "fieldrep2json" "unexpected fieldrep (Raw)"
 end;

fun manifest2json manif_elts =
 let open Json
     fun elt2json (t,frep) =
         AList [("fieldname", String(Parse.term_to_string t)),
                ("fieldrep", fieldrep2json frep)]
 in
   List (map elt2json manif_elts)
 end

val pp_fieldrep =
 let open Portable PP
     fun paren i j s1 s2 ps =
       if i < j then block CONSISTENT 0 ps
       else block INCONSISTENT (size s1)
                  (add_string s1 :: ps @ [add_string s2])
     fun pp_constr_code (constr,code) =
       paren 0 0 "(" ")"
          [add_string(fst(dest_const constr)),
           add_string",", add_string(Int.toString code)]
     fun pp i fieldrep =
      case fieldrep
       of Interval{span,encoding,endian,width,encoder,decoder,regexp,constraint} =>
           paren i 0 "(" ")"
            [add_string "Interval",
             add_break(1,0),
             paren i 0 "(" ")"
               [add_string(IntInf.toString (fst span)),
                add_string",",
                add_string(IntInf.toString (snd span))],
             add_break(1,0),
             paren i 0 "(" ")"
               (case width
                 of BITWIDTH i => [add_string "BITS", add_break (1,0),
                                   add_string (Int.toString i)]
                 |  BYTEWIDTH i => [add_string "BYTES", add_break (1,0),
                                   add_string (Int.toString i)]),
             add_break(1,0),
             add_string (encoding2string encoding),
             add_break(1,0),
             add_string (endian2string endian)]
        | Enumset{enum_type,constr_codes,elts,codec,regexp,constraint} =>
            paren i 0 "(" ")"
            [add_string "Enumset",
             add_break(1,0),
             let val {Tyop,Thy,Args} = dest_thy_type enum_type
             in paren i 0 "[" "]"
               [add_string Thy, add_string",", add_string Tyop]
             end,
             add_break(1,0),
             add_string "(BYTES 1)",
             add_break(1,0),
             paren i 0 "[" "]"
               (pr_list pp_constr_code
                   [add_string ",", add_break(0,0)] constr_codes),
             add_break(1,0),
             paren i 0 "[" "]"
               (pr_list (fn t => add_string (fst(dest_const t)))
                        [add_string ",", add_break(0,0)] elts)]
        | StringLit{strlit,regexp,constraint} => raise ERR "" ""
        | Raw {width,regexp,constraint} => raise ERR "" ""
 in pp 0
 end

fun manifest2pretty manif =
 let open Portable PP
     fun paren i j s1 s2 ps =
       if i < j then block CONSISTENT 0 ps
       else block INCONSISTENT (size s1)
                  (add_string s1 :: ps @ [add_string s2])
     fun pp_manif_elt i (t,fieldrep) =
          paren i 0 "(" ")"
             [add_string (Parse.term_to_string t),
              add_break(1,0), pp_fieldrep fieldrep]
 in
   block CONSISTENT 0
     (pr_list (pp_manif_elt 0) [NL] manif)
 end;

val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn fr => pp_fieldrep fr);

type filter_info
   = {name : string,
      regexp : Regexp_Type.regexp,
      manifest : (term * fieldrep) list, (* segments *)
      implicit_constraints : thm option,
      tv : term};

fun width_of atm =
 case atm
  of Interval{width,...} => width
   | Enumset _ => BYTEWIDTH 1
   | other => raise ERR "width_of" "";

fun regexp_of atm =
 case atm
  of Interval{regexp,...} => regexp
   | Enumset{regexp,...} => regexp
   | other => raise ERR "regexp_of" "";

fun constraint_of atm =
 case atm
  of Interval{constraint,...} => constraint
   | Enumset{constraint,...}  => constraint
   | other => raise ERR "regexp_of" "";

fun term_encoder(encoding,endian,width) =
 case (encoding,endian)
  of (Unsigned,LSB) =>
       ``splat$enc ^(numSyntax.term_of_int (width2bytes width))``
   | (Unsigned,MSB) =>
       ``\n. REVERSE
                (splat$enc ^(numSyntax.term_of_int (width2bytes width)) n)``
   | (Twos_comp,LSB) =>
       ``splat$enci ^(numSyntax.term_of_int (width2bytes width))``
   | (Twos_comp,MSB) =>
       ``\i. REVERSE
               (splat$enci ^(numSyntax.term_of_int (width2bytes width)) i)``
   | (Zigzag,LSB) =>
       ``splat$encZigZag ^(numSyntax.term_of_int (width2bytes width))``
   | (Zigzag,MSB) =>
       ``\i. REVERSE
              (splat$encZigZag ^(numSyntax.term_of_int (width2bytes width)) i)``
   | (Sign_mag,LSB)  =>
       ``splat$encSignMag ^(numSyntax.term_of_int (width2bytes width))``
   | (Sign_mag,MSB)  =>
       ``\i. REVERSE
               (splat$encSignMag ^(numSyntax.term_of_int (width2bytes width)) i)``

fun term_decoder(encoding,endian,width) =
 case (encoding,endian)
  of (Unsigned,LSB)  => ``splat$dec``
   | (Twos_comp,LSB) => ``splat$deci ^(numSyntax.term_of_int (width2bytes width))``
   | (Zigzag,LSB)    => ``splat$decZigZag``
   | (Sign_mag,LSB)  => ``splat$decSignMag``
   | (Unsigned,MSB)  =>
       ``\s. splat$deci ^(numSyntax.term_of_int (width2bytes width))
                        (REVERSE s)``
   | (Twos_comp,MSB) =>
       ``\s. splat$deci ^(numSyntax.term_of_int (width2bytes width))
                        (REVERSE s)``
   | (Zigzag,MSB)    => ``\s. splat$decZigZag (REVERSE s)``
   | (Sign_mag,MSB)  => ``\s. splat$decSignMag (REVERSE s)``

fun field_encoder atm =
 case atm
  of Interval{encoding,endian, width,...} => term_encoder(encoding,endian,width)
   | Enumset{codec,...} => #enc codec
   | other => raise ERR "field_encoder" "";

fun field_decoder atm =
 case atm
  of Interval{encoding,endian,width,...} => term_decoder(encoding,endian,width)
   | Enumset {codec,...} => #dec codec
   | other => raise ERR "field_decoder" "";

(*---------------------------------------------------------------------------*)
(* Checks that the intwidth is a multiple of eight and is adequately large   *)
(* to encode the interval.                                                   *)
(*---------------------------------------------------------------------------*)

fun mk_interval shrink enc dir (lo,hi) pred =
 let open Regexp_Numerics
     val min_ivl_width = interval_width enc (lo,hi)
     val width =
       (case shrink
         of Optimize i => min_ivl_width
         |  Uniform i =>
             let val bytewidth = i div 8
             in if min_ivl_width <= bytewidth
                then bytewidth
                else raise ERR "mk_interval"
                      (String.concat ["interval (",
                        IntInf.toString lo,",",IntInf.toString hi,
                        ") not representable in ",
                        Int.toString i, " bits"])
             end)
 in Interval{span = (lo,hi),
             encoding = enc,
             endian   = dir,
             width    = BYTEWIDTH width,
             encoder  = iint2string enc dir width,
             decoder  = string2iint enc dir,
             regexp    = interval_regexp enc dir width (lo,hi),
             constraint = pred}
 end;

fun mk_enumset (ety,elts,pred) =
  case Finmap.peek (Enum_Encode.the_enumMap(),ety)
   of SOME (clist,codec) =>
        let val ilist = List.map (fn e => op_assoc aconv e clist) elts
            val chars = List.map Char.chr ilist
            val cset = Regexp_Type.charset_of chars
        in
          Enumset{enum_type = ety,
                  constr_codes = clist,
                  elts = elts,
                  codec = codec,
                  regexp = Chset cset,
                  constraint = pred}
        end
    | NONE => raise ERR "mk_enumset"
         ("enumerated type "^Lib.quote (fst(dest_type ety))^" not registered")


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
(* Default parameters for representation of ints.                            *)
(*---------------------------------------------------------------------------*)

val ii2term = intSyntax.term_of_int o Arbint.fromLargeInt;

fun mk_lt ty =
  if ty = numSyntax.num then numSyntax.less_tm else
  if ty = intSyntax.int_ty then intSyntax.less_tm
  else raise ERR "mk_lt" "";

fun mk_le ty =
  if ty = numSyntax.num then numSyntax.leq_tm else
  if ty = intSyntax.int_ty then intSyntax.leq_tm
  else raise ERR "mk_le" "";

(*---------------------------------------------------------------------------*)
(* max_const expected to be used in constraints of form t < max_const, so    *)
(* will actually be one larger than the max *expressible* const for given    *)
(* bits and encoding                                                         *)
(*---------------------------------------------------------------------------*)

fun max_constFn (bits:int) encoding =
 let val maxnum =
      (case encoding
        of Unsigned  => twoE bits
         | otherwise => twoE (bits - 1))
 in fn ty =>
     if ty = numSyntax.num then
         numSyntax.mk_numeral (Arbnum.fromLargeInt maxnum)
     else
     if ty = intSyntax.int_ty then
         ii2term maxnum
     else raise ERR "max_const" ""
 end;

fun min_constFn bits encoding =
 let val minnum =
      (case encoding
        of Unsigned  => 0
         | Sign_mag  => IntInf.~(IntInf.-(twoE (bits - 1), 1))
         | otherwise => IntInf.~(twoE (bits - 1)))
 in fn ty =>
     if ty = numSyntax.num then
         numSyntax.zero_tm
     else
     if ty = intSyntax.int_ty then
         ii2term minnum
     else raise ERR "min_const" ""
 end;

fun fpath s =
  let open FileSys
      fun fail() = raise ERR "fpath"
             ("unable to create or access directory "^Lib.quote s)
      val path = fullPath s handle _ => (mkDir s ; fullPath s)
                            handle _ => fail()
      in if isDir path andalso access(path,[A_EXEC,A_READ,A_WRITE])
         then path else fail()
      end

(*---------------------------------------------------------------------------*)
(* Expects (x = C1) \/ (x = C2) \/ ...                                       *)
(* There are some special cases when the enumerated type is bool             *)
(*                                                                           *)
(* Note: this could be applied to finite sets of numbers, rather than finite *)
(* sets of enumerated constructors.                                          *)
(*---------------------------------------------------------------------------*)

fun constraint_enumset [ctr] =
    let val eqns =
           if not (is_disj ctr) then
               (if is_neg ctr then
                  [mk_eq (dest_neg ctr,boolSyntax.F)] else
                  [mk_eq (ctr,boolSyntax.T)])
           else strip_disj ctr
        val _ = if all is_eq eqns then ()
                 else raise ERR "constraint_enumset"
                    "expected disjunction of equations"
        val constlike = null o free_vars
        fun norm eqn =
          let val _ = if not(constlike eqn) then () else
                 raise ERR "constraint_enumset(norm)"
                      "expected at least one variable somewhere in eqn"
             val (l,r) = dest_eq eqn
          in if constlike l then mk_eq(r,l) else
             if constlike r then eqn else
             raise ERR "constraint_enumset (norm)" "expected a constructor"
          end
        val eqns' = map norm eqns
        val proj = lhs (hd eqns')
        val elts = map rhs eqns'
        val _ = if null elts then
                raise ERR "constraint_enumset" "no elements" else ()
        val enumty = type_of (hd elts)
        val etyname = fst(dest_type enumty)
        val _ = if 256 < length (TypeBase.constructors_of enumty) then
                  raise ERR "constraint_enumset"
                    ("enumerated type "^Lib.quote etyname
                     ^" has > 256 elements: too many")
                else ()
        val pvar = mk_var("x",enumty)
        val enumset_pred =
            mk_abs(pvar,subst [proj |-> pvar] (list_mk_disj eqns))
    in
         mk_enumset(enumty,elts,enumset_pred)
    end
  | constraint_enumset other =
    raise ERR "constraint_enumset" "expected a disjunction of equations";

(*---------------------------------------------------------------------------*)
(* gen_filter_artifacts takes the expanded wellformedness definition and     *)
(* extracts the per-field constraints on the underlying record type. The     *)
(* constraints are then translated to regular expressions (actually, one big *)
(* one.) Also, encoders and decoders are created, along with a suite of      *)
(* theorems showing the relationships between the encoder, decoder, and      *)
(* filter (generated from the big regular expression).                       *)
(*---------------------------------------------------------------------------*)

type int_format = shrink * Regexp_Numerics.endian * Regexp_Numerics.encoding

fun gen_filter_artifacts (intformat as (shrink,endian,encoding))
                         ((pkgName,fname),thm) =
 let val intwidth = shrinkVal shrink
     val max_const = max_constFn intwidth encoding
     val min_const = min_constFn intwidth encoding
     val (wfpred_apps, expansion) = dest_eq(concl thm)
     val recdvar =
        (case free_vars wfpred_apps
          of [x] => x
           | otherwise => raise ERR "gen_filter_artifacts" "expected 1 free var")
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
                    then [mk_leq(min_const ty,proj), mk_less(proj,max_const ty)]
                 else
                 if ty = numSyntax.num
                    then [numSyntax.mk_leq(numSyntax.zero_tm,proj),
                          numSyntax.mk_less(proj,max_const ty)]
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

     val implicit_constraints =
          List.mapPartial (C (op_assoc1 aconv) groups') omitted_projs
     val (wfpred_apps',iconstraints_opt) =
         if null implicit_constraints
         then (wfpred_apps,NONE)
         else
         let val implicit_constraints_tm =
                 list_mk_conj (map list_mk_conj implicit_constraints)
             val iconstr_name = fname^"_implicit_constraints"
             val iconstr_app =
                    mk_comb(mk_var(iconstr_name,recdty --> Type.bool),recdvar)
             val iconstr_def_tm = mk_eq(iconstr_app, implicit_constraints_tm)
             val implicit_constraints_def = TotalDefn.Define `^iconstr_def_tm`
             val implicit_constraints_const =
                  mk_const(dest_var(fst(dest_comb iconstr_app)))
         in
            (mk_conj(wfpred_apps,mk_comb(implicit_constraints_const,recdvar)),
             SOME implicit_constraints_def)
         end

     (*---------------------------------------------------------------------------*)
     (* Map constraints on a record field to an interval. The (lo,hi) pair        *)
     (* denotes the inclusive interval {i | lo <= i <= hi} so there is some       *)
     (* fiddling to translate all relations to <=. Elts of ctr expected to have   *)
     (* form relop t1 t2.                                                         *)
     (*---------------------------------------------------------------------------*)

     fun constraint_interval ctr =
      let val domtys = fst (strip_fun (type_of (fst (strip_comb (hd ctr)))))
          fun is_numeric ty = (ty = numSyntax.num orelse ty = intSyntax.int_ty)
          val _ = if Lib.all is_numeric domtys then ()
                  else raise ERR "constraint_interval" "not a numeric constraint"
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
               | other => raise ERR "constraint_interval"
                                    "expected term of form `relop a b`"
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
                 if op_mem aconv recdvar fvb andalso
                    op_mem aconv recdvar fvc andalso aconv b c
                   then (c1,c2)
                 else
                 if op_mem aconv recdvar fvd andalso
                    op_mem aconv recdvar fva andalso aconv a d
                   then (c2,c1)
                 else raise ERR "constraint_interval(sort)" "unexpected format"
              end
            | sort otherwise = raise ERR "constraint_interval(sort)"
                                         "unexpected format"
          val (loc,hic) = sort ctr''
          val (rel1,lo_tm,f1) = loc
          val (rel2,f2,hi_tm) = hic
          val vname =
             let val ty = type_of f1
             in if ty = numSyntax.num then
                   "n" else
                if ty = intSyntax.int_ty then
                   "i"
                else "v"
             end
          val ipvar = mk_var(vname,type_of f1)
          fun mk_ineq (rel,a,b) = list_mk_comb(rel,[a,b])
          val interval_pred = mk_abs(ipvar,
              subst[f1 |-> ipvar] (mk_conj (mk_ineq loc, mk_ineq hic)))
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
      in
           mk_interval shrink encoding endian
                       (Arbint.toLargeInt lo',Arbint.toLargeInt hi') interval_pred
      end

     fun mk_segment a =
        constraint_interval a
         handle HOL_ERR _ =>
        constraint_enumset a
         handle HOL_ERR _ =>
        raise ERR "mk_segment" (String.concat
         ["Unable to create regexp capturing the following constraints:\n\n  ",
          String.concatWith ",\n  " (map term_to_string a), "\n\n"])

     val manifest = map (I##mk_segment) groups'

     val _ = (let open FileSys TextIO
                  val pretty_segments = manifest2pretty manifest
                  val pretty_json = Json.pp_json(manifest2json manifest)
                  val ostrm1 = openOut(getDir() ^"/"^ fname^".segments")
                  val ostrm2 = openOut(getDir() ^"/"^ fname^".segments.json")
              in pp_ostrm ostrm1 pretty_segments;
                 pp_ostrm ostrm2 pretty_json;
                 closeOut ostrm1;
                 closeOut ostrm2
              end
              handle e =>
              raise ERR "gen_filter_artifacts" "unable to write segments file")

     (* Compute regexps for the fields *)

     val regexps = map (regexp_of o snd) manifest
     val the_regexp = Regexp_Match.normalize (catlist regexps)
     val the_regexp_tm = regexpSyntax.regexp_to_term the_regexp

     val encs = map (field_encoder o snd) manifest
     val preds = map (constraint_of o snd) manifest
     fun mk_set_abs a b =
      let val (v,body) = dest_abs b
      in pred_setSyntax.prim_mk_set_spec(mk_comb(a,v), body, [v])
      end
     val obs = map2 mk_set_abs encs preds
     val dotc = inst [alpha |-> stringSyntax.char_ty]
                   (prim_mk_const{Thy="FormalLang",Name="dot"})
     fun mk_dot l1 l2 = list_mk_comb(dotc,[l1,l2])
     val enc_spec = end_itlist mk_dot obs
     val svar = mk_var("s",stringSyntax.string_ty)
     val tv_tm = mk_eq (pred_setSyntax.mk_in (svar,mk_regexp_lang the_regexp_tm),
                        pred_setSyntax.mk_in (svar,enc_spec))
 in
     {name  = fname,
      regexp = the_regexp,
      implicit_constraints = iconstraints_opt,
      manifest = manifest,
      tv = tv_tm}
 end
 handle e => raise wrap_exn "splatLib" "gen_filter_artifacts" e;

(*
     val codings =
       List.map (fn atm => {enc = field_encoder atm, dec = field_decoder atm})
                (map snd manifest);

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

     val fwidths = List.map (width2bytes o width_of o snd) manifest
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
      implicit_constraints = iconstraints_opt,
      manifest = manifest}
 end
 handle e => raise wrap_exn "splatLib" "gen_filter_artifacts" e;
*)

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


(*---------------------------------------------------------------------------*)
(* Reduce charsets to constraints                                            *)
(*---------------------------------------------------------------------------*)

fun regexp_elts r =
   Regexp_Type.charset_elts
     (regexpSyntax.term_to_charset r);

fun charset_intervals r = regexpMisc.intervals (map Char.ord (regexp_elts r))

fun CHECK_SPEC_TAC (t1,t2) (asl,c) =
  (if can(find_term (aconv t1)) c
    then SPEC_TAC (t1,t2)
    else NO_TAC) (asl,c)

fun GEVAL_TAC (asl,c) =
    (if null(free_vars c) then EVAL_TAC else NO_TAC) (asl,c);

fun const_bound tm =
 let open numSyntax
 in (is_less tm orelse is_leq tm)
    andalso
    is_numeral (rand tm)
 end

val ordered_pop_tac =
 rpt (PRED_ASSUM (not o const_bound) mp_tac)
  >> PRED_ASSUM const_bound mp_tac;

val prover =
 let open numSyntax stringSyntax
     val cvar = mk_var("c",num)
     val nvar = mk_var("n",num)
     val ordtm = mk_ord(mk_var("c",char_ty))
 in
    rw_tac (list_ss ++ pred_setLib.PRED_SET_ss)
      [pred_setTheory.EXTENSION, regexpTheory.regexp_lang_def,
       charsetTheory.charset_mem_def, charsetTheory.alphabet_size_def,
       EQ_IMP_THM,strlen_eq,LE_LT1]
    >> full_simp_tac list_ss [dec_char,ORD_CHR_RWT]
    >> TRY (qexists_tac `ORD c` >> rw_tac list_ss [CHR_ORD])
    >> (GEVAL_TAC ORELSE
         (ordered_pop_tac
           >> (CHECK_SPEC_TAC (cvar,nvar) ORELSE
               CHECK_SPEC_TAC (ordtm,nvar))
           >> REPEAT (CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL))
           >> gen_tac >> ACCEPT_TAC TRUTH))
 end

(*---------------------------------------------------------------------------*)
(* Takes a term of the form                                                  *)
(*                                                                           *)
(*  s IN regexp_lang (Chset (Charset a b c d))                               *)
(*                                                                           *)
(* and returns                                                               *)
(*                                                                           *)
(* |- s IN regexp_lang (Chset (Charset a b c d)) <=>                         *)
(*    STRLEN s = 1 /\ lo <= dec s <= hi                                      *)
(*                                                                           *)
(* where lo and hi are the interval endpoints. If lo = 0 then it is omitted. *)
(* If lo=hi then we just have (dec s = lo)                                   *)
(*---------------------------------------------------------------------------*)

fun pure_in_charset_conv tm =
 let open regexpSyntax stringSyntax pred_setSyntax numSyntax
     val (s,rlang) = dest_in tm
     val reg = dest_chset(dest_regexp_lang rlang)
     val ivls = charset_intervals reg
     fun ivl_to_prop (lo,hi) =
         if lo = hi then
            ``dec ^s = ^(term_of_int lo)``
         else
         if lo = 0 then
            ``dec ^s < ^(term_of_int(hi + 1))``
         else
            ``^(term_of_int lo) <= dec ^s /\ dec ^s <= ^(term_of_int hi)``
     val slen = ``STRLEN ^s = 1``
     val property = mk_eq(tm, mk_conj(slen,list_mk_disj (map ivl_to_prop ivls)))
 in
    prove(property,prover)
 end

fun dest_in_chset tm =
 let open regexpSyntax
     val (s,rlang) = pred_setSyntax.dest_in tm
 in
     dest_chset(dest_regexp_lang rlang)
 end

(*---------------------------------------------------------------------------*)
(* Make a memo-izing version of the charset-to-interval conv.                *)
(*---------------------------------------------------------------------------*)

val in_charset_conv =
 let val conv =
      Conv.memoize
        (Lib.total dest_in_chset)
        (Redblackmap.fromList Term.compare [])
(*
          (map (fn th => (dest_in_chset(lhs(concl th)),th))
               charset_interval_lems))
*)
       (K true)
       (ERR "in_charset_conv (memoized)" "")
       pure_in_charset_conv
 in fn tm =>
      let val thm = conv tm
          val left = lhs(concl thm)
      in
        if aconv tm left then
          thm
        else
          INST (fst (match_term left tm)) thm
      end
 end;

(*---------------------------------------------------------------------------*)
(* Construct a simplification set from the memoized conversion.              *)
(*---------------------------------------------------------------------------*)

val in_charset_conv_ss =
 let val csvar = mk_var("cs",regexpSyntax.charset_ty)
     val svar = mk_var("s",stringSyntax.string_ty)
     val regexp_chset_pat = ``^svar IN regexp$regexp_lang ^(regexpSyntax.mk_chset csvar)``
 in
  simpLib.std_conv_ss
    {name = "in_charset_conv",
     conv = in_charset_conv,
     pats = [regexp_chset_pat]}
 end

(*===========================================================================*)
(* Support for proving translation validation theorem                        *)
(*===========================================================================*)

val norm_arith_relns =
 [intLib.ARITH_PROVE ``~(j <= (i:int)) <=> i < j``,
  intLib.ARITH_PROVE ``~(j < (i:int))  <=> i <= j``,
  intLib.ARITH_PROVE ``~(j >= (i:int)) <=> j < i``,
  intLib.ARITH_PROVE ``~(j > (i:int))  <=> j <= i``,
  numLib.ARITH_PROVE ``~(m < (n:num))  <=> n <= m``,
  numLib.ARITH_PROVE ``~(m <= (n:num)) <=> n < m``,
  numLib.ARITH_PROVE ``~(m > (n:num))  <=> m <= n``,
  numLib.ARITH_PROVE ``~(m >= (n:num)) <=> m < n``,
  arithmeticTheory.GREATER_DEF, arithmeticTheory.GREATER_EQ,
  integerTheory.int_gt, integerTheory.int_ge
]

val mesg_ss = list_ss
             ++ intSimps.INT_REDUCE_ss
             ++ intSimps.INT_RWTS_ss
             ++ intLib.INT_ARITH_ss
             ++ PRED_SET_ss
             ++ rewrites [ord_mod_256,CHR_ORD,ORD_CHR_RWT]
             ++ rewrites norm_arith_relns;

val regexp_lang_cat = el 2 (CONJUNCTS regexp_lang_def);
val regexp_lang_or = last (CONJUNCTS regexp_lang_def);


val splat_ss =
  mesg_ss ++ in_charset_conv_ss
          ++ rewrites [regexp_lang_cat,regexp_lang_or,IN_dot,
                       LIST_UNION_def,PULL_EXISTS,strlen_eq,dec_enc,dec_rec,
                       enc_bytes];

val var_eq_tac = rpt BasicProvers.VAR_EQ_TAC;
val subst_all_tac = SUBST_ALL_TAC;
val pop_kill_tac = pop_assum kall_tac;
val pop_keep_tac = pop_assum mp_tac;
val pop_subst_tac = pop_assum subst_all_tac;

val append_cong = Q.prove
(`!l1 l2 l3 l4.
    (l1 = l3) /\ (l2 = l4) ==> (APPEND l1 l2 = APPEND l3 l4)`,
 rw_tac bool_ss []);

(*---------------------------------------------------------------------------*)
(* Theorems about regexps and encodings                                      *)
(*---------------------------------------------------------------------------*)

val strcat_eq_tac = rpt (match_mp_tac append_cong ORELSE conj_tac)

fun constraint_tac (asl,c) =
 let val fvs = free_vars c
     val _ = if length fvs <> 1 then raise ERR "constraint_tac""" else ()
     val v = hd fvs
     fun nov tm = not (op_mem aconv v (free_vars tm))
 in rpt (WEAKEN_TAC nov)
    >> full_simp_tac splat_ss []
    >> var_eq_tac
    >> rpt (pop_assum mp_tac)
    >> rw_tac mesg_ss [deci_def,n2i_def,dec_char,dec_rec]
 end (asl,c);

fun weaken_constraint_tac (asl,c) =
 let val fvs = free_vars c
     val _ = if length fvs <> 1 then raise ERR "constraint_tac""" else ()
     val v = hd fvs
     fun nov tm = not (op_mem aconv v (free_vars tm))
 in rpt (WEAKEN_TAC nov)
 end (asl,c);

fun representable_tac (asl,c) =
 let val (enc_tm,lang_tm) = pred_setSyntax.dest_in c
     val i = rand enc_tm
     val width = rhs (concl (EVAL ``8n * ^(rand(rator enc_tm))``))
     val rep_tm = ``representable ^width ^i``
 in `^rep_tm` by rw_tac mesg_ss [representable_def]
 end (asl,c);

fun bounds_tac (asl,c) =
 let val (enc_tm,lang_tm) = pred_setSyntax.dest_in c
     val ntm = rand enc_tm
     val ntm_neg = numSyntax.is_minus ntm
     val topVal =
       let val (k,_) = numSyntax.dest_minus ntm
       in numSyntax.dest_numeral k
       end handle HOL_ERR _ => Arbnum.zero
     fun varlike tm = not (null (free_vars tm))
     val (los,his) = partition (varlike o rand) asl
     val _ = if length los <> 1 orelse length his <> 1 then
             raise ERR "bounds_tac" "unexpected constraint format" else ()
     val lo = rand (rator (hd los))
     val hi = rand (hd his)
     val n = mk_var("n",numSyntax.num)
     fun transOp t = if t ~~ intSyntax.less_tm then numSyntax.less_tm else
                     if t ~~ intSyntax.leq_tm then numSyntax.leq_tm else
                      raise ERR "bounds_tac" "transOp"
     fun transLit t =
       if ntm_neg
       then numSyntax.mk_numeral
                (Arbnum.-(topVal,
                          Arbint.toNat (Arbint.abs (intSyntax.int_of_term t))))
         else numSyntax.mk_numeral (Arbint.toNat (intSyntax.int_of_term t))
     fun transArg t = if is_var t then n else transLit t
     fun mk_nat t = list_mk_comb ((transOp##map transArg) (strip_comb t))
     val sgoal = mk_exists (n,
                  list_mk_conj (map mk_nat asl @ [mk_eq(ntm,n)]))
 in
   `^sgoal` by (exists_tac ntm >> rw_tac mesg_ss [] >> intLib.ARITH_TAC)
   >> MAP_EVERY (fn t => WEAKEN_TAC (aconv t)) asl
   >> pop_subst_tac
   >> rpt pop_keep_tac
   >> rw_tac splat_ss []
   >> intLib.ARITH_TAC
 end (asl,c)

fun flat_strcats tm =
 let open listSyntax
 in if is_append tm then
      let val (l1,l2) = dest_append tm
      in flat_strcats l1 @ flat_strcats l2
      end
    else [tm]
 end

fun insert_decoders_tac fieldreps (asl,c) =
 let val strcat_eqn = fst(dest_conj(snd(strip_exists c)))
     val (t1,t2) = dest_eq strcat_eqn
     val enc_info = zip (flat_strcats t1) (flat_strcats t2)
     val decs = map field_decoder fieldreps
     val dec_apps = map2 (curry mk_comb) decs (map fst enc_info)
 in
   MAP_EVERY EXISTS_TAC dec_apps
 end (asl,c)

fun insert_encoders_tac (asl,c) =
 let val strcat_eqn = fst(dest_conj(snd(strip_exists c)))
     val (t1,t2) = dest_eq strcat_eqn
 in
   MAP_EVERY EXISTS_TAC (flat_strcats t1)
 end (asl,c)

fun TV_TAC freps =
 rw_tac mesg_ss [regexp_lang_cat,IN_dot,PULL_EXISTS,EQ_IMP_THM]
  THENL [insert_decoders_tac freps, insert_encoders_tac]
  >> simp_tac mesg_ss []
  >- (conj_tac
      >- (strcat_eq_tac
           >> match_mp_tac enci_deci_lem >> simp_tac mesg_ss []
           >> weaken_constraint_tac
           >> full_simp_tac splat_ss [])
      >- rpt (conj_tac ORELSE constraint_tac)
     )
  >- (rpt conj_tac
      >> weaken_constraint_tac
      >> representable_tac
      >> rw_tac mesg_ss [enci_def, i2n_def]
      >> full_simp_tac mesg_ss [] >> rw_tac bool_ss []
      >> WEAKEN_TAC (can (match_term ``splat$representable w i``))
      >> bounds_tac
     );


end
