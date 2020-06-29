(*structure Contig =
struct
*)
val ERR = mk_HOL_ERR "Contig";

(*---------------------------------------------------------------------------*)
(* lvals designate locations where data lives. Exps are r-values. Since an   *)
(* lval can depend on runtime values, and rvals depend on lvals to read the  *)
(* values at locations, the types are mutually recursive.                    *)
(*---------------------------------------------------------------------------*)

datatype lval
  = VarName of string
  | RecdProj of lval * string
  | ArraySub of lval * exp
and exp
  = Loc of lval
  | intLit of int
  | ConstName of string
  | Add of exp * exp
  | Mult of exp * exp
;

datatype bexp
  = boolLit of bool
  | BLoc of lval
  | Bnot of bexp
  | Bor  of bexp * bexp
  | Band of bexp * bexp
  | Beq  of exp * exp
  | Blt  of exp * exp
  | Bgt  of exp * exp
  | Ble  of exp * exp
  | Bge  of exp * exp
  | DleA of Real.real * exp  (* Basic relations on doubles *)
  | DleB of exp * Real.real
;

(*---------------------------------------------------------------------------*)
(* Leaves of contig types. These are basically tags                          *)
(*---------------------------------------------------------------------------*)

datatype atom
  = Bool
  | Char
  | Float
  | Double
  | Signed of int
  | Unsigned of int
  | Enum of string
  | Blob
  | Scanned;

(*---------------------------------------------------------------------------*)
(* Contiguity types                                                          *)
(*---------------------------------------------------------------------------*)

datatype contig
  = Void  (* empty set of strings *)
  | Basic of atom
  | Declared of string
  | Raw of exp
  | Assert of bexp
  | Scanner of string -> (string * string) option
  | Recd of (string * contig) list
  | Array of contig * exp
  | Union of (bexp * contig) list;


(*---------------------------------------------------------------------------*)
(* lval comparison function used to build lval-keyed finite map.             *)
(*---------------------------------------------------------------------------*)

fun lval_compare pair =
 case pair
  of (VarName s1, VarName s2) => String.compare(s1,s2)
   | (VarName _, _) => LESS
   | (RecdProj _, VarName _) => GREATER
   | (RecdProj (e1,s1),RecdProj (e2,s2)) =>
       (case lval_compare(e1,e2)
         of EQUAL => String.compare(s1,s2)
	  | other => other)
   | (RecdProj _,_) => LESS
   | (ArraySub (a,b),ArraySub (c,d)) =>
       (case lval_compare(a,c)
         of EQUAL => exp_compare(b,d)
	  | other => other)
   | (ArraySub _, _) => GREATER
and
 exp_compare pair =
 case pair
  of (Loc lv1, Loc lv2) => lval_compare(lv1,lv2)
   | (Loc lv1, _) => LESS
   | (intLit _, Loc _) => GREATER
   | (intLit i, intLit j) => Int.compare(i,j)
   | (intLit i, other) => LESS
   | (ConstName _, Loc _) => GREATER
   | (ConstName _, intLit _) => GREATER
   | (ConstName s1, ConstName s2) => String.compare(s1,s2)
   | (ConstName s, _) => LESS
   | (Add _, Mult _) => LESS
   | (Add(a,b), Add(c,d)) =>
       (case exp_compare(a,c)
         of EQUAL => exp_compare(b,d)
	  | other => other)
   | (Add _, _) => GREATER
   | (Mult(a,b), Mult(c,d)) =>
       (case exp_compare(a,c)
         of EQUAL => exp_compare(b,d)
	  | other => other)
   | (Mult _, _) => GREATER
;

(*---------------------------------------------------------------------------*)
(* Expression evaluation                                                     *)
(*---------------------------------------------------------------------------*)

fun unopFn g e f =   (* Option.map f (g e); *)
  case g e
   of NONE => NONE
    | SOME v => SOME (f v)

fun binopFn g e1 e2 f =
  case g e1
   of NONE => NONE
    | SOME v1 =>
  case g e2
   of NONE => NONE
    | SOME v2 => SOME (f v1 v2);

fun firstOpt f [] = NONE
  | firstOpt f (h::t) =
    case f h
     of NONE => firstOpt f t
      | SOME x => SOME h;

fun concatOpts optlist =
    SOME(String.concat(List.map Option.valOf optlist)) handle _ => NONE;

 fun evalExp (E as (Delta,lvalMap,valFn)) exp =
 case exp
  of Loc lval =>
       (case Redblackmap.peek(lvalMap,lval)
         of NONE => NONE
          | SOME (a,s) => valFn a s)
   | intLit i =>  SOME i
   | ConstName s =>
       (case assoc1 s Delta
         of SOME(_,i) => SOME i
          | NONE => NONE)
   | Add(e1,e2) => binopFn (evalExp E) e1 e2 (curry op+)
   | Mult(e1,e2) => binopFn (evalExp E) e1 e2 (curry op*)
;

(*---------------------------------------------------------------------------*)
(* Formulas.                                                                 *)
(*---------------------------------------------------------------------------*)

fun evalBexp (E as (Delta,lvalMap,valFn,dvalFn)) bexp =
 let val evalE = evalExp (Delta,lvalMap,valFn)
   fun evalB bexp =
    case bexp
     of boolLit b => SOME b
      | BLoc lval =>
         (case Redblackmap.peek(lvalMap,lval)
           of NONE => NONE
            | SOME (Bool,s) =>
               (case valFn Bool s
                 of NONE => NONE
                  | SOME bint => (if bint = 0 then SOME false else SOME true))
            | otherwise => NONE)
      | Bnot b      => unopFn evalB b not
      | Bor(b1,b2)  => binopFn evalB b1 b2 (fn x => fn y => x orelse y)
      | Band(b1,b2) => binopFn evalB b1 b2 (fn x => fn y => x andalso y)
      | Beq (e1,e2) => binopFn evalE e1 e2 (curry op=)
      | Blt (e1,e2) => binopFn evalE e1 e2 (curry op<)
      | Bgt (e1,e2) => binopFn evalE e1 e2 (curry op>)
      | Ble (e1,e2) => binopFn evalE e1 e2 (curry op<=)
      | Bge (e1,e2) => binopFn evalE e1 e2 (curry op>=)
      | DleA (r,Loc lval) =>
         (case Redblackmap.peek(lvalMap,lval)
            of SOME (Double,s) =>
                (case dvalFn Double s
                  of NONE => NONE
                   | SOME r1 => SOME (Real.<=(r,r1)))
             | otherwise => NONE)
      | DleB (Loc lval,r) =>
         (case Redblackmap.peek(lvalMap,lval)
           of SOME (Double,s) =>
               (case dvalFn Double s
                  of NONE => NONE
                  | SOME r1 => SOME (Real.<=(r1,r)))
            | otherwise => NONE)
      | otherwise => NONE
 in
  evalB bexp
 end;

(*---------------------------------------------------------------------------*)
(* A distinctive feature of our approach is the use of lvals to describe     *)
(* locations in the message where values are stored. These values are used   *)
(* as the sizes for variable-sized arrays in the message. For convenience,   *)
(* we allow "location completion", so that partly-given locations can be     *)
(* as a convenient notation.                                                 *)
(*---------------------------------------------------------------------------*)

fun lval_append p lval =
 case lval
  of VarName s => RecdProj(p,s)
   | RecdProj (q,s) => RecdProj(lval_append p q, s)
   | ArraySub (q,dim) => ArraySub(lval_append p q, dim)
;

fun path_prefixes lval =
 case lval
  of VarName _ => [lval]
   | RecdProj (p,s) => lval :: path_prefixes p
   | ArraySub (VarName _,d) => [lval]
   | ArraySub (RecdProj(p,s),dim) => lval :: path_prefixes p
   | ArraySub (arr,dim) => lval :: path_prefixes arr (* goofy, may need to be revisited. *)


fun resolve_lval lvalMap path lval =
 let val prefixes = path_prefixes path
     val prospects = map (C lval_append lval) prefixes @ [lval]
 in firstOpt (Lib.curry Redblackmap.peek lvalMap) prospects
 end

fun resolveExp lvalMap p exp =
 case exp
  of Loc lval     => unopFn (resolve_lval lvalMap p) lval Loc
   | Add (e1,e2)  => binopFn(resolveExp lvalMap p) e1 e2 (curry Add)
   | Mult (e1,e2) => binopFn(resolveExp lvalMap p) e1 e2 (curry Mult)
   | otherwise    => SOME exp

fun resolveBexp lvalMap p bexp =
 case bexp
  of boolLit _   => SOME bexp
   | BLoc lval   => unopFn (resolve_lval lvalMap p) lval BLoc
   | Bnot b      => unopFn (resolveBexp lvalMap p) b Bnot
   | Bor(b1,b2)  => binopFn (resolveBexp lvalMap p) b1 b2 (curry Bor)
   | Band(b1,b2) => binopFn (resolveBexp lvalMap p) b1 b2 (curry Band)
   | Beq(e1,e2)  => binopFn (resolveExp lvalMap p) e1 e2 (curry Beq)
   | Blt (e1,e2) => binopFn (resolveExp lvalMap p) e1 e2 (curry Blt)
   | Bgt (e1,e2) => binopFn (resolveExp lvalMap p) e1 e2 (curry Bgt)
   | Ble (e1,e2) => binopFn (resolveExp lvalMap p) e1 e2 (curry Ble)
   | Bge (e1,e2) => binopFn (resolveExp lvalMap p) e1 e2 (curry Bge)
   | DleA (r,e)  => unopFn (resolveExp lvalMap p) e (curry DleA r)
   | DleB (e,r)  => unopFn (resolveExp lvalMap p) e (fn v => DleB(v,r))
;

(*---------------------------------------------------------------------------*)
(* Map from lvals to (atom,string) pairs, where kind signals what kind of    *)
(* type the string should be interpeted as.                                  *)
(*---------------------------------------------------------------------------*)

val empty_lvalMap
  : (lval,atom * string) Redblackmap.dict = Redblackmap.mkDict lval_compare;

(*---------------------------------------------------------------------------*)
(* Take n elements off the front of a string (list, resp.) if possible.      *)
(*---------------------------------------------------------------------------*)

fun tdrop n s =
 let open Substring
     val (ss1,ss2) = splitAt(extract(s,0,NONE),n)
 in SOME (string ss1, string ss2)
 end
 handle _ => NONE;

fun take_drop n list =
    SOME(List.take(list, n),List.drop(list, n)) handle _ => NONE


(*---------------------------------------------------------------------------*)
(* substFn is given an assignment for a contig and applies it to the contig, *)
(* yielding a string.                                                        *)
(*---------------------------------------------------------------------------*)

fun substFn E theta path contig =
 let val (Consts,Decls,atomWidth,valFn,dvalFn) = E
     fun thetaFn lval = Option.map snd (Redblackmap.peek(theta,lval))
 in
  case contig
   of Void     => NONE
    | Basic _  => thetaFn path  (* Should check expected width and actual? *)
    | Raw _    => thetaFn path
    | Assert b =>
       (case resolveBexp theta path b
         of NONE => NONE
          | SOME b' =>
        case evalBexp (Consts,theta,valFn,dvalFn) b'
         of SOME  true => SOME ""
          | otherwise => NONE)
    | Scanner _ => thetaFn path
    | Declared name => substFn E theta path (assoc name Decls)
    | Recd fields =>
       let fun fieldFn (fName,c) = substFn E theta (RecdProj(path,fName)) c
       in concatOpts (List.map fieldFn fields)
       end
    | Array (c,exp) =>
       (case resolveExp theta path exp
         of NONE => NONE
          | SOME exp' =>
        let val dim = Option.valOf (evalExp (Consts,theta,valFn) exp')
            fun indexFn i = substFn E theta (ArraySub(path,intLit i)) c
        in concatOpts (List.map indexFn (upto 0 (dim - 1)))
        end)
   | Union choices =>
       let fun choiceFn(bexp,c) =
             (case resolveBexp theta path bexp
               of NONE => false
                | SOME bexp' =>
                    Option.valOf(evalBexp (Consts,theta,valFn,dvalFn) bexp'))
       in case List.filter choiceFn choices
           of [(_,c)] => substFn E theta path c
            | otherwise => NONE
       end
 end
;

(*---------------------------------------------------------------------------*)
(* Matcher in worklist style                                                 *)
(*---------------------------------------------------------------------------*)

fun matchFn E (state as (worklist,s,theta)) =
 let val (Consts,Decls,atomWidth,valFn,dvalFn) = E
 in
 case worklist
  of [] => SOME (s,theta)
   | (_,Void)::_ => NONE
   | (path,Basic a)::t =>
       (case tdrop (atomWidth a) s
         of NONE => NONE
          | SOME (segment,rst) =>
              matchFn E (t,rst,
                         Redblackmap.insert(theta,path,(a,segment))))
   | (path,Declared name)::t => matchFn E ((path,assoc name Decls)::t,s,theta)
   | (path,Raw exp)::t =>
       (case resolveExp theta path exp
         of NONE => NONE
          | SOME exp' =>
        let val width = Option.valOf (evalExp (Consts,theta,valFn) exp')
        in case tdrop width s
           of NONE => NONE
            | SOME (segment,rst) =>
              matchFn E (t,rst,
                         Redblackmap.insert(theta,path,(Blob,segment)))
       end)
   | (path,Assert bexp)::t =>
       (case resolveBexp theta path bexp
        of NONE => NONE
         | SOME bexp' =>
        case evalBexp (Consts,theta,valFn,dvalFn) bexp'
         of NONE => NONE
          | SOME false => NONE
          | SOME true => matchFn E (t,s,theta))
   | (path,Scanner scanFn)::t =>
      (case scanFn s
        of NONE => NONE
         | SOME(segment,rst) =>
             matchFn E (t,rst, Redblackmap.insert(theta,path,(Scanned,segment))))
   | (path,Recd fields)::t =>
       let fun fieldFn (fName,c) = (RecdProj(path,fName),c)
       in matchFn E (map fieldFn fields @ t,s,theta)
       end
   | (path,Array (c,exp))::t =>
       (case resolveExp theta path exp
         of NONE => NONE
          | SOME exp'=>
        let val dim = Option.valOf (evalExp (Consts,theta,valFn) exp')
            fun indexFn i = (ArraySub(path,intLit i),c)
       in matchFn E (map indexFn (upto 0 (dim - 1)) @ t,s,theta)
       end)
   | (path,Union choices)::t =>
       let fun choiceFn(bexp,c) =
             (case resolveBexp theta path bexp
               of NONE => false
                | SOME bexp' => Option.valOf
                                 (evalBexp (Consts,theta,valFn,dvalFn) bexp'))
       in case filter choiceFn choices
           of [(_,c)] => matchFn E ((path,c)::t,s,theta)
            | otherwise => NONE
       end
 end
;

fun match E contig s = matchFn E ([(VarName"root",contig)],s,empty_lvalMap);

fun check_match E contig s =
 case match E contig s
  of NONE => raise ERR "check_match" "no match"
  |  SOME(s2,theta) =>
      case substFn E theta (VarName"root") contig
       of SOME s1 => (s1^s2 = s)
       |  NONE => raise ERR "check_match" "substFn failed"

(*---------------------------------------------------------------------------*)
(* Version of matchFn that checks assertions, acting as a predicate on       *)
(* messages.                                                                 *)
(*---------------------------------------------------------------------------*)

fun predFn E (state as (worklist,s,theta)) =
 let val (Consts,Decls,atomWidth,valFn,dvalFn) = E
 in
 case worklist
  of [] => PASS (s,theta)
   | (path,Void)::t => FAIL state
   | (path,Basic a)::t =>
       (case tdrop (atomWidth a) s
         of NONE => FAIL state
          | SOME (segment,rst) =>
              predFn E (t,rst,Redblackmap.insert(theta,path,(a,segment))))
   | (path,Declared name)::t => predFn E ((path,assoc name Decls)::t,s,theta)
   | (path,Raw exp)::t =>
       (case resolveExp theta path exp
         of NONE => FAIL state
          | SOME exp' =>
        let val width = Option.valOf (evalExp (Consts,theta,valFn) exp')
        in case tdrop width s
           of NONE => FAIL state
            | SOME (segment,rst) =>
              predFn E (t,rst, Redblackmap.insert(theta,path,(Blob,segment)))
        end)
   | (path,Assert bexp)::t =>
       (case resolveBexp theta path bexp
        of NONE => FAIL state
         | SOME bexp' =>
        case evalBexp (Consts,theta,valFn,dvalFn) bexp'
         of SOME true => predFn E (t,s,theta)
          | otherwise => FAIL state)
   | (path,Scanner scanFn)::t =>
      (case scanFn s
        of NONE => FAIL state
         | SOME(segment,rst) =>
             predFn E (t,rst, Redblackmap.insert(theta,path,(Scanned,segment))))
   | (path,Recd fields)::t =>
       let fun fieldFn (fName,c) = (RecdProj(path,fName),c)
       in predFn E (map fieldFn fields @ t,s,theta)
       end
   | (path,Array (c,exp))::t =>
       (case resolveExp theta path exp
         of NONE => FAIL state
          | SOME exp'=>
        let val dim = Option.valOf (evalExp (Consts,theta,valFn) exp')
            fun indexFn i = (ArraySub(path,intLit i),c)
        in predFn E (map indexFn (upto 0 (dim - 1)) @ t,s,theta)
        end)
   | (path,Union choices)::t =>
       let fun choiceFn(bexp,c) =
             (case resolveBexp theta path bexp
               of NONE => false
                | SOME bexp' => Option.valOf
                                 (evalBexp (Consts,theta,valFn,dvalFn) bexp'))
       in case filter choiceFn choices
           of [(_,c)] => predFn E ((path,c)::t,s,theta)
            | otherwise => FAIL state
       end
 end
;

fun wellformed E contig s =
 case predFn E ([(VarName"root",contig)],s,empty_lvalMap)
  of PASS _ => true
   | FAIL _ => false;

(*---------------------------------------------------------------------------*)
(* Parsing. First define a universal target type to parse into. It provides  *)
(* structure, but the leaf elements are left uninterpreted.                  *)
(*---------------------------------------------------------------------------*)

datatype ptree
  = LEAF of atom * string
  | RECD of (string * ptree) list
  | ARRAY of ptree list
;

(*---------------------------------------------------------------------------*)
(* Environments:                                                             *)
(*                                                                           *)
(*   Consts : maps constant names to integers                                *)
(*   Decls  : maps names to previously declared contigs                      *)
(*   atomWidth : gives width info for basic types                            *)
(*   valFn  : function for computing an integer value                        *)
(*            stored at the designated location in the string.               *)
(*   dvalFn : function for computing a double value                          *)
(*            stored at the designated location in the string.               *)
(*                                                                           *)
(* parseFn operates on a state tuple (stk,s,lvmap)                           *)
(*                                                                           *)
(*  stk  : ptree list         ;;; parser stack                               *)
(*  s    : string             ;;; remainder of string                        *)
(* lvmap : (lval |-> string)  ;;; previously seen values, accessed by path   *)
(*                                                                           *)
(* which is wrapped in the error monad.                                      *)
(*---------------------------------------------------------------------------*)

fun parseFn E path contig state =
 let val (Consts,Decls,atomWidth,valFn,dvalFn) = E
     val (stk,s,lvmap) = state
 in
 case contig
  of Void => NONE
   | Basic a =>
       let val awidth = atomWidth a
       in case tdrop awidth s
         of NONE => NONE
          | SOME (segment,rst) =>
             SOME(LEAF(a,segment)::stk,rst,
                  Redblackmap.insert(lvmap,path,(a,segment)))
       end
   | Declared name => parseFn E path (assoc name Decls) state
   | Raw exp =>
       let val exp' = resolveExp lvmap path exp
           val width = evalExp (Consts,lvmap,valFn) exp'
       in
         case tdrop width s
         of NONE => NONE
          | SOME (segment,rst) =>
              SOME(LEAF(Blob,segment)::stk,rst,
                   Redblackmap.insert(lvmap,path,(Blob,segment)))
       end
   | Assert bexp =>
       let val bexp' = resolveBexp lvmap path bexp
           val tval = evalBexp (Consts,lvmap,valFn,dvalFn) bexp'
       in
         if tval then SOME state
         else (print "Assertion failure"; NONE)
       end
   | Scanner scanFn =>
      (case scanFn s
        of NONE => raise ERR "parseFn" "Scanner failed"
         | SOME(segment,rst) =>
              SOME(LEAF(Scanned,segment)::stk,rst,
                   Redblackmap.insert(lvmap,path,(Scanned,segment))))
   | Recd fields =>
       let fun fieldFn fld NONE = NONE
             | fieldFn (fName,c) (SOME st) = parseFn E (RecdProj(path,fName)) c st
          fun is_assert (s,Assert _) = true
            | is_assert other = false
          val fields' = filter (not o is_assert) fields
       in case rev_itlist fieldFn fields (SOME state)
           of NONE => NONE
            | SOME (stk',s',lvmap') =>
               case take_drop (length fields') stk'
                of NONE => NONE
                 | SOME(elts,stk'') =>
                     SOME(RECD (zip (map fst fields') (rev elts))::stk'',
                          s', lvmap')
       end
   | Array (c,exp) =>
       let val exp' = resolveExp lvmap path exp
           val dim = evalExp (Consts,lvmap,valFn) exp'
           fun indexFn i NONE = NONE
             | indexFn i (SOME state) = parseFn E (ArraySub(path,intLit i)) c state
       in case rev_itlist indexFn (upto 0 (dim - 1)) (SOME state)
           of NONE => NONE
            | SOME (stk',s',lvmap') =>
               case take_drop dim stk'
                of NONE => NONE
                 | SOME(elts,stk'') =>
                     SOME(ARRAY (rev elts)::stk'', s', lvmap')
       end
   | Union choices =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolveBexp lvmap path bexp
             in evalBexp (Consts,lvmap,valFn,dvalFn) bexp'
             end
       in case filter choiceFn choices
           of [(_,c)] => parseFn E path c state
            | otherwise => raise ERR "parseFn" "Union: expected exactly one successful choice"
       end
 end
;

fun parse E contig s =
 case parseFn E (VarName"root") contig ([],s,empty_lvalMap)
  of SOME ([ptree],remaining,lvMap) => (ptree,remaining,lvMap)
   | SOME otherwise => raise ERR "parse" "expected stack of size 1"
   | NONE => raise ERR "parse" ""
;

(*---------------------------------------------------------------------------*)
(* Generation of strings conforming to a contig.                             *)
(*---------------------------------------------------------------------------*)

(* Using IntInf instead of Int.int

fun twoE i = IntInf.pow (IntInf.fromInt 2,i);

fun defaultNatRange n = (IntInf.fromInt 0,twoE n-1);

fun defaultIntRange n =
 let val m = n-1
 in (IntInf.~(twoE m), IntInf.-(twoE m,IntInf.fromInt 1))
 end;
*)

fun twoE i = Int.fromLarge (IntInf.pow (IntInf.fromInt 2,i));

fun defaultNatRange n = (0,twoE n-1);

fun defaultIntRange n =
 let val m = n-1
 in (~(twoE m), twoE m - 1)
 end;

val default_Bool_range = defaultNatRange 1;
val default_Char_range = defaultNatRange 8;
val default_Enum_range = defaultNatRange 32;  (* uxas wants 4 bytes for enums *)
val default_u8_range   = defaultNatRange 8;
val default_u16_range  = defaultNatRange 16;
val default_u32_range  = defaultNatRange 32;
val default_u64_range  = defaultNatRange 61;  (* convenient for now, but goal is 64 *)

val default_i16_range = defaultIntRange 16;
val default_i32_range = defaultIntRange 32;
val default_i64_range = defaultIntRange 61;  (* convenient for now, but goals is 64 *)

fun atom_range atm =
 case atm
  of Bool => default_Bool_range
   | Char => default_Char_range
   | Enum s => default_Enum_range
   | Signed i =>
      (if i = 2 then default_i16_range else
       if i = 4 then default_i32_range else
       if i = 8 then default_i64_range
       else raise ERR "atom_range" "unexpected number of bytes")
   | Unsigned i =>
      (if i = 1 then default_u8_range else
       if i = 2 then default_u16_range else
       if i = 4 then default_u32_range else
       if i = 8 then default_u64_range
       else raise ERR "atom_range" "unexpected number of bytes")
   | Float  => default_u32_range
   | Double => default_u64_range
   | Blob => raise ERR "atom_range" "Blob"
   | Scanned => raise ERR "atom_range" "Scanned"
;

fun intersect_intervals (lo1,hi1) (lo2,hi2) = (Int.max(lo1,lo2),Int.min(hi1,hi2));

fun dest_endpoints (intLit m,intLit n) = if m <= n then SOME(m,n) else NONE
  | dest_endpoints otherwise = NONE;

fun last_path_elt path =
 case path
  of VarName s => s
   | RecdProj(_,s) => s
   | ArraySub _ => raise ERR "last_path_elt" "ArraySub not handled yet";

fun vname_of (Loc(VarName s)) = s
  | vname_of otherwise = raise ERR "vname_of" "expected Loc(VarName ...)"

fun specified_field path e = (last_path_elt path = vname_of e)

fun gen_segment a path bexp (Consts,lvalMap,valFn,repFn,gn) =
 let val E = (Consts,lvalMap,valFn)
     fun randElt (lo,hi) = Random.range (lo,hi+1) gn
     fun randRealElt (lo,hi) =
       let open Real
       in if lo <= hi then
              lo + (Random.random gn * (hi - lo))
          else raise ERR "randRealElt" ""
       end
     fun randRep a = repFn a (randElt (atom_range a))
 in
 case bexp
  of Beq (e1,e2) =>
       if specified_field path e1 then
          repFn a (evalExp E e2)
       else
       if specified_field path e2 then
          repFn a (evalExp E e1)
       else randRep a
   | Blt (e1,e2) =>
       if specified_field path e1 then
          let val i = evalExp E e2
          in if 0 < i then
               repFn a (randElt (0,i-1))
             else
               randRep a
          end
       else randRep a
   | Ble (e1,e2) =>
       if specified_field path e1 then
          let val i = evalExp E e2
          in if 0 <= i then
               repFn a (randElt (0,i))
             else
               randRep a
          end
       else randRep a
   | Band(Ble(e1,e2),Ble(e3,e4)) =>
      if specified_field path e2 andalso e2=e3 then
        let val i = evalExp E e1
            val j = evalExp E e4
        in if i <= j then
             repFn a (randElt (i,j))
            else
             randRep a
        end
      else randRep a
   | Band(DleA(r1,e2),DleB(e3,r2)) =>
      if specified_field path e2 andalso e2=e3 then
        (if Real.<=(r1,r2) then
            Byte.bytesToString
              (PackRealBig.toBytes
                 (randRealElt (r1,r2)))
         else randRep a)
      else randRep a
   | otherwise => raise ERR "gen_segment" "unexpected case"
end
;


(*---------------------------------------------------------------------------*)
(* Counterpart to matchFn that generates random, but conforming, messages.   *)
(*---------------------------------------------------------------------------*)

fun randFn E (worklist,theta,acc) =
 let val (Consts,Decls,atomWidth,valFn,dvalFn,repFn,scanRandFn,gn) = E
 in
 case worklist
  of [] => rev acc
   | (path,Void)::t => raise ERR "randFn" "Void construct encountered"
   | (path,Basic a)::(_,Assert bexp)::t =>
       let val env = (Consts,theta,valFn,repFn,gn)
           val segment = gen_segment a path bexp env
       in
          randFn E (t,Redblackmap.insert(theta,path,(a,segment)),segment :: acc)
       end
  |  (path,Basic a)::t =>
       let fun randElt (lo,hi) = Random.range (lo,hi+1) gn
           val segment = repFn a (randElt (atom_range a))
       in
          randFn E (t,Redblackmap.insert(theta,path,(a,segment)),segment::acc)
       end
   | (path,Raw exp)::t =>
       let val exp' = resolveExp theta path exp
           val width = evalExp (Consts,theta,valFn) exp'
           val elts = List.tabulate (width, fn i => Random.range default_u8_range gn)
           val segment = String.implode (List.map Char.chr elts)
       in randFn E (t, Redblackmap.insert(theta,path,(Blob,segment)),segment::acc)
       end
   | (path,Declared name)::t => randFn E ((path,assoc name Decls)::t,theta,acc)
   | (path,Assert bexp)::t =>
       let val bexp' = resolveBexp theta path bexp
       in if evalBexp (Consts,theta,valFn,dvalFn) bexp'
            then randFn E (t,theta,acc)
            else raise ERR "randFn" "Assert failure"
       end
   | (path,Scanner scanFn)::t =>
       let val segment = scanRandFn path
       in randFn E (t, Redblackmap.insert(theta,path,(Scanned,segment)),segment::acc)
       end
   | (path,Recd fields)::t =>
       let fun fieldFn (fName,c) = (RecdProj(path,fName),c)
       in randFn E (map fieldFn fields @ t,theta,acc)
       end
   | (path,Array (c,exp))::t =>
       let val exp' = resolveExp theta path exp
           val dim = evalExp (Consts,theta,valFn) exp'
           fun indexFn i = (ArraySub(path,intLit i),c)
       in randFn E (map indexFn (upto 0 (dim - 1)) @ t,theta,acc)
       end
   | (path,Union choices)::t =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolveBexp theta path bexp
             in evalBexp (Consts,theta,valFn,dvalFn) bexp'
             end
       in case filter choiceFn choices
           of [(_,c)] => randFn E ((path,c)::t,theta,acc)
            | otherwise => raise ERR "randFn" "Union: require exactly one successful choice"
       end
 end
;

fun Interval fName (i,j) =
  Band(Ble(intLit i,Loc(VarName fName)),
       Ble(Loc(VarName fName),intLit j));

(* -------------------------------------------------------------------------- *)
(* Needs fixing so that                                                                            *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

fun delete_asserts Decls contig =
 case contig
  of Declared s => delete_asserts Decls (assoc s Decls)
   | Assert _ => SKIP
   | Recd fields =>
      let fun is_empty (s,Recd[]) = true
            | is_empty otherwise = false
          fun is_assert (s,Assert _) = true
            | is_assert other = false
          fun predUnion P1 P2 x = P1 x orelse P2 x
          fun fieldFn (s,c) = (s, delete_asserts Decls c)
      in Recd (filter (not o predUnion is_empty is_assert)
                      (map fieldFn fields))
      end
   | Array (c,e) => Array (delete_asserts Decls c, e)
   | Union bclist => Union(map (fn (b,c) => (b, delete_asserts Decls c)) bclist)
   | otherwise => contig;


(*---------------------------------------------------------------------------*)
(* Pretty printing                                                           *)
(*---------------------------------------------------------------------------*)

fun paren i j s1 s2 ps =
 let open PP
 in if i < j then
      block CONSISTENT 0 ps
    else
      block INCONSISTENT (size s1)
           (add_string s1 :: ps @ [add_string s2])
end;

fun pp_binop opr x y =
 let open PP
 in  paren 0 0 "(" ")"
	[x, add_string (" "^opr), add_break(1,0), y]
 end

local open Portable PP
in
fun pp_lval lval =
   case lval
    of VarName s => add_string s
     | RecdProj (p,s) =>
        block INCONSISTENT 0 [pp_lval p, add_string".",add_string s]
     | ArraySub (lval,d) =>
        block CONSISTENT 1 [pp_lval lval, paren 0 0 "[" "]" [pp_exp d]]
 and pp_exp exp =
   case exp
    of Loc lval => pp_lval lval
     | intLit i => add_string (Int.toString i)
     | ConstName s => add_string s
     | Add (e1,e2) => pp_binop "+" (pp_exp e1) (pp_exp e2)
     | Mult (e1,e2) => pp_binop "*" (pp_exp e1) (pp_exp e2)
end


fun pp_bexp bexp =
 let open PP
     fun pp_real r = add_string(Real.toString r)
 in
   case bexp
    of boolLit b => add_string (Bool.toString b)
     | BLoc lval => pp_lval lval
     | Bnot b    => block CONSISTENT 0
                     [add_string"not", paren 0 0 "(" ")" [pp_bexp b]]
     | Bor(b1,b2)  => pp_binop "or" (pp_bexp b1) (pp_bexp b2)
     | Band(b1,b2) => pp_binop "and" (pp_bexp b1) (pp_bexp b2)
     | Beq (e1,e2) => pp_binop "="  (pp_exp e1) (pp_exp e2)
     | Blt (e1,e2) => pp_binop "<"  (pp_exp e1) (pp_exp e2)
     | Bgt(e1,e2)  => pp_binop ">"  (pp_exp e1) (pp_exp e2)
     | Ble(e1,e2)  => pp_binop "<=" (pp_exp e1) (pp_exp e2)
     | Bge(e1,e2)  => pp_binop ">=" (pp_exp e1) (pp_exp e2)
     | DleA(r,e)   => pp_binop "<=" (pp_real r) (pp_exp e)
     | DleB(e,r)   => pp_binop "<=" (pp_exp e) (pp_real r)
 end;

fun pp_atom atom =
 let open PP
 in case atom
     of Bool => add_string "Bool"
      | Char => add_string "Char"
      | Float => add_string "Float"
      | Double => add_string "Double"
      | Signed i => add_string ("i"^Int.toString (i*8))
      | Unsigned i => add_string ("u"^Int.toString (i*8))
      | Enum s   => add_string ("Enum-"^s)
      | Blob    => add_string "Raw"
      | Scanned => add_string "Scanned"
 end;

fun is_recd (Recd _) = true
  | is_recd otherwise = false;

fun pp_contig contig =
 let open PP
 in
   case contig
    of Void => add_string "Void"
     | Basic atom => pp_atom atom
     | Declared s => add_string s
     | Raw exp => block CONSISTENT 1
            [add_string "Raw", add_string "(", pp_exp exp, add_string ")"]
     | Assert bexp => block CONSISTENT 1
            [add_string "Assert", add_string "(", pp_bexp bexp, add_string ")"]
     | Scanner _ =>  add_string "<scan-fn>"
     | Recd fields =>
        let fun pp_field (s,c) = block CONSISTENT 0
               [block CONSISTENT 1
                  [add_string s, add_string " :", add_break(1,0), pp_contig c],
                NL]
        in
          block CONSISTENT 1
             ([add_string "{" ] @ map pp_field fields @ [add_string "}"])
        end
     | Array (c,e) => block CONSISTENT 1
             [pp_contig c, add_string " [", pp_exp e, add_string "]"]
     | Union choices =>
        let fun pp_choice (bexp,c) = block CONSISTENT 0
              [block CONSISTENT 0
                 [add_string "(", pp_bexp bexp, add_string " -->",
                  add_break(1,2), pp_contig c,add_string ")"], NL]
        in
          block CONSISTENT 2
            [add_string "Union {", NL,
             block CONSISTENT 0 (map pp_choice choices),
             add_string "}"]
        end
 end

val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn lval => pp_lval lval);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn exp => pp_exp exp);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn bexp => pp_bexp bexp);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn atm => pp_atom atm);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn contig => pp_contig contig);



(* -------------------------------------------------------------------------- *)
(* Add enum contig to environment: the enum is a Basic thingy, and the        *)
(* constants (with associated numeric values) get added to the Consts.        *)
(* -------------------------------------------------------------------------- *)

fun add_enum_decl E (s,bindings) =
 let val (Consts,Decls,atomWidth,valFn,dvalFn) = E
     val enum = Basic(Enum s)
     val bindings' = map (fn (name,i) => (s^"'"^name,i)) bindings
 in
   (bindings' @ Consts, (s,enum)::Decls, atomWidth,valFn,dvalFn)
 end



(* -------------------------------------------------------------------------- *)
(* Widths for basic items, for UXAS. Only interesting thing is that enums are *)
(* 4 bytes and that bool is special: not an ordinary enum, since it takes     *)
(* 1 byte.                                                                    *)
(* -------------------------------------------------------------------------- *)

fun uxas_atom_width atm =
 case atm
  of Bool       => 1
   | Char       => 1
   | Signed i   => i
   | Unsigned i => i
   | Float      => 4
   | Double     => 8
   | Enum _     => 4
   | other      => raise ERR "atom_width" "unknown width of Raw or Scanner"
;

(* -------------------------------------------------------------------------- *)
(* Some basic contig types.                                                   *)
(* -------------------------------------------------------------------------- *)

val bool = Basic Bool;
val u8  = Basic(Unsigned 1);
val u16 = Basic(Unsigned 2);
val u32 = Basic(Unsigned 4);
val u64 = Basic(Unsigned 8);
val i16 = Basic(Signed 2);
val i32 = Basic(Signed 4);
val i64 = Basic(Signed 8);
val f32 = Basic Float;
val f64 = Basic Double;

(*---------------------------------------------------------------------------*)
(* A way of expressing the language consisting of just the empty string      *)
(*---------------------------------------------------------------------------*)

val SKIP = Recd [];


(*---------------------------------------------------------------------------*)
(* Support for the Scanner constructor. The end delimiter is left on the     *)
(* string.                                                                   *)
(*---------------------------------------------------------------------------*)

fun scanTo delim s =
 let open Substring
     val k = String.size delim
     val ss = full s
     val (ss1,ss2) = position delim ss
 in if isEmpty ss2 then
       NONE
    else
      let val (_,_,j) = base ss1
      in SOME ((string##string)(splitAt (ss,j+k)))
      end
 end

val scanCstring = scanTo (String.str(Char.chr 0));

end (* Contig *)
