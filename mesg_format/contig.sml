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

val ERR = mk_HOL_ERR "contig";

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

val empty_lvalMap : (lval,string) Redblackmap.dict = Redblackmap.mkDict lval_compare ;

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


fun evalExp (E as (Delta,lvalMap,valueFn)) exp =
 case exp
  of Loc lval =>
       (case Redblackmap.peek(lvalMap,lval)
         of SOME s => valueFn s
          | NONE => raise ERR "evalExp" "Lval binding failure")
   | intLit i => i
   | ConstName s =>
     (case assoc1 s Delta
       of SOME(_,i) => i
        | NONE => raise ERR "evalExp"
            ("unable to find value for constant named "^Lib.quote s))
   | Add(e1,e2) => evalExp E e1 + evalExp E e2
   | Mult(e1,e2) => evalExp E e1 * evalExp E e2
;

(*---------------------------------------------------------------------------*)
(* Atomic formulas                                                           *)
(*---------------------------------------------------------------------------*)

datatype bexp
  = boolLit of bool
  | Bnot of bexp
  | Bor  of bexp * bexp
  | Band of bexp * bexp
  | Beq  of exp * exp
  | Blt  of exp * exp
  | Bgtr of exp * exp
  | Bleq of exp * exp
  | Bgeq of exp * exp
;

fun evalBexp E bexp =
 case bexp
  of boolLit b   => b
   | Bnot b      => not (evalBexp E b)
   | Bor(b1,b2)  => (evalBexp E b1 orelse evalBexp E b2)
   | Band(b1,b2) => (evalBexp E b1 andalso evalBexp E b2)
   | Beq (e1,e2) => (evalExp E e1 = evalExp E e2)
   | Blt (e1,e2) => (evalExp E e1 < evalExp E e2)
   | Bgtr(e1,e2) => (evalExp E e1 > evalExp E e2)
   | Bleq(e1,e2) => (evalExp E e1 <= evalExp E e2)
   | Bgeq(e1,e2) => (evalExp E e1 >= evalExp E e2)
;

(*---------------------------------------------------------------------------*)
(* Contiguity types                                                          *)
(*---------------------------------------------------------------------------*)

datatype atom
  = Bool
  | Char
  | Float
  | Double
  | Signed of int
  | Unsigned of int
  | Enum of string * (string * int) list;

datatype contig
  = Basic of atom
  | Declared of string
  | Raw of exp
  | Scanner of (string -> (string * string) option)
  | Recd of (string * contig) list
  | Array of contig * exp
  | Union of (bexp * contig) list;

(*---------------------------------------------------------------------------*)
(* A distinctive feature of our approach is the use of lvals to describe     *)
(* locations in the message where values are stored. These values are used   *)
(* as the sizes for variable-sized arrays in the message. For convenience,   *)
(* we allow "location completion", so that partly-given locations can be     *)
(* as a convenient notation.                                                 *)
(*---------------------------------------------------------------------------*)

fun resolve_lvals lvalMap path lval =
 let val prefixes = path_prefixes path
     val prospects = map (C lval_append lval) prefixes @ [lval]
 in Lib.first (can (curry Redblackmap.find lvalMap)) prospects
 end
 handle HOL_ERR _ => raise ERR "resolve_lvals" "unsuccessful";

fun resolve_exp_lvals lvalMap path exp =
 case exp
  of Loc lval => Loc(resolve_lvals lvalMap path lval)
   | Add (e1,e2) => Add(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | Mult (e1,e2) => Mult(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | otherwise => exp

fun resolve_bexp_lvals lvalMap path bexp =
 case bexp
  of boolLit _   => bexp
   | Bnot b      => Bnot(resolve_bexp_lvals lvalMap path b)
   | Bor(b1,b2)  => Bor(resolve_bexp_lvals lvalMap path b1,resolve_bexp_lvals lvalMap path b2)
   | Band(b1,b2) => Band(resolve_bexp_lvals lvalMap path b1,resolve_bexp_lvals lvalMap path b2)
   | Beq(e1,e2)  => Beq(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | Blt (e1,e2) => Blt(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | Bgtr(e1,e2) => Bgtr(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | Bleq(e1,e2) => Bleq(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | Bgeq(e1,e2) => Bgeq(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
;

(*---------------------------------------------------------------------------*)
(* Take n elements off the front of a string, if possible.                   *)
(*---------------------------------------------------------------------------*)

fun tdrop n s =
 let open Substring
     val (ss1,ss2) = splitAt(extract(s,0,NONE),n)
 in SOME (string ss1, string ss2)
 end
 handle _ => NONE;

(*---------------------------------------------------------------------------*)
(* Environments:                                                             *)
(*                                                                           *)
(*   Consts : maps constant names to integers                                *)
(*   Decls  : maps names to previously declared contigs                      *)
(*   atomicWidths : gives width info for basic types                         *)
(*   valueFn : function for computing a value                                *)
(*             stored at the designated location in the string.              *)
(*                                                                           *)
(* segFn operates on a state tuple (segs,s,wvMap)                            *)
(*                                                                           *)
(*  segs : (string * int) list  ;;; list of segments and associated values   *)
(*  s    :  string              ;;; remainder of string                      *)
(* wvMap : (lval |-> int)       ;;; previously seen values, accessed by path *)
(*                                                                           *)
(* which is wrapped in the error monad.                                      *)
(*---------------------------------------------------------------------------*)

fun segFn E path contig state =
 let val (Consts,Decls,atomicWidths,valueFn) = E
     val (segs,s,WidthValMap) = state
 in
 case contig
  of Basic a =>
       let val awidth = atomicWidths a
       in case tdrop awidth s
         of NONE => NONE
          | SOME (segment,rst) =>
             SOME(segs@[segment],rst,
                  Redblackmap.insert(WidthValMap,path,segment))
       end
   | Declared name => segFn E path (assoc name Decls) state
   | Raw exp =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val width = evalExp (Consts,WidthValMap,valueFn) exp'
       in
         case tdrop width s
         of NONE => NONE
          | SOME (segment,rst) =>
              SOME(segs@[segment],rst,
                   Redblackmap.insert(WidthValMap,path,segment))
       end
   | Scanner scanFn =>
      (case scanFn s
        of NONE => raise ERR "segFn" "Scanner failed"
         | SOME(segment,rst) =>
              SOME(segs@[segment],rst,
                   Redblackmap.insert(WidthValMap,path,segment)))
   | Recd fields =>
       let fun fieldFn fld NONE = NONE
             | fieldFn (fName,c) (SOME st) = segFn E (RecdProj(path,fName)) c st
       in rev_itlist fieldFn fields (SOME state)
       end
   | Array (c,exp) =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val dim = evalExp (Consts,WidthValMap,valueFn) exp'
           fun indexFn i NONE = NONE
             | indexFn i (SOME state) = segFn E (ArraySub(path,intLit i)) c state
       in rev_itlist indexFn (upto 0 (dim - 1)) (SOME state)
       end
   | Union choices =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolve_bexp_lvals WidthValMap path bexp
             in evalBexp (Consts,WidthValMap,valueFn) bexp'
             end
       in case List.find choiceFn choices
           of NONE => raise ERR "segFn" "Union: no choices possible"
            | SOME(bexp,c) => segFn E path c state
       end
 end
;

fun segments E contig s = segFn E (VarName"root") contig ([],s,empty_lvalMap);

fun atomic_widths atm =
 case atm
  of Bool       => 1
   | Char       => 1
   | Signed i   => i
   | Unsigned i => i
   | Float      => 4
   | Double     => 8
   | Enum _     => 1
;

val u8  = Basic(Unsigned 1);
val u16 = Basic(Unsigned 2);
val u32 = Basic(Unsigned 4);
val u64 = Basic(Unsigned 8);
val i16 = Basic(Signed 2);
val i32 = Basic(Signed 4);
val i64 = Basic(Signed 8);

fun add_enum_decl E (s,bindings) =
 let val (Consts,Decls,atomicWidths,valueFn) = E
     val enum = Basic(Enum(s,bindings))
     val bindings' = map (fn (name,i) => (s^"'"^name,i)) bindings
 in
   (bindings' @ Consts, (s,enum)::Decls, atomicWidths,valueFn)
 end


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
 in
   case bexp
    of boolLit b => add_string (Bool.toString b)
     | Bnot b    => block CONSISTENT 0
                     [add_string"not", paren 0 0 "(" ")" [pp_bexp b]]
     | Bor(b1,b2)  => pp_binop "or" (pp_bexp b1) (pp_bexp b2)
     | Band(b1,b2) => pp_binop "and" (pp_bexp b1) (pp_bexp b2)
     | Beq (e1,e2) => pp_binop "=" (pp_exp e1) (pp_exp e2)
     | Blt (e1,e2) => pp_binop "<" (pp_exp e1) (pp_exp e2)
     | Bgtr(e1,e2) => pp_binop ">" (pp_exp e1) (pp_exp e2)
     | Bleq(e1,e2) => pp_binop "<=" (pp_exp e1) (pp_exp e2)
     | Bgeq(e1,e2) => pp_binop ">=" (pp_exp e1) (pp_exp e2)
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
      | Enum (s,list) => add_string s
 end;

fun pp_contig contig =
 let open PP
 in
   case contig
    of Basic atom => pp_atom atom
     | Declared s => add_string s
     | Raw exp => block CONSISTENT 1
            [add_string "Raw", add_string "(", pp_exp exp, add_string ")"]
     | Scanner _ =>  add_string "<scan-fn>"
     | Recd fields =>
        let fun pp_field (s,c) = block CONSISTENT 0
                 [add_string s, add_string " : ", pp_contig c,NL]
        in
          block CONSISTENT 1
             ([add_string "{" ] @ map pp_field fields @ [add_string "}"])
        end
     | Array (c,e) => block CONSISTENT 1
             [pp_contig c, add_string " [", pp_exp e, add_string "]"]
     | Union choices =>
        let fun pp_choice (bexp,c) = block CONSISTENT 2
                 [add_string "(", pp_bexp bexp, add_string " -->",
                  add_break(1,2), pp_contig c,add_string ")", NL]
        in
          block CONSISTENT 3
            ([add_string "Union {", NL] @ map pp_choice choices @ [add_string "}"])
        end
 end

val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn lval => pp_lval lval);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn exp => pp_exp exp);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn bexp => pp_bexp bexp);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn atm => pp_atom atm);
val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn contig => pp_contig contig);

(*---------------------------------------------------------------------------*)
(* Parsing. First define a universal target type to parse into. It provides  *)
(* structure, but the leaf elements are left uninterpreted.                  *)
(*---------------------------------------------------------------------------*)

datatype ptree
  = BOOL of string
  | CHAR of string
  | INT of int * string
  | UINT of int * string
  | FLOAT of string
  | DOUBLE of string
  | ENUM of string * string
  | BLOB of string
  | SCANNED of string
  | RECD of (string * ptree) list
  | ARRAY of ptree list
;

fun atom_constr atom =
case atom
 of Bool => BOOL
  | Char => CHAR
  | Float => FLOAT
  | Double => DOUBLE
  | Signed i => curry INT i
  | Unsigned i => curry UINT i
  | Enum (s,list) => curry ENUM s

fun take_drop n list =
 SOME(List.take(list, n),List.drop(list, n)) handle _ => NONE

(*---------------------------------------------------------------------------*)
(* Environments:                                                             *)
(*                                                                           *)
(*   Consts : maps constant names to integers                                *)
(*   Decls  : maps names to previously declared contigs                      *)
(*   atomicWidths : gives width info for basic types                         *)
(*   valueFn : function for computing a value                                *)
(*             stored at the designated location in the string.              *)
(*                                                                           *)
(* segFn operates on a state tuple (segs,s,wvMap)                            *)
(*                                                                           *)
(*  stk : ptree list        ;;; parser stack                                 *)
(*  s    :  string          ;;; remainder of string                          *)
(* wvMap : (lval |-> int)   ;;; previously seen values, accessed by path     *)
(*                                                                           *)
(* which is wrapped in the error monad.                                      *)
(*---------------------------------------------------------------------------*)

fun parseFn E path contig state =
 let val (Consts,Decls,atomicWidths,valueFn) = E
     val (stk,s,WidthValMap) = state
 in
 case contig
  of Basic a =>
       let val awidth = atomicWidths a
           val constrFn = atom_constr a
       in case tdrop awidth s
         of NONE => NONE
          | SOME (segment,rst) =>
             SOME(constrFn segment::stk,rst,
                  Redblackmap.insert(WidthValMap,path,segment))
       end
   | Declared name => parseFn E path (assoc name Decls) state
   | Raw exp =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val width = evalExp (Consts,WidthValMap,valueFn) exp'
       in
         case tdrop width s
         of NONE => NONE
          | SOME (segment,rst) =>
              SOME(BLOB segment::stk,rst,
                   Redblackmap.insert(WidthValMap,path,segment))
       end
   | Scanner scanFn =>
      (case scanFn s
        of NONE => raise ERR "parseFn" "Scanner failed"
         | SOME(segment,rst) =>
              SOME(SCANNED segment::stk,rst,
                   Redblackmap.insert(WidthValMap,path,segment)))
   | Recd fields =>
       let fun fieldFn fld NONE = NONE
             | fieldFn (fName,c) (SOME st) = parseFn E (RecdProj(path,fName)) c st
       in case rev_itlist fieldFn fields (SOME state)
           of NONE => NONE
            | SOME (stk',s',WidthValMap') =>
               case take_drop (length fields) stk'
                of NONE => NONE
                 | SOME(elts,stk'') =>
                     SOME(RECD (zip (map fst fields) (rev elts))::stk'',
                          s', WidthValMap')
       end
   | Array (c,exp) =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val dim = evalExp (Consts,WidthValMap,valueFn) exp'
           fun indexFn i NONE = NONE
             | indexFn i (SOME state) = parseFn E (ArraySub(path,intLit i)) c state
       in case rev_itlist indexFn (upto 0 (dim - 1)) (SOME state)
           of NONE => NONE
            | SOME (stk',s',WidthValMap') =>
               case take_drop dim stk'
                of NONE => NONE
                 | SOME(elts,stk'') =>
                     SOME(ARRAY (rev elts)::stk'', s', WidthValMap')
       end
   | Union choices =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolve_bexp_lvals WidthValMap path bexp
             in evalBexp (Consts,WidthValMap,valueFn) bexp'
             end
       in case List.find choiceFn choices
           of NONE => raise ERR "parseFn" "Union: no choices possible"
            | SOME(bexp,c) => parseFn E path c state
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
(* Version of segFn that uses a worklist style                               *)
(*---------------------------------------------------------------------------*)

fun matchFn E (state as (worklist,s,theta)) =
 let val (Consts,Decls,atomicWidths,valueFn) = E
 in
 case worklist
   of [] => SOME (s,theta)
   |  (Basic a,path)::t =>
       let val awidth = atomicWidths a
           val constrFn = atom_constr a
       in case tdrop awidth s
           of NONE => NONE
            | SOME (segment,rst) =>
              matchFn E (t,rst,
                         Redblackmap.insert(theta,path,constrFn segment))
       end
   | (Declared name,path)::t => matchFn E ((assoc name Decls,path)::t,s,theta)
   | (Raw exp,path)::t =>
       let val exp' = resolve_exp_lvals theta path exp
           val width = evalExp (Consts,theta,valueFn) exp'
       in case tdrop width s
           of NONE => NONE
            | SOME (segment,rst) =>
              matchFn E (t,rst,
                         Redblackmap.insert(theta,path,BLOB segment))
       end
   | (Scanner scanFn,path)::t =>
      (case scanFn s
        of NONE => raise ERR "matchFn" "Scanner failed"
         | SOME(segment,rst) =>
             matchFn E (t,rst, Redblackmap.insert(theta,path,SCANNED segment)))
   | (Recd fields,path)::t =>
       let fun fieldFn (fName,c) = (c,RecdProj(path,fName))
       in matchFn E (map fieldFn fields @ t,s,theta)
       end
   | (Array (c,exp),path)::t =>
       let val exp' = resolve_exp_lvals theta path exp
           val dim = evalExp (Consts,theta,valueFn) exp'
           fun indexFn i = (c,ArraySub(path,intLit i))
       in matchFn E (map indexFn (upto 0 (dim - 1)) @ t,s,theta)
       end
   | (Union choices,path)::t =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolve_bexp_lvals theta path bexp
             in evalBexp (Consts,theta,valueFn) bexp'
             end
       in case List.find choiceFn choices
           of NONE => raise ERR "matchFn" "Union: no choices possible"
            | SOME(bexp,c) => matchFn E ((c,path)::t,s,theta)
       end
 end
;


(*
Need to better handle tagging leaf nodes with target type info.

val lvalMap : (lval,ptree) Redblackmap.dict = Redblackmap.mkDict lval_compare ;

fun match E contig s = matchFn E ([(contig,VarName"root")],s,lvalMap);
*)
