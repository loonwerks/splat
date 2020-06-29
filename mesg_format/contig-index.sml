(*---------------------------------------------------------------------------*)
(* lvals designate locations where data lives. Exps are r-values. Since an   *)
(* lval can depend on runtime values, and rvals depend on lvals to read the  *)
(* values at locations, the types are mutually recursive.                    *)
(*---------------------------------------------------------------------------*)

val ERR = mk_HOL_ERR "contig-index";

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
(* An lvalMap is used to hold context: it maps an lval to an interval in the *)
(* input buffer. That interval can be evaluated to get a number.             *)
(*---------------------------------------------------------------------------*)

val empty_lvalMap
   : (lval,(int*int)) Redblackmap.dict = Redblackmap.mkDict lval_compare;

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


(*---------------------------------------------------------------------------*)
(* For convenience, and composability, we allow "location completion", so    *)
(* that partly-given locations can be a convenient notation. Completion      *)
(* effectively looks "up and to the left" in the original contig type for    *)
(* a full lval that the given lval is a suffix of. The full lval is used as  *)
(* key in lookups in expression evaluation.                                  *)
(*---------------------------------------------------------------------------*)

fun resolve_lval lvalMap path lval =
 let val prefixes = path_prefixes path
     val prospects = map (C lval_append lval) prefixes @ [lval]
 in Lib.first (can (curry Redblackmap.find lvalMap)) prospects
 end
 handle HOL_ERR _ => raise ERR "resolve_lval" "unsuccessful";

fun resolve_exp_lvals lvalMap path exp =
 case exp
  of Loc lval     => Loc(resolve_lval lvalMap path lval)
   | Add (e1,e2)  => Add(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | Mult (e1,e2) => Mult(resolve_exp_lvals lvalMap path e1,resolve_exp_lvals lvalMap path e2)
   | otherwise    => exp

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
(* Compute the big-endian integer from the slice between i and j in vector V *)
(*---------------------------------------------------------------------------*)

fun numBetwixt V (i,j) =
 let val _ = if i <= j andalso 0 <= i andalso 0 <= j then
              () else raise ERR "numBetwixt" "malformed range"
     fun atV index = Word8.toInt(Word8Vector.sub(V,index))
     fun valFn n acc =
       if n > j then
         acc
       else valFn (n+1) (acc * 256 + atV n)
 in valFn i 0
 end

(*  Check it works
load "regexpLib";
local open Regexp_Numerics
in
fun mk_u16 i = iint2string Unsigned MSB 2 (IntInf.fromInt i)
end

val string = List.concat(List.map mk_u16 [123, 9999,32000]);
val V = Byte.stringToBytes (String.concat(List.map mk_u16 [123, 9999,32000]));

numBetwixt V (0,1);
numBetwixt V (2,3);
numBetwixt V (4,5);
*)

(*---------------------------------------------------------------------------*)
(* Expression evaluation                                                     *)
(*---------------------------------------------------------------------------*)

fun evalExp (E as (constMap,lvalMap,V)) exp =
 case exp
  of Loc lval =>
       (case Redblackmap.peek(lvalMap,lval)
         of SOME (i,j) => numBetwixt V (i,j)
          | NONE => raise ERR "evalExp" "lval binding failure")
   | intLit i => i
   | ConstName s =>
     (case assoc1 s constMap
       of SOME(_,i) => i
        | NONE => raise ERR "evalExp"
            ("unable to find value for constant named "^Lib.quote s))
   | Add(e1,e2) => evalExp E e1 + evalExp E e2
   | Mult(e1,e2) => evalExp E e1 * evalExp E e2
;

(*---------------------------------------------------------------------------*)
(* Evaluate atomic formulas                                                  *)
(*---------------------------------------------------------------------------*)

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
  | Scanner of (Word8Vector.vector -> int -> int option)
  | Recd of (string * contig) list
  | Array of contig * exp
  | Union of (bexp * contig) list;

(*---------------------------------------------------------------------------*)
(* Check that one is not indexing off the end of the buffer.                 *)
(*---------------------------------------------------------------------------*)

fun indexable V i = (Word8Vector.sub(V,i); true) handle _ => false;

(*---------------------------------------------------------------------------*)
(* Environments:                                                             *)
(*                                                                           *)
(*   Consts : maps constant names to integers                                *)
(*   Decls  : maps names to previously declared contigs                      *)
(*   atomicWidths : gives width info for basic types                         *)
(*   V : vector being scanned/parsed                                         *)
(*                                                                           *)
(* segFn operates on a state tuple (segs,pos,wvMap)                          *)
(*                                                                           *)
(*  segs : (int * int) list      ;;; list of segments                        *)
(*  pos  :  int                  ;;; current position in vector              *)
(* lvMap : (lval |-> int * int)  ;;; locations of prev. seen elements        *)
(*                                                                           *)
(* which is wrapped in the error monad.                                      *)
(*---------------------------------------------------------------------------*)

fun segFn E path contig state V =
 let val (Consts,Decls,atomicWidths) = E
     val (segs,pos,WidthValMap) = state
 in
 case contig
  of Basic a =>
       let val j = pos + atomicWidths a - 1
       in if indexable V j then
             SOME(segs@[(pos,j)],j+1,
                  Redblackmap.insert(WidthValMap,path,(pos,j)))
          else NONE
       end
   | Declared name => segFn E path (assoc name Decls) state V
   | Raw exp =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val width = evalExp (Consts,WidthValMap,V) exp'
           val j = pos + width - 1
       in
         if indexable V j then
              SOME(segs@[(pos,j)],j+1,
                   Redblackmap.insert(WidthValMap,path,(pos,j)))
         else NONE
       end
   | Scanner scanFn =>
      (case scanFn V pos
        of NONE => raise ERR "segFn" "Scanner failed"
         | SOME j => (* index of last scanned char *)
              SOME(segs@[(pos,j)],j+1,
                   Redblackmap.insert(WidthValMap,path,(pos,j))))
   | Recd fields =>
       let fun fieldFn fld NONE = NONE
             | fieldFn (fName,c) (SOME st) = segFn E (RecdProj(path,fName)) c st V
       in rev_itlist fieldFn fields (SOME state)
       end
   | Array (c,exp) =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val dim = evalExp (Consts,WidthValMap,V) exp'
           fun indexFn i NONE = NONE
             | indexFn i (SOME state) = segFn E (ArraySub(path,intLit i)) c state V
       in rev_itlist indexFn (upto 0 (dim - 1)) (SOME state)
       end
   | Union choices =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolve_bexp_lvals WidthValMap path bexp
             in evalBexp (Consts,WidthValMap,V) bexp'
             end
       in case List.find choiceFn choices
           of NONE => raise ERR "segFn" "Union: no choices possible"
            | SOME(bexp,c) => segFn E path c state V
       end
 end
;

(*---------------------------------------------------------------------------*)
(* segFn with initial values given                                           *)
(*---------------------------------------------------------------------------*)

fun segments E contig V =
   segFn E (VarName"root") contig ([],0,empty_lvalMap) V;


(*---------------------------------------------------------------------------*)
(* Parsing. First define a universal target type to parse into. It provides  *)
(* structure, but the leaf elements are left as pairs of indices into the    *)
(* buffer.                                                                   *)
(*---------------------------------------------------------------------------*)

datatype ptree
  = BOOL of int * int
  | CHAR of int * int
  | INT of int * (int * int)
  | UINT of int * (int * int)
  | FLOAT of int * int
  | DOUBLE of int * int
  | ENUM of string * (int * int)
  | BLOB of int * int
  | SCANNED of int * int
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
  SOME(List.take(list, n),
       List.drop(list, n))
  handle _ => NONE;

(*---------------------------------------------------------------------------*)
(* Environments:                                                             *)
(*                                                                           *)
(*   Consts : maps constant names to integers                                *)
(*   Decls  : maps names to previously declared contigs                      *)
(*   atomicWidths : gives width info for basic types                         *)
(*                                                                           *)
(* parseFn operates on a state tuple (segs,s,wvMap)                          *)
(*                                                                           *)
(*  stk : ptree list  ;;; parsing stack                                      *)
(*  pos : int         ;;; current position in string                         *)
(* lvMap : (lval |-> int*int) ;;; locations of previously seen elements      *)
(*                                                                           *)
(* which is wrapped in the error monad.                                      *)
(*---------------------------------------------------------------------------*)

fun parseFn E path contig state V =
 let val (Consts,Decls,atomicWidths) = E
     val (stk,pos,WidthValMap) = state
 in
 case contig
  of Basic a =>
       let val j = pos + atomicWidths a - 1
           val constrFn = atom_constr a
       in if indexable V j then
             SOME(constrFn(pos,j)::stk,j+1,
                  Redblackmap.insert(WidthValMap,path,(pos,j)))
          else NONE
       end
   | Declared name => parseFn E path (assoc name Decls) state V
   | Raw exp =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val width = evalExp (Consts,WidthValMap,V) exp'
           val j = pos + width - 1
       in
         if indexable V j then
              SOME(BLOB(pos,j)::stk,j+1,
                   Redblackmap.insert(WidthValMap,path,(pos,j)))
         else NONE
       end
   | Scanner scanFn =>
      (case scanFn V pos
        of NONE => raise ERR "parseFn" "Scanner failed"
         | SOME j =>  (* index of last scanned char *)
              SOME(SCANNED (pos,j)::stk,j+1,
                   Redblackmap.insert(WidthValMap,path,(pos,j))))
   | Recd fields =>
       let fun fieldFn fld NONE = NONE
             | fieldFn (fName,c) (SOME st) = parseFn E (RecdProj(path,fName)) c st V
       in case rev_itlist fieldFn fields (SOME state)
           of NONE => NONE
            | SOME (stk',pos',WidthValMap') =>
               case take_drop (length fields) stk'
                of NONE => NONE
                 | SOME(elts,stk'') =>
                     SOME(RECD (zip (map fst fields) (rev elts))::stk'',
                          pos', WidthValMap')
       end
   | Array (c,exp) =>
       let val exp' = resolve_exp_lvals WidthValMap path exp
           val dim = evalExp (Consts,WidthValMap,V) exp'
           fun indexFn i NONE = NONE
             | indexFn i (SOME state) = parseFn E (ArraySub(path,intLit i)) c state V
       in case rev_itlist indexFn (upto 0 (dim - 1)) (SOME state)
           of NONE => NONE
            | SOME (stk',pos',WidthValMap') =>
               case take_drop dim stk'
                of NONE => NONE
                 | SOME(elts,stk'') =>
                     SOME(ARRAY (rev elts)::stk'', pos', WidthValMap')
       end
   | Union choices =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolve_bexp_lvals WidthValMap path bexp
             in evalBexp (Consts,WidthValMap,V) bexp'
             end
       in case List.find choiceFn choices
           of NONE => raise ERR "parseFn" "Union: no choices possible"
            | SOME(bexp,c) => parseFn E path c state V
       end
 end
;

fun parse E contig V =
 case parseFn E (VarName"root") contig ([],0,empty_lvalMap) V
  of SOME ([ptree],remaining,lvMap) => (ptree,remaining,lvMap)
  | SOME otherwise => raise ERR "parse" "expected stack of size 1"
  | NONE => raise ERR "parse" ""
;

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
(* Miscellaneous support stuff needed to make things work                    *)
(*---------------------------------------------------------------------------*)

fun atom_width atm =
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
 let val (Consts,Decls,atomicWidths) = E
     val enum = Basic(Enum(s,bindings))
     val bindings' = map (fn (name,i) => (s^"'"^name,i)) bindings
 in
   (bindings' @ Consts, (s,enum)::Decls, atomicWidths)
 end


(*---------------------------------------------------------------------------*)
(* Support for the Scanner constructor. The end delimiter is left on the     *)
(* string.                                                                   *)
(*---------------------------------------------------------------------------*)

fun scanTo byte V pos =
 let val top = Word8Vector.length V
     fun look i =
        if i >= top then
           NONE else
        if Word8Vector.sub(V,i) = byte then
           SOME i
        else look (i+1)
 in
   if pos < 0 then
     NONE
   else look pos
 end

val scanCstring = scanTo (Word8.fromInt 0)
