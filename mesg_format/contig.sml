(*---------------------------------------------------------------------------*)
(* l-values designate locations where data lives. Exps are r-values. I think *)
(* of "r" as designating "runtime" although the original conception was      *)
(* "right-hand-side" or assignment. Since lvals can depend on runtime values,*)
(* and rvals depend on lvals to read the values at locations, the types are  *)
(* mutually recursive.                                                       *)
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

val empty_lvalMap : (lval,int) Redblackmap.dict = Redblackmap.mkDict lval_compare ;

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


fun evalExp (E as (Delta,lvalMap)) exp =
 case exp
  of Loc lval =>
       (case Redblackmap.peek(lvalMap,lval)
         of SOME i => i
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
  of boolLit b => b
   | Bnot b    => not (evalBexp E b)
   | Bor(b1,b2)  => (evalBexp E b1 orelse evalBexp E b2)
   | Band(b1,b2) => (evalBexp E b1 andalso evalBexp E b2)
   | Beq (e1,e2) => (evalExp E e1 = evalExp E e2)
   | Blt (e1,e2) => (evalExp E e1 < evalExp E e2)
   | Bgtr(e1,e2) => (evalExp E e1 > evalExp E e2)
   | Bleq(e1,e2) => (evalExp E e1 <= evalExp E e2)
   | Bgeq(e1,e2) => (evalExp E e1 >= evalExp E e2)
;

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


 (*---------------------------------------------------------------------------*)
(* Contiguity types                                                          *)
(*---------------------------------------------------------------------------*)

datatype atom
  = Bool
  | Char
  | Float
  | Double
  | Signed of int
  | Unsigned of int;

datatype contig
  = Basic of atom
  | Declared of string
  | Recd of (string * contig) list
  | Array of contig * exp
  | Union of (bexp * contig) list;

fun pp_atom atom =
 let open PP
 in case atom
     of Bool => add_string "Bool"
      | Char => add_string "Char"
      | Float => add_string "Float"
      | Double => add_string "Double"
      | Signed i => add_string ("i"^Int.toString (i*8))
      | Unsigned i => add_string ("u"^Int.toString (i*8))
 end;

fun pp_contig contig =
 let open PP
 in
   case contig
    of Basic atom => pp_atom atom
     | Declared s => add_string s
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
(*   WidthVal : maps a path through a contig to the unsigned integer value   *)
(*              stored at the designated location in the string.             *)
(*                                                                           *)
(* segFn operates on a state tuple (segs,s,wvMap)                            *)
(*                                                                           *)
(*  segs : (string * int) list  ;;; list of segments and associated values   *)
(*  s    :  string              ;;; remainder of string                      *)
(* wvMap : (lval |-> int) map   ;;; previously seen values, accessed by path *)
(*                                                                           *)
(* which is wrapped in the error monad.                                      *)
(*---------------------------------------------------------------------------*)

fun segFn E path contig state =
 let val (Consts,Decls,atomicWidths) = E
     val (segs,s,WidthValMap) = state
 in
 case contig
  of Basic a =>
      let val (awidth,dir) = assoc a atomicWidths
      in case tdrop awidth s
         of NONE => NONE
          | SOME (segment,rst) =>
             let open Regexp_Numerics
                 val segval = IntInf.toInt(string2iint Unsigned dir segment)
             in SOME(segs@[(segment,segval)],rst,
                     Redblackmap.insert(WidthValMap,path,segval))
             end
      end
   | Recd fields =>
       let fun fieldFn fld NONE = NONE
             | fieldFn (fName,c) (SOME st) = segFn E (RecdProj(path,fName)) c st
       in rev_itlist fieldFn fields (SOME state)
       end
   | Array (c,exp) =>
      let val exp' = resolve_exp_lvals WidthValMap path exp
          val dim = evalExp (Consts,WidthValMap) exp'
          fun indexFn i NONE = NONE
            | indexFn i (SOME state) = segFn E (ArraySub(path,intLit i)) c state
       in rev_itlist indexFn (upto 0 (dim - 1)) (SOME state)
       end
   | Declared name => segFn E path (assoc name Decls) state
   | Union choices =>
       let fun choiceFn(bexp,c) =
             let val bexp' = resolve_bexp_lvals WidthValMap path bexp
             in evalBexp (Consts,WidthValMap) bexp'
             end
       in case List.find choiceFn choices
           of NONE => raise ERR "segFn" "Union: no choices possible"
            | SOME(bexp,c) => segFn E path c state
       end
 end
;

fun segments E contig s = segFn E (VarName"root") contig ([],s,empty_lvalMap);

val atomic_widths =  (* in bytes *)
 let val MSB = Regexp_Numerics.MSB
 in
   [(Bool,       (1,MSB)),
    (Char,       (1,MSB)),
    (Signed 1,   (1,MSB)),
    (Signed 2,   (2,MSB)),
    (Signed 4,   (4,MSB)),
    (Signed 8,   (8,MSB)),
    (Unsigned 1, (1,MSB)),
    (Unsigned 2, (2,MSB)),
    (Unsigned 4, (4,MSB)),
    (Unsigned 8, (8,MSB)),
    (Float,      (4,MSB)),
    (Double,     (8,MSB))]
 end

val E = ([],[],atomic_widths);

val u16 = Basic(Unsigned 2);
val i32 = Basic(Signed 4);
val i64 = Basic(Signed 8);

local open Regexp_Numerics
in
fun mk_u16 i = iint2string Unsigned MSB 2 (IntInf.fromInt i)
fun mk_i32 i = iint2string Twos_comp MSB 4 (IntInf.fromInt i)
fun mk_bool b =
  if b then
    iint2string Unsigned MSB 1 (IntInf.fromInt 1)
  else
    iint2string Unsigned MSB 1 (IntInf.fromInt 0)
fun mk_char c =
  iint2string Unsigned MSB 1 (IntInf.fromInt (Char.ord c))
fun mk_string s =
    mk_u16 (String.size s) :: map mk_char (String.explode s);
end;

(*===========================================================================*)

val contig = Recd [
   ("A", Basic Bool),
   ("B", Basic Char),
   ("len", u16),
   ("elts", Array (i32, Loc(VarName"len")))
 ];

val string = String.concat
  [mk_bool true,
   "g",
   mk_u16 3,
   mk_i32 25,
   mk_i32 2356,
   mk_i32 12345
  ];

val SOME(segs, remaining, lvalMap) = segments E contig string;

Redblackmap.listItems lvalMap;

(*===========================================================================*)

val contig = Recd [
   ("A", Array (u16,intLit 2)),
   ("elts", Array (i32, Loc(ArraySub(VarName"A",intLit 0))))
 ];

val string = String.concat
  [mk_u16 4,
   mk_u16 2,
   mk_i32 25,
   mk_i32 2356,
   mk_i32 12345,
   mk_i32 999,
   mk_i32 1000,
   mk_i32 1001
  ]

val SOME(segs, remaining, lvalMap) = segments E contig string;

Redblackmap.listItems lvalMap;

(*===========================================================================*)

val String =  (* varying length strings *)
  Recd [("len", Basic(Unsigned 2)),
        ("elts", Array(Basic Char,Loc (VarName"len")))
];

val E = ([],[("String",String)],atomic_widths);

val contig = Recd [
   ("len", u16),
   ("strings", Array (Declared "String", Loc(VarName"len")))
 ];

val string = String.concat
 [mk_u16 4,
  mk_u16 3, mk_char #"f",mk_char #"o",mk_char #"o",
  mk_u16 3, mk_char #"b",mk_char #"a",mk_char #"r",
  mk_u16 7, mk_char #"f",mk_char #"r",mk_char #"i",mk_char #"z",mk_char #"z",mk_char #"l",mk_char #"e",
  mk_u16 2, mk_char #"n",mk_char #"o"
  ]

val SOME(segs, remaining, lvalMap) = segments E contig string;

Redblackmap.listItems lvalMap;

(*===========================================================================*)


val KeyValuePairRecd =
  Recd [("key", Declared "String"),
        ("value", Declared "String")];

val E = ([],[("String",String), ("KeyValuePair", KeyValuePairRecd)],atomic_widths);

val contig = Recd [
   ("len", u16),
   ("kvpairs", Array (Declared "KeyValuePair", Loc(VarName"len")))
 ];

val string = String.concat
 ([mk_u16 4] @
   mk_string "foo"     @ mk_string "bar" @
   mk_string "serpent" @ mk_string "boar" @
   mk_string "rooster" @ mk_string "mustang" @
   mk_string "foot"    @ mk_string "ten-toes"
 )

val SOME(segs, remaining, lvalMap) = segments E contig string;

Redblackmap.listItems lvalMap;
