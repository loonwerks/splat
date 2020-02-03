(*---------------------------------------------------------------------------*)
(* Expressions represent field widths.                                       *)
(*---------------------------------------------------------------------------*)

datatype exp
  = intLit of int
  | BitsExp of exp
  | BytesExp of exp
  | FldName of string
  | ConstName of string
  | EnumName of string
  | Add of exp * exp
  | Mult of exp * exp
  | Diff of exp * exp
  | Mod of exp * exp

fun Bits i = intLit i
fun Bytes i = Bits (8 * i);

(*---------------------------------------------------------------------------*)
(* Environments. A FldName in an exp denotes the numeric value held in the   *)
(* named field. In the environment, it also has a width. A ConstName denotes *)
(* a number; it doesn't have a width. An EnumName is similar to a ConstName. *)
(*---------------------------------------------------------------------------*)

type fldEnv   = (string * (int * int)) list
type constEnv = (string * int) list
type enumEnv  = (string * int) list;

type env = fldEnv * constEnv * enumEnv;

fun flds_of (fEnv,cEnv,eEnv) = fEnv;
fun width_of (x,y) = x
fun value_of (x,y) = y;

(*---------------------------------------------------------------------------*)
(* evalExp E e --> width                                                     *)
(*---------------------------------------------------------------------------*)

fun evalExp (E as (fEnv,cEnv,eEnv)) e =
 case e
  of intLit i    => i
   | BitsExp e   => evalExp E e
   | BytesExp e  => 8 * evalExp E e
   | FldName s   => value_of(assoc s fEnv)
   | ConstName s => assoc s cEnv
   | EnumName s  => assoc s eEnv
   | Add(e1,e2)  => evalExp E e1 + evalExp E e2
   | Mult(e1,e2) => evalExp E e1 * evalExp E e2
   | Diff(e1,e2) => evalExp E e1 - evalExp E e2
   | Mod(e1,e2)  => (evalExp E e1) mod (evalExp E e2);

fun prim_vars e acc =
 case e
  of intLit _    => acc
   | BitsExp e   => prim_vars e acc
   | BytesExp e  => prim_vars e acc
   | FldName s   => insert s acc
   | ConstName s => acc
   | EnumName s  => acc
   | Add(e1,e2)  => prim_vars e2 (prim_vars e2 acc)
   | Mult(e1,e2) => prim_vars e2 (prim_vars e2 acc)
   | Diff(e1,e2) => prim_vars e2 (prim_vars e2 acc)
   | Mod(e1,e2)  => prim_vars e2 (prim_vars e2 acc);

val expVars = C prim_vars []

(*---------------------------------------------------------------------------*)
(* A "segments" is an expression tree capturing a set of possible message    *)
(* formats.                                                                  *)
(*---------------------------------------------------------------------------*)

datatype segments
  = Nullseg
  | Seg of (string * exp) * segments
  | Union of exp * (int * segments) list;

fun bitsVal list = failwith "bitsVal";

fun parse E Nullseg s = (flds_of E,s)
  | parse E (Seg((name,exp),rst)) s =
     let val width = evalExp E exp
         val bits = List.take (s,width)
         val n = bitsVal bits
         val s' = List.drop(s,width)
         val (fEnv,cEnv,eEnv) = E
     in parse ((name, (width,n)) :: fEnv,cEnv,eEnv) rst s'
     end
  | parse E (Union(exp,alist)) s = parse E (assoc (evalExp E exp) alist) s;


fun vars_of segs =
 case segs
  of Nullseg => []
   | Seg((_,e),t) => union (expVars e) (vars_of t)
   | Union (e,kids) => U (expVars e:: map (vars_of o snd) kids)

(*---------------------------------------------------------------------------*)
(* Example: 802-11 messages                                                  *)
(*---------------------------------------------------------------------------*)

val Const_Map = [("Frame_Width", 2)];
val Frame_Map =
    map swap (enumerate 0 ["Management","Control","Data","Reserved"]);

val initEnv = ([],Const_Map,Frame_Map);

(*---------------------------------------------------------------------------*)
(* preEval is used to preprocess descriptions to get rid of syntactic sugar. *)
(*---------------------------------------------------------------------------*)

val preEval = evalExp initEnv;

val macHeader =
 Seg (("protocol",  Bits 2),
 Seg (("tpe",       BitsExp (ConstName"Frame_Width")),
 Seg (("subType",   Bits 4),
 Seg (("toDS",      Bits 1),
 Seg (("fromDS",    Bits 1),
 Seg (("moreFrag",  Bits 1),
 Seg (("retry",     Bits 1),
 Seg (("powerMgmt", Bits 1),
 Seg (("moreData",  Bits 1),
 Seg (("wep",       Bits 1),
 Seg (("order",     Bits 1),
 Seg (("duration",  Bytes 2),
 Union
   (FldName "tpe",
     [(preEval (EnumName "Data"),
        Seg(("address1",   Bytes 6),
        Seg(("address2",   Bytes 6),
        Seg(("address3",   Bytes 6),
        Seg(("fragNumber", Bits 4),
        Seg(("seqNumber",  Bits 12),
        Seg(("address4",   Bytes 6), Nullseg))))))),
      (preEval (EnumName "Control"),
        Union
          (FldName "subType",
             [(11, Seg(("receiver",    Bytes 6),
                   Seg(("transmitter", Bytes 6),Nullseg))),
              (12, Seg(("receiver",    Bytes 6),Nullseg))]))])
 ))))))))))))
;

vars_of macHeader;
