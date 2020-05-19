use "contig.sml";
load "Regexp_Numerics";

fun valFn a s =
 let fun uvalFn s = IntInf.toInt
         (Regexp_Numerics.string2iint Regexp_Numerics.Unsigned Regexp_Numerics.MSB s)
     fun ivalFn s = IntInf.toInt
         (Regexp_Numerics.string2iint Regexp_Numerics.Twos_comp Regexp_Numerics.MSB s)
 in case a
  of Bool => uvalFn s
   | Char => uvalFn s
   | Enum s => uvalFn s
   | Signed w => ivalFn s
   | Unsigned w => uvalFn s
   | otherwise => raise ERR "valFn" ""
 end
;

fun repFn a i =
 let val u2string = Regexp_Numerics.iint2string Regexp_Numerics.Unsigned Regexp_Numerics.MSB
     val i2string = Regexp_Numerics.iint2string Regexp_Numerics.Twos_comp Regexp_Numerics.MSB
 in case a
  of Bool => u2string 1 (LargeInt.fromInt i)
   | Char => u2string 1 (LargeInt.fromInt i)
   | Enum s => u2string 1 (LargeInt.fromInt i)
   | Signed w => i2string w (LargeInt.fromInt i)
   | Unsigned w => u2string w (LargeInt.fromInt i)
   | other => raise ERR "repFn" ""
 end
;

fun dvalFn Double s = PackRealBig.fromBytes (Byte.stringToBytes s)
  | dvalFn other s = raise ERR "dvalFn" "expected Double"
;
fun drepFn Double r = Byte.bytesToString (PackRealBig.toBytes r)
  | drepFn other s = raise ERR "drepFn" "expected Double"
;

fun scanRandFn path = "foo";

val E = ([]:(string*int)list,
         []:(string*contig)list,
         atomic_widths,valFn,repFn,scanRandFn,Random.newgen());

fun genString contig =
  String.concat (randFn E ([(VarName"root",contig)],empty_lvalMap,[]));

val parseEnv =
  ([]:(string*int)list,
   []:(string*contig)list,
   atomic_widths,valFn);

val parseContig = parse parseEnv;

fun testContig contig =
 predFn parseEnv ([(VarName"root",contig)],
                  genString contig,empty_lvalMap);

val contig1 = Recd [
   ("A", Basic Bool),
   ("B", Basic Char),
   ("len", u16),
   ("len-bounds", Assert (Interval "len" (0,3))),
   ("elts", Array (i32, Loc(VarName"len")))
 ];

genString contig1;
parseContig contig1 it;

val contig2 = Recd [
   ("len", u8),
   ("len-bound", Assert (Interval "len" (1,32))),
   ("elts", Array (i32, Loc(VarName"len")))
 ];

genString contig2;
parseContig contig2 it;

val contig3 = Recd [
   ("A", Basic Bool),
   ("B", Basic Bool)
 ];

genString contig3;

val contig4 = Recd [
   ("A0", Basic Bool),
   ("A", Basic Char),
   ("A-bound", Assert (Interval "A" (0,1)))
 ];

genString contig4;

val latField = Recd [
   ("A", i32),
   ("A-val", Assert (Interval "A" (~90,90)))
 ];

genString latField;

val gps = Recd [
   ("lat", i32),
   ("lat-range", Assert (Interval "lat" (~90,90))),
   ("lon", i32),
   ("lon-range", Assert (Interval "lon" (~180,180))),
   ("alt", i32),
   ("alt-range", Assert (Interval "alt" (0,18000)))
 ];

(*---------------------------------------------------------------------------*)
(* Some message parsing stuff.                                               *)
(*---------------------------------------------------------------------------*)

val zone = Array (gps, intLit 2);

fun mk_gps ptree =
 case ptree
  of RECD [("lat", LEAF (p1, s1)),
           ("lon", LEAF (p2, s2)), ("alt", LEAF (p3, s3))] =>
       {lat = valFn p1 s1, lon = valFn p2 s2, alt = valFn p3 s3}
   | otherwise => raise ERR "mk_gps" "unexpected syntax";

mk_gps (#1 (parseContig gps (genString gps)));

fun mk_zone ptree =
 case ptree
   of ARRAY plist => Array.fromList (map mk_gps plist)
   | otherwise => raise ERR "mk_zone" "unexpected syntax";

mk_zone (#1 (parseContig zone (genString zone)));
