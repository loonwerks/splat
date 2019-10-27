open Json;

  datatype iexp 
    = Var of string
    | Const of int
    | EnumName of string
    | Add of iexp * iexp
    | Mult of iexp * iexp
    | Diff of iexp * iexp

  datatype segments
    = Segs of string list
    | Cseg of (string * iexp) * segments
    | Choice of iexp * (int -> segments)

val ([jpkg],ss) = Json.fromFile "mesg_format/802.11-spec.json";

val AList [("type", String "BitCodecGenSpec"),
           ("spec", spec),
           ("enums", enums),
           ("funs", funs)] = jpkg;

val AList [("type", String "Spec.Concat"), ("name", String fieldName),
           ("elements", List elts)] = spec
val [a,b,c] = elts;

val AList [("type", String "Spec.Concat"), ("name", String fieldName1),
           ("elements", List elts1)] = a
val [a1,b1,c1] = elts1;

val AList [("type", String "Spec.Concat"), ("name", String fieldName2),
           ("elements", List elts2)] = a1
val [a2,b2,c2,d2,e2,f2,g2,h2,i2,j2,k2] = elts2;

fun dest_bits spec =
 case spec
  of AList [("type", String "Spec.Bits"), 
            ("name", String fieldName),
            ("size", Number (Int i))] => (fieldName,Const i);

fun dest_bytes spec =
 case spec
  of AList [("type", String "Spec.Bytes"), 
            ("name", String fieldName),
            ("size", Number (Int i))] => (fieldName,Const (i*8));

fun dest_enum spec =
 case spec
  of AList [("type", String "Spec.Enum"), 
            ("name", String fieldName),
            ("objectName", String objName)] => (fieldName,EnumName objName);

fun gen_dest spec = 
  dest_bits spec handle _ => 
  dest_bytes spec handle _ => 
  dest_enum spec;

val elts2_segs = map gen_dest elts2

Flattened fields.
-----------------

map gen_dest [a2,b2,c2,d2,e2,f2,g2,h2,i2,j2,k2,b1,c1,b,c]
mapfilter gen_dest [a2,b2,c2,d2,e2,f2,g2,h2,i2,j2,k2,b1,c1,b,c]
map gen_dest elts2
 dest_union c1;
 dest_raw b;
 dest_bits c

fun dest_spec spec =
 case spec
  of AList [("type", String "Spec.Concat"), 
            ("name", String fieldName),
            ("elements", List elts)] => (fieldName,elts)
