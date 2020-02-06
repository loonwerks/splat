signature Segments =
sig
 datatype exp
  = intLit of int
  | BitsExp of exp
  | BytesExp of exp
  | Val of string
  | ConstName of string
  | EnumName of string
  | Add of exp * exp
  | Mult of exp * exp
  | Diff of exp * exp
  | Mod of exp * exp

 val prim_vars : exp -> string list -> string list
 val expVars : exp -> string list

  type fldEnv   = (string * (int * int)) list
  type constEnv = (string * int) list
  type enumEnv  = (string * int) list;

  type env = fldEnv * constEnv * enumEnv;

  val evalExp : env -> exp -> int

 type endian = Regexp_Numerics.endian
 type encoding = Regexp_Numerics.encoding

 type interpretation = endian * encoding

 datatype segments
  = Nullseg
  | Seg of (string * exp * interpretation) * segments
  | Union of exp * (int * segments) list

 val parse : env -> segments -> (string * (int * int) list) * string

end
