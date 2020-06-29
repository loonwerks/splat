signature Contig =
sig

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
    | DleA of Real.real * exp
    | DleB of exp * Real.real

  datatype atom
    = Bool
    | Char
    | Float
    | Double
    | Signed of int
    | Unsigned of int
    | Enum of string
    | Blob
    | Scanned

  datatype contig
    = Void
    | Basic of atom
    | Declared of string
    | Raw of exp
    | Assert of bexp
    | Scanner of string -> (string * string) option
    | Recd of (string * contig) list
    | Array of contig * exp
    | Union of (bexp * contig) list

  datatype ptree
    = LEAF of atom * string
    | RECD of (string * ptree) list
    | ARRAY of ptree list

  datatype ('a,'b) verdict = PASS of 'a | FAIL of 'b


  type env =
      (string * int) list             (* Integer constant bindings *)
    * (string * contig) list          (* Declared contigs *)
    * (atom -> int)                   (* Atom widths *)
    * (atom -> string -> int option)  (* Compute integer value *)
    * (atom -> string -> real option) (* Compute double value *)

  type lvalMap = (lval, atom * string) Redblackmap.dict
  type state   = (lval * contig) list * string * lvalMap

  val empty_lvalMap : lvalMap

  val substFn : env -> lvalMap -> lval -> contig -> string option
  val matchFn : env -> state -> (string * lvalMap) option
  val predFn  : env -> state -> (string * lvalMap, state) verdict


  val bool : contig
  val u8   : contig
  val u16  : contig
  val u32  : contig
  val u64  : contig
  val i16  : contig
  val i32  : contig
  val i64  : contig
  val f32  : contig
  val f64  : contig
  val SKIP : contig

  val scanTo : string -> string -> (string * string) option
  val scanCstring : string -> (string * string) option
end
