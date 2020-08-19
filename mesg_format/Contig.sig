signature Contig =
sig

  datatype exp =
      Add of exp * exp
    | ConstName of string
    | Loc of lval
    | Mult of exp * exp
    | intLit of int
  and lval =
      ArraySub of lval * exp
    | RecdProj of lval * string
    | VarName of string

  datatype bexp =
      BLoc of lval
    | Band of bexp * bexp
    | Beq of exp * exp
    | Bge of exp * exp
    | Bgt of exp * exp
    | Ble of exp * exp
    | Blt of exp * exp
    | Bnot of bexp
    | Bor of bexp * bexp
    | DleA of real * exp
    | DleB of exp * real
    | boolLit of bool

  datatype atom =
      Blob
    | Bool
    | Char
    | Double
    | Enum of string
    | Float
    | Scanned
    | Signed of int
    | Unsigned of int

  datatype contig =
      Array of contig * exp
    | Assert of bexp
    | Basic of atom
    | Declared of string
    | Raw of exp
    | Recd of (string * contig) list
    | Scanner of string -> (string * string) option
    | Union of (bexp * contig) list
    | Void

  datatype ptree =
      ARRAY of ptree list
    | LEAF of atom * string
    | RECD of (string * ptree) list

(*---------------------------------------------------------------------------*)
(* Environments                                                              *)
(*---------------------------------------------------------------------------*)

  type lvalMap = (lval, atom * string) Redblackmap.dict

  type evalenv =   (*  (constMap,lvalMap,valFn)  *)
      (string * int) list
    * (lval, atom * string) Redblackmap.dict
    * (atom -> string -> int option)

  type evalBenv =   (*  (constMap,lvalMap,valFn,dvalFn)  *)
      (string * int) list
    * (lval, atom * string) Redblackmap.dict
    * (atom -> string -> int option)
    * (atom -> string -> real option)

  type env = (*  (constMap,Decls,atomWidth,valFn,dvalFn)  *)
      (string * int) list
    * (string * contig) list
    * (atom -> int)
    * (atom -> string -> int option)
    * (atom -> string -> real option)

  type randenv =  (*  env ++ (repFn,scanRandFn,gn)  *)
      (string * int) list
    * (string * contig) list
    * (atom -> int)
    * (atom -> string -> int option)
    * (atom -> string -> real option)
    * (atom -> int -> string)
    * (lval -> string)
    * Random.generator

  type state = (lval * contig) list * string * lvalMap  (*  (worklist,s,theta)  *)
  type parsestate = ptree list * string * lvalMap       (*  (stack, s, lvmap)  *)


  val SKIP : contig
  val delete_asserts: (string * contig) list -> contig -> contig
  val add_enum_decl: env -> string * (string * int) list -> env

  val exp_compare: exp * exp -> order
  val lval_compare: lval * lval -> order

  val evalExp: evalenv -> exp -> int option
  val evalBexp: evalBenv -> bexp -> bool option

  val lval_append  : lval -> lval -> lval
  val path_prefixes: lval -> lval list

  val resolve_lval : lvalMap -> lval -> lval -> lval option
  val resolveExp   : lvalMap -> lval -> exp -> exp option
  val resolveBexp  : lvalMap -> lval -> bexp -> bexp option

  val empty_lvalMap : lvalMap

  val filterOpt: ('a -> bool option) -> 'a list -> 'a list option
  val tdrop: int -> string -> (string * string) option
  val take_drop: int -> 'a list -> ('a list * 'a list) option

  val substFn : env -> lvalMap -> lval -> contig -> string option
  val matchFn : env -> state -> (string * lvalMap) option
  val predFn  : env -> state -> (string * lvalMap, state) Lib.verdict
  val parseFn : env -> lval -> contig -> parsestate -> parsestate option
  val randFn  : randenv -> (lval * contig) list * lvalMap * string list -> string list

  val match      : env -> contig -> string -> -> (string * lvalMap) option
  val check_match: env -> contig -> string -> bool
  val wellformed : env -> contig -> string -> bool
  val parse      : env -> contig -> string -> ptree * string * lvalMap

  val Interval: string -> int * int -> bexp
  val pp_bexp: bexp -> PolyML.pretty
  val pp_binop: string -> PolyML.pretty -> PolyML.pretty -> PolyML.pretty
  val pp_exp: exp -> PolyML.pretty
  val pp_lval: lval -> PolyML.pretty
  val pp_atom: atom -> PolyML.pretty
  val is_recd: contig -> bool
  val pp_contig: contig -> PolyML.pretty

  val uxas_atom_width: atom -> int
  val bool = Bool: contig
  val u8 = u8: contig
  val u16 = u16: contig
  val u32 = u32: contig
  val u64 = u64: contig
  val i16 = i16: contig
  val i32 = i32: contig
  val i64 = i64: contig
  val f32 = Float: contig
  val f64 = Double: contig

  val scanTo : string -> string -> (string * string) option
  val scanCstring: string -> (string * string) option

end
