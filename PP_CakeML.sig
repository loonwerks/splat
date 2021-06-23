signature PP_CakeML =
sig
    type ty = AST.ty
    type id = string
    type qid = string * string
    type exp = AST.exp
    type decl = AST.decl
    type tydec = AADL.tydec
    type tmdec = AADL.tmdec
    type pretty = PolyML.pretty
    type contig = ByteContig.contig
    type inport = string * ty * string * string

    val pp_ty : int -> string -> ty -> pretty
    val pp_exp : int -> string -> exp -> pretty
    val pp_decl : int -> string -> decl -> pretty
    val pp_tydec : int -> string -> AADL.tydec -> pretty
    val pp_tmdec : int -> string -> AADL.tmdec -> pretty
    val pp_monitor : int -> AADL.monitor -> pretty
    val pp_pkg     : int -> AADL.pkg -> pretty

    val mk_tyE         : AADL.pkg list -> qid -> ty option
    val mk_constE      : AADL.pkg list -> string -> ty option
    val mk_recd_projns : tydec list -> tmdec list
    val empty_varE     : id -> ty option
    val assocFn        : (''a * 'b) list -> ''a -> 'b option
    val transRval      : ((qid -> ty option) * (id -> ty option)) * (id -> ty option) -> exp -> exp
    val transRval_decl : (qid -> ty option) * (id -> ty option) -> tmdec -> tmdec
    val tydec_to_ty    : tydec -> ty
    val contig_to_exp  : (string * contig) list -> contig -> exp
    val AppExp         : exp list -> exp
    val listLit        : exp list -> exp

    val pp_api : int -> string *
                        (string * int) list *      (* inport bufs *)
                        (string * string) list *   (* fillFns *)
                        (string * string) list *   (* sendFns *)
                        string -> pretty

    val pp_parser_struct
      : int -> string * inport list * (qid * contig) list * tmdec list
            -> pretty

    val pp_defs_struct : int -> string * tydec list * tmdec list -> pretty
end
