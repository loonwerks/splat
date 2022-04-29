signature PP_CakeML =
sig
    type ty = AST.ty
    type id = string
    type qid = string * string
    type exp = AST.exp
    type decl = AST.decl
    type tydec = AADL.tydec
    type tmdec = AADL.tmdec
    type outdec = AADL.outdec
    type pretty = PolyML.pretty
    type contig = ByteContig.contig
    type tyenvs = (id -> ty) * (qid -> ty) * (qid -> ty)
    type port = string * ty * string * string
    type ivar = string * ty * exp

    val pp_cake_ty : int -> string -> ty -> pretty
    val pp_cake_exp : int -> string -> tyenvs -> exp -> pretty
    val pp_tydec : int -> string -> AADL.tydec -> pretty
    val pp_tmdec : int -> string -> tyenvs -> AADL.tmdec -> pretty

    val pp_api : string *
                 (string * int) list *      (* inport bufs *)
                 (string * string) list *   (* fillFns *)
                 (string * string) list *   (* sendFns *)
                 string -> pretty

    val pp_parser_struct
       : string * port list * (qid * contig) list * tmdec list -> pretty

    val pp_defs_struct
       : tyenvs -> string * tydec list * tmdec list -> pretty

    val pp_gadget_struct
       : tyenvs -> string * port list * ivar list * outdec list -> pretty
end
