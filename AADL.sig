signature AADL =
sig
 include Abbrev

  type id = string
  type qid = string * string
  type ty = AST.ty
  type exp = AST.exp
  type tyEnv = (ty * ty) list
  type port = string * ty * string * string
  type vardec = string * ty * exp

 datatype tydec
    = EnumDec of qid * string list
    | RecdDec of qid * (string * ty) list
    | ArrayDec of qid * ty   (* ty is an ArrayTy *)
    | UnionDec of qid * (string * ty) list

 datatype tmdec
    = ConstDec of qid * ty * exp
    | FnDec of qid * (string * ty) list * ty * exp

 datatype outdec
   = Out_Data of string * ty * exp
   | Out_Event_Only of string * ty * exp
   | Out_Event_Data of string * ty * exp * exp

 (*---------------------------------------------------------------------------*)
 (* A contract holds all the relevant info scraped from an AGREE decl of      *)
 (* a {filter,monitor,gate}. These are all quite similar from the code gen    *)
 (* perspective so we sweep them all into a unified datatype.                 *)
 (*                                                                           *)
 (* Contract (name,kind,ports,latched,tydecs,tmdecs,ivars,(outdecs,otherGs))  *)
 (*                                                                           *)
 (* It doesn't capture everything that could do into an AGREE contract, eg    *)
 (* assumptions aren't grabbed.                                               *)
 (*---------------------------------------------------------------------------*)

 datatype contract =
   ContractDec
     of qid
      * string
      * port list
      * bool
      * tydec list  (* local tydecs *)
      * tmdec list  (* local tmdecs *)
      * vardec list (* state vars and temporaries *)
      * (string * string * outdec) list
      * (string * string * exp) list

 type decls = string * (tydec list * tmdec list * contract list)

 datatype pkg = Pkg of decls

 val scrape : Json.json -> decls
 val scrape_pkgs : Json.json -> decls list

 val tydec_qid : tydec -> qid
 val tmdec_qid : tmdec -> qid

 val outdecName : outdec -> string
 val outdecTy   : outdec -> ty

 val port_name  : port -> string
 val port_ty    : port -> ty
 val is_in_port : port -> bool
 val is_out_port: port -> bool
 val is_event   : port -> bool
 val is_data    : port -> bool

 val sort_tydecs : tydec list -> tydec list
 val sort_tmdecs : tmdec list -> tmdec list

 val tydec_to_ty : tydec -> ty
 val is_const_dec : tmdec -> bool
 val mk_tyE : pkg list -> qid -> ty option
 val mk_constE : pkg list -> id -> ty option
 val mk_recd_projns : tydec list -> tmdec list
end
