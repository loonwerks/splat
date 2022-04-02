signature AADL =
sig
 include Abbrev

  type qid = string * string
  type ty = AST.ty
  type exp = AST.exp
  type tyEnv = (ty * ty) list
  type port = string * ty * string * string

 datatype tydec
    = EnumDec of qid * string list
    | RecdDec of qid * (string * ty) list
    | ArrayDec of qid * ty   (* ty is an ArrayTy *)
    | UnionDec of qid * (string * ty) list

 datatype tmdec
    = ConstDec of qid * ty * exp
    | FnDec of qid * (string * ty) list * ty * exp

 datatype outdec
    = DataG of string * exp
    | EventG of string * exp
    | EDataG of string * exp * exp;

datatype filter (*  (name,ports,decs,ivars,(codeGs,otherGs))  *)
    = FilterDec
        of qid
        * (string * ty * string * string) list
        * tmdec list
        * (string * ty * exp) list
        * ((string * string * codeguar) list * (string * string * exp) list)

 datatype monitor  (*  (name,ports,latched,decs,ivars,(codeGs,otherGs))  *)
    = MonitorDec
       of qid
        * (string * ty * string * string) list
        * bool
        * tmdec list
        * (string * ty * exp) list
        * ((string * string * codeguar) list * (string * string * exp) list)


 type decls =
  (* pkgName *)  string *
  (* types *)    (tydec list *
  (* consts *)    tmdec list *
  (* filters *)   filter list *
  (* monitors *)  monitor list)

 datatype pkg = Pkg of decls

 val scrape : Json.json -> decls
 val scrape_pkgs : Json.json -> decls list

 val tydec_qid : tydec -> qid
 val tmdec_qid : tmdec -> qid

 val port_name : port -> string
 val port_ty   : port -> ty
 val is_in_port : port -> bool
 val is_out_port: port -> bool
 val is_event  :  port -> bool
 val is_data   :  port -> bool

 val sort_tydecs : tydec list -> tydec list
 val sort_tmdecs : tmdec list -> tmdec list
end
