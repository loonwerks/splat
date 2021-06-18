signature AADL =
sig
 include Abbrev

  type qid = string * string
  type ty = AST.ty
  type exp = AST.exp
  type tyEnv = (ty * ty) list

 datatype tydec
    = EnumDec of qid * string list
    | RecdDec of qid * (string * ty) list
    | ArrayDec of qid * ty   (* ty is an ArrayTy *)
    | UnionDec of qid * (string * ty) list

 datatype tmdec
    = ConstDec of qid * ty * exp
    | FnDec of qid * (string * ty) list * ty * exp

 datatype filter (*  (name,ports,decs,ivars,guars)  *)
    = FilterDec
        of qid
        * (string * ty * string * string) list
        * tmdec list
        * (string * ty * exp) list
        * (string * string * exp) list

 datatype monitor  (*  (name,ports,latched,decs,ivars,guars)  *)
    = MonitorDec of qid
                 * (string * ty * string * string) list
                 * bool
                 * tmdec list
                 * (string * ty * exp) list
                 * (string * string * exp) list

 type decls =
  (* pkgName *)  string *
  (* types *)    (tydec list *
  (* consts *)    tmdec list *
  (* filters *)   filter list *
  (* monitors *)  monitor list)

 datatype pkg = Pkg of decls

 val scrape : Json.json -> decls
 val scrape_pkgs : Json.json -> decls list

 val abstract_model_nums : decls -> decls

 val mk_pkg_defs
    : string
        -> tyEnv
          -> decls
            -> tyEnv * thm list (* types *)
                     * thm list (* constant defns *)
                     * ((string * string) * thm) list (* filters *)
                     * ((string * string) * thm) list (* monitors *)

 val pkgs2hol
      : string
         -> decls list
           -> tyEnv * thm list (* types *)
                    * thm list (* constant defns *)
                    * ((string * string) * thm) list (* filters *)
                    * ((string * string) * thm) list (* monitors *)

 val export_cakeml_filters : string -> (string * exp) list -> filter list -> unit

 datatype port
    = Event of string
    | Data of string * ty
    | EventData of string * ty;

 val tydec_qid : tydec -> qid
 val tmdec_qid : tmdec -> qid

 val sort_tydecs : tydec list -> tydec list
 val sort_tmdecs : tmdec list -> tmdec list
end
