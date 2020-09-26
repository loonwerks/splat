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
    | ArrayDec of qid * ty
    | UnionDec of qid * (string * ty) list

 datatype tmdec
    = ConstDec of qid * ty * exp
    | FnDec of qid * (string * ty) list * ty * exp

 datatype filter
    = FilterDec (* (name,ports,props) *)
        of qid * (string * ty * string * string) list * (string * exp) list

 datatype monitor
    = MonitorDec of qid * (string * ty * string * string) list
                        * bool
                        * (string * string * exp) list

 type decls =
  (* pkgName *)  string *
  (* types *)    (tydec list *
  (* consts *)    tmdec list *
  (* filters *)   filter list *
  (* monitors *)  monitor list)
  ;

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
end
