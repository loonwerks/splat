signature PP_CakeML =
sig
    type ty = AST.ty
    type exp = AST.exp
    type decl = AST.decl
    type pretty = PolyML.pretty

    val pp_ty : int -> string -> ty -> pretty
    val pp_exp : int -> string -> exp -> pretty
    val pp_decl : int -> string -> decl -> pretty
    val pp_tydec : int -> string -> AADL.tydec -> pretty
    val pp_tmdec : int -> string -> AADL.tmdec -> pretty
    val pp_filter : int -> AADL.filter -> pretty
    val pp_monitor : int -> AADL.monitor -> pretty
    val pp_pkg     : int -> AADL.pkg -> pretty

   val export_cakeml_monitors : string -> (string * exp) list -> AADL.monitor list -> unit
end
