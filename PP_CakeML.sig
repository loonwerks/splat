signature PP_CakeML =
sig
    type ty = AST.ty
    type exp = AST.exp
    type decl = AST.decl
    type pretty = PolyML.pretty

    val pp_ty : int -> ty -> pretty
    val pp_exp : int -> exp -> pretty
    val pp_decl : int -> decl -> pretty
    val pp_tydec : int -> AADL.tydec -> pretty
    val pp_tmdec : int -> AADL.tmdec -> pretty
    val pp_filter : int -> AADL.filter -> pretty
    val pp_monitor : int -> AADL.monitor -> pretty
    val pp_pkg     : int -> AADL.pkg -> pretty

end
