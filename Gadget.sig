signature Gadget =
sig

 type id = AST.id
 type qid = AST.qid
 type ty = AST.ty
 type exp = AST.exp
 type tydec = AADL.tydec
 type tmdec = AADL.tmdec
 type indec = AADL.indec
 type outdec = AADL.outdec
 type ivardec = string * ty * exp
 type port = string * ty * string * string
 type pkg = AADL.pkg
 type contract = AADL.contract

 datatype gadget =
  Gadget of
     qid
   * tydec list
   * tmdec list
   * port list
   * ivardec list
   * outdec list;

 val gadget_qid   : gadget -> qid
 val gadget_ports : gadget -> port list
 val get_ports    : gadget -> port list * port list
 val gadget_tydecs : gadget -> tydec list
 val gadget_tmdecs : gadget -> tmdec list
 val gadget_outdecs : gadget -> outdec list

 val gadgetIds  : gadget -> id list -> id list
 val gadgetQids : gadget -> qid list -> qid list

 val gadget_tyE : gadget -> (qid * ty) list
 val gadget_tyEnvs : gadget -> (string -> ty) * (qid -> ty) * (qid -> ty)

 val substQid_gadget : (qid, qid) Lib.subst -> gadget -> gadget
 val substExp_gadget : (exp, exp) AST.subst -> gadget -> gadget

 val contract_to_gadget : tydec list -> tmdec list -> contract -> gadget
 val mk_gadgets : pkg list -> gadget list

 val elim_projections  : (qid -> ty option) -> (id -> ty option) -> gadget -> gadget
 val corral_rogue_vars : gadget -> gadget
 val set_Defs_struct   : gadget -> gadget
 val set_type_constrs  : gadget -> gadget
 val set_sig_lower_case : gadget -> gadget
 val set_ports_and_ivars_lower_case : gadget -> gadget
 val add_inport_data_projns : gadget -> gadget
 val elim_defs : gadget -> gadget

end
