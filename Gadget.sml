(*---------------------------------------------------------------------------*)
(* A gadget is a refined version of AADL.contract type. It is mainly aimed   *)
(* at code generation to CakeML. The refinement is mainly that the "support" *)
(* for the computation in the gadget is pulled in from earlier AADL package  *)
(* declarations. Thus the tydecs and tmdecs provide the background to define *)
(* the computation specified by the ivardecs and outdecs.                    *)
(*---------------------------------------------------------------------------*)

structure Gadget :> Gadget =
struct

open Lib Feedback HolKernel boolLib ;
open MiscLib AST AADL;

fun substFn alist x =
 case subst_assoc (equal x) alist
  of SOME y => y
   | NONE => x

fun alistFn alist x = assoc x alist;

type port    = string * ty * string * string;  (* (id,ty,dir,kind) *)
type ivardec = string * ty * exp;
type guar    = string * string * exp;

val transRval   = AST.transRval;
val mk_tyE      = AADL.mk_tyE;
val tydec_to_ty = AADL.tydec_to_ty
val mk_constE   = AADL.mk_constE;
val mk_recd_projns = AADL.mk_recd_projns;

(*---------------------------------------------------------------------------*)
(* The gadget type + projections                                             *)
(*---------------------------------------------------------------------------*)

datatype gadget =
 Gadget of qid
           * tydec list
           * tmdec list
           * port list
           * ivardec list
           * outdec list;

fun gadget_qid (Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs)) = qid;
fun gadget_ports (Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs)) = ports;
fun gadget_tydecs (Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs)) = tydecs;
fun gadget_tmdecs (Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs)) = tmdecs;
fun gadget_outdecs (Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs)) = outdecs;

fun get_ports gdt =
 let val ports = gadget_ports gdt
 in (filter is_in_port ports,filter is_out_port ports)
 end

(*---------------------------------------------------------------------------*)
(* Create gadgets from a list of pkgs. This essentially moves all the type   *)
(* and term declarations from the ancestry of a contract into the contract   *)
(*---------------------------------------------------------------------------*)

fun set_tmdec_pkgName name tmdec =
 case tmdec
  of ConstDec((_,s),ty,exp) => ConstDec((name,s),ty,exp)
   | FnDec ((_,s),params,rty,exp) => FnDec ((name,s),params,rty,exp)

fun contract_to_gadget tydecs tmdecs (ContractDec condec) =
 let val (qid,_,ports,latched,con_tydecs,con_tmdecs,vdecs,odecs,A,G) = condec
     val tydecs'  = AADL.sort_tydecs (tydecs @ con_tydecs)
     val condecs' = map (set_tmdec_pkgName (snd qid)) con_tmdecs
     val tmdecs'  = AADL.sort_tmdecs (tmdecs @ condecs')
     val outdecs  = map #3 odecs
 in
   Gadget (qid, tydecs', tmdecs', ports, vdecs, outdecs)
 end;

(*---------------------------------------------------------------------------*)
(* A "pkg" represents an AADL package (roughly).                             *)
(*---------------------------------------------------------------------------*)

fun configure pkg (support,gadgets) =
 let val (pkgName,(tydecs,tmdecs,condecs)) = pkg
     val (stydecs,stmdecs) = support
     val tydecs' = tydecs @ stydecs
     val tmdecs' = tmdecs @ stmdecs
     val new = List.map (contract_to_gadget tydecs' tmdecs') condecs
 in
     ((tydecs',tmdecs'), new @ gadgets)
end

fun mk_gadgets pkgs = snd (rev_itlist configure pkgs (([],[]),[]));

(*---------------------------------------------------------------------------*)
(* Map substitution over gadget                                              *)
(*---------------------------------------------------------------------------*)

fun catE env1 env2 x =
  case env1 x
   of NONE => env2 x
    | SOME y => SOME y;

fun empty_varE _ = NONE;

fun transRval_dec E tmdec =
 case tmdec
  of ConstDec (qid,ty,exp) => ConstDec (qid,ty,transRval (E,empty_varE) exp)
   | FnDec (qid,params,ty,exp) =>
     FnDec (qid,params,ty, transRval (E,assocFn params) exp)
;

fun trans_ivardec E (s,ty,e) = (s,ty,transRval E e)

fun trans_outdec E odec =
 case odec
  of Out_Data (s,ty,e) => Out_Data (s,ty,transRval E e)
   | Out_Event_Only(s,ty,e) => Out_Event_Only(s,ty,transRval E e)
   | Out_Event_Data(s,ty,b,e) => Out_Event_Data(s,ty,transRval E b,transRval E e)

fun portE ports =
 let fun dest_port (id,ty,_,_) = (id,ty)
 in assocFn (map dest_port ports)
 end

fun ivarE ivars =
 let fun dest_ivar (id,ty,_) = (id,ty)
 in assocFn (map dest_ivar ivars)
 end

(*---------------------------------------------------------------------------*)
(* Add synthesized projn fn defs after eliminating record projections.       *)
(*---------------------------------------------------------------------------*)

fun transRval_gadget E gadget =
 let val Gadget (qid,tydecs, tmdecs, ports,ivardecs,outdecs) = gadget
     val tmdecs'   = map (transRval_dec E) tmdecs
     val tmdecs''  = mk_recd_projns tydecs @ tmdecs'
     val varE      = catE (portE ports) (ivarE ivardecs)
     val ivardecs' = map (trans_ivardec (E,varE)) ivardecs
     val outdecs'  = map (trans_outdec (E,varE)) outdecs
 in
    Gadget (qid, tydecs, tmdecs'', ports,ivardecs',outdecs')
 end

fun elim_projections tyE tmE gdt = transRval_gadget (tyE,tmE) gdt;

fun substExp_tmdec theta tmdec =
 case tmdec
  of ConstDec (qid,ty,e) => ConstDec (qid,ty,substExp theta e)
   | FnDec(qid,params,rty,e) => FnDec(qid,params,rty,substExp theta e)

fun substExp_ivar theta (s,ty,e) = (s,ty,substExp theta e)

fun substExp_outdec theta outdec =
 case outdec
  of Out_Data (s,ty,e) => Out_Data (s,ty,substExp theta e)
   | Out_Event_Only(s,ty,e) => Out_Event_Only(s,ty,substExp theta e)
   | Out_Event_Data(s,ty,b,e) =>
     Out_Event_Data(s,ty,substExp theta b,substExp theta e);


fun substExp_gadget theta gdt =
 let val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
 in Gadget(qid,tydecs,
           map (substExp_tmdec theta) tmdecs,
           ports,
           map (substExp_ivar theta) ivars,
           map (substExp_outdec theta) outdecs)
 end;

fun gadget_tyE gdt =
 let val Gadget (_,tydecs, _,_,_,_) = gdt
     fun mk_tydec_bind tydec = (tydec_qid tydec,tydec_to_ty tydec)
     val tydec_alist = map mk_tydec_bind tydecs
 in
   tydec_alist
 end

(*---------------------------------------------------------------------------*)
(* gadget_tyEnvs gdt = (varEnv,tyEnv,constEnv) where                         *)
(*                                                                           *)
(*  varEnv   : string -> ty  gives the types of variables                    *)
(*  tyEnv    : qid -> ty     expands NamedTys to their unabbrev'd defns      *)
(*  constEnv : qid -> ty     gives the return type for constants and fns     *)
(*---------------------------------------------------------------------------*)

fun gadget_tyEnvs gdt =
 let open AST
     val Gadget (qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     val tyE_0 = gadget_tyE gdt
     fun chase list = list
     val tyE = chase tyE_0
     fun rng (ConstDec(qid,ty,e)) = (qid,ty)
       | rng (FnDec(qid,params,rty,e)) = (qid,rty)
     val tmE = map rng tmdecs
     fun bind_of_port (id,ty,dir,kind) = (id,ty)
     fun bind_of_ivar (id,ty,e) = (id,ty)
     val varE = map bind_of_port ports @ map bind_of_ivar ivars
 in
     (alistFn varE, alistFn tyE, alistFn tmE)
 end

(*---------------------------------------------------------------------------*)
(* Types/Definitions can come from a variety of packages, but they all get   *)
(* thrown into the "Defs" structure, so we rename all the qids to reflect    *)
(* that.                                                                     *)
(*---------------------------------------------------------------------------*)

fun tmdec_qids tmdec set =
  case tmdec
   of ConstDec (qid,ty,exp) => AST.expQids exp (insert qid set)
    | FnDec (qid,parames,rty,exp) => AST.expQids exp (insert qid set);

fun ivardec_qids (s,ty,exp) set = AST.expQids exp set

fun outdec_qids outdec set =
 case outdec
  of Out_Data (s,ty,e) => AST.expQids e set
   | Out_Event_Only(s,ty,e) => AST.expQids e set
   | Out_Event_Data(s,ty,b,e) => AST.expQids e (AST.expQids e set)

fun gadgetQids gdt set =
 let val Gadget(qid,_,tmdecs,_,ivars,outdecs) = gdt
     val set1 = itlist tmdec_qids tmdecs set
     val set2 = itlist ivardec_qids ivars set1
     val set3 = itlist outdec_qids outdecs set2
 in set3
 end

fun subst_qid theta qid =
  case subst_assoc (equal qid) theta
   of NONE => qid
    | SOME qid' => qid';

fun substQid_tmdec theta tmdec =
  case tmdec
   of ConstDec (qid,ty,exp) =>
      ConstDec (subst_qid theta qid,ty,substQidExp theta exp)
    | FnDec (qid,parames,rty,exp) =>
      FnDec (subst_qid theta qid,parames,rty,substQidExp theta exp)

fun substQid_ivar theta (s,ty,exp) = (s,ty,substQidExp theta exp);

fun substQid_outdec theta outdec =
 case outdec
  of Out_Data (s,ty,e) => Out_Data (s,ty,substQidExp theta e)
   | Out_Event_Only(s,ty,e) => Out_Event_Only(s,ty,substQidExp theta e)
   | Out_Event_Data(s,ty,b,e) =>
      Out_Event_Data(s,ty,substQidExp theta b,substQidExp theta e)

fun substQid_gadget theta gdt =
 let val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
 in Gadget(qid,tydecs,
           map (substQid_tmdec theta) tmdecs,
           ports,
           map (substQid_ivar theta) ivars,
           map (substQid_outdec theta) outdecs)
 end;

fun set_Defs_struct gdt =
 let fun mk_def_qid (qid as (s1,s2)) acc =
        if s1 = "" then acc else (qid |-> ("Defs",s2))::acc
     val gqids = gadgetQids gdt []
     val theta = itlist mk_def_qid gqids []
 in substQid_gadget theta gdt
 end

(*---------------------------------------------------------------------------*)
(* Unhappily it can happen that identifiers that *are* the names of          *)
(* constants, and which *should* be constants, arrive in the .json as free   *)
(* variables. This manifests as a free variable occurring in one of the      *)
(* following cases                                                           *)
(*                                                                           *)
(*  - the body of a constant or function declaration (tmdecs)                *)
(*  - in the rhs of an ivar declaration (where the rhs can legitimately have *)
(*    other ivars, and ports, occurring as free vars)                        *)
(*  - in a guarantee (where the guar can have legit ivar and portname occs). *)
(*                                                                           *)
(* This pass is an attempt to repair such anomalies.                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun corral_rogue_vars gdt =
 let val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     fun free_tmdecV tmdec =
       case tmdec
        of ConstDec (_,_,e) => AST.expVars e
         | FnDec(_,params,_,e) => subtract (AST.expVars e) (map fst params)
     fun free_ivarsV (_,_,e) = AST.expVars e
     fun free_outdecV outdec =
       case outdec
       of Out_Data (s,ty,e) => AST.expVars e
        | Out_Event_Only(s,ty,e) => AST.expVars e
        | Out_Event_Data(s,ty,b,e) => Lib.union (AST.expVars b) (AST.expVars e)

     val constNames = map (snd o tmdec_qid) tmdecs
     val portNames = map #1 ports
     val ivarNames = map #1 ivars
     val taken = portNames @ ivarNames

     val tmdec_probs = intersect (bigU (map free_tmdecV tmdecs)) constNames
     val ivar_probs = subtract (bigU (map free_ivarsV ivars)) taken
     val odec_probs = subtract (bigU (map free_outdecV outdecs)) taken
     val problems = bigU [tmdec_probs, ivar_probs, odec_probs]
 in
   if null problems then
     gdt
   else
     let fun mk_bind id = (VarExp id |-> ConstExp(IdConst("Defs",id)))
         val theta = map mk_bind problems
     in
      substExp_gadget theta gdt
     end
 end;

(*---------------------------------------------------------------------------*)
(* A pass that sets type constructors and eliminates record expressions in   *)
(* favour of constructor application.                                        *)
(*---------------------------------------------------------------------------*)

fun constrs_of tydec =
 case tydec
  of EnumDec (qid,ids) => map (pair qid) ids
   | RecdDec (qid,fields) => [(qid,snd qid)]
   | UnionDec (qid,constrs) => map (pair qid o fst) constrs
   | ArrayDec _ => []

fun set_type_constrs gdt =
 let open AST
     val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     val tycE = List.concat (map constrs_of tydecs)
     val consts = gadgetQids gdt []
     fun equiv (pname,fName) (qname,constrName) = (fName = constrName)
     fun itFn qid acc =
       case total (first (equiv qid)) tycE
        of NONE => acc
	 | SOME cqid => (qid,cqid)::acc
   val theta = itlist itFn consts []
   fun assocConstr x alist =
    case assoc1 x alist
     of NONE => NONE
      | SOME (_,y) => SOME y
   fun subExp exp =
   case exp
    of VarExp _ => exp
     | ConstExp (IdConst qid) =>
        (case assocConstr qid theta
          of NONE => exp
          | SOME (tyqid,id) => ConstrExp(tyqid,id,[]))
     | ConstExp _ => exp
     | Unop(opr,e) => Unop(opr,subExp e)
     | Binop(opr,e1,e2) => Binop(opr,subExp e1,subExp e2)
     | ArrayExp elist => ArrayExp(map subExp elist)
     | ArrayIndex(e,elist) => ArrayIndex (subExp e, map subExp elist)
     | ConstrExp(qid,id,elist) => ConstrExp(qid,id,map subExp elist)
     | Fncall(qid,elist) =>
        (case assocConstr qid theta
          of NONE => Fncall(qid, map subExp elist)
           | SOME (tyqid,id) => ConstrExp(tyqid,id, map subExp elist))
     | RecdExp(tyqid,fields) => ConstrExp(tyqid,snd tyqid, map (subExp o snd) fields)
     | RecdProj(e,id) => RecdProj(subExp e,id)
   fun subDec tmdec =
     case tmdec
      of ConstDec(qid,ty,exp) => ConstDec(qid,ty,subExp exp)
       | FnDec(qid,params,rty,exp) => FnDec(qid,params,rty,subExp exp)
   fun subIvar (s,ty,exp) = (s,ty,subExp exp)
   fun subOutdec outdec =
    case outdec
     of Out_Data (s,ty,e) => Out_Data (s,ty,subExp e)
      | Out_Event_Only(s,ty,e) => Out_Event_Only(s,ty,subExp e)
      | Out_Event_Data(s,ty,b,e) =>
         Out_Event_Data(s,ty,subExp b,subExp e)
 in
    Gadget(qid,tydecs,
	   map subDec tmdecs,
           ports,
           map subIvar ivars,
           map subOutdec outdecs)
 end;

(*---------------------------------------------------------------------------*)
(* CakeML uses case to distinguish datatype constructors from variables      *)
(* (val bindings, fun params, etc). Constructors start with an upper case    *)
(* letter. Variables start with lower case. "set_defs_lower_case" is a pass  *)
(* lowering all const and fun names that don't comply. Probably need a       *)
(* corresponding "upper-case-ification" for any constructors that happen to  *)
(* start with a lower case letter.                                           *)
(*---------------------------------------------------------------------------*)

fun svariants start vlist =
 let fun fresh v (freshV,supp) =
      let val v' = MiscLib.numeric_string_variant "_" supp v
      in (v' :: freshV, v'::supp)
      end
 in
     fst(itlist fresh vlist ([],start))
 end;

val svariant = MiscLib.numeric_string_variant "_";

fun insertList list set = itlist insert list set;
fun id_of_qid (pkg,s) = if String.size pkg = 0 then "" else s;

fun gadgetIds gdt set =
 let fun expIds exp set =
      case exp
       of VarExp id => insert id set
        | ConstExp (IdConst qid) => insert (id_of_qid qid) set
        | ConstExp _ => set
        | Unop(opr,e) => expIds e set
        | Binop(opr,e1,e2) => expIds e2 (expIds e1 set)
        | ArrayExp elist => itlist expIds elist set
        | ArrayIndex(e,elist) => itlist expIds (e::elist) set
        | ConstrExp((_,id1),id2,elist) => itlist expIds elist set
        | Fncall(qid,elist) => itlist expIds elist (insert (id_of_qid qid) set)
        | RecdExp(qid,fields) => itlist expIds (map snd fields) set
        | RecdProj(e,id) => expIds e set

     fun tyExpIds ty set =
      case ty
       of BaseTy _ => set
       | NamedTy (_,id) => set
       | RecdTy((_,id),flist) => itlist (tyExpIds o snd) flist set
       | ArrayTy(ty,elist) => tyExpIds ty (itlist expIds elist set)

      fun tydecIds tydec set = (* constants can occur in array decs *)
       case tydec
        of EnumDec (qid, slist) => set
         | RecdDec (qid, flds) => itlist tyExpIds (map snd flds) set
         | ArrayDec (qid,ty) => tyExpIds ty set
         | UnionDec (qid, constrs) =>
           let fun constrIds (cname,ty) set = tyExpIds ty set
           in itlist constrIds constrs set
           end

      fun tmdecIds tmdec set =
        case tmdec
         of ConstDec (qid,ty,exp) =>
               expIds exp (tyExpIds ty (insert (id_of_qid qid) set))
          | FnDec (qid,params,rty,exp) =>
             let val (pIds,ptys) = unzip params
             in
              expIds exp
                 (itlist tyExpIds ptys
                      (insertList (id_of_qid qid :: pIds) set))
             end
      fun portIds (name,ty,_,_) set = tyExpIds ty (insert name set);
      fun ivardecIds (s,ty,exp) set = expIds exp (tyExpIds ty (insert s set));
      fun outdecIds outdec set =
        case outdec
         of Out_Data (s,ty,e) => expIds e (tyExpIds ty set)
          | Out_Event_Only(s,ty,e) => expIds e (tyExpIds ty set)
          | Out_Event_Data(s,ty,b,e) => expIds e (expIds b set)

      val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
 in
       itlist outdecIds outdecs
        (itlist ivardecIds ivars
          (itlist portIds ports
            (itlist tmdecIds tmdecs
              (itlist tydecIds tydecs set))))
 end;

fun is_upper s = 0 < String.size s andalso Char.isUpper (String.sub(s,0));
fun is_lower s = 0 < String.size s andalso Char.isLower (String.sub(s,0));
val mk_low = String.map Char.toLower

fun mk_low_qid (qid as (s1,s2)) (acc as (binds,taken)) =
 if s1 = "" orelse is_lower s2 then
    acc
 else
   let val s2' = svariant taken (mk_low s2)
   in ((qid |-> (s1,s2'))::binds, s2' :: taken)
   end

(*
fun set_sig_lower_case gdt =
 let open AST
   val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
   val gQids = gadgetQids gdt []
   val gIds = gadgetIds gdt []
   val (UC,LC_0) = List.partition is_upper gIds
   val LC = filter (fn s => 0 < String.size s) LC_0
   val (theta,LC') = itlist mk_low_qid gqids ([],LC)
   fun subExp (exp:exp) =
     case exp
      of VarExp _ => exp
       | ConstExp (IdConst qid) => ConstExp(IdConst (substFn theta qid))
       | ConstExp _ => exp
       | Unop(opr,e) => Unop(opr,subExp e)
       | Binop(opr,e1,e2) => Binop(opr,subExp e1,subExp e2)
       | ArrayExp elist => ArrayExp(map subExp elist)
       | ArrayIndex(e,elist) => ArrayIndex (subExp e, map subExp elist)
       | ConstrExp(qid,id,elist) => ConstrExp(qid,id,map subExp elist)
       | Fncall(qid,elist) => Fncall(substFn theta(qid), map subExp elist)
       | RecdExp(qid,fields) => RecdExp(qid, map (I##subExp) fields)
       | RecdProj(e,id) => RecdProj(subExp e,id)
   fun subTyExp ty =
      case ty
       of BaseTy _ => ty
        | NamedTy _ => ty
        | RecdTy(qid,flist) => RecdTy(qid, map (I##subTyExp) flist)
        | ArrayTy(ty,elist) => ArrayTy(subTyExp ty, map subExp elist)
   fun subDec tmdec =
     case tmdec
       of ConstDec(qid,ty,exp) =>
          ConstDec(substFn theta qid,subTyExp ty,subExp exp)
        | FnDec(qid,params,rty,exp) =>
          FnDec(substFn theta qid,
                map (I##subTyExp) params,
                subTyExp rty,subExp exp)
   fun subTyDec tydec =
     case tydec
      of EnumDec => tydec
       | RecdDec (qid, flds) => RecdDec(qid, map (I##subTyExp) flds)
       | ArrayDec (qid,ty) => ArrayDec(qid,subTyExp ty)
       | UnionDec (qid, constrs) =>
           let fun subConstr (cname,ty) = (cname,subTyExp ty)
           in UnionDec(qid,map subConstr constrs)
           end
   fun subPort (n,ty,x,y) = (n,subTyExp ty,x,y)
   fun subIvar (s,ty,exp) = (s,subTyExp ty,subExp exp)
   fun subOutdec outdec =
    case outdec
     of Out_Data (s,ty,e) => Out_Data (s,ty,subExp e)
      | Out_Event_Only(s,ty,e) => Out_Event_Only(s,ty,subExp e)
      | Out_Event_Data(s,ty,b,e) => Out_Event_Data(s,ty,subExp b,subExp e)

 in
   Gadget(qid,
          map subTyDec tydecs,
          map subDec tmdecs,
          map subPort ports,
          map subIvar ivars,
          map subOutdec outdecs)
 end;

    fun set_ports_and_ivars_lower_case gdt =
     let open AST
         val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
         val portNames = map #1 ports
         val ivarNames = map #1 ivars
         val lower = String.map Char.toLower
         fun mk_lowId id acc =
    	 if Char.isLower(String.sub(id,0)) then
    	     acc
             else (VarExp id |-> VarExp (lower id))::acc
         val theta = itlist mk_lowId (portNames@ivarNames) []
         fun substId s = if Char.isLower(String.sub(s,0)) then s else lower s
         fun substPort (s,ty,dir,kind) = (substId s,ty,dir,kind)
         fun substIvar theta (s,ty,exp) = (substId s,ty,substExp theta exp)
         fun substGuar theta (s1,s2,exp) = (s1,s2,substExp theta exp)
     in Gadget(qid,tydecs,tmdecs,
               map substPort ports,
               map (substIvar theta) ivars,
               map (substGuar theta) outdecs)
     end;
*)

fun set_sig_lower_case gdt =
 let open AST
     val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     val mk_low = String.map Char.toLower
     fun mk_low_qid (qid as (s1,s2)) acc =
         if s1 = "" orelse Char.isLower(String.sub(s2,0)) then
            acc
         else (qid |-> (s1,mk_low s2))::acc
     val gqids = gadgetQids gdt []
     val theta = itlist mk_low_qid gqids []

     fun subTy ty =   (* Not sure this is needed right now *)
      case ty
       of RecdTy(qid,flist) => RecdTy (qid,map (I##subTy) flist)
        | ArrayTy(ty,elist) => ArrayTy (subTy ty, map subExp elist)
        | otherwise => ty
     and
     subExp (exp:exp) =
     case exp
      of VarExp _ => exp
       | ConstExp (IdConst qid) => ConstExp(IdConst (substFn theta qid))
       | ConstExp _ => exp
       | Unop(opr,e) => Unop(opr,subExp e)
       | Binop(opr,e1,e2) => Binop(opr,subExp e1,subExp e2)
       | ArrayExp elist => ArrayExp(map subExp elist)
       | ArrayIndex(e,elist) => ArrayIndex (subExp e, map subExp elist)
       | ConstrExp(qid,id,elist) => ConstrExp(qid,id,map subExp elist)
       | Fncall(qid,elist) => Fncall(substFn theta(qid), map subExp elist)
       | RecdExp(qid,fields) => RecdExp(qid, map (I##subExp) fields)
       | RecdProj(e,id) => RecdProj(subExp e,id)
     fun subDec tmdec =
       case tmdec
        of ConstDec(qid,ty,exp) =>
           ConstDec(substFn theta qid,ty,subExp exp)
         | FnDec(qid,params,rty,exp) =>
           FnDec(substFn theta qid,params,rty,subExp exp)
     fun subIvar (s,ty,exp) = (s,ty,subExp exp)
   fun subOutdec outdec =
    case outdec
     of Out_Data (s,ty,e) => Out_Data (s,ty,subExp e)
      | Out_Event_Only(s,ty,e) => Out_Event_Only(s,ty,subExp e)
      | Out_Event_Data(s,ty,b,e) => Out_Event_Data(s,ty,subExp b,subExp e)
 in
   Gadget(qid,tydecs,
          map subDec tmdecs,
          ports,
          map subIvar ivars,
          map subOutdec outdecs)
 end;

fun set_ports_and_ivars_lower_case gdt =
 let open AST
     val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     val portNames = map #1 ports
     val ivarNames = map #1 ivars
     val lower = String.map Char.toLower
     fun mk_lowId id acc =
	 if Char.isLower(String.sub(id,0)) then
	     acc
         else (VarExp id |-> VarExp (lower id))::acc
     val theta = itlist mk_lowId (portNames@ivarNames) []
     fun substId s = if Char.isLower(String.sub(s,0)) then s else lower s
     fun substPort (s,ty,dir,kind) = (substId s,ty,dir,kind)
     fun substIvar theta (s,ty,exp) = (substId s,ty,substExp theta exp)
 in
   Gadget(qid,tydecs,tmdecs,
          map substPort ports,
          map (substIvar theta) ivars,
          map (substExp_outdec theta) outdecs)
 end;

(*---------------------------------------------------------------------------*)
(* At runtime input ports are parsed to port values. In the body of the      *)
(* stepFn, event(p) calls will extract whether or not there's an event on    *)
(* port p. Port p can also occur where it is not of the form "event(p)". In  *)
(* that case, the contract is implicitly extracting the data from the port,  *)
(* and so we replace "p" by a call "dataOf(p)".                               *)
(*---------------------------------------------------------------------------*)

fun add_inport_data_projns gdt =
 let open AST
     val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     val inports = filter is_in_port ports
     val eiports = filter is_event inports
     val portNames = map #1 eiports
     fun mk_bind1 s = (Fncall(("","event"),[VarExp s]) |-> VarExp("event--"^s))
     fun mk_bind2 s = (VarExp s |-> Fncall(("","Port.dataOf"),[VarExp s]))
     fun mk_bind3 s = (VarExp("event--"^s) |-> Fncall(("","Port.event"),[VarExp s]))
     val theta1 = map mk_bind1 portNames  (* move event(p) out of way *)
     val theta2 = map mk_bind2 portNames  (* do intended replacement *)
     val theta3 = map mk_bind3 portNames  (* restore event(p) *)
     fun substIvar theta (s,ty,exp) = (s,ty,substExp theta exp)
 in Gadget(qid,tydecs,tmdecs,ports,
           map (substIvar theta3
                 o substIvar theta2
                 o substIvar theta1) ivars,
           map (substExp_outdec theta3
                 o substExp_outdec theta2
                 o substExp_outdec theta1) outdecs)
 end;


(*---------------------------------------------------------------------------*)
(* At runtime input ports are parsed to port values. In the body of the      *)
(* stepFn, event(p) calls will extract whether or not there's an event on    *)
(* port p. Port p can also occur where it is not of the form "event(p)". In  *)
(* that case, the contract is implicitly extracting the data from the port,  *)
(* and so we replace "p" by an explicit call "dataOf(p)".                    *)
(*---------------------------------------------------------------------------*)

fun add_inport_data_projns gdt =
 let open AST
     val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     val inports = filter is_in_port ports
     val eiports = filter is_event inports
     val portNames = map #1 eiports
     fun mk_bind1 s = (Fncall(("","event"),[VarExp s]) |-> VarExp("event--"^s))
     fun mk_bind2 s = (VarExp s |-> Fncall(("","Port.dataOf"),[VarExp s]))
     fun mk_bind3 s = (VarExp("event--"^s) |-> Fncall(("","Port.event"),[VarExp s]))
     val theta1 = map mk_bind1 portNames  (* move event(p) out of way *)
     val theta2 = map mk_bind2 portNames  (* do intended replacement *)
     val theta3 = map mk_bind3 portNames  (* restore event(p) *)
     fun substIvar theta (s,ty,exp) = (s,ty,substExp theta exp)
 in Gadget(qid,tydecs,tmdecs,ports,
           map (substIvar theta3
                 o substIvar theta2
                 o substIvar theta1) ivars,
           map (substExp_outdec theta3
                 o substExp_outdec theta2
                 o substExp_outdec theta1) outdecs)
 end;


(*---------------------------------------------------------------------------*)
(* Eliminate definitions from gadget. (Currently just constant decls.)       *)
(*---------------------------------------------------------------------------*)

fun elim_defs gdt =
 let open AST
     val Gadget(qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt
     fun build tmdec theta =
       case tmdec
        of ConstDec (qid,ty,exp) =>
                (ConstExp(IdConst(qid)) |-> substExp theta exp) :: theta
         | FnDec (qid,params,ty,body) => theta
     val theta = rev_itlist build tmdecs []
 in
    Gadget(qid,tydecs,[],ports,
           map (substExp_ivar theta) ivars,
           map (substExp_outdec theta) outdecs)
 end


end
