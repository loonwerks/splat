(*---------------------------------------------------------------------------*)
(* Maps from Json representation of AADL to AST and then to CakeML code.     *)
(*---------------------------------------------------------------------------*)

open Lib Feedback HolKernel boolLib MiscLib bossLib;

(*
load "intrealSyntax";
*)

local open
   AADL regexpLib regexpSyntax realLib realSyntax intrealSyntax PP_CakeML Gen_Contig
in end

val ERR = Feedback.mk_HOL_ERR "splat";

fun printHelp() =
  MiscLib.stdErr_print
    ("Usage: splat [-target (hamr | standalone)]\n\
     \             [-outdir <dirname>]\n\
     \             [-intwidth <int>]\n\
     \             [-endian (LSB | MSB)]\n\
     \             <name>.json\n")

fun fail() = (printHelp(); MiscLib.fail())

fun failwithERR e =
  (MiscLib.stdErr_print (Feedback.exn_to_string e^"\n\n"); MiscLib.fail());

val FLAGS =
  {target   = ref NONE : string option ref,
   codegen  = ref NONE : string option ref,
   outDir   = ref NONE : string option ref,
   intwidth = ref NONE : int option ref,
   endian   = ref NONE : Regexp_Numerics.endian option ref,
   encoding = ref NONE : Regexp_Numerics.encoding option ref,
   preserve_model_nums = ref NONE : bool option ref};

(*---------------------------------------------------------------------------*)
(* If directory does not exist, create it. Also check that dir has rwe       *)
(* permissions.                                                              *)
(*---------------------------------------------------------------------------*)

fun set_target s =
  case !(#target FLAGS)
    of NONE => (#target FLAGS := SOME "Standalone")
     | SOME "standalone" => ()
     | SOME "hamr" => ()
     | SOME other => fail()

fun set_codegen lang =
 let val _ =
    if mem lang ["CakeML"] then () else fail()
 in case !(#codegen FLAGS)
     of NONE => (#codegen FLAGS := SOME lang)
      | SOME _ => ()
 end

fun set_outDir d =
 let open FileSys
     fun fpath s =
      let val path = fullPath s handle _ => (mkDir s ; fullPath s)
                                handle _ => fail()
      in if isDir path andalso access(path,[A_EXEC,A_READ,A_WRITE])
          then path else fail()
      end
 in
   case !(#outDir FLAGS)
    of NONE => (#outDir FLAGS := SOME (fpath d))
     | SOME _ => ()
 end

fun set_intwidth s =
 case !(#intwidth FLAGS)
  of NONE =>
      (case Int.fromString s
        of SOME i =>
           if i < 8 orelse not (i mod 8 = 0)
              then fail()
              else (#intwidth FLAGS := SOME i)
         |  NONE => fail())
   | SOME _ => ()
;

fun set_preserve_model_nums b =
 case !(#preserve_model_nums FLAGS)
  of NONE => (#preserve_model_nums FLAGS := SOME b)
   | SOME _ => ()

fun s2endian s =
 let open Regexp_Numerics
 in case s
     of "LSB" => LSB
      | "MSB" => MSB
      | other => fail()
 end

fun set_endian e =
 case !(#endian FLAGS)
  of NONE => (#endian FLAGS := SOME (s2endian e))
   | SOME _ => ()

fun s2encoding s =
 let open Regexp_Numerics
 in case s
     of "Unsigned"  => Unsigned
      | "Twos_comp" => Twos_comp
      | "Sign_mag"  => Sign_mag
      | "ZigZag"    => Zigzag
      | "Zigzag"    => Zigzag
      | other       => fail()
 end

fun set_encoding enc =
 case !(#encoding FLAGS)
  of NONE => (#encoding FLAGS := SOME (s2encoding enc))
   | SOME _ => ()

fun check_suffix id s =
 let val filename = FileSys.fullPath s
            handle e => (stdErr_print (Feedback.exn_to_string e); fail())
 in case String.tokens (equal #".") filename
     of [file,x] => if x=id then filename else fail()
      | otherwise => fail()
 end

fun parse_args args =
 if null args then fail()
 else
 let val (flags,file) = front_last args
     val jfile = check_suffix "json" file
     fun set_flags list =
       case list
        of [] =>
           let in
              set_target "Standalone";
              set_codegen "CakeML";
              set_outDir "./splat_outputs";
              set_intwidth "32";
              set_endian "MSB";
              set_encoding "Twos_comp";
              set_preserve_model_nums false
            end
         | "-target"   :: d :: t => (set_target d;   set_flags t)
         | "-codegen"  :: d :: t => (set_codegen d;  set_flags t)
         | "-outdir"   :: d :: t => (set_outDir d;   set_flags t)
         | "-intwidth" :: d :: t => (set_intwidth d; set_flags t)
         | "-endian"   :: d :: t => (set_endian d;   set_flags t)
         | "-encoding" :: d :: t => (set_encoding d; set_flags t)
         | "-preserve_model_nums"::t => (set_preserve_model_nums true; set_flags t)
         | otherwise => fail()
 in
     set_flags flags
   ; jfile
 end

fun extract_consts ("CM_Property_Set",(tydecs,fndecs,filtdecs,mondecs)) =
     let open AADL
         fun dest_const_dec (ConstDec ((_,cname),ty,i)) = (cname,i)
     in mapfilter dest_const_dec fndecs
     end
  | extract_consts otherwise = raise ERR "extract_consts" "unable to find package CM_Property_Set"

fun extract_filters (pkgName,(tydecs,fndecs,filtdecs,mondecs)) = filtdecs;
fun extract_monitors (pkgName,(tydecs,fndecs,filtdecs,mondecs)) = mondecs;

(*---------------------------------------------------------------------------*)
(* Transform to a set of "components", each of the form                      *)
(*                                                                           *)
(*  ([pkg_1,...,pkg_n],dec)                                                  *)
(*                                                                           *)
(*  where the pkg_i are packages used in dec, and dec is a filter, monitor,  *)
(*  or gate. The pkg_i can be trimmed to be minimal.                         *)
(*---------------------------------------------------------------------------*)

fun substFn alist x =
 case subst_assoc (equal x) alist
  of SOME y => y
   | NONE => x

fun alistFn alist x = assoc x alist;

open AST AADL;

type port = string * ty * string * string;  (* (id,ty,dir,kind) *)

type ivardec = string * ty * exp;

type guar = string * string * exp;

datatype gadget =
 Gadget of qid
           * tydec list
           * tmdec list
           * port list
           * ivardec list
           * guar list;

val sort_tydecs = AADL.sort_tydecs
val sort_tmdecs = AADL.sort_tmdecs;

fun set_tmdec_pkgName name tmdec =
 case tmdec
  of ConstDec((_,s),ty,exp) => ConstDec((name,s),ty,exp)
   | FnDec ((_,s),params,rty,exp) => FnDec ((name,s),params,rty,exp)

fun elim_monitor tydecs tmdecs (MonitorDec mondec) =
 let val (qid,ports,latched,mon_tmdecs,ivardecs,guars) = mondec
     val mon_tydecs = []
     val tydecs' = sort_tydecs (tydecs @ mon_tydecs)
     val mondecs' = map (set_tmdec_pkgName (snd qid)) mon_tmdecs
     val tmdecs' = sort_tmdecs (tmdecs @ mondecs')
 in Gadget (qid, tydecs', tmdecs', ports,ivardecs,guars)
 end;

fun elim_filter tydecs tmdecs (FilterDec filtdec) =
 let val (qid, ports,filt_tmdecs, ivardecs, guars) = filtdec
     val filt_tydecs = []
     val latched = false
     val tydecs' = sort_tydecs (tydecs @ filt_tydecs)
     val filtdecs' = map (set_tmdec_pkgName (snd qid)) filt_tmdecs
     val tmdecs' = sort_tmdecs (tmdecs @ filtdecs')
 in Gadget (qid, tydecs', tmdecs', ports,ivardecs,guars)
 end;

(*---------------------------------------------------------------------------*)
(* A "decls" thing represents an AADL package (roughly).                     *)
(*---------------------------------------------------------------------------*)

fun configure decls (support,gadgets) =
 let val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = decls
     val (stydecs,stmdecs) = support
     val tydecs' = tydecs @ stydecs
     val tmdecs' = tmdecs @ stmdecs
     val filter_gadgets = List.map (elim_filter tydecs' tmdecs') filtdecs
     val monitor_gadgets = List.map (elim_monitor tydecs' tmdecs') mondecs
 in
     ((tydecs',tmdecs'),
      filter_gadgets @ monitor_gadgets @ gadgets)
end

fun mk_gadgets pkgs = snd (rev_itlist configure pkgs (([],[]),[]));

val empty_varE = PP_CakeML.empty_varE;
val assocFn = PP_CakeML.assocFn;
val transRval = PP_CakeML.transRval;
val transRval_decl = PP_CakeML.transRval_decl;
val mk_tyE = PP_CakeML.mk_tyE;
val mk_constE = PP_CakeML.mk_constE;
val mk_recd_projns = PP_CakeML.mk_recd_projns;
val tydec_to_ty = PP_CakeML.tydec_to_ty

fun catE env1 env2 x =
  case env1 x
   of NONE => env2 x
    | SOME y => SOME y;

fun transRval_dec E tmdec =
 case tmdec
  of ConstDec (qid,ty,exp) => ConstDec (qid,ty,transRval (E,empty_varE) exp)
   | FnDec (qid,params,ty,exp) =>
     FnDec (qid,params,ty, transRval (E,assocFn params) exp)
;

fun trans_ivardec E (s,ty,e) = (s,ty,transRval E e)
fun trans_guar E (s1,s2,e) = (s1,s2,transRval E e)

fun portE ports =
 let fun dest_port (id,ty,_,_) = (id,ty)
 in assocFn (map dest_port ports)
 end

fun ivarE ivars =
 let fun dest_ivar (id,ty,_) = (id,ty)
 in assocFn (map dest_ivar ivars)
 end

(*---------------------------------------------------------------------------*)
(* Add synthesized projn fn defs after eliminating record projections. This  *)
(* is currently needed because the projection eliminator doesn't handle the  *)
(* case syntax properly.                                                     *)
(*---------------------------------------------------------------------------*)

fun transRval_gadget E gadget =
 let val Gadget (qid,tydecs, tmdecs, ports,ivardecs,guars) = gadget
     val tmdecs'  = map (transRval_decl E) tmdecs
     val tmdecs'' = mk_recd_projns tydecs @ tmdecs'
     val varE     = catE (portE ports) (ivarE ivardecs)
     val ivardecs' = map (trans_ivardec (E,varE)) ivardecs
     val guars'    = map (trans_guar (E,varE)) guars
 in
    Gadget (qid, tydecs, tmdecs'', ports,ivardecs',guars')
 end

fun elim_projections tyE tmE gdts = map (transRval_gadget (tyE,tmE)) gdts;

fun atomic_width atom =
let open ByteContig
 in case atom
     of Bool => 1
      | Char => 1
      | Float => 4
      | Double => 8
      | Signed i => i
      | Unsigned i => i
      | Blob => raise ERR "atomic_width" "Blob"
end;

val trivEnv = ([],[],atomic_width);

fun gadget_qid (Gadget(qid,tydecs,tmdecs,ports,ivars,guars)) = qid;
fun gadget_ports (Gadget(qid,tydecs,tmdecs,ports,ivars,guars)) = ports;
fun gadget_tydecs (Gadget(qid,tydecs,tmdecs,ports,ivars,guars)) = tydecs;
fun gadget_tmdecs (Gadget(qid,tydecs,tmdecs,ports,ivars,guars)) = tmdecs;

fun substExp_tmdec theta tmdec =
 case tmdec
  of ConstDec (qid,ty,e) => ConstDec (qid,ty,substExp theta e)
   | FnDec(qid,params,rty,e) => FnDec(qid,params,rty,substExp theta e)
fun substExp_ivar theta (s,ty,e) = (s,ty,substExp theta e)
fun substExp_guar theta (s1,s2,e) = (s1,s2,substExp theta e)
fun substExp_gadget theta gdt =
 let val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt
 in Gadget(qid,tydecs,
           map (substExp_tmdec theta) tmdecs,
           ports,
           map (substExp_ivar theta) ivars,
           map (substExp_guar theta) guars)
 end;

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
fun guar_qids (s1,s2,exp) set = AST.expQids exp set

fun gadgetQids gdt set =
 let val Gadget(qid,_,tmdecs,_,ivars,guars) = gdt
     val set1 = itlist tmdec_qids tmdecs set
     val set2 = itlist ivardec_qids ivars set1
     val set3 = itlist guar_qids guars set2
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
fun substQid_guar theta (s1,s2,exp) = (s1,s2,substQidExp theta exp);
fun substQid_gadget theta gdt =
 let val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt
 in Gadget(qid,tydecs,
           map (substQid_tmdec theta) tmdecs,
           ports,
           map (substQid_ivar theta) ivars,
           map (substQid_guar theta) guars)
 end;

fun set_Defs_struct gdt =
 let fun mk_def_qid (qid as (s1,s2)) acc =
        if s1 = "" then acc else (qid |-> ("Defs",s2))::acc
     val gqids = gadgetQids gdt []
     val theta = itlist mk_def_qid gqids []
 in substQid_gadget theta gdt
 end

(*---------------------------------------------------------------------------*)
(* Unhappily it can happen that identifiers that are the names of constants, *)
(* and which should be constants, can arrive in the .json as free variables. *)
(* This manifests as a free variable occurring in one of the following cases *)
(*                                                                           *)
(*  - the body of a constant or function declaration (tmdecs)                *)
(*  - in the rhs of an ivar declaration (where the rhs can legitimately have *)
(*    other ivars, and ports, occurring as free vars)                        *)
(*  - in a guarantee (where the guar can have legit ivar and portname occs). *)
(*                                                                           *)
(* This pass is an attempt to repair such anomalies.                         *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun corrall_rogue_vars gdt =
 let val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt
     fun free_tmdecV tmdec =
       case tmdec
        of ConstDec (_,_,e) => AST.expVars e
         | FnDec(_,params,_,e) => subtract (AST.expVars e) (map fst params)
     fun free_ivarsV (_,_,e) = AST.expVars e
     fun free_guarV (_,_,e) = AST.expVars e

     val constNames = map (snd o tmdec_qid) tmdecs
     val portNames = map #1 ports
     val ivarNames = map #1 ivars
     val taken = portNames @ ivarNames

     val tmdec_probs = intersect (bigU (map free_tmdecV tmdecs)) constNames
     val ivar_probs = subtract (bigU (map free_ivarsV ivars)) taken
     val guar_probs = subtract (bigU (map free_guarV guars)) taken
     val problems = bigU [tmdec_probs, ivar_probs, guar_probs]
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
     val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt
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
     | Quantified(q,qvars,e) => Quantified(q,qvars,subExp e)
   fun subDec tmdec =
     case tmdec
      of ConstDec(qid,ty,exp) => ConstDec(qid,ty,subExp exp)
       | FnDec(qid,params,rty,exp) => FnDec(qid,params,rty,subExp exp)
   fun subIvar (s,ty,exp) = (s,ty,subExp exp)
   fun subGuar (s1,s2,exp) = (s1,s2,subExp exp)
 in Gadget(qid,tydecs,
	   map subDec tmdecs,
           ports,
           map subIvar ivars,
           map subGuar guars)
 end;

(*---------------------------------------------------------------------------*)
(* CakeML uses case to distinguish datatype constructors from variables      *)
(* (val bindings, fun params, etc). Constructors start with an upper case    *)
(* letter. Variables start with lower case. We have a pass lowering all      *)
(* names that don't comply. Probably need a corresponding                    *)
(* "upper-case-ification" for any constructors that happen to start with a   *)
(* lower case letter.                                                        *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun set_vars_lower_case gdt =
 let open AST
   val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt
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
     | Quantified(q,qvars,e) => Quantified(q,qvars,subExp e)
   fun subDec tmdec =
     case tmdec
      of ConstDec(qid,ty,exp) =>
         ConstDec(substFn theta qid,ty,subExp exp)
       | FnDec(qid,params,rty,exp) =>
         FnDec(substFn theta qid,params,rty,subExp exp)
   fun subIvar (s,ty,exp) = (s,ty,subExp exp)
   fun subGuar (s1,s2,exp) = (s1,s2,subExp exp)
 in
    Gadget(qid,tydecs,
	   map subDec tmdecs,
           ports,
           map subIvar ivars,
           map subGuar guars)
 end;

fun set_ports_and_ivars_lower_case gdt =
 let open AST
     val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt
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
           map (substGuar theta) guars)
 end;

fun gadget_tyE gdt =
 let val Gadget (_,tydecs, _,_,_,_) = gdt
     fun mk_tydec_bind tydec = (tydec_qid tydec,tydec_to_ty tydec)
     val tydec_alist = map mk_tydec_bind tydecs
 in
   tydec_alist
 end

fun gadget_tyEnvs gdt =
 let open AST
     val Gadget (qid, tydecs, tmdecs,ports,ivars,guars) = gdt
     val tyE_0 = gadget_tyE gdt
     fun chase list = list  (* Stub *)
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


fun defs_struct_of gdt =
 let val tyEnvs = gadget_tyEnvs gdt
     val fodder = ("Defs",gadget_tydecs gdt,gadget_tmdecs gdt)
     val pretty = PP_CakeML.pp_defs_struct tyEnvs fodder
in
  pretty
end

fun port_ty (id,ty,dir,kind) = ty;
fun is_in_port (id,ty,"in",kind) = true
  | is_in_port otherwise = false;
fun is_out_port (id,ty,"out",kind) = true
  | is_out_port otherwise = false;
fun is_event (id,ty,dir,"DataPort") = false
  | is_event otherwise = true;

fun get_ports gdt =
 let val ports = gadget_ports gdt
 in (filter is_in_port ports,filter is_out_port ports)
 end

fun API_of (orig_gdt,gdt) =
let val qid = gadget_qid gdt
    val (inports, outports) = get_ports gdt
    val tyE = assocFn (gadget_tyE gdt)

    fun mk_inport_buf (iport as (id,ty,dir,kind)) =
      let val contig = Gen_Contig.contig_of tyE (port_ty iport)
          val size = Gen_Contig.size_of trivEnv contig
          val esize = if kind = "EventDataPort" then size+1 else size
      in
       (id^"_buffer", esize)
      end
    val inport_bufs = map mk_inport_buf inports

    val (orig_inports, orig_outports) = get_ports orig_gdt

    fun mk_fillFn ((iport as (id,ty,dir,kind)),(orig_id,_,_,_)) =
     let val bufName = id^"_buffer"
         val api_call = String.concat ["#(api_get_",orig_id,") \"\" ", bufName]
     in (bufName, api_call)
     end
    val fillFns = map mk_fillFn (zip inports orig_inports)

    fun mk_sendFn ((oport as (id,ty,dir,kind)),(orig_id,_,_,_)) =
      let val api_call = String.concat["#(api_send_",orig_id,") string Utils.emptybuf;"]
      in (id, api_call)
      end
    val sendFns = map mk_sendFn (zip outports orig_outports)

    val logInfo = "fun logInfo s = #(api_logInfo) s Utils.emptybuf;"
    val fodder = ("API",inport_bufs,fillFns,sendFns,logInfo)
    val pretty = PP_CakeML.pp_api fodder
in
  pretty
end;

fun parser_struct_of gdt =
let val qid = gadget_qid gdt
    val ports = gadget_ports gdt
    val inports = filter is_in_port ports
    val tyEalist = gadget_tyE gdt
    val tyE = assocFn tyEalist
    val contig_binds = map (I##Gen_Contig.contig_of tyE) tyEalist
    val decoder_defs = Gen_Contig.decoders tyE (map snd tyEalist)
    val fodder = ("Parse",inports, contig_binds, decoder_defs)
    val pretty = PP_CakeML.pp_parser_struct ~1 fodder
in
  pretty
end

fun apply gdts [] = gdts
  | apply gdts (f::t) = apply (f gdts) t ;

fun process_model jsonFile =
 let val ([jpkg],ss) = Json.fromFile jsonFile
     val pkgs = scrape_pkgs jpkg
     val tyE = mk_tyE (map Pkg pkgs)
     val tmE = mk_constE (map Pkg pkgs)
     val gdts1 = mk_gadgets pkgs
     val gdts = apply gdts1
                 [map corrall_rogue_vars,
                  map set_type_constrs,
                  map set_vars_lower_case,
                  map set_ports_and_ivars_lower_case,
                  elim_projections tyE tmE,
                  map set_Defs_struct]
     val apis = map API_of (zip gdts1 gdts)
     val parser_structs = map parser_struct_of gdts
     val defs_structs = map defs_struct_of gdts
 in
    (apis,parser_structs, defs_structs, gdts)
 end;

fun getFile path =
  let val istrm = TextIO.openIn path
      val vector = TextIO.inputAll istrm
      val () = TextIO.closeIn istrm
  in
    vector
  end;

val Utils_Src      = getFile "Lego/Utils.cml";
val ByteContig_Src = getFile "Lego/ByteContig.cml";
val basis_ffi_Src  = getFile "Lego/basis_ffi.c";
val Makefile_Src   = getFile "Lego/Makefile";

(* val Cake_Src       = getFile "Lego/cake.S"; *)

fun export_implementation dir (api,parser,defs,gdt) =
 let open FileSys
     val (pkgName,compName) = gadget_qid gdt
     val gadgetName = pkgName^"_"^compName
     val _ = stdErr_print ("\nProcessing "^qid_string (gadget_qid gdt)^".\n")
     val origDir = getDir()
     val () = stdErr_print ("Invocation dir: "^ origDir ^ "\n")
     val gadgetDir = String.concat[dir,"/",gadgetName]
     val _ = ((mkDir gadgetDir handle _ => ()); chDir gadgetDir)
     val _ = stdErr_print ("  Writing basis_ffi.c\n")
     val ostrm = TextIO.openOut "basis_ffi.c"
     val () = TextIO.output(ostrm,basis_ffi_Src)
     val () = TextIO.closeOut ostrm
     val _ = stdErr_print ("  Writing Makefile\n")
     val ostrm = TextIO.openOut "Makefile"
     val () = TextIO.output(ostrm, Makefile_Src)
     val () = TextIO.closeOut ostrm
     val gadgetFile = gadgetName^".cml"
     val () = stdErr_print ("  Writing "^gadgetFile^"\n")
     val ostrm = TextIO.openOut gadgetFile
     fun add s = TextIO.output(ostrm,s)
     val () = add Utils_Src
     val () = add "\n\n"
     val () = add ByteContig_Src
     val () = add "\n\n"
     val () = PPfns.pp_ostrm ostrm defs
     val () = add "\n\n"
     val () = PPfns.pp_ostrm ostrm parser
     val () = add "\n\n"
     val () = PPfns.pp_ostrm ostrm api
     val () = TextIO.closeOut ostrm
     val fullgadgetDir = origDir^"/"^gadgetDir
     val () = stdErr_print ("Code written to directory: "^fullgadgetDir ^ "\n")
     val () = stdErr_print ("Done.\n")
 in
  chDir origDir
 end

(*
val jsonFile = "examples/SW.json";
val args = [jsonFile];
val thyName = "SW";
val dir = ".";

val (apis,parsers,defs,gdts) = process_model "examples/SW.json";
val [gdt1, gdt2, gdt3] = gdts;
val [api1,api2,api3] = apis;
val [p1,p2,p3] = parsers;
val [defs1,defs2,defs3] = defs;

export_implementation "tmp" (api1,p1,defs1,gdt1);
export_implementation "tmp" (api2,p2,defs2,gdt2);
export_implementation "tmp" (api3,p3,defs3,gdt3);

fun envFn env x = assoc x env;

val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt1;
val env as (env1,env2,env3) = expTy_env gdt1;
val E = (envFn env1, envFn env2, envFn env3);

val tmdec = el 11 tmdecs;
val FnDec(qid,params,rty,exp) = tmdec;
val Binop(And,e1,e2) = exp
expTy E e1;
expTy E e2;
val Binop(_,e2a,e2b) = e2;
expTy E e2a;
expTy E e2b;

val ([jpkg],ss) = Json.fromFile jsonFile
val pkgs = scrape_pkgs jpkg
val tyE = mk_tyE (map Pkg pkgs)
val tmE = mk_constE (map Pkg pkgs)
val gdts1 = mk_gadgets pkgs

val gdts = apply gdts1
  [map corrall_rogue_vars,
   map set_type_constrs,
   map set_vars_lower_case
];

val [gdt1,gdt2,gdt3] = gdts

val gdts = apply gdts1
  [map corrall_rogue_vars,
   map set_type_constrs,
   map set_ports_and_ivars_lower_case,
   elim_projections tyE tmE,
   map set_Defs_struct
];

val gdt2a = corrall_rogue_vars gdt1;
val gdt2b = set_type_constrs gdt2a;
val Gadget(qid,tydecs,tmdecs,ports,ivars,guars) = gdt2b;
val gdt2c = set_ports_and_ivars_lower_case gdt2b;
val gdt3 = elim_projections tyE tmE [gdt2c];

     val gdts4 = map set_Defs_struct gdts3
     val gdts5 = map set_vars_lower_case gdts4
     val apis = map API_of gdts5
     val parser_structs = map parser_struct_of gdts5
     val defs_structs = map defs_struct_of gdts5
 in
    (apis,parser_structs, defs_structs, gdts5)
 end;

val Gadget(qid,tydecs,tmdecs,(ports,ivars,guars)) = gdt2;

val gdt2_qids = gadgetQids gdt2 [];

val gdt2' =
  Gadget(qid,tydecs,
         map (substQid_tmdec theta) tmdecs,
         ports,
         map (substQid_ivar theta) ivars,
         map (substQid_guar theta) guars);

val gdt2_qids' = gadgetQids gdt2' [];
val theta = itlist mk_def_qid (gadgetQids gdt2 []) [];

gadgetQids gdt1 [];
gadgetQids gdt2 [];
gadgetQids gdt3 [];

val _qid = fun substQid
List.app (print o PPfns.pp_string) apis;
List.app (print o PPfns.pp_string) parsers

dir (api,parser,gdt) =

val tyE_assoc = gadget_tyE gdt1;
val tyE = assocFn tyE_assoc;

val support = hd (gadget_support gdt1);
val tydecs = fst(snd support);
val tys = map tydec_to_ty tydecs;

val contig = Gen_Contig.contig_of tyE (hd tys);
PP_CakeML.contig_to_exp [] contig;

val contigs = map (Gen_Contig.contig_of tyE) tys;
map (PP_CakeML.contig_to_exp []) contigs;


val gdt1_tyE = gadget_tyE gdt1;

val ([jpkg],ss) = Json.fromFile jsonFile;

open AADL;

val [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7] = pkgs;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg7;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg5;
val [mondec1,mondec2,mondec3] = mondecs;
val [filtdec1,filtdec2,filtdec3,filtdec4] = filtdecs;
*)

(*
fun process_filter intformat flags ((pkgName,fname),thm) =
 let open FileSys
     val _ = stdErr_print ("\nProcessing filter "^Lib.quote fname^".\n")
     val wDir = getDir()
     val filterDir = String.concat[wDir,"/",pkgName,"_",fname]
     val _ = ((mkDir filterDir handle _ => ()); chDir filterDir)
     val (checkprops,codegen,testgen,alevel) = flags
     val filter_artifacts =
         apply_with_chatter
           (splatLib.gen_filter_artifacts intformat) ((pkgName,fname),thm)
           "Defining filter artifacts ... " "succeeded.\n"

     val _ = if checkprops = true then
               apply_with_chatter
                  prove_filter_props filter_artifacts
                  "Proving translation validation property ... " "succeeded.\n"
             else ()

    val {regexp,...} = filter_artifacts

    val regexp_compiler =
         case alevel
          of Basic => regexpLib.SML
	   | HOL   => regexpLib.HOL
	   | other => failwithERR
             (ERR "splat" "Cake regexp compilation not handled at present")

    val DFA as (certificate, start, finals, table) =
        deconstruct (regexpLib.gen_dfa regexp_compiler regexp)

    val (match_state_thm, match_def) = mk_matcher fname certificate

    val (langGen,suffix) =
     case codegen
      of "C" => (DFA_Codegen.C,".c")
       | "SML" => (DFA_Codegen.SML,".sml")
       | "Ada" => (DFA_Codegen.Ada,".ada")
       | "Java" => (DFA_Codegen.Java,".java")
       | "Slang" => (Code_Gen.Slang,".scala")
       | other    => raise ERR "process_filter" "unsupported target language"

    (* Smuggling architecture info through the name. To be handled (so far)
       only in Slang code generation, which wants the AADL path to the filter
    *)
    val slang_path_name =
     if codegen = "Slang" then
       String.concat[pkgName,".",fname]
     else fname
 in
     Code_Gen.export_dfa langGen (slang_path_name,suffix) regexp finals table
   ;
     stdErr_print ("End processing filter "^Lib.quote fname^".\n\n")
   ;
     chDir wDir
   ;
     filter_artifacts
 end
*)

(*

val args = ["examples/uxaslite.json"];
val thyName = "uxaslite";
val dir = ".";

val args = ["examples/gate.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/mon3a.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/mon4a.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/mon5a.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/UAS.json"];
val thyName = "UAS";
val dir = ".";

val jsonfile = parse_args args;
val ([jpkg],ss) = Json.fromFile jsonfile;
open AADL;

val pkgs = scrape_pkgs jpkg;

val [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7] = pkgs;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg7;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg5;
val [mondec1,mondec2,mondec3] = mondecs;
val [filtdec1,filtdec2,filtdec3,filtdec4] = filtdecs;

val const_alist = tryfind extract_consts pkgs

val MonitorDec(qid,features,decs,eq_stmts,outCode) = mondec1;
val MonitorDec(qid,features,decs,eq_stmts,outCode) = mondec2;
val MonitorDec(qid,features,decs,eq_stmts,outCode) = mondec3;

val plist = map Pkg pkgs;
val plist' = transRval_pkglist plist ;
*)

(*
HAMR::Bit_Codec_Max_Size: It is attached to the types declared for the channel.

val args = ["examples_monitor/req_resp_monitor.json"];
val args = ["examples_monitor/geo_monitor.json"];
val args = ["examples_monitor/Coord-Mon.json"];
val args = ["examples_monitor/Resp-Mon.json"];
val args = ["examples_monitor/Coord-Mon.json"];
val args = ["examples_monitor/SW-Mon-1.json"];
val args = ["examples_monitor/SW-Mon.json"];
val args = ["examples_monitor/RunTimeMonitor_Simple_Example_V1.json"];
val args = ["examples_monitor/Datacentric_monitor.json"];
*)

fun main () =
 let val _ = stdErr_print "splat-mon: \n"
     val args = CommandLine.arguments()
     val jsonfile = parse_args args
     val ([jpkg],ss) = apply_with_chatter Json.fromFile jsonfile
	   ("Parsing "^jsonfile^" ... ") "succeeded.\n"
     val pkgs = apply_with_chatter AADL.scrape_pkgs jpkg
                  "Converting Json to AST ... " "succeeded.\n"
     val thyName = "SPLAT"  (* Need something better: get it from modelUnits from jpkg *)

     val filter_decs = List.concat (map extract_filters pkgs)
     val monitor_decs = List.concat (map extract_monitors pkgs)
     val _ = stdErr_print ("Found "^Int.toString (List.length filter_decs)^" filter declarations.\n")
     val _ = stdErr_print ("Found "^Int.toString (List.length monitor_decs)^" monitor declarations.\n")
     val const_alist = tryfind extract_consts pkgs

(*
     val _ = AADL.export_cakeml_monitors dir const_alist monitor_decs
     val _ = AADL.export_cakeml_filters dir const_alist filter_decs
*)
  in
    MiscLib.succeed()
 end
 handle e =>
    let open MiscLib
    in stdErr_print "\n\nSPLAT-MON FAILED!!\n\n";
       failwithERR e
    end
