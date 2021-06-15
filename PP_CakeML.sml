structure PP_CakeML :> PP_CakeML =
struct

open Lib Feedback MiscLib PPfns AST AADL;

val ERR = mk_HOL_ERR "PP_CakeML";
fun unimplemented s = ERR s "unimplemented";

fun pp_qid ("",s) = s
  | pp_qid (s1,s2) = String.concat[s1,".",s2];

fun qid_string p = pp_qid p;

fun pp_pkg_qid pkgName (pkg,s) =
    if pkg=pkgName then pp_qid ("",s) else pp_qid (pkg,s);

(*---------------------------------------------------------------------------*)
(* CakeML Prettyprinters for AST                                             *)
(*---------------------------------------------------------------------------*)

fun base_ty_name BoolTy   = "bool"
  | base_ty_name CharTy   = "char"
  | base_ty_name StringTy = "string"
  | base_ty_name FloatTy  = "Double.double"
  | base_ty_name DoubleTy  = "Double.double"
  | base_ty_name (IntTy _) = "int"
  | base_ty_name RegexTy   = raise ERR "base_ty_name" "regex"

fun pp_ty depth pkgName ty =
 let open PolyML
 in if depth = 0 then PrettyString "<ty>"
   else
   case ty
    of BaseTy bty => PrettyString (base_ty_name bty)
     | NamedTy nty => PrettyString (pp_pkg_qid pkgName nty)
     | ArrayTy(eltype,dims) =>
         PrettyBlock(2,true,[],
            [PrettyString"(",
             pp_ty (depth-1) pkgName eltype, PrettyBreak (1,0), PrettyString "array)"])
     | RecdTy(qid,fields) => PrettyString"<RecdTy>!?"
 end

fun pp_exp depth pkgName exp =
  let open PolyML
  in if depth = 0 then PrettyString "<exp>"
    else
    case exp
     of VarExp id => PrettyString id
      | ConstExp (IdConst qid) => PrettyString (pp_pkg_qid pkgName qid)
      | ConstExp (BoolLit true) => PrettyString "True"
      | ConstExp (BoolLit false) => PrettyString "False"
      | ConstExp (CharLit c) => PrettyString ("'#"^Char.toString c^"'")
      | ConstExp (StringLit s) => PrettyString (Lib.quote(String.toString s))
      | ConstExp (IntLit{kind, value}) => PrettyString (Int.toString value)
      | ConstExp (FloatLit r) => PrettyString (Real.toString r)
      | ConstExp (RegexLit r) => PrettyString ("<RegexLit>!?")
      | Unop(Not,e) => PrettyBlock(2,true,[],
           [PrettyString"not",PrettyBreak(0,1),
            PrettyString"(",pp_exp (depth-1) pkgName e,PrettyString")"])
      | Unop(UMinus,e) => PrettyBlock(2,true,[],
           [PrettyString"~",
            PrettyString"(",pp_exp (depth-1) pkgName e,PrettyString")"])
      | Unop(ChrOp,e) => PrettyBlock(2,true,[],
           [PrettyString"Char.chr",
            PrettyString"(",pp_exp (depth-1) pkgName e,PrettyString")"])
      | Unop(OrdOp,e) => PrettyBlock(2,true,[],
           [PrettyString"Char.ord",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Binop(Or,e1,e2) => pp_infix depth pkgName ("orelse",e1,e2)
      | Binop(And,e1,e2) => pp_infix depth pkgName ("andalso",e1,e2)
      | Binop(Equal,e1,e2) => pp_infix depth pkgName ("=",e1,e2)
      | Binop(NotEqual,e1,e2) => pp_infix depth pkgName ("<>",e1,e2)
      | Binop(Greater,e1,e2) => pp_infix depth pkgName (">",e1,e2)
      | Binop(GreaterEqual,e1,e2) => pp_infix depth pkgName (">=",e1,e2)
      | Binop(Less,e1,e2) => pp_infix depth pkgName ("<",e1,e2)
      | Binop(LessEqual,e1,e2) => pp_infix depth pkgName ("<=",e1,e2)
      | Binop(Minus,e1,e2) => pp_infix depth pkgName ("-",e1,e2)
      | Binop(Multiply,e1,e2) => pp_infix depth pkgName ("*",e1,e2)
      | Binop(Plus,e1,e2) => pp_infix depth pkgName ("+",e1,e2)
      | Binop(Divide,e1,e2) => pp_exp depth "" (Fncall (("Int","div"),[e1,e2]))
      | Binop(Modulo,e1,e2) => pp_exp depth "" (Fncall (("Int","mod"),[e1,e2]))
      | Binop(Fby,e1,e2) => pp_infix depth pkgName ("->",e1,e2)
      | ArrayExp elist => PrettyBlock(0,true,[],
          [PrettyString "Array.fromList",Space,
           PrettyString"[",
            pp_list_with_style false Comma [emptyBreak] (pp_exp (depth-1) pkgName ) elist,
            PrettyString"]"])
      | ArrayIndex(A,dims) =>
         let fun trans exp [] = exp
               | trans exp (d::dims) = trans (Fncall (("Array","sub"),[exp,d])) dims
         in pp_exp depth pkgName (trans A dims)
         end
      | Fncall ((_,"Comment"),elist) =>
            gen_pp_list emptyString [Line_Break] (pp_exp (depth-1) pkgName) elist
      | Fncall ((_,"unitExp"),[]) => PrettyString "()"
      | Fncall ((_,"IfThenElse"),[e1,e2,e3]) =>
          PrettyBlock(2,true,[],
            [PrettyString"if ", pp_exp (depth-1) pkgName  e1, PrettyString" then", Space,
             pp_exp (depth-1) pkgName  e2,Space,
             PrettyString"else ", pp_exp (depth-1) pkgName  e3])
      | Fncall ((_,"LET"),eqlist) =>
	let val (binds,res) = front_last eqlist
        in PrettyBlock(5,true,[],
              [PrettyString"let ",
               PrettyBlock(0,true,[],
                 [gen_pp_list emptyString [Line_Break] (pp_valbind (depth-1) pkgName) binds]),
               Space, PrettyString"in",
               Space, pp_exp (depth-1) pkgName res,
               Line_Break, PrettyString "end"])
	end
      | Fncall(("","Tuple"),list) =>
          if null list then
            PrettyString "()"
          else if length list = 1 then
             pp_exp (depth-1) pkgName (hd list)
          else PrettyBlock(1,false,[],
                 List.concat [[PrettyString "("],
                  iter_pp Comma [emptyBreak] (pp_exp (depth-1) pkgName) list,
                  [PrettyString")"]])
      | Fncall(("","Lambda"),list) =>
         (case list
           of [v,e] =>
                PrettyBlock(2,true,[],
                 [PrettyString"(fn ", pp_exp (depth-1) pkgName v, PrettyString" =>", Space,
                  pp_exp (depth-1) pkgName e,
                  PrettyString")"])
            | otherwise => PrettyString "!!<Lambda-as-Fncall needs 2 args>!!")
      | Fncall(("","Array_Forall"),list) =>
         (case list
           of [v,arry,P] =>
                pp_exp (depth-1) pkgName
                   (Fncall(("Array","all"), [Fncall(("","Lambda"),[v,P]),arry]))
            | otherwise => PrettyString "!!<Array_Forall needs 3 args>!!")
      | Fncall(("","Array_Exists"),list) =>
         (case list
           of [v,arry,P] =>
                pp_exp (depth-1) pkgName
                   (Fncall(("Array","exists"), [Fncall(("","Lambda"),[v,P]),arry]))
            | otherwise => PrettyString "!!<Array_Exists needs 3 args>!!")
      | Fncall(("","AssignExp"),[v,e]) => pp_infix (depth-1) pkgName (":=",v,e)
      | Fncall (qid,args) => PrettyBlock(2,false,[],
           [PrettyString"(",
            PrettyString(pp_pkg_qid pkgName qid), PrettyString" ",
            if null args then PrettyString "()" else
            pp_list_with_style false Space [emptyBreak] (pp_exp (depth-1) pkgName) args,
            PrettyString")"])
      | ConstrExp(qid, constr,argOpt) =>
         PrettyBlock(2,true,[],
           [PrettyString(pp_pkg_qid pkgName (fst qid,constr)), Space,
            PrettyBlock(0,false,[],
             case argOpt of NONE => []
               | SOME vexp => [PrettyString"(", pp_exp (depth-1) pkgName  vexp,
                               PrettyString")"])])
      | RecdExp (qid,fields) => PrettyBlock(2,true,[],
           [PrettyString("("),PrettyString(pp_pkg_qid pkgName qid), Space,
            PrettyBlock(0,false,[],
                        [pp_space_list (pp_exp (depth-1) pkgName) (map snd fields)]),
            PrettyString")"])
      | RecdProj(recd,field) => PrettyBlock(0,false,[],
           [pp_exp (depth-1) pkgName recd,PrettyString".",PrettyString field])
      | other => PrettyString "<UNKNOWN AST NODE>!?"
  end
and pp_infix d pkgName (str,e1,e2) =
    let open PolyML
    in PrettyBlock(2,true,[],
        [PrettyString"(",pp_exp (d-1) pkgName e1,
         Space, PrettyString str, Space,
         pp_exp (d-1) pkgName e2,PrettyString")"])
    end
and pp_valbind d pkgName (Binop(Equal,e1,e2)) =
    let open PolyML
    in case e1
        of Fncall(("","FUN"), VarExp fName::args) =>
           PrettyBlock(5,true,[],
             [PrettyString ("fun "^fName^" "),
              gen_pp_list Space [emptyBreak] (pp_exp (d-1) pkgName) args,
              PrettyString" =", Space, pp_exp (d-1) pkgName e2])
         | otherwise =>
           case e2
             of Fncall(("","Comment"),_) => pp_exp (d-1) pkgName e2
              | _ => PrettyBlock(5,true,[],
                       [PrettyString "val ",
                        pp_exp (d-1) pkgName e1,
                        PrettyString " =", Space,
                        pp_exp (d-1) pkgName e2])
    end
  | pp_valbind other input stuff = PolyML.PrettyString"!!<MALFORMED LET BINDING>!!"
;

fun pp_decl depth pkgName decl =
 let open PolyML
     fun pp_space_list pp list =
	 PrettyBlock(0,false,[],
	     iter_pp Space [PrettyBreak(0,0)] pp list)
 in if depth = 0 then PrettyString "<decl>"
  else
   case decl
    of TyAbbrevDecl(id,ty)
       => PrettyBlock(2,true,[],
           [PrettyString "type ", PrettyString id, PrettyString " = ",
            pp_ty (depth-1) pkgName ty, PrettyString";"])
     | DatatypeDecl(id,constrs) =>
       let fun pp_constr d (id,tys) =
               PrettyBlock(3,false,[],
                  [PrettyString id,Space,
                   pp_space_list (pp_ty (d-1) pkgName) tys])
              fun pp_constr_list d list =
               let fun iter [] = []
                 | iter [x] = [pp_constr (d-1) x]
                 | iter (h::t) = pp_constr (d-1) h ::
                                 PrettyString" |" :: Space::iter t
               in
                 PrettyBlock(0,true,[],iter list)
                end
          in PrettyBlock(2,true,[],
             [PrettyString "datatype ", PrettyString id, PrettyString " =", Space,
              pp_constr_list (depth-1) constrs,
              PrettyString";"])
          end
     | ConstDecl(id,ty,exp)
       => PrettyBlock(2,true,[],
             [PrettyString ("val "^id^" ="),Space,
              pp_exp (depth-1) pkgName exp, PrettyString";"])
     | FnDecl(id,params,retvalOpt,locals,stmts)
       => PrettyString "<FnDecl>!?"

(*
let fun pp_params() = PrettyBlock (2,true,[],
                   [PrettyString id,Space,
                    PrettyBlock(0,false,[],
                         [pp_space_list (pp_param (depth-1)) params])])
             fun pp_body() = PrettyBlock(0,true,[],
                    iter_pp emptyString  [Line_Break] (pp_stmt (depth-1)) pkgName stmts)
              fun pp_top_stmt [] = pp_body()
                | pp_top_stmt locals =
                    PrettyBlock(0,false,[],
                      [PrettyString"var",
                       PrettyBreak (1,0),
                       PrettyBlock(0,true,[],
                         iter_pp emptyString [Line_Break] (pp_vdec_semi (depth-1)) locals),
                       Line_Break,
                       PrettyString"in",
                       Line_Break,
                       pp_body()])
          in
           PrettyBlock(2,false,[],
             [PrettyString "function ", pp_params(),
              PrettyString" {", Line_Break,
              PrettyString " ",
              pp_top_stmt locals,
              Line_Break,
              PrettyString"}"])
          end
*)
     | otherwise => PrettyString"<!!Unexpected decl!!>"
 end


(*---------------------------------------------------------------------------*)
(* Translate record declarations to datatype declarations. Generate          *)
(* projection function declarations for each field of each record. This      *)
(* supports CakeML code generation.                                          *)
(*---------------------------------------------------------------------------*)

fun pp_tydec depth pkgName tydec =
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
   else
   case tydec
    of EnumDec(qid,enums) =>
         pp_decl depth pkgName (DatatypeDecl(snd qid, map (fn e => (e,[])) enums))
     | RecdDec(qid,fields) =>
        let val tyName = snd qid
            val tys = map snd fields
            val dty = DatatypeDecl (tyName,[(tyName^"Recd",tys)])
        in pp_decl depth pkgName dty
        end
     | UnionDec(qid,constrs) =>
        let val tyName = snd qid
            val constrs' = map (fn (id,ty) => (id, [ty])) constrs
            val dty = DatatypeDecl (tyName, constrs')
        in pp_decl depth pkgName dty
        end
     | ArrayDec(qid,ty) =>
         PrettyBlock(0,true,[],
           [PrettyString "type ",
            PrettyString (snd qid),
            PrettyString " =", Space,
            pp_ty (depth-1) pkgName ty,
            Semicolon])
 end;

(*---------------------------------------------------------------------------*)
(* CakeML doesn't have records, so we replace records by single-constructor  *)
(* datatypes, and implement field accesses by application of projection      *)
(* functions.                                                                *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Replace all record field projections with explicit function calls.        *)
(*---------------------------------------------------------------------------*)

(*
fun convert_tydec tydec =
 let open AST
 in
  case tydec
   of EnumDec (qid, enames) => DatatypeDecl (snd qid, map (fn s => (s,[])) enames)
    | RecdDec (qid, fields) => RecdDecl(snd qid, fields)
    | ArrayDec (qid, ty)    => TyAbbrevDecl (snd qid,ty)
    | UnionDec (qid, constrs) =>
        DatatypeDecl (snd qid, map (fn (s,ty) => (s,[ty])) constrs)
 end

fun convert_tmdec tmdec =
 let open AST
 in
  case tmdec
   of ConstDec (qid,ty,exp) => ConstDecl(snd qid,ty,exp)
    | FnDec (qid, args, rty, body) =>
      FnDecl(snd qid, map In args,
             SOME ("retVal",rty),[],
             [Assign(VarExp"retVal",body)])
 end

fun tmdecs_of_mon mondec =
 case mondec
  of MonitorDec(qid,ports,latched,decs,ivars,guars) => decs
;

fun pkg_to_package (pkg:AADL.pkg) =
 let val Pkg (pkgName,(tydecs,tmdecs,filters,monitors)) = pkg
     val tydecls = map convert_tydec tydecs
     val mondecs = List.concat (map tmdecs_of_mon monitors)
     val tmdecs' = tmdecs @ mondecs
     val tmdecls = map convert_tmdec tmdecs'
 in
    (pkgName, tydecls@tmdecls) : AST.package
 end

val plist = map (pkg_to_package o Pkg) pkgs;

val tyE = tyEnvs pkg

val tyE = itlist (fn p => fn E =>
*)

(*---------------------------------------------------------------------------*)
(* Type of array elements.                                                   *)
(*---------------------------------------------------------------------------*)

fun eltyper n tyE ty =
 if n <= 0 then raise ERR "eltype" "too many links chased, maybe circular"
 else
 case ty
  of ArrayTy(elty,_) => elty
   | NamedTy qid =>
       (case tyE qid
        of SOME ty' => eltyper (n-1) tyE ty'
         | NONE => raise ERR "eltype" ("Named type not found : "^qid_string qid))
   | BaseTy _ => raise ERR "eltype" "expected an array type; found BaseTy"
   | RecdTy(qid,_) => raise ERR "eltype"
           ("expected an array type; found RecdTy "^qid_string qid)

val eltype = eltyper 12;

(*---------------------------------------------------------------------------*)
(* Replace field projections in L/Rvals by projection functions              *)
(*                                                                           *)
(* tyE maps qids to declared types, varE maps function parameters to their   *)
(* types, TODO: add an environment for constants, since it is possible to    *)
(* have  a constant  that is a record, and to access a field of it, etc.     *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* A record projection function is the concatenation of the record name and  *)
(* the fieldName, and then "_of"                                             *)
(*---------------------------------------------------------------------------*)

fun recd_projFn_name tyName fieldName = tyName^"_"^fieldName^"_of";

fun fieldFn tyE rty fieldName =
 let fun recdtyper n tyE ty =
       if n <= 0 then
          raise ERR "recdtyper" "too many links chased, maybe circular"
       else
       case ty
         of RecdTy _ => ty
          | NamedTy qid =>
            (case tyE qid
              of SOME ty' => recdtyper (n-1) tyE ty'
               | NONE => raise ERR "recdtyper"
                          ("Named type not found : "^qid_string qid))
          | otherwise => raise ERR "recdtyper" "not a record type"
 in
   case recdtyper 12 tyE rty
    of RecdTy((qid as (pkgName,recdName)),fields)
        => (case assoc1 fieldName fields
             of NONE => raise ERR "fieldFn"
                 ("seeking "^fieldName^" in type "^qid_string qid)
              | SOME (_,fty) => ((pkgName,recd_projFn_name recdName fieldName),fty))
     | otherwise => raise ERR "fieldFn" "expected a RecdTy"
 end;

fun proj_intro (E as ((tyE,constE),varE)) exp =
 (case exp
   of VarExp id =>
        (case varE id
          of SOME ty => (exp, ty)
           | NONE =>
         case constE id
          of SOME ty => (exp,ty)
           | NONE => raise ERR "proj_intro" ("Unable to find identifier "^Lib.quote id))
    | ArrayIndex(e', i) =>
       let val (e'', ty) = proj_intro E e'
       in (ArrayIndex(e'',i),eltype tyE ty)
       end
    | RecdProj(e, fldName) =>
       let val (e', rty) = proj_intro E e
           val (proj_qid,fty) = fieldFn tyE rty fldName
       in (Fncall(proj_qid,[e']), fty)
       end
    | otherwise => (exp,NamedTy("--","--"))
 )
 handle e =>
  let val pretty = pp_exp 72 "<PKG>" exp
      val buf = ref []
      fun addbuf s = buf := s :: !buf
      val _ = PolyML.prettyPrint (addbuf,72) pretty
      val expString = String.concat (rev (!buf))
  in raise wrap_exn "PP_CakeML" ("proj_intro on expression : "^expString)  e
  end;

fun extendE env (v,u) x =
 case env x
  of SOME y => SOME y
   | NONE => if x = v then SOME u else NONE;

fun dest_varExp (VarExp id) = id
  | dest_varExp otherwise = raise ERR "dest_varExp" "expected a VarExp";

fun transRval E e =
 case e
  of ConstExp _ => e
   | Unop (uop,e')     => Unop(uop,transRval E e')
   | Binop (bop,e1,e2) => Binop (bop,transRval E e1, transRval E e2)
   | ArrayExp elist    => ArrayExp (map (transRval E) elist)
   | ConstrExp(qid,id,eOpt) => ConstrExp(qid,id,Option.map (transRval E) eOpt)
   | Fncall(qid as ("","Array_Forall"),elist) =>
      (case elist
        of [v,arry,P] =>
            let val (E1 as (tyE,constE),varE) = E
                val (arry',aty) = proj_intro E arry
                val elty = eltype tyE aty
                val id = dest_varExp v
            in
              Fncall(qid,[v, arry', transRval(E1,extendE varE (id, elty)) P])
            end
         | otherwise => raise ERR "transRval" "malformed Array_Forall")
   | Fncall(qid as ("","Array_Exists"),elist) =>
      (case elist
        of [v,arry,P] =>
            let val (E1 as (tyE,constE),varE) = E
                val (arry',aty) = proj_intro E arry
                val elty = eltype tyE aty
                val id = dest_varExp v
            in
              Fncall(qid,[v, arry', transRval(E1,extendE varE (id, elty)) P])
            end
         | otherwise => raise ERR "transRval" "malformed Array_Forall")
   | Fncall(qid,elist)      => Fncall(qid,map (transRval E) elist)
   | RecdExp(qid,fields)    => RecdExp(qid,map (I##transRval E) fields)
   | Quantified (q,params,exp) => Quantified (q,params,transRval E exp)
   | otherwise => fst(proj_intro E e)
;

fun empty_varE _ = NONE;

fun assocFn alist x =
 case assoc1 x alist
  of NONE => NONE
   | SOME (a,b) => SOME b;


fun transRval_decl E tmdec =
 case tmdec
  of ConstDec (qid,ty,exp)
       => ConstDec (qid,ty,transRval (E,empty_varE) exp)
   | FnDec (qid,params,ty,exp)
       => FnDec (qid,params,ty, transRval (E,assocFn params) exp)
;

fun transRval_filter E filterdec =
 case filterdec
 of FilterDec (qid,ports,props) =>
      let val props' = map (I##transRval (E,empty_varE)) props
      in FilterDec (qid,ports,props')
      end handle e => raise wrap_exn "PP_CakeML" "transRval_filter" e;

fun transRval_monitor E mondec =
  let fun ivarFn(a,b,e) = (a,b,transRval (E,empty_varE) e)
      fun guarFn (a,b,e) = (a,b,transRval (E,empty_varE) e)
  in
   case mondec
    of MonitorDec (qid,ports,latched,decs,ivardecs,guars) =>
        let val decs' = map (transRval_decl E) decs
            val ivardecs' = map ivarFn ivardecs
            val guars' = map guarFn guars
        in MonitorDec(qid,ports,latched,decs',ivardecs',guars')
        end
  end
  handle e => raise wrap_exn "PP_CakeML" "transRval_monitor" e;

fun transRval_pkg E (Pkg (pkgName,(tydecs,tmdecs,filters,monitors))) =
 Pkg(pkgName,
       (tydecs,
        map (transRval_decl E) tmdecs,
        map (transRval_filter E) filters,
        map (transRval_monitor E) monitors));

fun tydec_to_ty tydec =
  case tydec
   of RecdDec (qid,fields) => RecdTy(qid,fields)
    | ArrayDec(qid,ty) => ty
    | EnumDec (qid,_) => NamedTy qid
    | UnionDec(qid,_) => NamedTy qid

fun mk_tyE pkglist =
 let fun tydecs_of (Pkg(pkgName,(tys,consts,filters,monitors))) = tys
     val all_tydecs = List.concat (map tydecs_of pkglist)
     fun mk_tydec_bind tydec = (tydec_qid tydec,tydec_to_ty tydec)
     val tydec_alist = map mk_tydec_bind all_tydecs
 in assocFn tydec_alist
 end

fun is_const_dec (ConstDec _) = true | is_const_dec other = false;

fun mk_constE pkglist =
 let fun cdecs_of (Pkg(pkgName,(tys,consts,filters,monitors))) = consts
     val all_cdecs = List.concat (map cdecs_of pkglist)
     val all_const_decs = filter is_const_dec all_cdecs
     fun mk_const_bind (ConstDec(qid,ty,e)) = (snd qid,ty)
       | mk_const_bind otherwise = raise ERR "mk_constE" "expected a ConstDec"
     val alist = map mk_const_bind all_const_decs
 in assocFn alist
 end

fun transRval_pkglist plist =
 let val tyE = mk_tyE plist
     val constE = mk_constE plist
 in map (transRval_pkg (tyE,constE)) plist
 end;

fun dest_recd_dec (RecdDec (qid, fields)) = (qid,fields)
  | dest_recd_dec otherwise = raise ERR "dest_recd_dec" ""

fun mk_recd_projns tys =
 let open AST
     val recd_tydecs = mapfilter dest_recd_dec tys

     fun mk_proj (tyqid as (pkgName,tyName)) vars ((fieldName,ty),var) =
         let val fnName = recd_projFn_name tyName fieldName
         in FnDec((pkgName,fnName),
                  [("recd", NamedTy tyqid)], ty,
                  Fncall(("","Record-Projection"),var::vars))
         end
     fun mk_projFns (qid,fields) =
	  let val vars = map (fn i => VarExp("v"^Int.toString i))
                         (upto 1 (length fields))
              val field_vars = zip fields vars
          in map (mk_proj qid vars) field_vars
          end
     val projFns = List.concat (map mk_projFns recd_tydecs)
 in
   projFns
 end

fun dest_recd_projnFn tmdec =
 case tmdec
  of FnDec(qid,[("recd", NamedTy tyqid)], ty,
           Fncall(("","Record-Projection"),var::vars)) => SOME(qid,tyqid,var,vars)
   | otherwise => NONE
;

fun pp_projFn depth pkgName (qid,tyqid,var,vars) =
 let open PolyML
 in if null vars then
       PrettyString "<BADLY FORMED PROJECTION FN!>"
    else
      PrettyBlock(2,true,[],
        [PrettyString "fun ",
         PrettyString ("lc"^snd qid), PrettyString " recd =",Space,
         PrettyString "case recd", Line_Break,
         PrettyString "  of ", PrettyString (snd tyqid^"Recd"), PrettyString " ",
         pp_list_with_style false Space [emptyBreak]
                (pp_exp (depth-1) pkgName) vars,
         PrettyString " => ", (pp_exp (depth-1) pkgName) var,
         Semicolon])
 end;

fun pp_tmdec depth pkgName tmdec =
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
    else
  case tmdec
   of ConstDec (qid,ty,exp) =>
      PrettyBlock(3,true,[],
        [PrettyString "val ",
         PrettyString (snd qid),
         PrettyString " =", Space,
         pp_exp (depth-1) pkgName exp,
         Semicolon])
    | FnDec (qid,params,ty,exp) =>
       let fun pp_param (s,ty) = PolyML.PrettyString s
       in case dest_recd_projnFn tmdec
           of NONE =>
                PrettyBlock(0,true,[],
                  [PrettyString "fun ",
                   PrettyString (snd qid), PrettyString " ",
                   if null params then PrettyString"()" else
                   gen_pp_list Space [emptyBreak] pp_param params,
                   PrettyString " =", Space,
                   pp_exp (depth-1) pkgName exp,
                   Semicolon])
           | SOME data => pp_projFn depth pkgName data
       end
 end;


fun pp_filter depth (FilterDec (qid,ports,props)) =
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
    else
      PrettyBlock(0,true,[],
	  [PrettyString "FILTER: ",
	   PrettyString (qid_string qid)])
 end;

fun dest_inout (InOut p) = p
  | dest_inout otherwise = raise ERR "dest_inout" "";
fun dest_in (In p) = p
  | dest_in otherwise = raise ERR "dest_in" "";

fun portname (Event s) = s
  | portname (Data(s,ty)) = s
  | portname (EventData(s,ty)) = s;

(*---------------------------------------------------------------------------*)
(* The stepFn synthesized for a monitor has the form                         *)
(*                                                                           *)
(*  stepFn inports outports stateVars =                                      *)
(*    let val (ip1,..., ipn) = inports                                       *)
(*        val (op1,...,opj) = outports                                       *)
(*        val (initStep,sv1,...,svk) = stateVars                             *)
(*    in                                                                     *)
(*      if initStep then                                                     *)
(*        let val sv1 = ie1                                                  *)
(*              ...                                                          *)
(*            val svk = iek                                                  *)
(*        in (False,sv1,...,svk)                                             *)
(*        end                                                                *)
(*      else                                                                 *)
(*        let val sv1 = e1                                                   *)
(*              ...                                                          *)
(*            val svk = ek                                                   *)
(*        in (False,sv1,...,svk)                                             *)
(*        end                                                                *)
(*    end                                                                    *)
(*                                                                           *)
(* where (ie1,...,iek) = init = the updates made in the first step           *)
(* and (e1,...,ek) = step = updates made in all subsequent steps.            *)
(*                                                                           *)
(* Contiguity type parser can be written to model ports as follows:          *)
(*                                                                           *)
(*   EventDataPort = 'a option                                               *)
(*   DataPort = 'a                                                           *)
(*   Event = bool  (* or possibly unit option *)                             *)
(*                                                                           *)
(* For each call to Event(p), the type of port for p has to be calculated so *)
(* that the correct projection function can be used.                         *)
(*---------------------------------------------------------------------------*)

val boolTy = BaseTy BoolTy;
val dummyTy = NamedTy("","dummyTy");
val unitExp = Fncall(("","unitExp"),[]);
val emptyString = VarExp(Lib.quote"")

fun mk_ite(b,e1,e2) = Fncall(("","IfThenElse"),[b,e1,e2]);
fun mk_assignExp v e = Fncall(("","AssignExp"),[v,e]);
fun mk_tuple list = Fncall(("","Tuple"),list)

fun letExp binds exp =
    let val eqs = map (fn (a,b) => Binop(Equal,a,b)) binds
    in Fncall(("","LET"),eqs@[exp])
    end;

fun localFnExp (name,args,body) = (Fncall(("","FUN"),VarExp name :: args),body)

val NoneExp = ConstrExp(("Option","option"),"None",NONE);
fun mk_Some e = ConstrExp(("Option","option"),"Some",SOME e)

fun mk_boolOpt e = mk_ite(e,mk_Some unitExp,NoneExp)

fun mk_comment slist = Fncall(("","Comment"), map VarExp slist);

fun mk_ref e = Fncall(("","Ref"),[e]);
fun mk_deref e = Fncall(("","!"),[e]);

(*---------------------------------------------------------------------------*)
(* There should be enough information in the outgoing FnDecl so that code    *)
(* can be generated, and also logic definitions.                             *)
(*                                                                           *)
(* Wondering if output ports should be part of the state. Seems like there   *)
(* should be a state variable for an output port if the port value is used   *)
(* subsequent computations. But it would be possible to have an output port  *)
(* value calculated from an expression ... hmmm maybe this isn't a           *)
(* distinction worth making.                                                 *)
(*                                                                           *)
(* TODO: sort Lustre variables in dependency order. Right now I assume that  *)
(* has been done by the programmer/system designer.                          *)
(*---------------------------------------------------------------------------*)

fun feature2port (s,ty,dir,kind) =
 case kind
  of "EventDataPort" => EventData(s,ty)
   | "DataPort" => Data(s,ty)
   | "EventPort" => Event s
   | otherwise => raise ERR "feature2port" "";

fun split_fby exp =
  case exp
   of Binop(Fby,e1,e2) => (e1,e2)
    | otherwise => (exp,exp);

fun outCode_target (gName,docstring,codeG) =
 case codeG
  of Binop(Equal,e1,e2) =>
      (case e1
        of Fncall(("","event"),[VarExp p]) => p
         | VarExp p => p
         | otherwise => raise ERR "outCode_target" "unexpected syntax")
   | Fncall(("","IfThenElse"),[b,e1,e2]) =>
      (case e1
        of Binop(And,Fncall(("","event"),[VarExp p]),
                     Binop(Equal,VarExp p1,exp))
           => if p=p1 then p
              else raise ERR "outCode_target" "inconsistent port names"
         | otherwise => raise ERR "outCode_target" "unexpected syntax")
   | otherwise => raise ERR "outCode_target" "unexpected syntax";

fun mk_outExp (gName,docstring,codeG) =
 case codeG
  of Binop(Equal,e1,e2) =>
      (case e1
        of Fncall(("","event"),_) => mk_boolOpt e2
         | VarExp p => e2
         | otherwise => raise ERR "mk_outExp" "unexpected syntax")
   | Fncall(("","IfThenElse"),[b,e1,e2]) =>
      (case e1
        of Binop(And,_,Binop(Equal,_,exp)) => mk_ite (b,mk_Some exp,NoneExp)
         | otherwise => raise ERR "mk_outExp" "unexpected syntax")
   | otherwise => raise ERR "mk_outExp" "unexpected syntax";

val stateVar = VarExp"state";
val initStepVar = VarExp"initStep";

val stateVal_comment =
 (VarExp"foo",
  mk_comment ["",
	      "(*--------------------------*)",
              "(* Compute new state values *)",
              "(*--------------------------*)",""]);

val outVal_comment =
 (VarExp"foo",
  mk_comment ["",
	      "(*-----------------------*)",
              "(* Compute output values *)",
              "(*-----------------------*)", ""]);

(*---------------------------------------------------------------------------*)
(* Mapping AADL types to contiguity type names. The corresponding contig     *)
(* types will be found in structure Uxas. The mapping is used to generate    *)
(* parsers via a call                                                        *)
(*                                                                           *)
(*   Contig.parseFn Uxas.uxasEnv                                             *)
(*           (Contig.VarName"root")                                          *)
(*           contig                                                          *)
(*           ([],string,Contig.mk_empty_lvalMap())                           *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val parseTable =
  [(NamedTy("CMASI","AddressAttributedMessage"), "aaMesg"),
   (NamedTy("CMASI","OperatingRegion"),          "OperatingRegion"),
   (NamedTy("CMASI","LineSearchTask"),           "LineSearchTask"),
   (NamedTy("CMASI","AutomationRequest"),        "AutomationRequest"),
   (NamedTy("CMASI","AutomationResponse"),       "AutomationResponse"),
   (NamedTy("CMASI","AddressArray"),             "address_array"),
   (NamedTy("CMASI","Polygon"),                  "polygon")]

(*
fun mk_parseFn_call inputs =
 let val table =

fun mk_predFn_call inputs =
 let val table =
*)

fun mk_mon_stepFn mondec =
 let val MonitorDec(qid,ports,latched,decs,ivardecs,outCode) = mondec
     val stepFn_name = "stepFn"
     val (inports,outports) = Lib.partition (fn (_,_,mode,_) => mode = "in") ports
     val inputs    = map feature2port inports
     val outputs   = map outCode_target outCode
     val outVars   = map VarExp outputs
     val outVarT   = mk_tuple outVars
     val stateVars = map (fn (name,ty,exp) => VarExp name) ivardecs
     val stateVarT = mk_tuple stateVars
     val pre_stmts = map (fn (s,ty,exp) => (VarExp s, split_fby exp)) ivardecs
     val init_code = map (fn (v,(e1,e2)) => (v, e1)) pre_stmts
                     @ [(unitExp, mk_assignExp initStepVar (ConstExp(BoolLit false)))]
     val step_code = map (fn (v,(e1,e2)) => (v, e2)) pre_stmts
     val inportBs  = (mk_tuple(map (VarExp o portname) inputs),VarExp"inports")
(*     val inportVs  = (mk_tuple(map (VarExp o portname) inputs),
                      mk_tuple (map mk_parse inputs))
*)
     val stateBs   = (mk_tuple stateVars,VarExp"stateVars")
     val outportBs = (mk_tuple(map VarExp outputs),VarExp"outports")
     val pre_def   = localFnExp("pre",[VarExp"x"],VarExp"x")
     val retTuple  = mk_tuple stateVars
     val initExp   = letExp init_code retTuple
     val stepExp   = letExp step_code retTuple
     val condExp   = Fncall(("","IfThenElse"),[mk_deref initStepVar,initExp,stepExp])
     val topBinds  = letExp ([inportBs,(* inportVs,*)
                              stateBs,pre_def, stateVal_comment,
                              (stateVarT,condExp),outVal_comment]
                             @ zip outVars (map mk_outExp outCode))
                            (mk_tuple [stateVarT,outVarT])
  in
    FnDec((fst qid,"stepFn"),
          [("inports",dummyTy),("stateVars",dummyTy)],
          dummyTy,
          topBinds)
 end;

(*---------------------------------------------------------------------------*)
(* Takes a "code guarantee" and generates output code from it. There are 3   *)
(* possible forms expected for the guarantee, depending on the output port   *)
(* type.                                                                     *)
(*                                                                           *)
(*  1. Event port. The expected form is                                      *)
(*                                                                           *)
(*       event(port) = exp                                                   *)
(*                                                                           *)
(*     This indicates that port is an event port and it will be set (or not) *)
(*     according to the value of exp, which is boolean.                      *)
(*                                                                           *)
(*  2. Data port. The expected form is                                       *)
(*                                                                           *)
(*       port = exp                                                          *)
(*                                                                           *)
(*     This indicates that port is a data port and that the value of exp     *)
(*     will be written to it.                                                *)
(*                                                                           *)
(*  3. Event data port. The expected form is                                 *)
(*                                                                           *)
(*       if exp1 then                                                        *)
(*         event (port) and port = exp2                                      *)
(*       else not (event port)                                               *)
(*                                                                           *)
(*     This checks the condition exp1 to see whether an event on port will   *)
(*     happen, and exp2 gives the output value if so. Note that any input    *)
(*     event (or event data) port p occurring in exp2 must be guaranteed to  *)
(*     have an event by event(-) checks in computed in exp1.                 *)
(*                                                                           *)
(* In all of 1,2,3, the expressions should not mention any output ports,     *)
(* i.e. the value to be sent out is determined by a computation over input   *)
(* ports and state variables only.                                           *)
(*---------------------------------------------------------------------------*)

fun mk_callFFI_out portName d =
  Fncall(("API","callFFI"),[VarExp (Lib.quote ("put_"^portName)),d]);

fun mk_output ports (gName,docstring,code) =
 case code
  of Binop(Equal,e1,e2) =>
      (case e1
        of Fncall(("","event"),[VarExp p]) =>
            mk_ite(e2,mk_callFFI_out p (VarExp (Lib.quote"")),
                   unitExp)
         | VarExp portName => mk_callFFI_out portName e2
         | otherwise => raise ERR "mk_output"
            "unexpected syntax in output port code spec")
   | Fncall(("","IfThenElse"),[b,e1,e2]) =>
        (case e1
          of Binop(And,Fncall(("","event"),[VarExp p]), Binop(Equal,VarExp p1,exp))
             => mk_ite(b,mk_callFFI_out p exp, unitExp)
           | otherwise => raise ERR "mk_output"
                         "unexpected syntax in output port code spec")
   | otherwise => raise ERR "mk_output" "unexpected syntax in output port code spec"


fun mk_mon_cycleFn mondec =
 let val MonitorDec(qid,ports,latched,decs,ivardecs,outCode) = mondec
     val inputsVar = VarExp "inputs"
     val theStateVar = VarExp "theState"
     val stateValsVar = VarExp "stateVals"
     val outputValsVar = VarExp "outputVals"
     val inputsBind = (unitExp, Fncall(("","receiveInputs"),[unitExp]))
     val inbufsBind = (inputsVar, Fncall(("","fill_input_buffers"),[unitExp]))
     val stepRetBind = (mk_tuple[stateValsVar,outputValsVar],
                        Fncall(("","stepFn"),[inputsVar,mk_deref theStateVar]))
     val fill_outbufs = (unitExp, Fncall(("","fill_output_buffers"),[outputValsVar]))
     val update_state = (unitExp, mk_assignExp theStateVar stateValsVar)
     val outputsBind = (unitExp, Fncall(("","sendOutputs"),[unitExp]))
     val bodyExp = letExp [inputsBind,inbufsBind,stepRetBind,
                           fill_outbufs,update_state,outputsBind] unitExp
 in
    FnDec((fst qid,"cycleFn"), [], dummyTy, bodyExp)
 end

(*---------------------------------------------------------------------------*)
(* Buffer sizes for messages declared in CM_Property_Set.                    *)
(*---------------------------------------------------------------------------*)

fun byteSize e = Binop(Divide,e,mk_uintLit 8);

fun mk_buf pkgName (name,ty,dir,kind) =
 case ty
  of NamedTy(pkg,tyName) =>
     let val exp = Fncall(("Word8Array","array"),
             [byteSize(VarExp("CM_Property_Set."^tyName^"_Bit_Codec_Max_Size")),
              VarExp("Utils.w8zero")])
     in ConstDec((pkgName,name^"Buf"),dummyTy, exp)
     end
  | otherwise => raise ERR "mk_buf" "expected a named type";

fun is_data_port (name,ty,dir,kind) = not(kind = "EventPort");
fun is_inport (name,ty,dir,kind) = (dir = "in")

fun mk_fillFn inports =
 let val names = map (fn (name,ty,dir,kind) => name)  inports
     val bufnames = map (fn p => p^"Buf") names
     val bufVars = map VarExp bufnames
     fun mk_clear v = (unitExp,Fncall(("Utils","clearBuf"),[v]))
     fun mk_get name v = (unitExp,Fncall(("","#(api_get_"^name^")"),[emptyString,v]))
     fun mk_b2s v = Fncall(("Utils","buf2string"),[v])
     val clears = map mk_clear bufVars
     val gets = map2 mk_get names bufVars
     val strings = mk_tuple (map mk_b2s bufVars)
     val bodyExp = letExp (clears @ gets) strings
 in
  FnDec (("","fill_input_buffers"),[],dummyTy, bodyExp)
 end

fun mk_stateVardecs n =
  let val NoneExp = ConstrExp(("","Option"),"None",NONE)
      val nexpList = map (K NoneExp) (upto 1 n)
      val Some_True_Exp = ConstrExp(("","Option"),"Some",SOME (ConstExp(BoolLit true)))
      val intial_stateVar_contents = Some_True_Exp::nexpList
      val refTuple = Fncall(("","Ref"),[mk_tuple nexpList])
  in ConstDec(("","theState"),dummyTy, refTuple)
  end

(*---------------------------------------------------------------------------*)
(* Monitor declaration results in                                            *)
(*                                                                           *)
(* - I/O buffers declared, one per port, sizes taken from CM_Property_Set    *)
(* - declare maps (decoders) from buffers to datastructures                  *)
(* - declare stateVars as refs to NONE                                       *)
(* - declare stepFn and all related computational support                    *)
(* - declare cycleFn                                                         *)
(*---------------------------------------------------------------------------*)

fun pp_monitor depth mondec =
 let val MonitorDec(qid,ports,latched,decs,ivardecs,outCode) = mondec
     val stepFn = mk_mon_stepFn mondec
     val cycleFn = mk_mon_cycleFn mondec
     val dataports = filter is_data_port ports
     val iobufdecs = map (mk_buf (fst qid)) dataports
     val infiller_dec = mk_fillFn (filter is_inport dataports)
     val stateVars_dec = mk_stateVardecs (length ivardecs)
     val decs1 = iobufdecs @ [infiller_dec,stateVars_dec] @ decs @ [stepFn,cycleFn]
     val decs2 = stateVars_dec :: (decs @ [stepFn])
 in
  end_pp_list Line_Break Line_Break (pp_tmdec (depth-1) (fst qid)) decs2
 end
(*---------------------------------------------------------------------------*)
(* Add in projection functions, and tranform expressions with field          *)
(* projections.                                                              *)
(*---------------------------------------------------------------------------*)

fun pp_pkg depth (Pkg(pkgName,(types,consts,filters,monitors))) =
 let open PolyML
     val projFns = mk_recd_projns types
     val consts' = projFns @ consts
 in if depth = 0 then PrettyString "<decl>"
   else
    PrettyBlock(2,true,[],
        [PrettyString ("structure "^pkgName^" = "), Line_Break,
         PrettyString "struct", Line_Break_2,
         end_pp_list Line_Break Line_Break (pp_tydec (depth-1) pkgName) types,   Line_Break,
         end_pp_list Line_Break Line_Break (pp_tmdec (depth-1) pkgName) consts', Line_Break,
         end_pp_list Line_Break Line_Break (pp_filter (depth-1)) filters,        Line_Break,
         end_pp_list Line_Break Line_Break (pp_monitor (depth-1)) monitors,      Line_Break,
         PrettyString "end"
        ])
 end

val _ = PolyML.addPrettyPrinter (fn i => fn () => fn ty => pp_ty i "<pkg>" ty);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn e => pp_exp i "<pkg>" e);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tydec => pp_tydec i "<pkg>" tydec);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tmdec => pp_tmdec i "<pkg>" tmdec);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn mon => pp_monitor i mon);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn pkg => pp_pkg i pkg);


(*---------------------------------------------------------------------------*)
(* Instantiate monitor template                                              *)
(*---------------------------------------------------------------------------*)

local
(*---------------------------------------------------------------------------*)
(* Read in the template file "splat/codegen/monitor-template"                *)
(*---------------------------------------------------------------------------*)
val filter_template_ss =
    let val istrm = TextIO.openIn "codegen/monitor-template"
	val string = TextIO.inputAll istrm
    in TextIO.closeIn istrm;
       Substring.full string
    end;
in
fun locate pat ss =
 let val (chunkA, suff) = Substring.position pat ss
     val chunkB = Substring.triml (String.size pat) suff
 in (chunkA,chunkB)
 end

(*---------------------------------------------------------------------------*)
(* New file contents:                                                        *)
(*           chunk0 . input-buf-decls .                                       *)
(*           chunk1 . fill-inputs-decl .                                     *)
(*           chunk2 . FFI-outputs-decl .                                     *)
(*           chunk3 . size-origin .                                          *)
(*           chunk4 . buf-size .                                             *)
(*           chunk5 . inport-name .                                          *)
(*           chunk6 . inport-name .                                          *)
(*           chunk7 . contig-qid .                                           *)
(*           chunk8                                                          *)
(*---------------------------------------------------------------------------*)
val replace  =
 let val (chunk0,suff0) = locate "<<INPUT-BUF-DECLS>>" filter_template_ss
     val (chunk1,suff1) = locate "<<FILL-INPUT-BUFS>>" suff0
     val (chunk2,suff2) = locate "<<FFI-OUTPUT-CALLS>>" suff1
     val (chunk3,suff3) = locate "<<INPUT-BUF-DECLS>>" suff2
     val (chunk4,suff4) = locate "<<FILL-INPUT-BUFS>>" suff3
     val (chunk5,suff5) = locate "<<INPORT>>" suff4
     val (chunk6,suff6) = locate "<<INPORT>>" suff5
     val (chunk7,suff7) = locate "<<CONTIG>>" suff6
 in fn input_buf_decl =>
    fn fill_inputs_decl =>
    fn ffi_outputs_decl =>
    fn size_origin =>
    fn bufsize =>
    fn inport =>
    fn contig =>
      Substring.concat
         [chunk0, input_buf_decl,
          chunk1, fill_inputs_decl,
          chunk2, ffi_outputs_decl,
          chunk3, size_origin,
          chunk4, bufsize,
          chunk5, inport,
          chunk6, inport,
          chunk7, contig,suff7]
 end
end;

fun numBytes n = 1 + Int.div(n,8);

fun dest_namedTy (NamedTy qid) = qid
  | dest_namedTy other = raise ERR "dest_namedTy" "";

fun dest_intLit exp =
 case exp
  of ConstExp(IntLit{value,kind = AST.Int NONE}) => value
   | otherwise => raise ERR "dest_intLit" "";

fun isIn (name,ty,"in",style) = true
  | isIn otherwise = false

fun mk_inbuf_decl const_alist (pname,ty,d,style) =
 let val (pkg,tyName) = dest_namedTy ty
     val sizeName = tyName^"_Bit_Codec_Max_Size"
     val bitsize_exp = assoc sizeName const_alist
     val bitsize = dest_intLit bitsize_exp
     val byte_size_string = Int.toString (1 + numBytes bitsize) (* for event byte *)
     val () = stdErr_print (String.concat
                ["    Buffer size (bits/bytes) : ",
                 Int.toString bitsize,"/",byte_size_string,"\n"])
     val inbufName = pname^"_buffer"
 in
   (inbufName,
    String.concat
     ["(*---------------------------------------------------------------------------*)\n",
      "(* Size computed from ",sizeName, "                  *)\n",
      "(*---------------------------------------------------------------------------*)\n\n",
      "val ",inbufName," = Word8Array.array ", byte_size_string, " Utils.w8zero;"])
 end;

fun mk_fill_inbufs portNames inbufNames =
 let val clearStrings =
         map (fn bname => ("val () = Utils.clear_buf "^bname)) inbufNames
     val fillStrings =
         map2 (fn pn => fn bn =>
                ("val () = #(api_get_"^pn^") \"\" "^bn))
             portNames inbufNames
     val cpStrings =
         map (fn bname => ("Utils.buf2string "^bname)) inbufNames
 in
 String.concatWith "\n"
["(*---------------------------------------------------------------------------*)",
 "(* Clear buffers, read ports into buffers, copy buffers to strings           *)",
 "(*---------------------------------------------------------------------------*)",
 "",
 "fun fill_input_buffers () =",
 "  let "^String.concatWith "\n      " clearStrings,
 "      "^String.concatWith "\n      " fillStrings,
 "   in",
 "      ("^String.concatWith ",\n       " cpStrings^")",
 "   end;"
]
end;

fun mk_output_call (name,ty,_,_) =
    String.concat ["#(api_put_",name,") ","string Utils.emptybuf"]

fun paren s = String.concat["(",s,")"];

fun mk_output_calls oports =
 let val body =
       (case oports
         of [] => raise ERR "mk_output_calls" ""
          | [port] => mk_output_call port
          | multiple => paren(String.concatWith ";\n    "
                               (map mk_output_call oports)))
 in String.concat
       ["fun output_calls string =\n   ",body,";"]
 end

(*---------------------------------------------------------------------------*)
(* Instantiate monitor template with monitor-specific info                   *)
(*---------------------------------------------------------------------------*)

fun export_cakeml_monitors s list monlist = ();

(*
fun inst_monitor_template dir const_alist mondec =
 let open Substring
 in
 case mondec
  of MonitorDec (qid,ports,latched,decs,ivardecs,guars) =>
     let val () = stdErr_print ("-> "^qid_string qid^"\n")
         val (inports, outports) = Lib.partition isIn ports
         val inportNames = map #1 inports
         val inbuf_decls = map (mk_inbuf_decl const_alist) inports
         val inbufNames = map fst inbuf_decls
         val inbuf_decl_string = String.concatWith "\n\n" (map snd inbuf_decls)^"\n"
         val fill_inputs_decl = mk_fill_inbufs inportNames inbufNames
         val outFns = mk_output_calls outports
   | otherwise => raise ERR "inst_monitor_template" "expected a MonitorDec"
 end

fun export_cakeml_monitors dir const_alist mondecs =
  if null mondecs then
     ()
  else
  let val qids = map mondec_qid mondecs
      val names = map qid_string qids
      val _ = stdErr_print (String.concat
         ["Creating CakeML monitor implementation(s) for:\n   ",
          String.concatWith "\n   " names, "\n"])
  in
     List.app (inst_monitor_template dir const_alist) mondecs
   ; stdErr_print " ... Done.\n\n"
  end
*)

end (* PP_CakeML *)
