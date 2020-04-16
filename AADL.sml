(*---------------------------------------------------------------------------*)
(* Translation from AADL (in Json syntax) to an AST form, and then to HOL    *)
(*---------------------------------------------------------------------------*)

structure AADL :> AADL =
struct

open Lib Feedback HolKernel boolLib bossLib MiscLib AST Json;

local open
   stringLib stringSimps fcpLib
   regexpLib regexpSyntax aadl_basetypesTheory ptltlSyntax
in end;

 type qid = string * string;
 type ty = AST.ty;
 type exp = AST.exp;
 type tyEnv = (ty * ty) list;

 datatype tydec
    = EnumDec of qid * string list
    | RecdDec of qid * (string * ty) list
    | ArrayDec of qid * ty;

 datatype tmdec
    = ConstDec of qid * ty * exp
    | FnDec of qid * (string * ty) list * ty * exp;

 datatype filter
    = FilterDec of qid * (string * ty * string * string) list * (string * exp) list

 datatype monitor
    = MonitorDec of qid * (string * ty * string * string) list * (string * exp) list

 type decls =
  (* pkgName *)  string *
  (* types *)    (tydec list *
  (* consts *)    tmdec list *
  (* filters *)   filter list *
  (* monitors *)  monitor list)
  ;

val ERR = Feedback.mk_HOL_ERR "AADL";

(*---------------------------------------------------------------------------*)
(* Json to AST (types, expressions, function definitions, and filters)       *)
(*---------------------------------------------------------------------------*)

fun dest_qid s =
 let val chunks = String.tokens (fn c => equal #"." c orelse equal #":" c) s
 in case Lib.front_last chunks
     of ([a,b],"Impl") => (a,b)
      | ([a],"Impl") => ("",a)
      | ([],"Impl") => raise ERR "dest_qid" "unexpected format"
      | ([a],b) => (a,b)
      | ([],b)  => ("",b)
      | otherwise => raise ERR "dest_qid" "unexpected format"
 end;

(* Principled approach, doing a one-for-one mapping between AADL integer types and,
   eventually, HOL types. Not sure how well it will work with all AGREE specs limited
   to be (unbounded) Integer. Example: a field "f : Integer_32" may be constrained by
   an AGREE formula to be less than 42, say. But AGREE only believes in Integer, so
   the constraint is not well-typed. A system of coercions can be built, so that

       toInteger (f) < 42

    or

       f < toInteger_32(42)

   deliver a well-typed formula. The first coercion above (toInteger)
   is total; the second is not, and adds a "wellformedness
   obligation", namely that the argument of toInteger_32(-) is in
   range; moreover, in case that the argument is a compound
   expression, it requires the coercion to be recursively pushed down
   through the expression. So, for example, coercing to Integer_32 in

      f < toInteger_32(x + 256)

   means rewriting to

      f < Integer_32_plus (toInteger_32(x), toInteger_32 (256))

fun dest_tyqid dotid =
 let open AST
     val UnbInt = BaseTy(IntTy(Int NONE))
 in case dest_qid dotid
     of (_,"Integer")     => UnbInt
      | (_,"Natural")     => UnbInt
      | (_,"Unsigned_8")  => UnbInt
      | (_,"Unsigned_16") => UnbInt
      | (_,"Unsigned_32") => UnbInt
      | (_,"Unsigned_64") => UnbInt
      | (_,"Integer_8")   => UnbInt
      | (_,"Integer_16")  => UnbInt
      | (_,"Integer_32")  => UnbInt
      | (_,"Integer_64")  => UnbInt
      | (_,"Bool")        => BaseTy BoolTy
      | (_,"Boolean")     => BaseTy BoolTy
      | (_,"String")  => BaseTy StringTy
      | (_,"Char")    => BaseTy CharTy
      | (_,"Float")   => BaseTy FloatTy
      | (a,b)         => NamedTy (a,b)
 end;
*)

fun dest_tyqid dotid =
 case dest_qid dotid
  of (_,"Integer") => BaseTy(IntTy(AST.Int NONE))
   | (_,"Natural") => BaseTy(IntTy(AST.Nat NONE))
   | (_,"Unsigned_8")  => BaseTy(IntTy(AST.Nat (SOME 8)))
   | (_,"Unsigned_16") => BaseTy(IntTy(AST.Nat (SOME 16)))
   | (_,"Unsigned_32") => BaseTy(IntTy(AST.Nat (SOME 32)))
   | (_,"Unsigned_64") => BaseTy(IntTy(AST.Nat (SOME 64)))
   | (_,"Integer_8")   => BaseTy(IntTy(AST.Int (SOME 8)))
   | (_,"Integer_16")  => BaseTy(IntTy(AST.Int (SOME 16)))
   | (_,"Integer_32")  => BaseTy(IntTy(AST.Int (SOME 32)))
   | (_,"Integer_64")  => BaseTy(IntTy(AST.Int (SOME 64)))
   | (_,"Bool")    => BaseTy BoolTy
   | (_,"Boolean") => BaseTy BoolTy
   | (_,"String")  => BaseTy StringTy
   | (_,"Char")    => BaseTy CharTy
   | (_,"Float")   => BaseTy FloatTy
   | (a,b)         => NamedTy (a,b)
;

fun get_tyinfo tyinfo =
 case tyinfo
  of [("kind", String "recordType"),
      ("recordType",
       AList [("kind", String "typeId"), ("name", String dotid)])]
     => dest_tyqid dotid
   | [("kind", String "recordType"),
      ("recordType",
       AList [("kind", String "nestedDotId"), ("name", String dotid)])]
     => dest_tyqid dotid
   | [("kind", String "typeId"), ("name", String tyname)]
     => dest_tyqid tyname
   | [("kind", String "DoubleDotRef"), ("name", String tyname)]
     => dest_tyqid tyname
   | [("kind", String "primType"), ("primType", String "bool")]
     => BaseTy BoolTy
   | [("kind", String "PrimType"), ("primType", String "bool")]
     => BaseTy BoolTy
   | [("kind", String "primType"), ("primType", String "int")]
     => BaseTy(IntTy (AST.Int NONE))
   | [("kind", String "PrimType"), ("primType", String "int")]
     => BaseTy(IntTy (AST.Int NONE))
   | otherwise => raise ERR "get_tyinfo" "unable to construct type";

fun dest_ty ty =
 case ty
  of AList [("kind", String "type"), ("type", AList tyinfo)] => get_tyinfo tyinfo
   | AList tyinfo => get_tyinfo tyinfo
   | otherwise => raise ERR "dest_ty" "expected a type expression"
;

fun mk_dotid did =
  case Lib.front_last (String.tokens (equal #".") did)
  of ([],v) => VarExp v
   | (v::t,proj) => rev_itlist (C (curry RecdProj)) (t @ [proj]) (VarExp v)
;

fun mk_unop (opr,e) =
 let val oexp =
       case opr
        of "not" => Not
         | "-"   => UMinus
         | other => raise ERR "mk_unop"
               ("unknown unary operator "^Lib.quote other)
 in Unop(oexp,e)
 end

fun mk_binop (opr,e1,e2) =
 let val oexp =
       case opr
        of "+"   => Plus
         | "-"   => Minus
         | "*"   => Multiply
         | "<"   => Less
         | "<="  => LessEqual
         | ">"   => Greater
         | ">="  => GreaterEqual
	 | "=>"  => Imp
         | "="   => Equal
         | "and" => And
         | "or"  => Or
         | other => raise ERR "mk_binop"
               ("unknown binary operator "^Lib.quote other)
 in Binop(oexp,e1,e2)
 end

fun mk_intLit i = ConstExp(IntLit{value=i, kind=AST.Int NONE});

fun mk_int str =
  case Int.fromString str
   of SOME i => mk_intLit i
    | NONE =>
       raise ERR "mk_int" ("expected an int constant, but got: "^Lib.quote str)

fun mk_bool_const str =
 case Bool.fromString str
  of SOME b => ConstExp (BoolLit b)
   | NONE => raise ERR "mk_bool_const" "expected true or false";

fun mk_fncall(pkgname, fname, args) = Fncall((pkgname,fname),args);

fun mk_nullary_constr(cname, ty) =
 case ty
  of NamedTy tyqid => ConstrExp(tyqid,cname,NONE)
   |  otherwise => raise ERR "mk_nullary_constr"
       ("unable to determine type of constructor "^Lib.quote cname)

fun mk_and a b = mk_binop("and",a,b);

(*---------------------------------------------------------------------------*)
(* AADL scraping.                                                            *)
(*---------------------------------------------------------------------------*)

val _ = defaultNumKind := AST.Int NONE;

fun dropString (String s) = s
  | dropString otherwise = raise ERR "dropString" "not a json String application";

fun dropList (List list) = list
  | dropList otherwise = raise ERR "dropList" "not a json List application";

fun dropAList (AList list) = list
  | dropAList otherwise = raise ERR "dropAList" "not a json AList application";

fun dropImpl s =
     case String.tokens (equal #".") s
      of [x,"Impl"] => SOME x
       | otherwise => NONE;

fun dest_named_ty (NamedTy qid) = qid
  | dest_named_ty other = raise ERR "dest_named_ty" "expected a NamedTy";

fun dest_exp e =
 case e
  of AList [("kind", String "NamedElmExpr"), ("name", String s)]
       => VarExp s
   | AList [("kind", String "EventExpr"),
            ("id", AList [("kind", String "NamedElmExpr"),("name", String s)])]
       => mk_fncall("","Event",[VarExp s])
   | AList [("kind", String "BoolLitExpr"), ("value", String bstr)]
       => mk_bool_const bstr
   | AList [("kind", String "IntLitExpr"), ("value", String intstr)]
       => mk_int intstr
   | AList [("kind", String "StringLitExpr"), ("value", String str)]
       => ConstExp(StringLit str)
   | AList [("kind", String "UnaryExpr"), ("operand", e), ("op", String opr)]
       => mk_unop (opr,dest_exp e)
   | AList [("kind", String "BinaryExpr"),
            ("left", le), ("op", String opr), ("right",re)]
       => mk_binop (opr,dest_exp le, dest_exp re)
   | AList [("kind", String "RecordLitExpr"),
            ("recordType", rty), ("value", AList jfields)]
       => RecdExp(dest_named_ty (dest_ty rty), map mk_field jfields)
   | AList [("kind", String "Selection"), ("target", target), ("field", String fname)]
       => RecdProj (dest_exp target, fname)
   | AList [("kind", String "CallExpr"),
            ("function", AList alist),
            ("args", List args)]
       => let val pkg = dropString (assoc "packageName" alist) handle _ => ""
              val fname = dropString (assoc "name" alist) handle _ => ""
          in mk_fncall(pkg,fname,map dest_exp args)
          end
   | AList [("kind", String "AadlEnumerator"),
            ("type", AList tyinfo), ("value", String constrname)]
       => mk_nullary_constr (constrname,get_tyinfo tyinfo)
   | AList [("kind", String "ForallExpr"),
            ("binding", String bvarname),
            ("array", jarr),
            ("expr", jexp)]
       => mk_fncall ("","Array_Forall",[VarExp bvarname, dest_exp jarr, dest_exp jexp])
   | AList [("kind", String "ExistsExpr"),
            ("binding", String bvarname),
            ("array", jarr),
            ("expr", jexp)]
       => mk_fncall ("","Array_Exists",[VarExp bvarname, dest_exp jarr, dest_exp jexp])
   | AList [("kind", String "IfThenElseExpr"),
            ("if", e1),
            ("then",e2),
            ("else",e3)]
       => mk_fncall ("","IfThenElse",[dest_exp e1, dest_exp e2, dest_exp e3])
   | AList [("kind", String "PrevExpr"),
            ("delay", e1),
            ("init",e2)]
       => mk_fncall ("","Prev",[dest_exp e1, dest_exp e2])
   | other => raise ERR "dest_exp" "unexpected expression form"
and
mk_field (fname,e) = (fname, dest_exp e);

fun dest_param param =
 case param
  of AList [("name", String pname), ("type", ty)] => (pname,dest_ty ty)
   | otherwise => raise ERR "dest_param" "unexpected input";

fun mk_fun_def pkgName json =
 case json
  of AList (("kind", String "FnDef")::binds) =>
     (case (assoc "name" binds,
            assoc "args" binds,
            assoc "type" binds,
            assoc "expr" binds)
       of (String fname, List params, ty, body) =>
           FnDec((pkgName,fname), map dest_param params, dest_ty ty, dest_exp body)
       |  otherwise => raise ERR "mk_fun_def" "unexpected input")
   | otherwise => raise ERR "mk_fun_def" "unexpected input";

fun mk_const_def pkgName json =
 case json
  of AList [("kind", String "ConstStatement"),
            ("name", String cname),
            ("type", ty),
            ("expr", body)] => ConstDec((pkgName,cname), dest_ty ty, dest_exp body)
  |  otherwise => raise ERR "mk_const_def" "unexpected input";

fun dest_feature (AList alist) =
    (dropString (assoc "name" alist),
     (dest_tyqid o dropString) (assoc "classifier" alist));

fun mk_property_stmt_def compName features (AList alist) =
     (case (assoc "kind" alist,
            assoc "name" alist,
	    assoc "expr" alist)
       of (String "PropertyStatement", String fname, e)
          => let val boolTy = BaseTy BoolTy
                 val exp = dest_exp e
                 val compParams = map dest_feature features
                 val free_names = expFrees [] exp
                 val params = filter (fn cp => mem (fst cp) free_names) compParams
             in
                FnDec((compName,fname), params, boolTy, exp)
             end
       | otherwise => raise ERR "mk_property_def" "unexpected syntax")
  | mk_property_stmt_def any other thing = raise ERR "mk_property_def" "unexpected syntax"
;

fun mk_eq_stmt_def compName features (AList alist) =
     (case (assoc "kind" alist,
            assoc "left" alist,
	    assoc "expr" alist)
       of (String "EqStatement", List [AList LHS], e)
          => let val fName = dropString(assoc "name" LHS)
                 val lhs_ty = dest_ty (assoc "type" LHS)
                 val exp = dest_exp e
                 val compParams = map dest_feature features
                 val free_names = expFrees [] exp
                 val params = filter (fn cp => mem (fst cp) free_names) compParams
             in
                FnDec((compName,fName), params, lhs_ty, exp)
             end
       | otherwise => raise ERR "mk_eq_stmt_def" "unexpected syntax")
  | mk_eq_stmt_def any other thing = raise ERR "mk_eq_stmt_def" "unexpected syntax"
;

fun mk_def pkgName features json =
  mk_const_def pkgName json    handle HOL_ERR _ =>
  mk_fun_def pkgName json      handle HOL_ERR _ =>
  mk_property_stmt_def pkgName features json handle HOL_ERR _ =>
  mk_eq_stmt_def pkgName features json handle HOL_ERR _ =>
  raise ERR "mk_def" "unexpected syntax";

fun get_annex_stmts (AList alist) =
    (case (assoc "name" alist,
           assoc "parsedAnnexLibrary" alist
            handle _ =>
           assoc "parsedAnnexSubclause" alist)
      of (String "agree", AList [("statements", List decls)]) => decls
       | otherwise => raise ERR "get_annex_stmts" "unexpected syntax")
  | get_annex_stmts otherwise = raise ERR "get_annex_stmts" "unexpected syntax"

fun mk_annex_defs pkgName features annex =
  mapfilter (mk_def pkgName features) (get_annex_stmts annex)

(*---------------------------------------------------------------------------*)
(* compName is of the form "<pkgName>::<actual_compName>", so futz around to *)
(* get the name into the form "<pkgName>__<actual_compName".                 *)
(*---------------------------------------------------------------------------*)

fun mk_comp_defs comp =  (* annex inside package component *)
 let val futz = String.map (fn ch => if ch = #":" then #"_" else ch)
 in
 case comp
  of AList alist =>
     let val compName = dropString (assoc "name" alist) handle _ => ""
         val features = dropList (assoc "features" alist) handle _ => []
         val annexes = dropList (assoc "annexes" alist)
     in List.concat(map (mk_annex_defs (futz compName) features) annexes)
     end
   | otherwise => raise ERR "mk_comp_defs" "unexpected annex format"
 end;


(*
val [d1,d2,d3,d4,d5,d6,d7,d8,d9,d10] = decls;
*)

fun fldty tystr = dest_tyqid tystr;

(*
fun fldty tystr =  (* replace with dest_ty? *)
 case dest_qid tystr
  of ("Base_Types","Integer") => BaseTy(IntTy (Int NONE))
   | ("Base_Types","Boolean") => BaseTy BoolTy
   | ("Base_Types","Char")    => BaseTy CharTy
   | ("Base_Types","String")  => BaseTy StringTy
   | (pkg,tyname) => NamedTy(pkg,tyname);
*)

(*---------------------------------------------------------------------------*)
(* Support for detecting and implementing record type extension              *)
(*---------------------------------------------------------------------------*)

val null_ty = NamedTy("","Missing Field");

fun mk_extender orig_name = ("--Extends--", NamedTy(dest_qid orig_name))
fun dest_extender (RecdDec (qid, ("--Extends--", NamedTy orig_qid)::t)) =
      (qid,orig_qid,t)
  | dest_extender otherwise = raise ERR "dest_extender" "";


fun dest_field subcomp =
 case subcomp
  of AList [("name", String fldname),
            ("kind", String "Subcomponent"),
            ("category", String "data"),
            ("classifier", typ)] =>
               (case typ
                 of String tystr => (fldname, fldty tystr)
                  | Null => (fldname, null_ty)
                  | other => raise ERR "dest_field" "unexpected field classifier")
   | AList [("name", String fldname),
            ("kind", String "Subcomponent"),
            ("category", String "data")] => (fldname, null_ty)
   | otherwise => raise ERR "dest_field" "expected a record field";

fun recd_decl pkgName names decl =
 case decl
  of AList (("packageName", String pkg) ::
            ("name", String name_impl) ::
            ("localName", _) ::
            ("kind",String "ComponentImplementation") ::
            ("category", String "data") ::
	    ("subcomponents", List subcomps)::_)
     => if mem name_impl names andalso not(null subcomps)
        then RecdDec(dest_qid (Option.valOf (dropImpl name_impl)),
                     map dest_field subcomps)
        else raise ERR "recd_decl" "expected a record implementation"
   | AList (("packageName", String pkg) ::
            ("name", String name_impl) ::
            ("localName",_) ::
            ("kind", String "ComponentImplementation") ::
            ("category", String "data") ::
            ("extends", extension) ::
            ("subcomponents", List subcomps) :: _)
     => (case extension
          of String partial_recd_impl =>
              (case dropImpl name_impl
	        of NONE => raise ERR "recd_decl" "expected .Impl suffix"
                 | SOME name =>
               case dropImpl partial_recd_impl
                of NONE => raise ERR "recd_decl" "expected .Impl suffix"
                 | SOME orig_name =>
                     RecdDec(dest_qid name,
                         mk_extender orig_name :: map dest_field subcomps))
           | AList orig_recd_spec =>
              (case dropImpl name_impl
                of NONE => raise ERR "recd_decl" "expected .Impl suffix"
                 | SOME name => RecdDec(dest_qid name,[]))
           | other => raise ERR "recd_decl" "unexpected extension syntax")
   | other => raise ERR "recd_decl" "expected a record declaration";

fun enum_decl decl =
 case decl
  of AList (("name", String ename) ::
            ("localName",_) ::
            ("kind",String "ComponentType") ::
            ("category", String "data") ::
            ("properties",
             List [AList [("name", String "Data_Model::Data_Representation"),
                          ("kind", String "PropertyAssociation"),
                          ("value", String "Enum")],
                   AList [("name", String "Data_Model::Enumerators"),
                          ("kind", String "PropertyAssociation"),
                          ("value", List names)]]) :: _)
      => EnumDec(dest_qid ename, map dropString names)
  | other => raise ERR "enum_decl" "expected an enum declaration";

fun array_decl decl =
 case decl
  of AList (("name", String name)::
            ("localName",_) ::
            ("kind",String "ComponentType") ::
            ("category", String "data") ::
	    ("properties", List
             [AList [("name", String "Data_Model::Data_Representation"),
                     ("kind", String "PropertyAssociation"),
                     ("value", String "Array")],
              AList [("name", String "Data_Model::Base_Type"),
                     ("kind", String "PropertyAssociation"),
                     ("value", List [String baseTyName])],
              AList [("name", String "Data_Model::Dimension"),
                     ("kind", String "PropertyAssociation"),
                     ("value", List [Number (Int d)])]]) :: _)
     => let val basety = get_tyinfo [("kind", String "typeId"),
                                     ("name", String baseTyName)]
            val dim = mk_uintLit d
        in ArrayDec(dest_qid name, ArrayTy(basety,[dim]))
        end
  | other => raise ERR "array_decl" "expected an array declaration";

fun data_decl_name (AList(("packageName", String pkg) ::
                          ("name", String dname) ::
                          ("localName", _) ::
                          ("kind", String "ComponentImplementation") ::
                          ("category", String "data") :: _)) = dname

fun get_tydecl pkgName names thing =
   enum_decl thing handle HOL_ERR _ =>
   recd_decl pkgName names thing handle HOL_ERR _ =>
   array_decl thing handle HOL_ERR _ => raise ERR "get_tydecl" "";

fun get_tydecls pkgName complist =
 let val data_tynames = mapfilter data_decl_name complist
 in mapfilter (get_tydecl pkgName data_tynames) complist
 end;

fun get_port port =
 case port
  of AList [("name", String pname),
            ("kind", String conn_style),
            ("classifier", String tyqidstring),
            ("direction", String flowdir)]
      => (pname,dest_tyqid tyqidstring,flowdir,conn_style)
    | otherwise => raise ERR "get_port" "unexpected port format"

(*---------------------------------------------------------------------------*)
(* This enables "Req001_Filter" to be equal to "Req001_RadioDriver_Filter"   *)
(*---------------------------------------------------------------------------*)

fun filter_req_name_eq s1 s2 =
 let fun is_underscore ch = (ch = #"_")
     val s1_tokens = String.tokens is_underscore s1
     val s2_tokens = String.tokens is_underscore s2
 in not (null s1_tokens) andalso not(null s2_tokens) andalso
    hd s1_tokens = hd s2_tokens andalso
    last s1_tokens = last s2_tokens
 end;

fun get_guarantee (String rname) stmt =
   (case stmt
     of AList [("kind", String "GuaranteeStatement"),
               ("name", String gname),
               ("label", String gdoc),
               ("expr", gprop)]
        => if filter_req_name_eq rname gname
            then (gdoc, dest_exp gprop)
           else raise ERR "get_guarantee"
		   (String.concat["expected named guarantee ", Lib.quote rname,
				  " but encountered ", Lib.quote gname])
     | otherwise => raise ERR "get_guarantee" "unexpected input format"
   )
  | get_guarantee _ _ = raise ERR "get_guarantee"
                                "expected a String in first argument"
;

fun get_named_guarantees rnames stmts =
 let fun gtees_of rname = mapfilter (get_guarantee rname) stmts
 in
    List.concat (map gtees_of rnames)
 end

(*---------------------------------------------------------------------------*)
(* Note that a single filter can have multiple properties attached.          *)
(*---------------------------------------------------------------------------*)

fun get_annex_stmts (AList alist) =
    (case (assoc "name" alist,
           assoc "parsedAnnexLibrary" alist
            handle _ =>
           assoc "parsedAnnexSubclause" alist)
      of (String "agree", AList [("statements", List decls)]) => decls
       | otherwise => raise ERR "get_annex_stmts" "unexpected syntax")
  | get_annex_stmts otherwise = raise ERR "get_annex_stmts" "unexpected syntax"

fun get_filter decl =
 case decl
  of AList
      [("name", String fname),
       ("localName", _),
       ("kind",String "ComponentType"),
       ("category", String "thread"),
       ("features", List ports),
       ("properties",
          List [AList [("name", String pname1), _, ("value", String "FILTER")],
                AList [("name", String pname2), _, ("value", List rnames)]]),
       ("annexes", List annexen)]
    => if mem pname1 ["CASE_Properties::COMP_TYPE","CASE_Properties::Component_Type"]
          andalso
          mem pname2 ["CASE_Properties::COMP_SPEC","CASE_Properties::Component_Spec"]
       then
       let val stmts = List.concat (map get_annex_stmts annexen)
       in case get_named_guarantees rnames stmts
           of [] => raise ERR "get_filter" "no properties!"
            | glist => FilterDec(dest_qid fname, map get_port ports, glist)
       end
       else raise ERR "get_filter" "unable to scrape filter information"
   | otherwise => raise ERR "get_filter" "not a filter thread";

(*
fun get_monitor_guarantee (AList(("kind", String thing)::binds)) =
    if mem thing ["PropertyStatement", "GuaranteeStatement"] then
      (let val String gdoc = assoc "label" binds handle _ => String ""
           val expr = assoc "expr" binds
       in SOME(gdoc, dest_exp expr)
       end handle _ => NONE)
    else
      NONE
  | get_monitor_guarantee otherwise = NONE
;

fun mk_and a b = Binop(And,a,b);

fun get_monitor_guarantees _ [] = NONE
  | get_monitor_guarantees names neList =
     let val aexps = List.mapPartial get_monitor_guarantee neList
         val exps = map snd aexps
         val string_things = String.concatWith "\n\n" (map fst aexps)
     in
       SOME(string_things, end_itlist mk_and exps)
     end
*)

(*---------------------------------------------------------------------------*)
(* The temporal logic formula for a monitor is obtained by grabbing a        *)
(* collection of named GuaranteeStatements in the monitor component, and     *)
(* building a temporal formula from their conjunction. This will be massaged *)
(* into a pure temporal formula (moving AGREE boolean operations into TL) and*)
(* passed to Thomas' translator.                                             *)
(*---------------------------------------------------------------------------*)

fun get_monitor_port port =
 case port
  of AList [("name", String pname),
            ("kind", String conn_style),
            ("classifier", classif),
            ("direction", String flowdir)]
      => let val ty = (case classif
                        of Null => dest_tyqid "Bool" (* why is Null there? *)
                         | String tyqidstring => dest_tyqid tyqidstring
                         | other => raise ERR "get_monitor_port" "unexpected type")
          in (pname,ty,flowdir,conn_style)
          end
   | otherwise => raise ERR "get_monitor_port" "unexpected port format"

fun get_guar_names json =
 case json
  of List (AList [("name", String "CASE_Properties::Component_Type"), _,
                  ("value", String "MONITOR")]
           ::
           AList [("name", String "CASE_Properties::Component_Spec"), _,
                  ("value", List TL_guarantee_names)]
           :: _)
      => TL_guarantee_names
   | otherwise => raise ERR "get_guar_names" "requirement name(s) not found";

fun get_monitor (AList alist) =
     (case (assoc "name" alist,
            assoc "features" alist,
            get_guar_names(assoc "properties" alist),
            assoc "annexes" alist)
       of (String fname, List ports, monitor_names, List annexen)
          => let val qid = dest_qid fname
                 val portL = map get_monitor_port ports
                 val stmts = List.concat (map get_annex_stmts annexen)
             in
              case get_named_guarantees monitor_names stmts
               of [] => raise ERR "get_monitor" "not a monitor spec"
                | glist => MonitorDec(qid, portL, glist)
             end
       | otherwise => raise ERR "get_monitor" "unexpected syntax")
  | get_monitor otherwise = raise ERR "get_monitor" "unexpected syntax"
;

fun dest_publist plist =
 let fun dest_with ("with", List wlist) = wlist
       | dest_with other = raise ERR "dest_with" ""
     fun dest_renames ("renames", List rlist) = rlist
       | dest_renames other = raise ERR "dest_renames" ""
     fun dest_comps ("components", List clist) = clist
       | dest_comps other = raise ERR "dest_comps" ""
     fun dest_annexes ("annexes", List alist) = alist
       | dest_annexes other = raise ERR "dest_annexes" ""
 in
    (List.concat (mapfilter dest_with plist),
     List.concat (mapfilter dest_renames plist),
     List.concat (mapfilter dest_annexes plist),
     List.concat (mapfilter dest_comps plist)
     )
 end

fun get_data_model pkg =
 case pkg
  of AList [("name", String dmName),
            ("kind", String "PropertySet"),
            ("properties", proplist)] => (dmName,proplist)
  |  otherwise => raise ERR "get_data_model" "unexpected format"
;

(*
val [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
     c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28,
     c29, c30, c31, c32, c33, c34,c35] = complist;

val [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14]
   = complist;
*)

(*---------------------------------------------------------------------------*)
(* Scoping. A package has a name (pkgName), which is used to help name       *)
(* definitions arising from any annexes hanging immediately underneath it.   *)
(* A component also has a name (compName) which is used to distinguish       *)
(* definitions arising from those in any other annexes within the component, *)
(* as well as any made in top-level annexes. So we can have                  *)
(*                                                                           *)
(*  FnDec((pkgName,fnName), ...)  in the first case and                      *)
(*  FnDec((pkgName__compName,fnName), ...)  in the second case               *)
(*                                                                           *)
(* See mk_annex_defs and mk_comp_defs for details.                           *)
(*---------------------------------------------------------------------------*)

fun scrape pkg =
 case pkg
  of AList (("name", String pkgName) ::
            ("kind", String "AadlPackage") ::
            ("public", AList publist) :: _)
     => let val (withs,renamings,annexlist,complist) = dest_publist publist
            val tydecls = get_tydecls pkgName complist
            (* pkg-level annex has no features *)
	    val annex_fndecls = List.concat(mapfilter (mk_annex_defs pkgName []) annexlist)
            val comp_fndecls =  List.concat(mapfilter mk_comp_defs complist)
            val filters = mapfilter get_filter complist
            val monitors = mapfilter get_monitor complist
        in
           (pkgName,(tydecls, annex_fndecls@comp_fndecls, filters, monitors))
        end
  | otherwise => raise ERR "scrape" "unexpected format";

fun dest_with ("with", List wlist) = map dropString wlist
  | dest_with other = raise ERR "dest_with" "";

(*---------------------------------------------------------------------------*)
(* For any declaration of a partial record type there should be a later      *)
(* declaration of an extension to that type, giving the supplementary fields *)
(* to be added. We remove the first declaration and add its fields to the    *)
(* given extension fields.                                                   *)
(*---------------------------------------------------------------------------*)

fun dest_recd_dec (RecdDec args) = args
  | dest_recd_dec other = raise ERR "dest_recd_dec" ""

fun refine_recd_decs declist =
 let fun is_extensible tydec =
      case tydec
       of RecdDec (qid,flds) => exists (fn (s,ty) => eqTy(ty,null_ty)) flds
        | otherwise => false
     fun lift_extensibles (s, (tydecs,tmdecs,filters,monitors)) =
       let val (extensibles,tydecs') = partition is_extensible tydecs
       in (extensibles, (s,(tydecs',tmdecs,filters,monitors)))
       end
     val itner = map lift_extensibles declist
     val partial_decs = map dest_recd_dec (List.concat (map fst itner))
     val modlist = map snd itner
     fun refine pdec module =
       let val (oqid,oflds) = pdec
           val (pkgName, (tydecs,tmdecs,filters,monitors)) = module
           fun try_extension eflds (s,ty) =
               case assoc1 s eflds
                of NONE => (s,ty)
                 | SOME fld => fld
           fun augment tydec =
             case Lib.total dest_extender tydec
              of NONE => tydec
               | SOME (qid,base_qid,eflds) =>
                  if base_qid = oqid
                  then RecdDec(qid,map (try_extension eflds) oflds)
                 else tydec
	   val tydecs' = map augment tydecs
       in
         (pkgName, (tydecs',tmdecs,filters,monitors))
       end
     fun refine_modules pdec modlist = map (refine pdec) modlist
 in
   itlist refine_modules partial_decs modlist
 end;

fun scrape_pkgs json =
 let fun uses (A as AList (("name", String AName) ::
                           ("kind", String "AadlPackage")::
                           ("public", AList publist):: _))
              (B as AList (("name", String BName) ::
                           ("kind", String "AadlPackage") :: _)) =
          let val Auses = List.concat (mapfilter dest_with publist)
          in mem BName Auses
          end
       | uses other wise = false
     fun run pkgs =
      let val opkgs = rev (topsort uses pkgs)
          val modlist = mapfilter scrape opkgs
          val modlist' = refine_recd_decs modlist
      in
	modlist'
      end
 in
    case json
     of List pkgs => run pkgs
      | AList alist => run (dropList (assoc "modelUnits" alist))
      | otherwise => raise ERR "scrape_pkgs" "unexpected format"
 end

(*
fun uses (A as AList (("name", String AName) ::
                      ("kind", String "AadlPackage")::
                      ("public", AList publist):: _))
              (B as AList (("name", String BName) ::
                           ("kind", String "AadlPackage") :: _)) =
          let val Auses = List.concat (mapfilter dest_with publist)
          in mem BName Auses
          end
       | uses other wise = false;

val AList alist = jpkg;
val pkgs = dropList (assoc "modelUnits" alist);

val (opkgs as [pkg1, pkg2, pkg3, pkg4, pkg5, pkg6, pkg7,
               pkg8, pkg9, pkg10, pkg11,pkg12,pkg13,pkg14,pkg15]) = rev (topsort uses pkgs);

val declist = mapfilter scrape opkgs;

scrape pkg1;
scrape pkg2;
scrape pkg3;
scrape pkg4;
scrape pkg5;
scrape pkg6;
scrape pkg7;
scrape pkg8;
scrape pkg9;
scrape pkg10;
scrape pkg11;
scrape pkg12;
scrape pkg13;
scrape pkg14;
scrape pkg15;
*)

(*---------------------------------------------------------------------------*)
(* AST to AST                                                                *)
(*---------------------------------------------------------------------------*)

fun amn_ty ty =
 let open AST
 in case ty
     of BaseTy (IntTy _)     => BaseTy (IntTy (Int NONE))
      | RecdTy (qid, fldtys) => RecdTy(qid, map (I##amn_ty) fldtys)
      | ArrayTy (ty,dims)    => ArrayTy(amn_ty ty,dims)
      | other => ty
 end

fun amn_exp exp =
 let open AST
 in case exp
     of VarExp _ => exp
      | ConstExp(IntLit vk) => ConstExp(IntLit{value = #value(vk),kind=Int NONE})
      | ConstExp _ => exp
      | Unop (uop,e) => Unop(uop,amn_exp e)
      | Binop (bop,e1,e2) => Binop(bop,amn_exp e1,amn_exp e2)
      | RecdProj(e,id) => RecdProj(amn_exp e,id)
      | RecdExp(qid,fields) => RecdExp(qid,map (I##amn_exp) fields)
      | ConstrExp(qid,id,NONE) => exp
      | ConstrExp(qid,id, SOME e) => ConstrExp(qid,id, SOME (amn_exp e))
      | Fncall (qid,exps) => Fncall(qid,map amn_exp exps)
      | ArrayIndex(A,indices) => ArrayIndex(amn_exp A, map amn_exp indices)
      | ArrayExp elist => ArrayExp (map amn_exp elist)
      | Quantified(quant,qvars,exp) =>
          Quantified(quant, map (I##amn_ty) qvars, amn_exp exp)
 end

fun amn_tydec tydec =
 case tydec
  of EnumDec _ => tydec
   | RecdDec (qid,fields) => RecdDec(qid,map (I##amn_ty) fields)
   | ArrayDec (qid,ty) => ArrayDec(qid, amn_ty ty)

fun amn_tmdec tdec =
 case tdec
  of ConstDec (qid,ty,exp) => ConstDec(qid,amn_ty ty,amn_exp exp)
   | FnDec (qid,params,ty,exp) =>
       FnDec (qid,map (I##amn_ty) params, amn_ty ty, amn_exp exp)
;

fun amn_filter_dec fdec =
 let fun amn_port (s1,ty,s2,s3) = (s1,amn_ty ty,s2,s3)
     fun amn_cprop (s,e) = (s,amn_exp e)
 in case fdec
     of FilterDec(qid, ports, cprops) =>
        FilterDec(qid, map amn_port ports, map amn_cprop cprops)
 end
;

fun amn_monitor_dec fdec =
 let fun amn_port (s1,ty,s2,s3) = (s1,amn_ty ty,s2,s3)
     fun amn_cprop (s,e) = (s,amn_exp e)
 in case fdec
     of MonitorDec(qid, ports, cprops) =>
        MonitorDec(qid, map amn_port ports, map amn_cprop cprops)
 end
;

fun abstract_model_nums (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) =
  (pkgName,
    (map amn_tydec tydecs,
     map amn_tmdec tmdecs,
     map amn_filter_dec filtdecs,
     map amn_monitor_dec mondecs));

(*---------------------------------------------------------------------------*)
(* AST to HOL                                                                *)
(*---------------------------------------------------------------------------*)

fun list_mk_array_type(bty,dims) =
 let open fcpSyntax
     fun mk_arr dimty bty = mk_cart_type(bty,dimty)
 in rev_itlist mk_arr dims bty
 end

(*---------------------------------------------------------------------------*)
(* Translate AGREE types to HOL types                                        *)
(*---------------------------------------------------------------------------*)

val u8 =  ``:u8``
val u16 = ``:u16``
val u32 = ``:u32``
val u64 = ``:u64``

val i8 =  ``:i8``
val i16 = ``:i16``
val i32 = ``:i32``
val i64 = ``:i64``

fun mk_i8_uminus t =  ``i8_uminus ^t``;
fun mk_i16_uminus t = ``i16_uminus ^t``;
fun mk_i32_uminus t = ``i32_uminus ^t``;
fun mk_i64_uminus t = ``i64_uminus ^t``;

fun mk_u8_signed t  = ``u8_signed ^t``;
fun mk_u16_signed t = ``u16_signed ^t``;
fun mk_u32_signed t = ``u32_signed ^t``;
fun mk_u64_signed t = ``u64_signed ^t``;

fun mk_i8_unsigned t  = ``i8_unsigned ^t``;
fun mk_i16_unsigned t = ``i16_unsigned ^t``;
fun mk_i32_unsigned t = ``i32_unsigned ^t``;
fun mk_i64_unsigned t = ``i64_unsigned ^t``;

fun mk_i8int  t =  ``i8int ^t``;
fun mk_i16int t = ``i16int ^t``;
fun mk_i32int t = ``i32int ^t``;
fun mk_i64int t = ``i64int ^t``;
fun mk_u8num  t =  ``u8num ^t``;
fun mk_u16num t = ``u16num ^t``;
fun mk_u32num t = ``u32num ^t``;
fun mk_u64num t = ``u64num ^t``;

fun mk_u8_plus  (t1,t2) = ``u8_plus ^t1 ^t2``
fun mk_u16_plus (t1,t2) = ``u16_plus ^t1 ^t2``
fun mk_u32_plus (t1,t2) = ``u32_plus ^t1 ^t2``
fun mk_u64_plus (t1,t2) = ``u64_plus ^t1 ^t2``
fun mk_i8_plus  (t1,t2) = ``i8_plus ^t1 ^t2``
fun mk_i16_plus (t1,t2) = ``i16_plus ^t1 ^t2``
fun mk_i32_plus (t1,t2) = ``i32_plus ^t1 ^t2``
fun mk_i64_plus (t1,t2) = ``i64_plus ^t1 ^t2``

fun mk_u8_minus  (t1,t2) = ``u8_minus ^t1 ^t2``
fun mk_u16_minus (t1,t2) = ``u16_minus ^t1 ^t2``
fun mk_u32_minus (t1,t2) = ``u32_minus ^t1 ^t2``
fun mk_u64_minus (t1,t2) = ``u64_minus ^t1 ^t2``
fun mk_i8_minus  (t1,t2) = ``i8_minus ^t1 ^t2``
fun mk_i16_minus (t1,t2) = ``i16_minus ^t1 ^t2``
fun mk_i32_minus (t1,t2) = ``i32_minus ^t1 ^t2``
fun mk_i64_minus (t1,t2) = ``i64_minus ^t1 ^t2``

fun mk_u8_mult  (t1,t2) = ``u8_mult ^t1 ^t2``
fun mk_u16_mult (t1,t2) = ``u16_mult ^t1 ^t2``
fun mk_u32_mult (t1,t2) = ``u32_mult ^t1 ^t2``
fun mk_u64_mult (t1,t2) = ``u64_mult ^t1 ^t2``
fun mk_i8_mult  (t1,t2) = ``i8_mult ^t1 ^t2``
fun mk_i16_mult (t1,t2) = ``i16_mult ^t1 ^t2``
fun mk_i32_mult (t1,t2) = ``i32_mult ^t1 ^t2``
fun mk_i64_mult (t1,t2) = ``i64_mult ^t1 ^t2``

fun mk_u8_exp  (t1,t2) = ``u8_exp ^t1 ^t2``
fun mk_u16_exp (t1,t2) = ``u16_exp ^t1 ^t2``
fun mk_u32_exp (t1,t2) = ``u32_exp ^t1 ^t2``
fun mk_u64_exp (t1,t2) = ``u64_exp ^t1 ^t2``
fun mk_i8_exp  (t1,t2) = ``i8_exp ^t1 ^t2``
fun mk_i16_exp (t1,t2) = ``i16_exp ^t1 ^t2``
fun mk_i32_exp (t1,t2) = ``i32_exp ^t1 ^t2``
fun mk_i64_exp (t1,t2) = ``i64_exp ^t1 ^t2``

fun mk_u8_div  (t1,t2) = ``u8_div ^t1 ^t2``
fun mk_u16_div (t1,t2) = ``u16_div ^t1 ^t2``
fun mk_u32_div (t1,t2) = ``u32_div ^t1 ^t2``
fun mk_u64_div (t1,t2) = ``u64_div ^t1 ^t2``
fun mk_i8_div  (t1,t2) = ``i8_div ^t1 ^t2``
fun mk_i16_div (t1,t2) = ``i16_div ^t1 ^t2``
fun mk_i32_div (t1,t2) = ``i32_div ^t1 ^t2``
fun mk_i64_div (t1,t2) = ``i64_div ^t1 ^t2``

fun mk_u8_mod  (t1,t2) = ``u8_mod ^t1 ^t2``
fun mk_u16_mod (t1,t2) = ``u16_mod ^t1 ^t2``
fun mk_u32_mod (t1,t2) = ``u32_mod ^t1 ^t2``
fun mk_u64_mod (t1,t2) = ``u64_mod ^t1 ^t2``
fun mk_i8_mod  (t1,t2) = ``i8_mod ^t1 ^t2``
fun mk_i16_mod (t1,t2) = ``i16_mod ^t1 ^t2``
fun mk_i32_mod (t1,t2) = ``i32_mod ^t1 ^t2``
fun mk_i64_mod (t1,t2) = ``i64_mod ^t1 ^t2``

fun mk_u8_less  (t1,t2) = ``u8_less ^t1 ^t2``
fun mk_u16_less (t1,t2) = ``u16_less ^t1 ^t2``
fun mk_u32_less (t1,t2) = ``u32_less ^t1 ^t2``
fun mk_u64_less (t1,t2) = ``u64_less ^t1 ^t2``
fun mk_i8_less  (t1,t2) = ``i8_less ^t1 ^t2``
fun mk_i16_less (t1,t2) = ``i16_less ^t1 ^t2``
fun mk_i32_less (t1,t2) = ``i32_less ^t1 ^t2``
fun mk_i64_less (t1,t2) = ``i64_less ^t1 ^t2``

fun mk_u8_gtr  (t1,t2) = ``u8_gtr ^t1 ^t2``
fun mk_u16_gtr (t1,t2) = ``u16_gtr ^t1 ^t2``
fun mk_u32_gtr (t1,t2) = ``u32_gtr ^t1 ^t2``
fun mk_u64_gtr (t1,t2) = ``u64_gtr ^t1 ^t2``
fun mk_i8_gtr  (t1,t2) = ``i8_gtr ^t1 ^t2``
fun mk_i16_gtr (t1,t2) = ``i16_gtr ^t1 ^t2``
fun mk_i32_gtr (t1,t2) = ``i32_gtr ^t1 ^t2``
fun mk_i64_gtr (t1,t2) = ``i64_gtr ^t1 ^t2``

fun mk_u8_leq  (t1,t2) = ``u8_leq ^t1 ^t2``
fun mk_u16_leq (t1,t2) = ``u16_leq ^t1 ^t2``
fun mk_u32_leq (t1,t2) = ``u32_leq ^t1 ^t2``
fun mk_u64_leq (t1,t2) = ``u64_leq ^t1 ^t2``
fun mk_i8_leq  (t1,t2) = ``i8_leq ^t1 ^t2``
fun mk_i16_leq (t1,t2) = ``i16_leq ^t1 ^t2``
fun mk_i32_leq (t1,t2) = ``i32_leq ^t1 ^t2``
fun mk_i64_leq (t1,t2) = ``i64_leq ^t1 ^t2``

fun mk_u8_geq  (t1,t2) = ``u8_geq ^t1 ^t2``
fun mk_u16_geq (t1,t2) = ``u16_geq ^t1 ^t2``
fun mk_u32_geq (t1,t2) = ``u32_geq ^t1 ^t2``
fun mk_u64_geq (t1,t2) = ``u64_geq ^t1 ^t2``
fun mk_i8_geq  (t1,t2) = ``i8_geq ^t1 ^t2``
fun mk_i16_geq (t1,t2) = ``i16_geq ^t1 ^t2``
fun mk_i32_geq (t1,t2) = ``i32_geq ^t1 ^t2``
fun mk_i64_geq (t1,t2) = ``i64_geq ^t1 ^t2``
;

fun transTy tyEnv ty =
 let open AST
 in case ty
  of NamedTy (pkg,id) =>
      (case Lib.op_assoc1 (curry AST.eqTy) ty tyEnv
        of SOME ty' => transTy tyEnv ty'
         | NONE =>
           let val pkgName = current_theory()
           in case TypeBase.read{Thy=pkgName,Tyop=id}
               of SOME tyinfo => TypeBasePure.ty_of tyinfo
                | NONE => raise ERR "transTy"
                  ("Unable to find type "^id^" declared in theory "^Lib.quote pkg)
	   end)
   | BaseTy BoolTy   => Type.bool
   | BaseTy CharTy   => stringSyntax.char_ty
   | BaseTy StringTy => stringSyntax.string_ty
   | BaseTy RegexTy  => regexpSyntax.regexp_ty
   | BaseTy FloatTy  => raise ERR "transTy" "FloatTy: not implemented"
   | BaseTy (IntTy(Nat NONE)) => numSyntax.num
   | BaseTy (IntTy(Int NONE)) => intSyntax.int_ty
   | BaseTy (IntTy(Nat(SOME w))) =>
       if w = 8 then  u8 else
       if w = 16 then u16 else
       if w = 32 then u32 else
       if w = 64 then u64 else
       raise ERR "transTy" "unexpected size for unsigned type"
   | BaseTy (IntTy(AST.Int(SOME w))) =>
       if w = 8 then  i8 else
       if w = 16 then i16 else
       if w = 32 then i32 else
       if w = 64 then i64 else
       raise ERR "transTy" "unexpected size for signed type"
   | ArrayTy(ty,dims) =>
      let fun transDim (ConstExp(IntLit{value,kind})) =
                fcpSyntax.mk_int_numeric_type value
            | transDim (VarExp id) = mk_vartype id
            | transDim otherwise = raise ERR "transTy"
                 "array bound must be a variable or number constant"
      in
        list_mk_array_type(transTy tyEnv ty, map transDim dims)
      end
   | otherwise => raise ERR "transTy" "unknown kind of ty"
 end

fun undef s = raise ERR "transExp" ("undefined case: "^Lib.quote s);

fun lift_int {value,kind} =
 let open AST
 in case kind
     of Nat NONE => numSyntax.term_of_int value
      | Int NONE => intSyntax.term_of_int (Arbint.fromInt value)
      | Nat (SOME w) =>
        let val n = numSyntax.term_of_int value
        in
          if w = 8 then  ``mk_u8 ^n``  else
          if w = 16 then ``mk_u16 ^n`` else
          if w = 32 then ``mk_u32 ^n`` else
          if w = 64 then ``mk_u64 ^n`` else
          raise ERR "lift_int" "unexpected size for signed type"
        end
      | Int (SOME w) =>
        let val i = intSyntax.term_of_int (Arbint.fromInt value)
        in
          if w = 8 then  ``mk_i8 ^i``  else
          if w = 16 then ``mk_i16 ^i`` else
          if w = 32 then ``mk_i32 ^i`` else
          if w = 64 then ``mk_i64 ^i`` else
          raise ERR "lift_int" "unexpected size for signed type"
        end
 end;

val gdl_mk_chr =
 let open stringSyntax
 in fn tm =>
     if type_of tm = numSyntax.num
     then mk_chr tm
     else raise ERR "gdl_mk_chr" "expected arg. with type num"
 end;

val gdl_mk_ord =
 let open stringSyntax
 in fn tm => mk_ord tm
    handle HOL_ERR _ => raise ERR "gdl_mk_ord" "expected arg. with type char"
 end

fun unop (uop,e) t =
 let open AST
     val ty = type_of t
     fun lift f = f t
 in case uop
     of ChrOp  => lift gdl_mk_chr
      | OrdOp  => lift gdl_mk_ord
      | Not    => if ty = ptltlSyntax.formula then
                    ptltlSyntax.mk_Not t
                  else boolSyntax.mk_neg t
      | BitNot => undef "BitNot"
      | UMinus =>
         if ty = intSyntax.int_ty then
            lift intSyntax.mk_negated else
         if ty = i8 then
           lift mk_i8_uminus else
         if ty = i16 then
           lift mk_i16_uminus else
         if ty = i32 then
           lift mk_i32_uminus else
         if ty = i64 then
           lift mk_i64_uminus
         else raise ERR "unop (UMinus)"
                   "expected type of operand to be int\
                   \ (either fixed width or unbounded)"
      | Signed =>
          if ty = intSyntax.int_ty orelse mem ty [i8,i16,i32,i64] then
              lift combinSyntax.mk_I else
          if ty = numSyntax.num then
             lift intSyntax.mk_injected else
          if ty = u8 then
             lift mk_u8_signed else
          if ty = u16 then
           lift mk_u16_signed else
          if ty = u32 then
           lift mk_u32_signed else
          if ty = u64 then
           lift mk_u64_signed
          else raise ERR "unop (Signed)" "unexpected type of operand"
      | Unsigned =>
          if ty = numSyntax.num orelse mem ty [u8,u16,u32,u64] then
              lift combinSyntax.mk_I else
          if ty = intSyntax.int_ty then
             lift intSyntax.mk_Num else
          if ty = i8 then
             lift mk_i8_unsigned else
          if ty = i16 then
           lift mk_i16_unsigned else
          if ty = i32 then
           lift mk_i32_unsigned else
          if ty = i64 then
           lift mk_i64_unsigned
          else raise ERR "unop (Unsigned)" "unexpected type of operand"
      | Unbounded =>
          if ty = intSyntax.int_ty orelse ty = numSyntax.num
              then lift combinSyntax.mk_I else
          if ty = u8  then lift mk_u8num else
          if ty = u16 then lift mk_u16num else
          if ty = u32 then lift mk_u32num else
          if ty = u64 then lift mk_u64num else
          if ty = i8  then lift mk_i8int else
          if ty = i16 then lift mk_i16int else
          if ty = i32 then lift mk_i32int else
          if ty = i64 then lift mk_i64int
          else raise ERR "unop (Unbounded)" "expected numeric type"
      | Yesterday => lift ptltlSyntax.mk_Yester
      | ZYesterday => lift ptltlSyntax.mk_Zyester
      | Historically => lift ptltlSyntax.mk_Histor
 end;

fun binop (bop,e1,_) t1 t2 =
 let open AST ptltlSyntax
     fun lift f = f (t1,t2)
     val ty1 = type_of t1
     val ty2 = type_of t2
 in
  case bop
   of Equal =>
        if ty1=bool andalso ty2=formula then
           mk_Equiv(bool2pltl t1,t2) else
        if ty1=formula andalso ty2=bool then
           mk_Equiv(t1,bool2pltl t2) else
        if ty1=formula andalso ty2=formula then
           mk_Equiv(t1,t2)
        else
	   lift boolSyntax.mk_eq
    | NotEqual => raise ERR "binop" "NotEqual should already be translated away"
    | Or =>
       if ty1 = bool andalso ty2 = bool then
         mk_disj(t1,t2) else
       if ty1 = bool then
        mk_Or(bool2pltl t1, t2) else
       if ty2 = bool then
        mk_Or(t1, bool2pltl t2)
       else
        mk_Or(t1,t2)
    | And =>
       if ty1 = bool andalso ty2 = bool then
         mk_conj(t1,t2) else
       if ty1 = bool then
        mk_And(bool2pltl t1, t2) else
       if ty2 = bool then
        mk_And(t1, bool2pltl t2)
       else
        mk_And(t1,t2)
    | Imp =>
       if ty1 = bool andalso ty2 = bool then
         mk_imp(t1,t2) else
       if ty1 = bool then
        mk_Imp(bool2pltl t1, t2) else
       if ty2 = bool then
        mk_Imp(t1, bool2pltl t2)
       else
        mk_Imp(t1,t2)
    | Plus =>
       if ty1 = numSyntax.num then lift numSyntax.mk_plus else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_plus else
       if ty1 = u8  then lift mk_u8_plus else
       if ty1 = u16 then lift mk_u16_plus else
       if ty1 = u32 then lift mk_u32_plus else
       if ty1 = u64 then lift mk_u64_plus else
       if ty1 = i8  then lift mk_i8_plus else
       if ty1 = i16 then lift mk_i16_plus else
       if ty1 = i32 then lift mk_i32_plus else
       if ty1 = i64 then lift mk_i64_plus else
       raise ERR "Plus" "expected numeric arguments"
    | Minus =>
       if ty1 = numSyntax.num then lift numSyntax.mk_minus else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_minus else
       if ty1 = u8  then lift mk_u8_minus else
       if ty1 = u16 then lift mk_u16_minus else
       if ty1 = u32 then lift mk_u32_minus else
       if ty1 = u64 then lift mk_u64_minus else
       if ty1 = i8  then lift mk_i8_minus else
       if ty1 = i16 then lift mk_i16_minus else
       if ty1 = i32 then lift mk_i32_minus else
       if ty1 = i64 then lift mk_i64_minus else
       raise ERR "Minus" "expected numeric arguments"
    | Multiply =>
       if ty1 = numSyntax.num then lift numSyntax.mk_mult else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_mult else
       if ty1 = u8  then lift mk_u8_mult else
       if ty1 = u16 then lift mk_u16_mult else
       if ty1 = u32 then lift mk_u32_mult else
       if ty1 = u64 then lift mk_u64_mult else
       if ty1 = i8  then lift mk_i8_mult else
       if ty1 = i16 then lift mk_i16_mult else
       if ty1 = i32 then lift mk_i32_mult else
       if ty1 = i64 then lift mk_i64_mult else
       raise ERR "Multiply" "expected numeric arguments"
    | Exponent =>
       if ty1 = numSyntax.num then lift numSyntax.mk_exp else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_exp else
       if ty1 = u8  then lift mk_u8_exp else
       if ty1 = u16 then lift mk_u16_exp else
       if ty1 = u32 then lift mk_u32_exp else
       if ty1 = u64 then lift mk_u64_exp else
       if ty1 = i8  then lift mk_i8_exp else
       if ty1 = i16 then lift mk_i16_exp else
       if ty1 = i32 then lift mk_i32_exp else
       if ty1 = i64 then lift mk_i64_exp else
       raise ERR "Exponent" "expected numeric arguments"
    | Divide =>
       if ty1 = numSyntax.num then lift numSyntax.mk_div else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_div else
       if ty1 = u8  then lift mk_u8_div else
       if ty1 = u16 then lift mk_u16_div else
       if ty1 = u32 then lift mk_u32_div else
       if ty1 = u64 then lift mk_u64_div else
       if ty1 = i8  then lift mk_i8_div else
       if ty1 = i16 then lift mk_i16_div else
       if ty1 = i32 then lift mk_i32_div else
       if ty1 = i64 then lift mk_i64_div else
       raise ERR "Divide" "expected numeric arguments"
    | Modulo =>
       if ty1 = numSyntax.num then lift numSyntax.mk_mod else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_mod else
       if ty1 = u8  then lift mk_u8_mod else
       if ty1 = u16 then lift mk_u16_mod else
       if ty1 = u32 then lift mk_u32_mod else
       if ty1 = u64 then lift mk_u64_mod else
       if ty1 = i8  then lift mk_i8_mod else
       if ty1 = i16 then lift mk_i16_mod else
       if ty1 = i32 then lift mk_i32_mod else
       if ty1 = i64 then lift mk_i64_mod else
       raise ERR "Modulo" "expected numeric arguments"
    | Less =>
       if ty1 = numSyntax.num then lift numSyntax.mk_less else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_less else
       if ty1 = u8  then lift mk_u8_less else
       if ty1 = u16 then lift mk_u16_less else
       if ty1 = u32 then lift mk_u32_less else
       if ty1 = u64 then lift mk_u64_less else
       if ty1 = i8  then lift mk_i8_less else
       if ty1 = i16 then lift mk_i16_less else
       if ty1 = i32 then lift mk_i32_less else
       if ty1 = i64 then lift mk_i64_less else
       raise ERR "Less" "expected numeric arguments"
    | Greater =>
       if ty1 = numSyntax.num then lift numSyntax.mk_greater else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_great else
       if ty1 = u8  then lift mk_u8_gtr else
       if ty1 = u16 then lift mk_u16_gtr else
       if ty1 = u32 then lift mk_u32_gtr else
       if ty1 = u64 then lift mk_u64_gtr else
       if ty1 = i8  then lift mk_i8_gtr else
       if ty1 = i16 then lift mk_i16_gtr else
       if ty1 = i32 then lift mk_i32_gtr else
       if ty1 = i64 then lift mk_i64_gtr else
       raise ERR "Modulo" "expected numeric arguments"
    | LessEqual =>
       if ty1 = numSyntax.num then lift numSyntax.mk_leq else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_leq else
       if ty1 = u8  then lift mk_u8_leq else
       if ty1 = u16 then lift mk_u16_leq else
       if ty1 = u32 then lift mk_u32_leq else
       if ty1 = u64 then lift mk_u64_leq else
       if ty1 = i8  then lift mk_i8_leq else
       if ty1 = i16 then lift mk_i16_leq else
       if ty1 = i32 then lift mk_i32_leq else
       if ty1 = i64 then lift mk_i64_leq else
       raise ERR "LessEqual" "expected numeric arguments"
    | GreaterEqual =>
       if ty1 = numSyntax.num then lift numSyntax.mk_geq else
       if ty1 = intSyntax.int_ty then lift intSyntax.mk_geq else
       if ty1 = u8  then lift mk_u8_geq else
       if ty1 = u16 then lift mk_u16_geq else
       if ty1 = u32 then lift mk_u32_geq else
       if ty1 = u64 then lift mk_u64_geq else
       if ty1 = i8  then lift mk_i8_geq else
       if ty1 = i16 then lift mk_i16_geq else
       if ty1 = i32 then lift mk_i32_geq else
       if ty1 = i64 then lift mk_i64_geq else
       raise ERR "GreaterEqual" "expected numeric arguments"
    | Since => undef "Since"
    | Trigger => undef "Trigger"
    | RegexMatch => lift regexpSyntax.mk_regexp_matcher
    | CastWidth     => undef "CastWidth"
    | BitOr         => undef "BitOr"
    | BitAnd        => undef "BitAnd"
    | BitXOR        => undef "BitXOR"
    | LogicalLShift => undef "LogicalLShift"
    | LogicalRShift => undef "LogicalRShift"
    | ArithmeticRShift => undef "ArithmeticRShift"
 end;

fun mk_constr_const currentpkg (pkg,ty) cname =
    case Term.decls cname
     of [] => raise ERR "mk_constr_const"
              (Lib.quote cname^" not a declared constant")
      | [c] => c
      | more_than_one =>
         (HOL_MESG ("mk_constr_const: multiple declarations for "
                    ^Lib.quote cname)
         ; hd more_than_one);

fun organize_fields progfields tyinfo_fields =
 let fun reorg [] _ = []
       | reorg ((s,_)::t) list =
          let val (x,list') = Lib.pluck (equal s o fst) list
          in x::reorg t list'
          end
 in
  reorg progfields tyinfo_fields
 end;

fun fromMLbool b = if b then T else F;


(*---------------------------------------------------------------------------*)
(* ptltl formulas are handled separately, even the boolean structure.        *)
(*---------------------------------------------------------------------------*)

fun trans_ptLTL pkgName varE formula =
    case formula
     of Fncall(("AGREE_PLTL","Yesterday"),[e]) =>
          ptltlSyntax.mk_Yester(trans_ptLTL pkgName varE e)
      | Fncall(("AGREE_PLTL","Zyesterday"),[e]) =>
         ptltlSyntax.mk_Zyester(trans_ptLTL pkgName varE e)
      | Fncall(("AGREE_PLTL","Historically"),[e]) =>
         ptltlSyntax.mk_Histor(trans_ptLTL pkgName varE e)
      | Fncall(("AGREE_PLTL","Since"),[e1,e2]) =>
         ptltlSyntax.mk_Since
              (trans_ptLTL pkgName varE e1,
               trans_ptLTL pkgName varE e2)
      | Fncall(("AGREE_PLTL","Trigger"),[e1,e2]) =>
         ptltlSyntax.mk_Trigger
              (trans_ptLTL pkgName varE e1,
               trans_ptLTL pkgName varE e2)
      | Fncall(("AGREE_PLTL",s),_) =>
        raise ERR "trans_ptLTL" ("unknown AGREE_PTLTL operator: "^Lib.quote s)
      | VarExp id => ptltlSyntax.mk_Eid (stringSyntax.fromMLstring id)  (* temporary *)
      | ConstExp (BoolLit b) => ptltlSyntax.mk_Prim (fromMLbool b)
      | Unop(Not,e) => ptltlSyntax.mk_Not(trans_ptLTL pkgName varE e)
      | Binop(Equal,e1,e2) =>
         ptltlSyntax.mk_Equiv
              (trans_ptLTL pkgName varE e1,
               trans_ptLTL pkgName varE e2)
      | Binop(Imp,e1,e2) =>
         ptltlSyntax.mk_Imp
              (trans_ptLTL pkgName varE e1,
               trans_ptLTL pkgName varE e2)
      | Binop(Or,e1,e2) =>
         ptltlSyntax.mk_Or
              (trans_ptLTL pkgName varE e1,
               trans_ptLTL pkgName varE e2)
      | Binop(And,e1,e2) =>
         ptltlSyntax.mk_And
              (trans_ptLTL pkgName varE e1,
               trans_ptLTL pkgName varE e2)
      | otherwise =>
        raise ERR "trans_ptLTL" "unknown syntax inside AGREE_PTLTL operator"

datatype expect = Unknown | Expected of hol_type;

fun mk_id varE ety id =
 case assoc1 id varE
  of SOME (_,v) => v
   | NONE =>
 case ety
  of Expected ty => (mk_const(id,ty) handle HOL_ERR _ => mk_var(id,ty))
   | Unknown =>
     case Term.decls id
      of [const] => const
       | [] => raise ERR "transExp" ("unknown free variable: "^Lib.quote id)
       | otherwise => raise ERR "transExp"
           ("multiple choices for resolving free variable: "^Lib.quote id);

fun transExp pkgName varE ety exp =
  case exp
   of VarExp id => mk_id varE ety id
    | ConstExp (BoolLit b)   => boolSyntax.lift_bool ind b
    | ConstExp (CharLit c)   => stringSyntax.lift_char ind c
    | ConstExp (StringLit s) => stringSyntax.lift_string ind s
    | ConstExp (IntLit vk)   => lift_int vk
    | ConstExp (RegexLit r)  => undef "RegexLit"  (* lift_regex r *)
    | ConstExp (FloatLit f)  => undef "FloatLit"
    | Unop (node as (uop,e)) => unop node (transExp pkgName varE Unknown e)
    | Binop (NotEqual,e1,e2) =>
        transExp pkgName varE (Expected bool) (Unop(Not,Binop(Equal,e1,e2)))
    | Binop (node as (_,e1,e2)) =>
         let val t1 = transExp pkgName varE Unknown e1
             val t2 = transExp pkgName varE Unknown e2
         in binop node t1 t2
         end
    | RecdProj(e,id) =>   (* record projection *)
         let val t = transExp pkgName varE Unknown e
             val recdty = type_of t
             val projName = fst(dest_type recdty)^"_"^id
             val fld_proj = prim_mk_const{Name=projName,Thy=pkgName}
         in
            mk_comb(fld_proj,t)
         end
    | RecdExp(qid,fields) =>
      let val rty = mk_type (snd qid,[])
      in case TypeBase.fetch rty
          of NONE => raise ERR "transExp"
                     ("failed attempt to construct record with type "^Lib.quote (snd qid))
	   | SOME rtyinfo =>
             let val fieldnames = map fst fields
                 val tyfields = TypeBasePure.fields_of rtyinfo
                 val tyfields' = organize_fields fields tyfields
                 val expectedtys = map (Expected o #ty o snd) tyfields'
                 val field_exps = map2 (transExp pkgName varE) expectedtys (map snd fields)
             in TypeBase.mk_record (rty,zip fieldnames field_exps)
             end
      end
    | ConstrExp(qid,id, NONE) => mk_constr_const pkgName qid id
    | ConstrExp(qid,id, SOME e) => undef "ConstrExp with arg"
    | Fncall ((_,"IfThenElse"),[e1,e2,e3]) =>
       let open ptltlSyntax
           val a = transExp pkgName varE (Expected bool) e1
           val b = transExp pkgName varE ety e2
           val c = transExp pkgName varE ety e3
           val bty = type_of b
           val cty = type_of c
       in
         (mk_pltl_cond(bool2pltl a, bool2pltl b, bool2pltl c)
          handle HOL_ERR _ =>
          mk_cond(a,b,c))
       end
    | Fncall ((_,"Array_Forall"),[VarExp bv,e2,e3]) =>
      let open fcpSyntax
	  val A = transExp pkgName varE Unknown e2
          val (elty,dimty) = dest_cart_type (type_of A)
          val v = mk_var(bv,elty)
          val varE' = (bv,v)::varE
          val Pbody = transExp pkgName varE' (Expected bool) e3
          val fcp_every_tm' = inst [alpha |-> dimty, beta |-> elty] fcp_every_tm
      in list_mk_comb(fcp_every_tm',[mk_abs(v,Pbody), A])
      end
    | Fncall ((_,"Array_Forall"),_) => raise ERR "transExp" "Array_Forall: unexpected syntax"
    | Fncall ((_,"Array_Exists"),[VarExp bv,e2,e3]) =>
      let open fcpSyntax
	  val A = transExp pkgName varE Unknown e2
          val (elty,dimty) = dest_cart_type (type_of A)
          val v = mk_var(bv,elty)
          val varE' = (bv,v)::varE
          val Pbody = transExp pkgName varE' (Expected bool) e3
          val fcp_exists_tm' = inst [alpha |-> dimty, beta |-> elty] fcp_exists_tm
      in list_mk_comb(fcp_exists_tm',[mk_abs(v,Pbody), A])
      end
    | Fncall ((_,"Array_Exists"),_) => raise ERR "transExp" "Array_Exists: unexpected syntax"
    | Fncall ((_,"Event"),_) => raise ERR "transExp" "Event"
    | Fncall (("AGREE_PLTL",_),args) => trans_ptLTL pkgName varE exp
    | Fncall ((thyname,cname),expl) =>
       (let val thyname' = if thyname = "" then pkgName else thyname
            val c = prim_mk_const{Thy=thyname',Name=cname}
        in list_mk_comb(c,map (transExp pkgName varE Unknown) expl)
        end handle e as HOL_ERR _ => raise wrap_exn "" "transExp" e)
    | ConstExp (IdConst qid) => undef "ConstExp: IdConst"
    | ArrayIndex(A,indices) => undef "ArrayIndex"
    | ArrayExp elist => undef "ArrayExp"
    | Quantified(quant,qvars,exp) => undef "Quantified"

(* TOPSORT GUNK : second thing mentions the first *)

fun called_by (FnDec((_,id),_,_,_)) (FnDec(_,_,_,exp)) =
      mem id (map snd (AST.exp_calls [exp] []))
  | called_by (FnDec((_,id),_,_,_)) (ConstDec (_,_,exp)) =
      mem id (map snd (AST.exp_calls [exp] []))
  | called_by (ConstDec((_,id),_,_)) (FnDec (_,_,_,exp)) = mem id (expIds exp [])
  | called_by (ConstDec((_,id),_,_)) (ConstDec (_,_,exp)) = mem id (expIds exp []);

fun declare_hol_enum ((pkgName,ename),cnames) =
    if Lib.can mk_type (ename,[])
    then stdErr_print ("Enumeration "^Lib.quote ename^" has been predeclared\n")
    else
    let open Datatype ParseDatatype
        val _ = astHol_datatype [(ename,Constructors (map (C pair []) cnames))]
        val ety = mk_type(ename,[])
        val clist = TypeBase.constructors_of ety
        val ety_encoding = Enum_Encode.define_enum_encoding ety
    in
	Enum_Encode.insert_enum_type(ety,clist,ety_encoding);
        stdErr_print ("Declared enumeration "^Lib.quote ename^"\n")
    end;

(*---------------------------------------------------------------------------*)
(* Puts type alpha in place of null. Morally, I should put a different type  *)
(* variable at each occurrence, but that can come later. There is also an    *)
(* assumption that all declarations of records, enums, etc, are taking place *)
(* in the current theory, so the pkgName is ignored.                         *)
(*---------------------------------------------------------------------------*)

fun declare_hol_record tyEnv ((_,rname),fields) =
    let open Datatype ParseDatatype
        fun ty2pretype ty =
	    case ty
	     of NamedTy ("","null") => dVartype "'a"
              | NamedTy ("Base_Types",_) => dAQ (transTy tyEnv ty)
(*              | NamedTy qid =>
                 (case op_assoc1 (curry tyEq) ty tyEnv
                   of SOME ty' => dAQ (ty'
                   |   => dTyop{Tyop=s,Thy=NONE,Args=[]}
*)
              | ty => dAQ (transTy tyEnv ty)
        fun mk_field(s,ty) = (s,ty2pretype ty)
    in
      astHol_datatype [(rname,Record (map mk_field fields))]
    ; stdErr_print ("Declared record "^Lib.quote rname^"\n")
    end

(*
fun declare_hol_array (name, ArrayTy(bty,[dim])) =
    let val dim_tm = transExp (current_theory()) [] Unknown dim
        val base_ty = transTy bty
        open Datatype ParseDatatype
    in
	astHol_datatype
         [(name, Record [("size", dAQ numSyntax.num),
                        ("elts", dAQ (listSyntax.mk_list_type base_ty))])]
      ;
        stdErr_print ("Declared array "^Lib.quote name^"\n")
    end
  | declare_hol_array otherwise = raise ERR "declare_hol_array" "unexpected syntax";
*)

(*---------------------------------------------------------------------------*)
(* Array decs get added to a tyEnv (really just an arrayEnv for now). Hack:  *)
(* the parser does not alway give a package name to named types, and this    *)
(* matters when mapping named types to array types, so we just add the       *)
(* anonymous pkgName qid to the domain of the env.                           *)
(*---------------------------------------------------------------------------*)

fun declare_hol_type (EnumDec enum) tyEnv = (declare_hol_enum enum; tyEnv)
  | declare_hol_type (RecdDec recd) tyEnv = (declare_hol_record tyEnv recd; tyEnv)
  | declare_hol_type (ArrayDec (qid,ty)) tyEnv =
      let val ty' = substTyTy (map op|-> tyEnv) ty
          val anon_pkg_qid = ("",snd qid)
      in (NamedTy qid, ty') :: (NamedTy anon_pkg_qid,ty') :: tyEnv
      end

(*---------------------------------------------------------------------------*)
(* Includes declaration of HOL constants                                     *)
(*---------------------------------------------------------------------------*)

fun declare_hol_fn tyEnv ((_,name),params,ty,body) =
    let fun mk_hol_param (s,ty) = (s, mk_var(s,transTy tyEnv ty))
        val varE = map mk_hol_param params
        val param_vars = map snd varE
        val ety = Expected (transTy tyEnv ty)
        val pkgName = current_theory()
        val body_tm = transExp pkgName varE ety body
        val def_var = mk_var(name,
                       list_mk_fun (map type_of param_vars, type_of body_tm))
        val def_tm = mk_eq(list_mk_comb(def_var,param_vars),body_tm)
	val def = PURE_REWRITE_RULE [GSYM CONJ_ASSOC]
                           (new_definition(name^"_def", def_tm))
    in
       stdErr_print ("Defined function "^Lib.quote name^"\n")
     ; def
    end

fun declare_hol_term tyEnv (ConstDec (qid,ty,exp)) =
        declare_hol_fn tyEnv (qid,[],ty,exp)
  | declare_hol_term tyEnv (FnDec fninfo) = declare_hol_fn tyEnv fninfo;

fun mk_filter_spec (thyName,tyEnv,fn_defs)
		   (FilterDec ((pkgName,fname), ports, cprops)) =
    let val outport = Lib.first (fn (_,_,dir,_) => (dir = "out")) ports
	val inport = Lib.first (fn (_,_,dir,_) => (dir = "in")) ports
        val iname = #1 inport
        val oname = #1 outport
        val ty = transTy tyEnv (#2 outport)
        val varIn = (iname,mk_var(iname,ty))
        val varOut = (oname,mk_var(oname,ty))
        val prop = end_itlist mk_and (map #2 cprops)
        val spec = transExp thyName [varIn,varOut] (Expected bool) prop
        val wf_message_thm = PURE_REWRITE_CONV fn_defs spec
        val array_forall_expanded =
             wf_message_thm
               |> SIMP_RULE (srw_ss()) [splatTheory.fcp_every_thm]
               |> SIMP_RULE arith_ss
                    [arithmeticTheory.BOUNDED_FORALL_THM,
                     GSYM CONJ_ASSOC,GSYM DISJ_ASSOC]
        val full_name = String.concatWith "__" [pkgName,fname]
    in
       ((pkgName,fname),
        save_thm (full_name,array_forall_expanded))
    end
    handle e => raise wrap_exn "AADL" "mk_filter_spec" e;
;
fun mk_monitor_spec (thyName,tyEnv,fn_defs)
                    (MonitorDec ((pkgName,fname), ports, cprops)) =
    let val outport = Lib.first (fn (_,_,dir,_) => (dir = "out")) ports
	val inport = Lib.first (fn (_,_,dir,_) => (dir = "in")) ports
        val iname = #1 inport
        val oname = #1 outport
        val ty = transTy tyEnv (#2 outport)
        val varIn = (iname,mk_var(iname,ty))
        val varOut = (oname,mk_var(oname,ty))
        val prop = end_itlist mk_and (map #2 cprops)
        val spec = transExp thyName [varIn,varOut] (Expected bool) prop
        val spec_thm = QCONV (PURE_REWRITE_CONV fn_defs) spec
        val spec_def = TotalDefn.Define
                        `^(mk_eq(mk_var(fname^"_MONITOR_SPEC",ptltlSyntax.formula), spec))’
(*        val array_forall_expanded =
             spec_thm
(*               |> SIMP_RULE (srw_ss()) [splatTheory.fcp_every_thm] *)
               |> SIMP_RULE arith_ss
                    [arithmeticTheory.BOUNDED_FORALL_THM,
                     GSYM CONJ_ASSOC,GSYM DISJ_ASSOC]
*)
        val full_name = String.concatWith "__" [pkgName,fname]
    in
       ((pkgName,fname),spec_def)
    end
    handle e => raise wrap_exn "AADL" "mk_monitor_spec" e;
;

val is_datatype =
    same_const (prim_mk_const{Thy="bool",Name="DATATYPE"}) o rator o concl;


val paramsEq =
    Lib.all2 (fn (id1:string,ty1) => fn (id2,ty2) => id1 = id2 andalso eqTy(ty1,ty2));

fun same_tmdec tmdec1 tmdec2 =
  case (tmdec1,tmdec2)
   of (ConstDec(qid1,ty1,exp1), ConstDec(qid2,ty2,exp2))
       => qid1 = qid2 andalso AST.eqTy(ty1,ty2) andalso AST.eqExp(exp1,exp2)
    | (FnDec(qid1,params1,ty1,exp1), FnDec(qid2,params2,ty2,exp2))
       => qid1 = qid2 andalso paramsEq params1 params2 andalso
          AST.eqTy(ty1,ty2) andalso AST.eqExp(exp1,exp2)
    | otherwise => false
;

fun mk_pkg_defs thyName tyEnv (pkgName,(tydecs,tmdecs,filters,monitors)) =
    let val tyEnv' = rev_itlist declare_hol_type tydecs tyEnv
        val tydecls = List.filter (is_datatype o snd) (theorems thyName)
        val tmdecs' = op_mk_set same_tmdec tmdecs
        val tmdecs'' = topsort called_by tmdecs'
        val fn_defs = map (declare_hol_term tyEnv') tmdecs''
        val info = (thyName,tyEnv',fn_defs)
        val filter_specs = map (mk_filter_spec info) filters
        val monitor_specs = map (mk_monitor_spec info) monitors
    in
      (tyEnv', map snd tydecls, fn_defs, filter_specs, monitor_specs)
    end;

fun pkgs2hol thyName list =
 let fun iter [] acc = acc
       | iter (pkg::t) (tyE,tyD,tmD,fS,mS) =
          let val (tyEnv',tydefs,fndefs,filtspecs,monspecs)
                = mk_pkg_defs thyName tyE pkg
          in iter t (tyEnv', tydefs@tyD, fndefs@tmD, filtspecs@fS, monspecs@mS)
          end
 in iter list ([],[],[],[],[])
 end;

end
