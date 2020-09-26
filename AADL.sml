(*---------------------------------------------------------------------------*)
(* Translation from AADL (in Json syntax) to an AST form, and then to HOL    *)
(*---------------------------------------------------------------------------*)

structure AADL :> AADL =
struct

open Lib Feedback HolKernel boolLib bossLib MiscLib AST Json;

local open
   stringLib stringSimps fcpLib realLib
   regexpLib regexpSyntax aadl_basetypesTheory ptltlSyntax
in end;

 type qid = string * string;
 type ty = AST.ty;
 type exp = AST.exp;
 type tyEnv = (ty * ty) list;

 datatype tydec
    = EnumDec of qid * string list
    | RecdDec of qid * (string * ty) list
    | ArrayDec of qid * ty
    | UnionDec of qid * (string * ty) list;

 datatype tmdec
    = ConstDec of qid * ty * exp
    | FnDec of qid * (string * ty) list * ty * exp;

 datatype filter
    = FilterDec   (* (name,ports,props,bufsize) *)
        of qid *
           (string * ty * string * string) list *
           (string * exp) list

 datatype monitor  (*  (name,ports,latched, props)  *)
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

val ERR = Feedback.mk_HOL_ERR "AADL";

(*---------------------------------------------------------------------------*)
(* Json syntax ops                                                           *)
(*---------------------------------------------------------------------------*)

fun dropBool (Boolean b) = b
  | dropBool otherwise = raise ERR "dropBool" "not a json Boolean application";

fun dropInt (Number (Int i)) = i
  | dropInt otherwise = raise ERR "dropInt" "not a json integer";

fun dropString (String s) = s
  | dropString otherwise = raise ERR "dropString" "not a json String application";

fun dropList (List list) = list
  | dropList otherwise = raise ERR "dropList" "not a json List application";

fun dropAList (AList list) = list
  | dropAList otherwise = raise ERR "dropAList" "not a json AList application";

fun name_of (AList alist) = assoc "name" alist;
fun kind_of (AList alist) = assoc "kind" alist;
fun classifier_of (AList alist) = assoc "classifier" alist;
fun features_of (AList alist) = assoc "features" alist;
fun properties_of (AList alist) = assoc "properties" alist;
fun annexes_of (AList alist) = assoc "annexes" alist;
fun value_of (AList alist) = assoc "value" alist;
fun classifier_of (AList alist) = assoc "classifier" alist;
fun dimensions_of (AList alist) = assoc "dimensions" alist;
fun subcomponents_of (AList alist) = assoc "subcomponents" alist;
fun label_of (AList alist) = dropString (assoc "label" alist);
fun expr_of (AList alist) = assoc "expr" alist;

fun ty_occurs ty1 ty2 =
 case ty2
  of RecdTy (_,flds) => exists (fn (id,fty) => ty_occurs ty1 fty) flds
   | ArrayTy (ty,_)  => ty_occurs ty1 ty
   | otherwise       => eqTy(ty1,ty2)

(*---------------------------------------------------------------------------*)
(* Json to AST (types, expressions, function definitions, and filters)       *)
(*---------------------------------------------------------------------------*)

fun dest_qid s =
 let val chunks = String.tokens (fn c => equal #"." c orelse equal #":" c) s
 in case Lib.front_last chunks
     of ([a,b],"Impl") => (a,b)
      | ([a],"Impl") => ("",a)
      | ([],"Impl") => raise ERR "dest_qid" "unexpected format"
      | ([a,b],"i") => (a,b)
      | ([a],"i") => ("",a)
      | ([],"i") => raise ERR "dest_qid" "unexpected format"
      | ([a],b) => (a,b)
      | ([],b)  => ("",b)
      | otherwise => raise ERR "dest_qid" "unexpected format"
 end;

val qid_compare = Lib.pair_compare (String.compare,String.compare);

fun dec_qid (EnumDec (qid,_)) = qid
  | dec_qid (RecdDec (qid,_)) = qid
  | dec_qid (ArrayDec(qid,_)) = qid
  | dec_qid (UnionDec(qid,_)) = qid;

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

   | (_,"int8")        => BaseTy(IntTy(AST.Int (SOME 8)))
   | (_,"int16")       => BaseTy(IntTy(AST.Int (SOME 16)))
   | (_,"int32")       => BaseTy(IntTy(AST.Int (SOME 32)))
   | (_,"int64")       => BaseTy(IntTy(AST.Int (SOME 64)))

   | (_,"Bool")    => BaseTy BoolTy
   | (_,"Boolean") => BaseTy BoolTy
   | (_,"String")  => BaseTy StringTy
   | (_,"Char")    => BaseTy CharTy
   | (_,"Float_32") => BaseTy FloatTy
   | (_,"Float_64") => BaseTy DoubleTy
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
   | [("kind", String "PrimType"), ("primType", String "real")]
     => BaseTy FloatTy
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
         | "<=>" => Equal
         | "and" => And
         | "or"  => Or
         | "->"  => Fby
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

fun mk_floatLit r = ConstExp(FloatLit r)

fun mk_float str =
  case Real.fromString str
   of SOME r => mk_floatLit r
    | NONE =>
       raise ERR "mk_float" ("expected a floating-point constant, but got: "^Lib.quote str)

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

fun dropImpl s =
     case String.tokens (equal #".") s
      of [x,"i"] => SOME x
       | [x,"Impl"] => SOME x
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
  | AList [("kind", String "RealLitExpr"), ("value", String realstr)]
       => mk_float realstr
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
   | AList [("kind", String "SelectionExpr"), ("target", lval), ("field", String fname)]
       => RecdProj (dest_exp lval, fname)
   | AList [("kind", String "ArraySubExpr"), ("array", aexp), ("index", iexp)]
       => ArrayIndex(dest_exp aexp, [dest_exp iexp])
   | AList [("kind", String "CallExpr"),
            ("function", AList alist),
            ("args", List args)]
       => let val pkg = dropString (assoc "packageName" alist) handle _ => ""
              val fname = dropString (assoc "name" alist) handle _ => ""
          in mk_fncall(pkg,fname,map dest_exp args)
          end
   | AList [("kind", String "AadlEnumerator"),
            ("type", AList tyinfo),
            ("value", String constrname)]
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
   | AList [("kind", String "PreExpr"), ("expr", e)]
       => mk_fncall("","Pre",[dest_exp e])
   | other => raise ERR "dest_exp" "unexpected expression form"
and
mk_field (fname,e) = (fname, dest_exp e);

fun dest_param param =
 case param
  of AList [("name", String pname), ("type", ty)] => (pname,dest_ty ty)
   | otherwise => raise ERR "dest_param" "unexpected input";

fun mk_fun_def compName json =
 case json
  of AList (("kind", String "FnDef")::binds) =>
      (case (assoc "name" binds,
             assoc "args" binds,
             assoc "type" binds,
             assoc "expr" binds)
       of (String fname, List params, ty, body) =>
           FnDec((compName,fname), map dest_param params, dest_ty ty, dest_exp body)
       |  otherwise => raise ERR "mk_fun_def" "unexpected input")
   | otherwise => raise ERR "mk_fun_def" "unexpected input";

fun mk_const_def compName json =
 case json
  of AList [("kind", String "ConstStatement"),
            ("name", String cname),
            ("type", ty),
            ("expr", body)] => ConstDec((compName,cname), dest_ty ty, dest_exp body)
  |  otherwise => raise ERR "mk_const_def" "unexpected input";

fun dest_feature (AList alist) =
    (dropString (assoc "name" alist),
     (dest_tyqid o dropString) (assoc "classifier" alist));

fun mk_property_stmt_def compName features (AList alist) =
     (case (assoc "kind" alist,
            assoc "name" alist,
	    assoc "expr" alist)
       of (String kname, String fname, e)
          => if mem kname ["PropertyStatement","GuaranteeStatement"] then
             let val boolTy = BaseTy BoolTy
                 val exp = dest_exp e
                 val compParams = map dest_feature features
                 val free_names = expFrees [] exp
                 val params = filter (fn cp => mem (fst cp) free_names) compParams
             in
                FnDec((compName,fname), params, boolTy, exp)
             end
             else raise ERR "mk_property_def" "expected Property or Guarantee statement"
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

fun mk_def compName features json =
  mk_const_def compName json    handle HOL_ERR _ =>
  mk_fun_def compName json      handle HOL_ERR _ =>
  mk_property_stmt_def compName features json handle HOL_ERR _ =>
  mk_eq_stmt_def compName features json handle HOL_ERR _ =>
  raise ERR "mk_def" "unexpected syntax";

fun get_annex_stmts (AList alist) =
    (case (assoc "name" alist,
           assoc "parsedAnnexLibrary" alist
            handle _ =>
           assoc "parsedAnnexSubclause" alist)
      of (String "agree", AList [("statements", List decls)]) => decls
       | otherwise => raise ERR "get_annex_stmts" "unexpected syntax")
  | get_annex_stmts otherwise = raise ERR "get_annex_stmts" "unexpected syntax"

fun mk_annex_defs compName features annex =
  mapfilter (mk_def compName features) (get_annex_stmts annex)

(*
val stmts = get_annex_stmts annex;
val [stmt1, stmt2, stmt3, stmt4, stmt5, stmt6, stmt7, stmt8, stmt9, stmt10,
     stmt11, stmt12, stmt13, stmt14, stmt15, stmt16, stmt17, stmt18, stmt19, stmt20,
     stmt21, stmt22, stmt23, stmt24, stmt25, stmt26, stmt27, stmt28, stmt29] = stmts;

mk_def pkgName features stmt1;
mk_def pkgName features stmt2;
mk_def pkgName features stmt3;
mk_def pkgName features stmt4;
mk_def pkgName features stmt5;
mk_def pkgName features stmt6;
mk_def pkgName features stmt7;
mk_def pkgName features stmt8;
mk_def pkgName features stmt9;
mk_def pkgName features stmt10;

mk_def pkgName features stmt11;
mk_def pkgName features stmt12;
mk_def pkgName features stmt13;
mk_def pkgName features stmt14;
mk_def pkgName features stmt15;
mk_def pkgName features stmt16;
mk_def pkgName features stmt17;
mk_def pkgName features stmt18;
mk_def pkgName features stmt19;
mk_def pkgName features stmt20;

mk_def pkgName features stmt21;
mk_def pkgName features stmt22;
mk_def pkgName features stmt23;
mk_def pkgName features stmt24;
mk_def pkgName features stmt25;
mk_def pkgName features stmt26;
mk_def pkgName features stmt27;
mk_def pkgName features stmt28;
mk_def pkgName features stmt29;


mk_def pkgName features stmt30;
mk_def pkgName features stmt31;
mk_def pkgName features stmt32;
mk_def pkgName features stmt33;
mk_def pkgName features stmt34;
mk_def pkgName features stmt35;
mk_def pkgName features stmt36;
mk_def pkgName features stmt37;
mk_def pkgName features stmt38;
mk_def pkgName features stmt39;

mk_def pkgName features stmt40;
mk_def pkgName features stmt41;

*)


(*---------------------------------------------------------------------------*)
(* compName is of the form "<pkgName>::<actual_compName>", so futz around to *)
(* get the name into the form "<pkgName>__<actual_compName".                 *)
(*---------------------------------------------------------------------------*)

val futz = String.map (fn ch => if ch = #":" then #"_" else ch)

fun mk_comp_defs comp =  (* annex inside package component *)
 case comp
  of AList alist =>
     let val compName = dropString (assoc "name" alist) handle _ => ""
         val compName' = futz compName
         val features = dropList (assoc "features" alist) handle _ => []
         val annexes = dropList (assoc "annexes" alist)
     in List.concat(map (mk_annex_defs compName' features) annexes)
     end
   | otherwise => raise ERR "mk_comp_defs" "unexpected annex format"
;

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
fun dest_extender (RecdDec (qid, ("--Extends--", NamedTy base_qid)::t)) =
      (qid,base_qid,t)
  | dest_extender otherwise = raise ERR "dest_extender" "";


fun dest_field subcomp =
 let fun mk_ty typ =
        case typ
         of String tystr => fldty tystr
          | Null => null_ty
          | other => raise ERR "dest_field" "unexpected field classifier"
     fun mk_dim [dim] = mk_intLit (dropInt (value_of dim))
       | mk_dim otherwise = raise ERR "dest_field (mk_dim)"
                "unexpected concrete array dimension"
     fun is_array_spec spec = (* decoding arb-dim array spec *)
      ("Array" = dropString (value_of (value_of (hd (dropList spec)))))
      handle _ => false
 in
 case subcomp
  of AList (("name", String fldname) ::
            ("kind", String "Subcomponent") ::
            ("category", String "data") :: tail)
     => if null tail then
          (fldname, null_ty)
        else
         (case (Option.map snd (assoc1 "classifier" tail),
                Option.map (dropList o snd) (assoc1 "dimensions" tail),
                Option.map snd (assoc1 "properties" tail))
           of (NONE,_,_) => raise ERR "dest_field" "can't extract field type"
            | (SOME typ, NONE, NONE) => (fldname,mk_ty typ)
            | (SOME typ, SOME dim, NONE) => (fldname,ArrayTy(mk_ty typ, [mk_dim dim]))
            | (SOME typ, NONE, SOME spec) =>
                if is_array_spec spec
                 then (fldname,ArrayTy(mk_ty typ,[VarExp"--ARBSIZE--"]))
                 else raise ERR "dest_field" "expected array type spec"
            | (SOME _, SOME _, SOME _)
               => raise ERR "dest_field" "confused, can't extract field type")
   | otherwise => raise ERR "dest_field" "expected a record field"
 end
;

(*---------------------------------------------------------------------------*)
(* There are several flavours of record declaration. A standard decl has a   *)
(* list of fields. One can also declare a record to be an *extension* of     *)
(* another record. In this case, we create a special "extender" field which  *)
(* gets taken care of in post-processing (function extend_recd_decs).        *)
(*                                                                           *)
(* Fields can also have special processing. A field is usually a pair of a   *)
(* field name and a type. It can happen that the type is instead Null,       *)
(* indicating a partial record, to be filled in by post-processing           *)
(* (function finalize_partial_recd_decs). It can also be that an array type  *)
(* has an unspecified dimension, which results in a variable dimension being *)
(* used. See dest_field for details.                                         *)
(*---------------------------------------------------------------------------*)

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
            subcomps_maybe)
     => let val subcomps =
             (case subcomps_maybe
              of [] => []
               | ("subcomponents", List scomps) :: _ => scomps
               | otherwise => raise ERR "recd_decl" "missing extension information")
        in
        case extension
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
           | other => raise ERR "recd_decl" "unexpected extension syntax"
        end
   | AList (("packageName", String pkg) ::
            ("name", String name_impl) ::
            ("localName", _) ::
            ("kind",String "ComponentImplementation") ::
            ("category", String "data") ::_)
     => RecdDec(dest_qid (Option.valOf (dropImpl name_impl)),[])
   | other => raise ERR "recd_decl" "expected a record declaration";

fun dest_enum_props (alist1,alist2) =
  if dropString (value_of (value_of alist1)) = "Enum" then
     let val elist = value_of(value_of alist2)
     in map (dropString o value_of) (dropList elist)
     end
  else raise ERR "dest_enum_props" "";

fun enum_decl decl =
 case decl
  of AList (("name", String ename) ::
            ("localName",_) ::
            ("kind",String "ComponentType") ::
            ("category", String "data") ::
            ("extends", _) ::
            ("properties", List (alist1::alist2::_)) :: _)
      => (case total dest_enum_props (alist1,alist2)
           of NONE => raise ERR "enum_decl" "expected an enum declaration"
            | SOME names => EnumDec(dest_qid ename, names))
  | other => raise ERR "enum_decl" "expected an enum declaration";

fun array_decl decl =
 case decl
  of AList (("name", String name)::
            ("localName",_) ::
            ("kind",String "ComponentType") ::
            ("category", String "data") ::
	    ("properties", List (alist1::alist2::alist3::_)) :: _)
     => if SOME "Array" = total (dropString o value_of o value_of) alist1 then
         let val jbasety = value_of(hd(dropList(value_of(value_of alist2))))
             val basety = get_tyinfo[("kind",String"typeId"),("name",jbasety)]
             val d = dropInt(value_of(hd(dropList(value_of(value_of alist3)))))
         in ArrayDec(dest_qid name, ArrayTy(basety,[mk_uintLit d]))
         end
        else raise ERR "array_decl" "expected an array declaration"
  | other => raise ERR "array_decl" "expected an array declaration";

fun data_decl_name decl =
 case decl
  of AList(("packageName", String pkg) ::
           ("name", String dname) ::
           ("localName", _) ::
           ("kind", String "ComponentImplementation") ::
           ("category", String "data") :: _) => dname
   | otherwise => raise ERR "data_decl_name" "";


fun get_tydecl pkgName names thing =
   enum_decl thing handle HOL_ERR _ =>
   recd_decl pkgName names thing handle HOL_ERR _ =>
   array_decl thing handle HOL_ERR _ => raise ERR "get_tydecl" "";

(* -------------------------------------------------------------------------- *)
(* Pulling out data declarations is a bit involved. First, we extract enums   *)
(* and expunge all other comps with the name of an enum. (This helps with an  *)
(* unfortunate overlap with empty record declarations.) All info about an enum*)
(* is held in its ComponentType spec. We delete the corresponding Component-  *)
(* -Implementation. Then we go sequentially through the rest, expected to be  *)
(* Union, Array, or Recd declarations. A Union declaration spans both its     *)
(* ComponentType spec (which declares that it is in fact a union) and the     *)
(* ComponentImplementation spec, which tells which types are in the union. An *)
(* Array declaration is easy: the ComponentType declaration has all the       *)
(* information. Everything else is a Recd, but there is (afaik) no syntax     *)
(* that explicitly declares that an element is in fact a record type, so we   *)
(* just look at the ComponentImplementation to locate the fields (held in     *)
(* "subcomponents"). However, if the fields are *empty*, then there is no     *)
(* subcomponents element so we have to account for those empty records.       *)
(* -------------------------------------------------------------------------- *)

fun enum_decls [] (edecs,comps) = (rev edecs, rev comps)
  | enum_decls (h::t) (edecs,comps) =
    case total enum_decl h
     of SOME edec => enum_decls t (edec::edecs,comps)
      | NONE => enum_decls t (edecs,h::comps)

fun union_qids comps =
 let fun pred comp =
      ("Union" = dropString
                   (value_of(value_of(hd (dropList (properties_of comp))))))
      handle _ => false
 in
    map (dest_qid o dropString o name_of) (filter pred comps)
 end;

fun union_decl uqids comp =
  if dropString (kind_of comp) = "ComponentImplementation"
     andalso
     mem (dest_qid (dropString (name_of comp))) uqids
  then
    UnionDec
      (dest_qid(dropString (name_of comp)),
      List.map (fn sc => (dropString (name_of sc),
                          NamedTy(dest_qid (dropString (classifier_of sc)))))
               (dropList (subcomponents_of comp)))
  else raise ERR "union_decl" "expected a Union implementation";

fun drop_seen_comps qids complist =
 let fun seen comp = mem (dest_qid (dropString (name_of comp))) qids
 in filter (not o seen) complist
 end;

fun drop_seen_impls qids complist =
 let fun is_seen_impl comp =
       mem (dest_qid (dropString (name_of comp))) qids
       andalso
       dropString (kind_of comp) = "ComponentImplementation";
 in filter (not o is_seen_impl) complist
 end;

fun tydec_usedBy tydec1 tydec2 =
 case (tydec1,tydec2)
  of (EnumDec _, _) => false
   | (_, EnumDec _) => false
   | (_, RecdDec(_,flds)) => exists (ty_occurs (NamedTy (dec_qid tydec1))) (map snd flds)
   | (_, ArrayDec(_,ty)) => ty_occurs (NamedTy (dec_qid tydec1)) ty
   | (_, UnionDec(_,ctrs)) => exists (ty_occurs (NamedTy (dec_qid tydec1))) (map snd ctrs)
;

(*---------------------------------------------------------------------------*)
(* There is some ambiguity in type declarations. Unions, Enums, and Arrays   *)
(* are declared as such in ComponentType declarations. Everything that needs *)
(* to be known for Enums and Arrays is held in the ComponentType decl. For a *)
(* Union type, the constructor information for the union is held in the      *)
(* corresponding ComponentImplementation declaration. Everything that isn't  *)
(* a Union, Enum, or Array is treated as a Recd. Recds are defined by their  *)
(* fields, which are held in the ComponentImplementation declaration for the *)
(* record. Because of obscure reasons having to do with the possibility of   *)
(* empty records looking like implementations of some other kind of type, we *)
(* drop all Union, Enum, and Array ComponentImplementation decls before      *)
(* handling record declarations.                                             *)
(*---------------------------------------------------------------------------*)

fun get_tydecls pkgName complist =
 let val uqids = union_qids complist
     val udecs = mapfilter (union_decl uqids) complist
     val comps0 = drop_seen_comps uqids complist
     val (enum_decs,comps1) = enum_decls comps0 ([],[])
     val eqids = map dec_qid enum_decs
     val comps2 = drop_seen_comps eqids comps1
     val aqids = mapfilter (dec_qid o array_decl) comps2
     val comps3 = drop_seen_impls aqids comps2
     val names = mapfilter data_decl_name comps3
     val decs = mapfilter (get_tydecl pkgName names) comps3
     val alldecs = enum_decs @ udecs @ decs
     val ordered_decs = topsort tydec_usedBy alldecs
 in
   ordered_decs
 end

fun get_port port =
 case port
  of AList [("name", String pname),
            ("kind", String conn_style),
            ("classifier", String tyqidstring),
            ("direction", String flowdir)]
      => (pname,dest_tyqid tyqidstring,flowdir,conn_style)
    | otherwise => raise ERR "get_port" "unexpected port format"

fun get_named_props name_equivFn rnames stmts =
 let fun get_named_exp rname (AList alist) =
         if name_equivFn rname (assoc "name" alist) then
            (dropString rname, dest_exp (assoc "expr" alist))
         else raise ERR "get_named_exp" "not found"
       | get_named_exp _ _ = raise ERR "get_named_exp" "expected an AList"
     fun prop_of rname = tryfind (get_named_exp rname) stmts
 in
    mapfilter prop_of rnames
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

(*---------------------------------------------------------------------------*)
(* This enables "Req001_Filter" to be equal to "Req001_RadioDriver_Filter"   *)
(*---------------------------------------------------------------------------*)

fun filter_req_name_eq js1 js2 =
 let val s1 = dropString js1
     val s2 = dropString js2
     fun is_underscore ch = (ch = #"_")
     val s1_tokens = String.tokens is_underscore s1
     val s2_tokens = String.tokens is_underscore s2
 in not (null s1_tokens) andalso not(null s2_tokens) andalso
    hd s1_tokens = hd s2_tokens andalso
    last s1_tokens = last s2_tokens
 end;

fun is_filter props =
 let fun isaFilter prop =
          dropString(name_of prop) = "CASE_Properties::Component_Type"
          andalso
          (dropString(value_of (value_of prop)) = "FILTER" handle _ => false)
 in exists isaFilter props
 end

fun get_filter_rqtNames props =
 let fun get prop =
       case total (dropString o name_of) prop
        of SOME "CASE_Properties::Component_Spec" =>
            (map value_of (dropList (value_of (value_of prop)))
             handle _ => raise ERR "get_filter_rqtNames" "")
         | otherwise => raise ERR "get_filter_rqtNames" ""
 in
   tryfind get props
 end

fun get_filter decl =
 case decl
  of AList
      [("name", String fname),
       ("localName", _),
       ("kind",String "ComponentType"),
       ("category", String "thread"),
       ("features", List ports),
       ("properties", List props),
       ("annexes", List annexen)]
    => if is_filter props then
        let val rqtNames = get_filter_rqtNames props
            val stmts = List.concat (map get_annex_stmts annexen)
            val glist = get_named_props filter_req_name_eq rqtNames stmts
       in if null glist then
              raise ERR "get_filter" "no properties!"
           else FilterDec (dest_qid fname, map get_port ports, glist)
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

fun get_spec_names properties =
 let fun get_spec prop =
     if dropString(name_of prop) = "CASE_Properties::Component_Spec"
     then (map (dropString o value_of)
              (dropList(value_of(value_of prop)))
           handle _ => raise ERR "get_guar_names" "")
     else raise ERR "get_guar_names" ""
 in
   tryfind get_spec properties
 end

fun get_latched properties =
 let fun getLatch prop =
       if dropString(name_of prop) = "CASE_Properties::Monitor_Latched"
        then dropBool (value_of (value_of prop))
        else raise ERR "get_latched" "expected Monitor_Latched property"
 in tryfind getLatch properties
 end

fun is_monitor props =
 let fun isaMon prop =
          dropString(name_of prop) = "CASE_Properties::Component_Type"
          andalso
          (dropString (value_of(value_of prop)) = "MONITOR"
           handle _ => false)
 in exists isaMon props
 end

fun get_policy policyName jlist =
 let fun property (AList list) =
          if dropString(assoc "name" list) = policyName then
            dest_exp (assoc "expr" list)
          else raise ERR "get_policy" ""
       | property otherwise = raise ERR "get_policy" ""
 in tryfind property jlist
 end

fun dest_property_stmt (AList alist) =
    (case (assoc "kind" alist, assoc "name" alist, assoc "expr" alist)
       of (String "PropertyStatement", String pname, e) => (pname,dest_exp e)
        | otherwise => raise ERR "dest_property_stmt" "unexpected syntax")
  | dest_property_stmt any_other_thing = raise ERR "dest_property_stmt" "unexpected syntax"
;

fun dest_eq_stmt (AList alist) =
    (case (assoc "kind" alist, assoc "left" alist, assoc "expr" alist)
       of (String "EqStatement", List [AList LHS], e) =>
           let val eqName = dropString(assoc "name" LHS)
               val lhs_ty = dest_ty (assoc "type" LHS)
           in (eqName,lhs_ty,dest_exp e)
           end
        | otherwise => raise ERR "dest_eq_stmt" "unexpected syntax")
  | dest_eq_stmt any_other_thing = raise ERR "dest_eq_stmt" "unexpected syntax"
;

fun dest_guar_stmt stmt =
 if dropString (kind_of stmt) = "GuaranteeStatement" then
    ((dropString (name_of stmt), label_of stmt, dest_exp (expr_of stmt))
     handle _ => raise ERR "dest_guar_stmt" "unexpected syntax")
 else raise ERR "dest_guar_stmt" "unexpected syntax"
;

fun jname_eq s1 s2 = (dropString s1 = dropString s2)

fun get_monitor comp =
 let val properties = dropList(properties_of comp)
     val _ = if is_monitor properties then ()
             else raise ERR "get_monitor" "unable to find MONITOR property"
     val qid = dest_qid (dropString (name_of comp))
     val ports = dropList (features_of comp)
     val annexen = dropList (annexes_of comp)
     val specNames = get_spec_names properties
     val is_latched = get_latched properties
     val portL = map get_monitor_port ports
     val stmts = List.concat (map get_annex_stmts annexen)
     val eq_stmts   = mapfilter dest_eq_stmt stmts (* should turn into FnDecs elsewhere in scrape *)
     val prop_stmts = mapfilter dest_property_stmt stmts
     fun is_policy(s,_) = last (String.tokens (equal #"_") s) = "policy"
     val ((pname,policy),prop_stmts') = pluck is_policy prop_stmts
     val guar_stmts = mapfilter dest_guar_stmt stmts
     val monitor_guars = filter (C mem specNames o #1) guar_stmts
 in
     MonitorDec(qid, portL, is_latched, (pname,"",policy)::monitor_guars)
 end
 handle _ => raise ERR "get_monitor" "unexpected syntax"
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

fun dest_propertyConst json =
 case json
  of AList (("name", String qid) ::
            ("kind", _) ::
            ("propertyType", expect_aadl_integer) ::
            ("value", valuegunk) :: _) =>
     (case total value_of valuegunk
      of SOME (Number (Int i)) =>
             ConstDec (dest_qid qid,BaseTy(IntTy (AST.Int NONE)), mk_intLit i)
       | unexpected =>  raise ERR "dest_propertyConst" "expected an integer literal")
   | otherwise => raise ERR "dest_propertyConst" ""


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
   | AList (("name", String pkgName) ::
            ("kind", String "PropertySet") ::
            ("propertyConstants", List pconsts) :: _)
     => let val const_decls = mapfilter dest_propertyConst pconsts
        in (pkgName,([], const_decls, [], []))
        end
   | AList (("name", String pkgName) :: _) => (pkgName,([], [], [], []))
   | otherwise => raise ERR "scrape" "unexpected format"

fun dest_with ("with", List wlist) = map dropString wlist
  | dest_with other = raise ERR "dest_with" "";

fun uptoWith string lo hi =
   String.concat
    ["[", String.concatWith ","
            (map (fn i => string^Int.toString i) (upto lo hi)),
     "]\n"]


(*
uptoWith "comp" 1 108;

val [comp1,comp2,comp3,comp4,comp5,comp6,comp7,comp8,comp9,comp10,
     comp11,comp12,comp13,comp14,comp15,comp16,comp17,comp18,comp19,comp20,
     comp21,comp22,comp23,comp24,comp25,comp26,comp27,comp28,comp29,comp30,
     comp31,comp32,comp33,comp34,comp35,comp36,comp37,comp38,comp39,comp40,
     comp41,comp42,comp43,comp44,comp45,comp46,comp47,comp48,comp49,comp50,
     comp51,comp52,comp53,comp54,comp55,comp56,comp57,comp58,comp59,comp60,
     comp61,comp62,comp63,comp64,comp65,comp66,comp67,comp68,comp69,comp70,
     comp71,comp72,comp73,comp74,comp75,comp76,comp77,comp78,comp79,comp80,
     comp81,comp82,comp83,comp84,comp85,comp86,comp87,comp88,comp89,comp90,
     comp91,comp92,comp93,comp94,comp95,comp96,comp97,comp98,comp99,comp100,
     comp101,comp102,comp103,comp104,comp105,comp106,comp107,comp108] = complist;

*)

(*---------------------------------------------------------------------------*)
(* For any declaration of a partial record type there should be a later      *)
(* declaration of an completion of that type, giving the missing field(s)    *)
(* to be added. We remove the first declaration and add its fields to the    *)
(* given extension fields.                                                   *)
(*---------------------------------------------------------------------------*)

fun dest_recd_dec (RecdDec args) = args
  | dest_recd_dec other = raise ERR "dest_recd_dec" ""

fun finalize_partial_recd_decs declist =
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

(*---------------------------------------------------------------------------*)
(* Another kind of record extension: essentially a kind of concatenation.    *)
(*                                                                           *)
(*      recdMap : qid -> field list                                          *)
(*---------------------------------------------------------------------------*)
(*
fun dom fmap = List.map fst (Redblackmap.listItems fmap);

val modlist = mapfilter scrape opkgs
val (pkg as (pkgName, (tydecs, fndecs, fdecs, mdecs))) = el 8 modlist;
*)

fun extend_recd dec (recdMap,decs) =
  case total dest_extender dec
   of NONE => (recdMap, dec::decs)
    | SOME (qid,base_qid,flds) =>
  case Redblackmap.peek(recdMap,base_qid)
   of NONE => raise ERR "extend_recd_dec"
              ("Declaration for "^Lib.quote (qid_string base_qid)^" not found")
    | SOME base_fields =>
      let val fields' = base_fields @ flds
          val dec' = RecdDec(qid, fields')
        in
         (Redblackmap.insert(recdMap,qid,fields'),
          dec'::decs)
        end

fun extend_recd_decs (pkgName,(tydecs,fndecs,fdecs,mdecs)) =
 let val recd_assoc_list = mapfilter dest_recd_dec tydecs
     val recdMap = Redblackmap.fromList qid_compare recd_assoc_list
     val (recdMap',tydecs') = rev_itlist extend_recd tydecs (recdMap,[])
 in
   (pkgName,(rev tydecs',fndecs,fdecs,mdecs))
 end;

fun empty_pkg (_,([],[],[],[])) = true
  | empty_pkg ("Common_Data",_) = true
  | empty_pkg otherwise = false;

(*
fun scrub_pkg (name,(tydecs,tmdecs,fdecs,mdecs)) =
 let fun empty_recd (RecdDec(qid,[])) = true
       | empty_recd otherwise = false
 in
    (name,(filter (not o empty_recd) tydecs, tmdecs, fdecs, mdecs))
 end
*)

fun scrub_pkg x = x;

fun scrape_pkgs json =
 let fun uses (A as AList (("name", String AName) ::
                           ("kind", String "AadlPackage") ::
                           ("public", AList publist):: _))
              (B as AList (("name", String BName) :: _)) =
          let val Auses = List.concat (mapfilter dest_with publist)
          in mem BName Auses
          end
       | uses other wise = false
     fun run pkgs =
      let val opkgs = rev (topsort uses pkgs)
          val modlist = mapfilter scrape opkgs
          val modlist' = finalize_partial_recd_decs modlist
          val modlist'' = map extend_recd_decs modlist'
          val modlist''' = filter (not o empty_pkg)
                                  (map scrub_pkg modlist'')
      in modlist'''
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
         (B as AList (("name", String BName) :: _)) =
   let val Auses = List.concat (mapfilter dest_with publist)
   in mem BName Auses
   end
  | uses other wise = false;

val AList alist = jpkg;
val pkgs = dropList (assoc "modelUnits" alist);

val (opkgs as
 [pkg1, pkg2, pkg3, pkg4, pkg5, pkg6, pkg7,pkg8, pkg9, pkg10,
  pkg11,pkg12, pkg13,pkg14,pkg15,pkg16,pkg17, pkg18, pkg19, pkg20,
  pkg21, pkg22,pkg23, pkg24, pkg25, pkg26,pkg27,pkg28,pkg29]) = rev (topsort uses pkgs);

val pkgNames = map name_of opkgs;

val declist = mapfilter scrape opkgs;

scrape pkg1;
scrape pkg2;
scrape pkg3;
scrape pkg4;
scrape pkg5;
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
scrape pkg16;
scrape pkg17;
scrape pkg18;
scrape pkg19;
scrape pkg20;
scrape pkg21;
scrape pkg22;
scrape pkg23;
scrape pkg24;
scrape pkg25;
scrape pkg26;
scrape pkg27;
scrape pkg28;
scrape pkg29;
scrape pkg30;

for UAS pkg CMASI is pkg7

for pkg SW:

val [comp1, comp2, comp3, comp4, comp5, comp6, comp7,comp8, comp9, comp10,
     comp11,comp12, comp13,comp14,comp15,comp16,comp17, comp18, comp19, comp20,
     comp21, comp22,comp23, comp24, comp25, comp26,comp27,comp28,comp29,comp30,
     comp31, comp32, comp33, comp34, comp35, comp36, comp37,comp38, comp39, comp40,
     comp41, comp42, comp43, comp44, comp45, comp46, comp47,comp48, comp49, comp50,
     comp51, comp52, comp53, comp54] = complist;

-- comp9 is AttGate (a monitor);
   * fndef IS_TRUSTED inside annex has reference to variable "trusted_ids" which is
     a feature of the component, and not a param of the fndef. Must think about how
     to spot this non-local parameter parameter!

-- comp13 is LST filter;

mk_comp_defs comp1;
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
   | UnionDec (qid,choices) => UnionDec(qid, map (I##amn_ty) choices)

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
        FilterDec(qid, map amn_port ports,
                  map amn_cprop cprops)
 end
;

fun amn_monitor_dec fdec =
 let fun amn_port (s1,ty,s2,s3) = (s1,amn_ty ty,s2,s3)
     fun amn_cprop (s1,s2,e) = (s1,s2,amn_exp e)
 in case fdec
     of MonitorDec(qid, ports, b, cprops) =>
        MonitorDec(qid, map amn_port ports, b, map amn_cprop cprops)
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
   | BaseTy FloatTy  => realSyntax.real_ty
   | BaseTy DoubleTy => realSyntax.real_ty
   | BaseTy (IntTy(Nat _)) => numSyntax.num
   | BaseTy (IntTy(Int _)) => intSyntax.int_ty
(* | BaseTy (IntTy(Nat NONE)) => numSyntax.num
   | BaseTy (IntTy(Nat (SOME _))) => raise ERR "transTy" "fixed-width nums not supported"
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
*)
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

(*
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
*)
fun lift_int {value,kind} =
 let open AST
 in case kind
     of Nat _ => numSyntax.term_of_int value
      | Int _ => intSyntax.term_of_int (Arbint.fromInt value)
 end;


(* Rounds for now in order to do injection *)
fun lift_float r =
  intrealSyntax.mk_real_of_int
      (intSyntax.term_of_int (Arbint.fromInt(Real.round r)));

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

val real_ty = realSyntax.real_ty;

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
         if mem ty [intSyntax.int_ty,i8,i16,i32,i64] then
            lift intSyntax.mk_negated else
         if ty = real_ty then
           lift realSyntax.mk_negated
         else raise ERR "unop (UMinus)"
                   "expected type of operand to be int\
                   \ (either fixed width or unbounded)"
      | Yesterday => lift ptltlSyntax.mk_Yester
      | ZYesterday => lift ptltlSyntax.mk_Zyester
      | Historically => lift ptltlSyntax.mk_Histor
      | Signed => undef "Signed"
      | Unsigned => undef "Unsigned"
      | Unbounded => undef "Unbounded"
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
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
         then lift intSyntax.mk_plus else
       if ty1 = real_ty then lift realSyntax.mk_plus
       else raise ERR "Plus" "expected numeric arguments"
    | Minus =>
       if ty1 = numSyntax.num then lift numSyntax.mk_minus else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_minus else
       if ty1 = real_ty then lift realSyntax.mk_minus else
       raise ERR "Minus" "expected numeric arguments"
    | Multiply =>
       if ty1 = numSyntax.num then lift numSyntax.mk_mult else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_mult else
       if ty1 = real_ty then lift realSyntax.mk_mult else
       raise ERR "Multiply" "expected numeric arguments"
    | Exponent =>
       if ty1 = numSyntax.num then lift numSyntax.mk_exp else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_exp else
       if ty1 = real_ty then lift realSyntax.mk_pow else
       raise ERR "Exponent" "expected numeric arguments"
    | Divide =>
       if ty1 = numSyntax.num then lift numSyntax.mk_div else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_div else
       if ty1 = real_ty then lift realSyntax.mk_div else
       raise ERR "Divide" "expected numeric arguments"
    | Modulo =>
       if ty1 = numSyntax.num then lift numSyntax.mk_mod else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_mod else
       raise ERR "Modulo" "expected numeric arguments"
    | Less =>
       if ty1 = numSyntax.num then lift numSyntax.mk_less else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_less else
       if ty1 = real_ty then lift realSyntax.mk_less else
       raise ERR "Less" "expected numeric arguments"
    | Greater =>
       if ty1 = numSyntax.num then lift numSyntax.mk_greater else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_great else
       if ty1 = real_ty then lift realSyntax.mk_great else
       raise ERR "Modulo" "expected numeric arguments"
    | LessEqual =>
       if ty1 = numSyntax.num then lift numSyntax.mk_leq else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_leq else
       if ty1 = real_ty then lift realSyntax.mk_leq else
       raise ERR "LessEqual" "expected numeric arguments"
    | GreaterEqual =>
       if ty1 = numSyntax.num then lift numSyntax.mk_geq else
       if mem ty1 [intSyntax.int_ty,u8,u16,u32,u64,i8,i16,i32,i64]
          then lift intSyntax.mk_geq else
       if ty1 = real_ty then lift realSyntax.mk_geq else
       raise ERR "GreaterEqual" "expected numeric arguments"
    | Since => undef "Since"
    | Trigger => undef "Trigger"
    | Fby => undef "Fby"
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

fun trans_ptLTL frmula =
 let open ptltlSyntax
     fun mk_obsVar i = ("obsVar_"^Int.toString i)
     val obStrm = Lib.mk_istream (fn x => x+1) 1 mk_obsVar
  fun sweep form bindings =
    case form
     of Fncall(("AGREE_PLTL","Yesterday"),[e]) => (mk_Yester ## I) (sweep e bindings)
      | Fncall(("AGREE_PLTL","Zyesterday"),[e]) => (mk_Zyester ## I) (sweep e bindings)
      | Fncall(("AGREE_PLTL","Historically"),[e]) => (mk_Histor ## I) (sweep e bindings)
      | Fncall(("AGREE_PLTL","Since"),[e1,e2]) =>
          let val (tm1,binds1) = sweep e1 bindings
              val (tm2,binds2) = sweep e2 binds1
          in (mk_Since (tm1, tm2), binds2)
          end
      | Fncall(("AGREE_PLTL","Trigger"),[e1,e2]) =>
          let val (tm1,binds1) = sweep e1 bindings
              val (tm2,binds2) = sweep e2 binds1
          in (mk_Trigger (tm1, tm2), binds2)
          end
      | Fncall(("AGREE_PLTL",s),_) => raise ERR "trans_ptLTL"
              ("unknown AGREE_PTLTL operator: "^Lib.quote s)
      | VarExp id => (mk_Eid (stringSyntax.fromMLstring id), bindings)
      | ConstExp (BoolLit b) => (mk_Prim (fromMLbool b), bindings)
      | Unop(Not,e) => (mk_Not ## I) (sweep e bindings)
      | Binop(Equal,e1,e2) =>
          let val (tm1,binds1) = sweep e1 bindings
              val (tm2,binds2) = sweep e2 binds1
          in (mk_Equiv (tm1, tm2), binds2)
          end
      | Binop(Imp,e1,e2) =>
          let val (tm1,binds1) = sweep e1 bindings
              val (tm2,binds2) = sweep e2 binds1
          in (mk_Imp (tm1, tm2), binds2)
          end
      | Binop(Or,e1,e2) =>
          let val (tm1,binds1) = sweep e1 bindings
              val (tm2,binds2) = sweep e2 binds1
          in (mk_Or (tm1, tm2), binds2)
          end
      | Binop(And,e1,e2) =>
          let val (tm1,binds1) = sweep e1 bindings
              val (tm2,binds2) = sweep e2 binds1
          in (mk_And (tm1, tm2), binds2)
          end
      | otherwise =>
          let val obsvar = Lib.state obStrm
              val obsvarTL = mk_Eid (stringSyntax.fromMLstring obsvar)
              val obsvar  = VarExp obsvar
              val _ = Lib.next obStrm
          in (obsvarTL, (form,obsvar)::bindings)
          end
 in sweep frmula []
 end

fun mk_array_access(A,[]) = A
  | mk_array_access(A,h::t) =
      let val ty = type_of h
          val i =
           if ty = numSyntax.num then h else
           if ty = intSyntax.int_ty then intSyntax.mk_Num h
           else raise ERR "mk_array_access" "expected a num or int"
      in
       mk_array_access(fcpSyntax.mk_fcp_index(A,i),t)
      end

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
    | ConstExp (FloatLit f)  => lift_float f
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
    | ArrayIndex(A,indices) =>
         let open fcpSyntax
               val Atm = transExp pkgName varE Unknown A
               val inds = map (transExp pkgName varE (Expected intSyntax.int_ty)) indices
         in
            mk_array_access(Atm,inds)
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
    | Fncall ((_,"Event"),[arg]) =>
         optionSyntax.mk_is_some (transExp pkgName varE Unknown arg)
    | Fncall ((_,"Event"),_) => raise ERR "transExp" "Event: unexpected number of args"
    | Fncall (("AGREE_PLTL",_),_) => raise ERR "transExp" "AGREE_PTLTL unexpected"
    | Fncall ((thyname,cname),expl) =>
       (let val thyname' = if thyname = "" then pkgName else thyname
            val c = prim_mk_const{Thy=thyname',Name=cname}
        in list_mk_comb(c,map (transExp pkgName varE Unknown) expl)
        end handle e as HOL_ERR _ => raise wrap_exn "" "transExp" e)
    | ConstExp (IdConst qid) => undef "ConstExp: IdConst"
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


fun ty2pretype tyEnv ty =
 let open Datatype ParseDatatype
 in case ty
     of NamedTy ("","null") => dVartype "'a"
      | NamedTy ("Base_Types",_) => dAQ (transTy tyEnv ty)
      | ty => dAQ (transTy tyEnv ty)
 end

fun declare_hol_record tyEnv ((_,rname),fields) =
 let open ParseDatatype ParseDatatype_dtype
     fun mk_field(s,ty) = (s,ty2pretype tyEnv ty)
 in
    if null fields then  (* Empty records get mapped to a trivial datatype *)
     Datatype.astHol_datatype
          [(rname,Constructors[(rname,[dAQ oneSyntax.one_ty])])]
     else Datatype.astHol_datatype [(rname,Record (map mk_field fields))]
   ; stdErr_print ("Declared record "^Lib.quote rname^"\n")
 end

fun declare_hol_union tyEnv (qid,choices) =
 let open ParseDatatype
     val tyName = snd qid
     fun mk_constr (s,ty) = (s,[ty2pretype tyEnv ty])
 in
   Datatype.astHol_datatype [(tyName,Constructors (map mk_constr choices))]
   ; stdErr_print ("Declared union type "^Lib.quote tyName^"\n")
 end

(* ArrayDecs are currently treated as type abbrevs

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
    let val arrName = snd qid
        val anon_pkg_qid = ("",arrName)
        val ty' = substTyTy (map op|-> tyEnv) ty
        val _ = stdErr_print
                   ("Declared type abbrev for array "^Lib.quote arrName^"\n")
    in (NamedTy qid, ty') :: (NamedTy anon_pkg_qid,ty') :: tyEnv
    end
  | declare_hol_type (UnionDec (qid,choices)) tyEnv =
    (declare_hol_union tyEnv (qid,choices); tyEnv)

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
    handle HOL_ERR _ => raise ERR "declare_hol_fn"
           ("failed to define "^Lib.quote name)

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

fun is_event kind = mem kind ["EventPort","EventDataPort"];
fun is_event_port (_,_,_,kind) = is_event kind;

(*fun build_mon_dfa (policyName,policy_exp) =
 let val (policy_tm,obsBinds) = trans_ptLTL policy_exp
     val policy_def = TotalDefn.Define
          `^(mk_eq(mk_var(fname^"_POLICY",ptltlSyntax.formula), policy_tm))`
     val mk_dfa_input = ptltlSyntax.mk_table_data1
                           (ptltlSyntax.mk_relational_data(policy_tm,T))
      val _ = print "\ngenerating monitor DFA ... "
      val dfa_thm = EVAL mk_dfa_input
      val _ = print " done.\n"
      val [state_to_index, elm_to_idx, finals, table, start_idx]
          = pairSyntax.strip_pair (rhs (concl dfa_thm))
      val dfa_stepFn =
      val dfa_acceptFn =
 in
   (dfa_stepFn,dfa_acceptFn,dfa_thm)
 end;

fun mk_monitor_spec (thyName,tyEnv,fn_defs)
                    (MonitorDec ((pkgName,fname), ports, is_latched, cprops)) =
    let val is_latched_def_tm = mk_eq(mk_var(fname^"_is_latched",bool),
				      if is_latched then T else F)
        val is_latched_def = Define `^is_latched_def_tm`
        val outports = filter (fn (_,_,dir,_) => (dir = "out")) ports
	val inports = filter (fn (_,_,dir,_) => (dir = "in")) ports
        fun mk_port_binding(s,ty,dir,kind) =
           let val holty = transTy tyEnv ty
               val holty' =
                  if is_event kind then
                    optionSyntax.mk_option holty
                  else holty
           in (s,mk_var(s,holty'))
           end
        val portEnv = map mk_port_binding (inports @ outports)
        val policy = hd cprops
        val (dfa_stepfn,dfa_acceptfn) = build_mon_dfa policy
        val prop = end_itlist mk_and (map snd (tl cprops))

(*        val inportVars = map mk_port_var inports
        val outportVars = map mk_port_var outports
        val spec = transExp thyName portEnv (Expected bool) prop
        val spec_thm = QCONV (PURE_REWRITE_CONV fn_defs) spec

(*        val array_forall_expanded =
             spec_thm
(*               |> SIMP_RULE (srw_ss()) [splatTheory.fcp_every_thm] *)
               |> SIMP_RULE arith_ss
                    [arithmeticTheory.BOUNDED_FORALL_THM,
                     GSYM CONJ_ASSOC,GSYM DISJ_ASSOC]
*)
        val full_name = String.concatWith "__" [pkgName,fname]
*)
    in
       ((pkgName,fname),policy_def)
    end
    handle e => raise wrap_exn "AADL" "mk_monitor_spec" e;
;
*)

fun mk_monitor_spec _ _ = raise ERR "mk_monitor" ""

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

fun revitFail f [] acc = (acc,[])
  | revitFail f (h::t) acc =
     case (SOME (f h acc) handle _ => NONE)
      of NONE => (acc,h::t)
       | SOME x => revitFail f t x
;

fun mk_pkg_defs thyName tyEnv (pkgName,(tydecs,tmdecs,filters,monitors)) =
 let val (tyEnv',rst) = revitFail declare_hol_type tydecs tyEnv
 in if not(null rst) then
       raise ERR "mk_pkg_defs" "failure to define a declared type"
    else
 let val tydecls = List.filter (is_datatype o snd) (theorems thyName)
     val tmdecs' = op_mk_set same_tmdec tmdecs
     val tmdecs'' = topsort called_by tmdecs'
     val fn_defs = map (declare_hol_term tyEnv') tmdecs''
     val info = (thyName,tyEnv',fn_defs)
     val filter_specs = map (mk_filter_spec info) filters
     val monitor_specs = map (mk_monitor_spec info) monitors
 in
      (tyEnv', map snd tydecls, fn_defs, filter_specs, monitor_specs)
 end end;
G
fun pkgs2hol thyName pkgs =
 let fun step pkg (tyE,tyD,tmD,fS,mS) =
        let val (tyEnv',tydefs,fndefs,filtspecs,monspecs) = mk_pkg_defs thyName tyE pkg
        in (tyEnv', tydefs@tyD, fndefs@tmD, filtspecs@fS, monspecs@mS)
        end
      val init = ([],[],[],[],[])
 in
   rev_itlist step pkgs init
 end;

(*
val [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7] = pkgs;

val thyName = "UAS";

(* Each constructor wraps an existing unary type *)

fun step pkg (tyE,tyD,tmD,fS,mS) =
  let val (tyEnv',tydefs,fndefs,filtspecs,monspecs) = mk_pkg_defs thyName tyE pkg
  in (tyEnv', tydefs@tyD, fndefs@tmD, filtspecs@fS, monspecs@mS)
  end

val init = ([],[],[],[],[])

val res1 = step pkg1 init;
val res2 = step pkg2 res1;
val res3 = step pkg3 res2;
val res4 = step pkg4 res3;
val res5 = step pkg5 res4;
val res6 = step pkg6 res5;
val res7 = step pkg7 res6;
*)

(*---------------------------------------------------------------------------*)
(* Generate contig-based filter code in CakeML concrete syntax.              *)
(*---------------------------------------------------------------------------*)

fun dest_intLit exp =
 case exp
  of ConstExp(IntLit{value,kind = AST.Int NONE}) => value
   | otherwise => raise ERR "dest_intLit" "";

(*---------------------------------------------------------------------------*)
(* Get the template file "./TEMPLATE" to be instantiated                     *)
(*---------------------------------------------------------------------------*)

val template_ss =
    let val istrm = TextIO.openIn "TEMPLATE"
	val string = TextIO.inputAll istrm
    in TextIO.closeIn istrm;
       Substring.full string
    end;

(*---------------------------------------------------------------------------*)
(* New file: chunk0 . port-contig-type .                                     *)
(*           chunk1 . bufsize .                                              *)
(*           chunk2 . callFFI-def .                                          *)
(*           chunk3 . get-filter-in .                                        *)
(*           chunk4 . port-contig-type .                                     *)
(*           chunk5 . put-filter-out .                                       *)
(*           chunk6                                                          *)
(*---------------------------------------------------------------------------*)

fun locate pat ss =
 let val (chunkA, suff) = Substring.position pat ss
     val chunkB = Substring.triml (String.size pat) suff
 in (chunkA,chunkB)
 end

val replace  =
 let val (chunk0,suff0) = locate "<<PORT-CONTIG-TYPE>>" template_ss
     val (chunk1,suff1) = locate "<<BUFSIZE>>" suff0
     val (chunk2,suff2) = locate "<<CALL-FFI-DECL>>" suff1
     val (chunk3,suff3) = locate "<<GET-FILTER-IN>>" suff2
     val (chunk4,suff4) = locate "<<PORT-CONTIG-TYPE>>" suff3
     val (chunk5,chunk6) = locate"<<PUT-FILTER-OUT>>" suff4
 in fn buffer_size =>
    fn call_ffi_decl =>
    fn get_filter_in =>
    fn port_contig =>
    fn put_filter_out =>
      Substring.concat
         [chunk0, port_contig,
          chunk1, buffer_size,
          chunk2, call_ffi_decl,
          chunk3, get_filter_in,
          chunk4, port_contig,
          chunk5, put_filter_out, chunk6]
 end

fun dest_namedTy (NamedTy p) = p
  | dest_namedTy otherwise = raise ERR "dest_namedTy" "";

fun mk_api_call s = String.concat["#(api_",s, ")"];

fun mk_call (name,ty,"in",_) =
     let val getName = "get_"^name in (getName,mk_api_call getName) end
  | mk_call (name,ty,"out",_) = ("put_"^name,mk_api_call ("send_"^name))
  | mk_call otherwise = raise ERR "mk_call" "";

fun mk_callstring (name,api) =
    String.concat ["  if name = ", Lib.quote name, " then ", api, " istr buf\n   else\n"]

fun isIn (name,ty,"in",style) = true
  | isIn otherwise = false

fun mk_ffi_callFn ports =
 case List.partition isIn ports
  of ([inport],outports as _::_) =>
      let val calls = List.map mk_call ports
      in String.concat
          ("fun callFFI name istr buf =\n"
           :: List.map mk_callstring calls
            @ [String.concat
               ["  (logInfo (",
                Lib.quote "callFFI: unknown request: ",
                "^name);\n   raise FFI_RQT)\n"]])
      end
   | otherwise => raise ERR "mk_ffi_callFn"
      "expected exactly one inport and at least one outport"

fun mk_output_call (name,ty,_,_) =
 String.concat ["API.callFFI ", Lib.quote ("put_"^name)," string Utils.emptybuf"]


fun mk_filter_outputs ports =
 case Lib.filter (not o isIn) ports
  of [] => raise ERR "mk_filter_outputs" "no output ports"
   | oports => String.concatWith ";\n           " (map mk_output_call oports)

val contigNameMap =
  [("OperatingRegion",   "fullOperatingRegionMesg"),
   ("AutomationRequest","fullAutomationRequestMesg"),
   ("LineSearchTask",   "fullLineSearchTaskMesg"),
   ("AutomationResponse", "fullAutomationResponseMesg"),
   ("AirVehicleState","fullAirVehicleStateMesg")];

(* -------------------------------------------------------------------------- *)
(* Map a filter declaration to a CakeML file. Assumes filter has only one     *)
(* input port but could have multiple outputs.                                *)
(* -------------------------------------------------------------------------- *)

fun inst_filter_template targetDir const_alist dec =
 let open Substring
 in
 case dec
  of FilterDec (qid, ports as _::_, props) =>
     let val (name,ty,dir,style) = hd ports
         val (pname,tyName) = dest_namedTy ty
         val sizeName = tyName^"_Bit_Codec_Max_Size"
         val bitsize_exp = assoc sizeName const_alist
         val bitsize = dest_intLit bitsize_exp
         val byte_size = if bitsize mod 8 = 0 then
                           1 + bitsize div 8
                         else 2 + bitsize div 8
         val byte_size_string = Int.toString byte_size
         val call_ffi_decl = mk_ffi_callFn ports
         val get_filter_in = "API.callFFI \"get_filter_in\" \"\" filterBuf"
         val contig = assoc tyName contigNameMap
         val put_filter_out = mk_filter_outputs ports
         val filter_string =
		  replace (full byte_size_string)
                          (full call_ffi_decl)
                          (full get_filter_in)
                          (full contig)
                          (full put_filter_out)
         val fileName = String.concat [targetDir, "/", snd qid, ".cml"]
         val ostrm = TextIO.openOut fileName
     in
         TextIO.output(ostrm,filter_string);
         TextIO.closeOut ostrm
     end
   | otherwise => raise ERR "inst_filter_template" "expected a FilterDec"
 end
 handle e => raise wrap_exn "inst_filter_template" "" e

end
