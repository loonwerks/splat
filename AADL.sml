(*---------------------------------------------------------------------------*)
(* Translation from AADL (in Json syntax) to an AST form, and then to HOL    *)
(*---------------------------------------------------------------------------*)

structure AADL :> AADL =
struct

open Lib Feedback HolKernel boolLib bossLib MiscLib AST Json;

local open
   stringLib stringSimps fcpLib realLib intrealSyntax
in end;

 type qid = string * string;
 type ty = AST.ty;
 type exp = AST.exp;
 type tyEnv = (ty * ty) list;
 type port = string * ty * string * string
 type vardec = string * ty * exp

 datatype tydec
    = EnumDec of qid * string list
    | RecdDec of qid * (string * ty) list
    | ArrayDec of qid * ty
    | UnionDec of qid * (string * ty) list;

 datatype tmdec
    = ConstDec of qid * ty * exp
    | FnDec of qid * (string * ty) list * ty * exp;

 datatype indec
   = In_Data of string * ty * exp
   | In_Event_Only of string * ty * exp
   | In_Event_Data of string * ty * exp * exp;

 datatype outdec
   = Out_Data of string * ty * exp
   | Out_Event_Only of string * ty * exp
   | Out_Event_Data of string * ty * exp * exp;

(*---------------------------------------------------------------------------*)
(* A contract holds all the relevant info scraped from an AGREE decl of      *)
(* a {filter,monitor,gate}. These are all quite similar from the code gen    *)
(* perspective so we sweep them all into a unified datatype.                 *)
(*                                                                           *)
(* ContractDec                                                               *)
(*   (name,kind,ports,latched,tydecs,tmdecs,vardecs,outdecs,assums,guars)    *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

 datatype contract =
   ContractDec
     of qid
      * string  (* {Filter,Monitor,Gate} *)
      * port list
      * bool
      * tydec list  (* local tydecs *)
      * tmdec list  (* local tmdecs *)
      * vardec list (* state vars and temporaries *)
      * (string * string * outdec) list
      * (string * string * exp) list   (* assums *)
      * (string * string * exp) list   (* guars  *)


type pkg = string * (tydec list * tmdec list * contract list);

val ERR = Feedback.mk_HOL_ERR "AADL";

fun is_const_dec (ConstDec _) = true
  | is_const_dec other = false;

fun dest_recd_dec (RecdDec (qid, fields)) = (qid,fields)
  | dest_recd_dec otherwise = raise ERR "dest_recd_dec" ""

fun port_name (s,ty,dir,kind) = s;
fun port_ty (id,ty,dir,kind) = ty;
fun is_in_port (id,ty,"in",kind) = true
  | is_in_port otherwise = false;
fun is_out_port (id,ty,"out",kind) = true
  | is_out_port otherwise = false;
fun is_event (id,ty,dir,"DataPort") = false
  | is_event otherwise = true;
fun is_data(id,ty,dir,"EventPort") = false
  | is_data otherwise = true;

fun tydec_to_ty tydec =
  case tydec
   of RecdDec (qid,fields) => RecdTy(qid,fields)
    | ArrayDec(qid,ty) => ty
    | EnumDec (qid,_) => NamedTy qid
    | UnionDec(qid,_) => NamedTy qid;

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
fun category_of (AList alist) = assoc "category" alist;
fun is_data_comp comp = (dropString (category_of comp) = "data");

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
     val isImpl = C mem ["Impl", "impl", "i"]
 in case Lib.front_last chunks
     of ([a,b],x) =>
          if isImpl x then (a,b) else raise ERR "dest_qid" "unexpected format"
      | ([a],x) => if isImpl x then ("",a) else (a,x)
      | ([],x)  =>
          if isImpl x then raise ERR "dest_qid" "unexpected format" else ("",x)
      | otherwise  => raise ERR "dest_qid" "unexpected format"
 end;

val qid_compare = Lib.pair_compare (String.compare,String.compare);

fun tydec_qid (EnumDec (qid,_)) = qid
  | tydec_qid (RecdDec (qid,_)) = qid
  | tydec_qid (ArrayDec(qid,_)) = qid
  | tydec_qid (UnionDec(qid,_)) = qid;

fun tmdec_qid (ConstDec (qid,_,_)) = qid
  | tmdec_qid (FnDec (qid,_,_,_)) = qid

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
   | (a,b)          => NamedTy (a,b)
;

val boolTy = BaseTy BoolTy;

fun mk_intLit i = ConstExp(IntLit{value=i, kind=AST.Int NONE});

fun mk_int str =
  case Int.fromString str
   of SOME i => mk_intLit i
    | NONE =>
       raise ERR "mk_int" ("expected an int constant, but got: "^Lib.quote str)

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
   | [("kind", String "ArrayType"),
      ("size", String decString),
      ("arrayType", String dcolon)]
     => ArrayTy(dest_tyqid dcolon,[mk_int decString])
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
         | "<>"  => NotEqual
         | "<=>" => Equal
         | "and" => And
         | "or"  => Or
         | "->"  => Fby
         | "div" => Divide
         | other => raise ERR "mk_binop"
               ("unknown binary operator "^Lib.quote other)
 in Binop(oexp,e1,e2)
 end

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
  of NamedTy tyqid => ConstrExp(tyqid,cname,[])
   | otherwise => raise ERR "mk_nullary_constr"
       ("unable to determine type of constructor "^Lib.quote cname)

fun mk_and a b = mk_binop("and",a,b);

(*---------------------------------------------------------------------------*)
(* AADL scraping.                                                            *)
(*---------------------------------------------------------------------------*)

val _ = defaultNumKind := AST.Int NONE;

fun dropImpl s =
     case String.tokens (equal #".") s
      of [x,"i"] => SOME x
       | [x,"impl"] => SOME x
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
       => mk_fncall("","event",[VarExp s])
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
       => let val pkg = dropString (assoc "packageName" alist) handle _ => "?"
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
       => (case jarr
            of AList[("kind", String"IndicesExpr"),("array",jarr1)]
                => mk_fncall ("","Array_Forall_Indices",
                              [VarExp bvarname, dest_exp jarr1, dest_exp jexp])
            | _ => mk_fncall ("","Array_Forall",
                              [VarExp bvarname, dest_exp jarr, dest_exp jexp]))
   | AList [("kind", String "ExistsExpr"),
            ("binding", String bvarname),
            ("array", jarr),
            ("expr", jexp)]
       => (case jarr
            of AList[("kind", String"IndicesExpr"),("array",jarr1)]
                => mk_fncall ("","Array_Exists_Indices",
                              [VarExp bvarname, dest_exp jarr1, dest_exp jexp])
            | _ => mk_fncall ("","Array_Exists",
                              [VarExp bvarname, dest_exp jarr, dest_exp jexp]))
   | AList [("kind", String "FlatmapExpr"),
            ("binding", String bvarname),
            ("array", jarr),
            ("expr", jexp)]
       => (case dest_exp jexp
            of ArrayExp [elt] =>
                mk_fncall ("","Array_Tabulate",[VarExp bvarname, dest_exp jarr, elt])
             | exp => mk_fncall ("","Array_Flatmap",
                                 [VarExp bvarname, dest_exp jarr, exp]))
   | AList [("kind", String "ArrayLiteralExpr"),
            ("elems", List elist)]
       => ArrayExp (map dest_exp elist)
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
       => mk_fncall("","pre",[dest_exp e])
   | AList [("kind", String "RealCast"), ("expr", e)]
       => mk_fncall("","int_to_real",[dest_exp e])
   | AList [("kind", String "GetPropertyExpr"), ("property", String pname),_]
     => mk_fncall("","getProperty",[VarExp pname])
   | AList [("kind", String "IndicesExpr"), ("array", e)]
     => dest_exp e
   | AList [("kind", String "FoldLeftExpr"),
            ("binding", e1), ("array", e2), ("accumulator",e3), ("initial",e4), ("expr",e5)]
     => (case e2
          of AList[("kind", String"IndicesExpr"),("array",arr)]
               => mk_fncall ("","Array_Foldl_Indices",
                     [VarExp (dropString e1), VarExp (dropString e3), dest_exp e5,
                      dest_exp arr, dest_exp e4])
           | _ => mk_fncall("","Array_Foldl",
                     [VarExp (dropString e1), VarExp (dropString e3), dest_exp e5,
                      dest_exp e2, dest_exp e4]))
   | AList [("kind", String "FoldRightExpr"),
            ("binding", e1), ("array", e2), ("accumulator",e3), ("initial",e4), ("expr",e5)]
     => (case e2
          of AList[("kind", String"IndicesExpr"),("array",arr)]
               => mk_fncall ("","Array_Foldr_Indices",
                     [VarExp (dropString e1), VarExp (dropString e3), dest_exp e5,
                      dest_exp arr, dest_exp e4])
           | _ => mk_fncall("","Array_Foldr",
                     [VarExp (dropString e1), VarExp (dropString e3), dest_exp e5,
                      dest_exp e2, dest_exp e4]))
| other => raise ERR "dest_exp" "unexpected expression form"
and
mk_field (fname,e) = (fname, dest_exp e);

fun dest_param param =
 case param
  of AList [("name", String pname), ("type", ty)] => (pname,dest_ty ty)
   | otherwise => raise ERR "dest_param" "unexpected input";

fun mk_fun_def compName json =
 let fun dest_binds binds =
         FnDec ((compName,dropString (assoc "name" binds)),
                 map dest_param (dropList (assoc "args" binds)),
                dest_ty (assoc "type" binds),
                dest_exp (assoc "expr" binds))
         handle _ => raise ERR "mk_fun_def" "unexpected format"
     fun dest_uninterp_binds binds =
       let val fname = dropString (assoc "name" binds)
           val args = map dest_param (dropList (assoc "args" binds))
       in
         FnDec ((compName,fname),args,
                dest_ty (assoc "type" binds),
                Fncall(("FFI",fname),map (VarExp o fst) args))
       end handle _ => raise ERR "mk_fun_def" "unexpected format"
 in
   case json
    of AList (("kind", String "FnDef")::binds) => dest_binds binds
     | AList (("kind", String "UninterpretedFnDef")::binds) =>
           dest_uninterp_binds binds
     | otherwise => raise ERR "mk_fun_def" "unexpected function kind"
 end;

fun mk_const_def compName json =
 case json
  of AList [("kind", String "ConstStatement"),
            ("name", String cname),
            ("type", ty),
            ("expr", body)] => ConstDec((compName,cname), dest_ty ty, dest_exp body)
  |  otherwise => raise ERR "mk_const_def" "unexpected input";

fun mk_def compName features dec =
  mk_const_def compName dec    handle HOL_ERR _ =>
  mk_fun_def compName dec      handle HOL_ERR _ =>
  raise ERR "mk_def" "unexpected syntax";

fun get_annex_stmts (AList alist) =
    (case (assoc "name" alist,
           assoc "parsedAnnexLibrary" alist
            handle _ =>
           assoc "parsedAnnexSubclause" alist)
      of (String "Agree", AList [("statements", List decls)]) => decls
       | (String "agree", AList [("statements", List decls)]) => decls
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

*)

fun propName prop = dropString(name_of prop)
fun propValue prop = value_of (value_of prop) handle _ => value_of prop

(*
fun is_filter props =
 let fun isaFilter prop =
     (propName prop = "CASE_Properties::Filtering"
      orelse
      mem (propName prop)
          ["CASE_Properties::Component_Type", "CASE_Properties::COMP_TYPE"]
      andalso
      mem (dropString(propValue prop)) ["FILTER","Filtering"]) handle _ => false
 in exists isaFilter props
 end

fun is_monitor props =
 let fun isaMon prop =
      (propName prop = "CASE_Properties::Monitoring"
       orelse
       propName prop = "CASE_Properties::Gating"
       orelse
       mem (propName prop)
           ["CASE_Properties::Component_Type","CASE_Properties::COMP_TYPE"]
       andalso
       mem (dropString(propValue prop))
           ["MONITOR","Monitoring","Gating"]) handle _ => false
 in exists isaMon props
 end
*)

fun is_cyber_gadget props =
 let fun isaGadget prop =
      (propName prop = "CASE_Properties::Monitoring"
       orelse
       propName prop = "CASE_Properties::Gating"
       orelse
       propName prop = "CASE_Properties::Filtering"
       orelse
       mem (propName prop)
           ["CASE_Properties::Component_Type","CASE_Properties::COMP_TYPE"]
       andalso
       mem (dropString(propValue prop))
           ["MONITOR","Monitoring","GATE","Gating","FILTER","Filtering"])
           handle _ => false
 in exists isaGadget props
 end

(*---------------------------------------------------------------------------*)
(* compName is of the form "<pkgName>::<actual_compName>", so futz around to *)
(* get the name into the form "<pkgName>__<actual_compName". Monitors and    *)
(* filters, and their associated definitions, are handled elsewhere.         *)
(*---------------------------------------------------------------------------*)

val futz = String.map (fn ch => if ch = #":" then #"_" else ch)

fun mk_comp_defs comp =  (* annex inside package component *)
 case comp
  of AList alist =>
     let val compName = dropString (assoc "name" alist) handle _ => ""
         val compName' = futz compName
         val features = dropList (assoc "features" alist) handle _ => []
         val properties = dropList (assoc "properties" alist) handle _ => []
         val annexes = dropList (assoc "annexes" alist)
     in if is_cyber_gadget properties then
           raise ERR "mk_comp_defs"
          "treating filter, monitor, and gate declarations specially"
        else List.concat(map (mk_annex_defs compName' features) annexes)
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

val null_ty = NamedTy("","--NullTy--");
fun is_null_ty ty = eqTy(null_ty,ty);

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
     => RecdDec(dest_qid (Option.valOf (dropImpl name_impl)),[]) (* no fields *)
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
   | (_, RecdDec(_,flds)) => exists (ty_occurs (NamedTy (tydec_qid tydec1))) (map snd flds)
   | (_, ArrayDec(_,ty)) => ty_occurs (NamedTy (tydec_qid tydec1)) ty
   | (_, UnionDec(_,ctrs)) => exists (ty_occurs (NamedTy (tydec_qid tydec1))) (map snd ctrs)
;

val sort_tydecs = topsort tydec_usedBy;

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
 let val datacomps = filter is_data_comp complist
     val uqids = union_qids datacomps
     val udecs = mapfilter (union_decl uqids) datacomps
     val comps0 = drop_seen_comps uqids datacomps
     val (enum_decs,comps1) = enum_decls comps0 ([],[])
     val eqids = map tydec_qid enum_decs
     val comps2 = drop_seen_comps eqids comps1
     val aqids = mapfilter (tydec_qid o array_decl) comps2
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

fun get_contract_port port =
 case port
  of AList [("name", String pname),
            ("kind", String conn_style),
            ("classifier", classif),
            ("direction", String flowdir)]
      => let val ty = (case classif
                        of Null => dest_tyqid "Bool" (* why is Null there? *)
                         | String tyqidstring => dest_tyqid tyqidstring
                         | other => raise ERR "get_contract_port" "unexpected type")
          in (pname,ty,flowdir,conn_style)
          end
   | otherwise => raise ERR "get_contract_port" "unexpected port format"


fun get_latched properties =
 let fun getLatch prop =
       if dropString(name_of prop) = "CASE_Properties::Monitor_Latched"
        then dropBool (value_of (value_of prop))
        else raise ERR "get_latched" "expected Monitor_Latched property"
 in tryfind getLatch properties
 end

fun dest_eq_or_property_stmt (AList alist) =
 (case assoc "kind" alist
   of String "EqStatement" =>
            (case (assoc "left" alist, assoc "expr" alist)
              of (List [AList LHS], e) =>
                  let val eqName = dropString(assoc "name" LHS)
                      val lhs_ty = dest_ty (assoc "type" LHS)
                  in (eqName,lhs_ty,dest_exp e)
                  end
               |  otherwise => raise ERR "dest_eq_or_property_stmtm" "")
    | String "PropertyStatement" =>
            (case (assoc "name" alist, assoc "expr" alist)
              of (name,e) =>
                  let val eqName = dropString name
                  in (eqName,boolTy,elim_imp (dest_exp e))
                  end)
    |  otherwise => raise ERR "dest_eq_or_property_stmtm" "")
  | dest_eq_or_property_stmt any_other_thing =
    raise ERR "dest_eq__or_property_stmt" "unexpected syntax"
;

(*---------------------------------------------------------------------------*)
(* Takes a "code guarantee" and categorizes it. There are 3 possible forms   *)
(* expected for a code guarantee, depending on the output port type.         *)
(*                                                                           *)
(*  1. Event port. The expected form is                                      *)
(*                                                                           *)
(*       event(port) = exp                                                   *)
(*                                                                           *)
(*     This indicates that port is an event port and it will be set (or not) *)
(*     according to the value of exp, which is boolean. Returns              *)
(*                                                                           *)
(*       Out_Event_Only(port,exp).                                           *)
(*                                                                           *)
(*                                                                           *)
(*  2. Data port. The expected form is                                       *)
(*                                                                           *)
(*       port = exp                                                          *)
(*                                                                           *)
(*     This indicates that port is a data port and that the value of exp     *)
(*     will be written to it. Returns                                        *)
(*                                                                           *)
(*        Out_Data(port,exp).                                                *)
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
(*     have an event by event(-) checks in computed in exp1. Returns         *)
(*                                                                           *)
(*       Out_Event_Data(port,exp1,exp2).                                     *)
(*                                                                           *)
(* In all of 1,2,3, the expressions should not mention any output ports,     *)
(* i.e. the value to be sent out is determined by a computation over input   *)
(* ports and state variables only.                                           *)
(*---------------------------------------------------------------------------*)

fun outdecName (Out_Data (s,_,_)) = s
  | outdecName (Out_Event_Only(s,_,_)) = s
  | outdecName (Out_Event_Data (s,_,_,_)) = s;

fun outdecTy (Out_Data (s,ty,_)) = ty
  | outdecTy (Out_Event_Only(s,ty,_)) = ty
  | outdecTy (Out_Event_Data (s,ty,_,_)) = ty;

fun is_not_event p e =
  case e of
    Unop(Not,Fncall(("","event"),[VarExp p1])) => p = p1
  | otherwise => false;

fun mk_outdec otyEnv codeG =
 let fun port_type pname =
        assoc pname otyEnv handle _ =>
        raise ERR "mk_outdec" (Lib.quote pname^" not found in output ports")
in
 case codeG
  of Binop(Equal,VarExp p,e)
       => Out_Data(p,port_type p, e)
   | Binop(Equal,Fncall(("","event"),[VarExp p]),e)
       => Out_Event_Only(p,port_type p, e)
   | Binop other => raise ERR "mk_outdec" "unexpected syntax in equality exp"
   | Fncall(("","IfThenElse"),[b,e1,e2]) =>
      (case e1
        of Binop(And,Fncall(("","event"),[VarExp p]),
                     Binop(Equal,VarExp p1,exp))
           => (if p=p1 andalso is_not_event p e2 then
	         Out_Event_Data(p,port_type p, b,exp)
               else raise ERR "mk_outdec"
	         "unexpected syntax when looking for event-data output spec(1)")
         | otherwise => raise ERR "mk_outdec"
	         "unexpected syntax when looking for event-data output spec(2)")
   | otherwise => raise ERR "mk_outdec" "unexpected syntax"
 end;

fun mk_codeG otyEnv (s1,s2,e) = (s1,s2,mk_outdec otyEnv e);

fun dest_assume_stmt stmt =
 if dropString (kind_of stmt) = "AssumeStatement" then
     ((dropString (name_of stmt) handle _ => "",
      label_of stmt,
      dest_exp(expr_of stmt))
     handle _ => raise ERR "dest_assume_stmt" "unexpected syntax")
 else raise ERR "dest_assume_stmt" "unexpected syntax"
;

fun dest_guar_stmt stmt =
 if dropString (kind_of stmt) = "GuaranteeStatement" then
     ((dropString (name_of stmt) handle _ => "",
      label_of stmt,
      dest_exp(expr_of stmt))
     handle _ => raise ERR "dest_guar_stmt" "unexpected syntax")
 else raise ERR "dest_guar_stmt" "unexpected syntax"
;

fun mk_oty_env ports =
 let fun dest_oport (n,ty,dir,k) = if dir = "out" then (n,ty) else failwith""
 in mapfilter dest_oport ports
 end

fun check_outdecs_cover_oports cgs ports =
 let fun oportName (n,ty,dir,k) = if dir = "out" then n else failwith""
     val opnames = mapfilter oportName ports
     val outdecNames = map (fn (_,_,cg) => outdecName cg) cgs
 in
    if length opnames = length outdecNames andalso
       set_eq opnames outdecNames
    then ()
    else raise ERR "check_outdecs_cover_oports"
         "mismatch between output port names and code guarantees"
 end

fun is_pure_dec json =
  let val id = dropString(kind_of json)
  in mem id ["ConstStatement","FnDef","UninterpretedFnDef"]
  end
  handle HOL_ERR _ => false;

fun get_agree_annex caller comp =
  case dropList (annexes_of comp)
   of [x] => x
    | otherwise => raise ERR caller "unexpected annex structure";

fun get_code_contract comp =
 let val properties = dropList(properties_of comp)
     val _ = if is_cyber_gadget properties then ()
             else raise ERR "get_cyber_gadget"
              "unable to find {Filtering, Monitoring, Gating} property"
     val is_latched = get_latched properties
                      handle _ => false (* might not be an alert line *)
     val qid = dest_qid (dropString (name_of comp))
     val (pkgName,thrName) = qid
     val ports = map get_contract_port(dropList (features_of comp))
     val stmts = get_annex_stmts (get_agree_annex "get_code_contract" comp)
     val (pdecs,others) = List.partition is_pure_dec stmts
     val tydecs = []  (* todo ... *)
     val tmdecs = map (mk_def pkgName []) pdecs  (* consts and fndecs *)
     val vardecs = mapfilter dest_eq_or_property_stmt others
     val assums = mapfilter dest_assume_stmt others
     val guardecs = mapfilter dest_guar_stmt others
     val otyEnv = mk_oty_env ports
     val outdecs = mapfilter (mk_codeG otyEnv) guardecs
     val _ = check_outdecs_cover_oports outdecs ports
     val otherGs = filter (not o can (mk_codeG otyEnv)) guardecs
 in
   ContractDec
     (qid, "Code Contract", ports, is_latched,
      tydecs, tmdecs, vardecs, outdecs, assums, otherGs)
 end
 handle e => raise wrap_exn "get_code_contract" "unexpected syntax" e
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
            val code_contracts = mapfilter get_code_contract complist
        in
           (pkgName,(tydecls,annex_fndecls@comp_fndecls,code_contracts))
        end
   | AList (("name", String pkgName) ::
            ("kind", String "PropertySet") ::
            ("propertyConstants", List pconsts) :: _)
     => let val const_decls = mapfilter dest_propertyConst pconsts
        in (pkgName,([], const_decls, []))
        end
   | AList (("name", String pkgName) :: _) => (pkgName,([], [], []))
   | otherwise => raise ERR "scrape" "unexpected format"

fun dest_with ("with", List wlist) = map dropString wlist
  | dest_with other = raise ERR "dest_with" "";

fun uptoWith string lo hi =
  print
   (String.concat
     ["val [", String.concatWith ","
            (map (fn i => string^Int.toString i) (upto lo hi)),
     "] = \n"]);

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

comp9 is attestationGate
*)

(*---------------------------------------------------------------------------*)
(* For any declaration of a partial record type, one with a field with form  *)
(*                                                                           *)
(*   name : null;                                                            *)
(*                                                                           *)
(* there should be a later declaration of a new type that completes that     *)
(* field, giving a replacement type for null. When the map to HOL happens,   *)
(* the null field in the original record type is replaced by a type variable.*)
(*---------------------------------------------------------------------------*)

fun dest_recd_dec (RecdDec args) = args
  | dest_recd_dec other = raise ERR "dest_recd_dec" ""

fun replace_null_fields declist =
 let fun has_null tydec =
      case tydec
       of RecdDec (qid,flds) => exists (fn (s,ty) => eqTy(ty,null_ty)) flds
        | otherwise => false
     fun lift_nulls (s, (tydecs,_,_)) = filter has_null tydecs
     val partial_decs = map dest_recd_dec (List.concat (map lift_nulls declist))
     fun refine pdec module =
       let val (oqid,oflds) = pdec
           val (pkgName, (tydecs,tmdecs,cdecs)) = module
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
         (pkgName, (tydecs',tmdecs,cdecs))
       end
     fun refine_modules pdec decs = map (refine pdec) decs
 in
   itlist refine_modules partial_decs declist
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

fun extend_recd_decs (pkgName,(tydecs,fndecs,cdecs)) =
 let val recd_assoc_list = mapfilter dest_recd_dec tydecs
     val recdMap = Redblackmap.fromList qid_compare recd_assoc_list
     val (recdMap',tydecs') = rev_itlist extend_recd tydecs (recdMap,[])
 in
   (pkgName,(rev tydecs',fndecs,cdecs))
 end;

fun empty_recd (RecdDec(qid,[])) = true
  | empty_recd otherwise = false

fun empty_pkg (_,(tydecs,[],[])) = List.all empty_recd tydecs
  | empty_pkg otherwise = false;

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
          val modlist' = replace_null_fields modlist
          val modlist'' = map extend_recd_decs modlist'
          val modlist''' = filter (not o empty_pkg) modlist''
      in modlist'''
      end
 in
    case json
     of List pkgs => run pkgs
      | AList alist => run (dropList (assoc "modelUnits" alist))
      | otherwise => raise ERR "scrape_pkgs" "unexpected format"
 end

fun called_by (FnDec((_,id),_,_,_)) (FnDec(_,_,_,exp)) =
      mem id (map snd (AST.exp_calls [exp] []))
  | called_by (FnDec((_,id),_,_,_)) (ConstDec (_,_,exp)) =
      mem id (map snd (AST.exp_calls [exp] []))
  | called_by (ConstDec((_,id),_,_)) (FnDec (_,_,_,exp)) = mem id (expIds exp [])
  | called_by (ConstDec((_,id),_,_)) (ConstDec (_,_,exp)) = mem id (expIds exp []);

fun sort_tmdecs list = topsort called_by list;


fun mk_tyE pkglist =
 let fun tydecs_of (pkgName,(tys,consts,contracts)) = tys
     val all_tydecs = List.concat (map tydecs_of pkglist)
     fun mk_tydec_bind tydec = (tydec_qid tydec,tydec_to_ty tydec)
     val tydec_alist = map mk_tydec_bind all_tydecs
 in assocFn tydec_alist
 end

fun tmdecs_of_contract
   (ContractDec (qid,s,ports,b,tydecs,tmdecs,
                 vardecs,outdecs,assums,guars)) = tmdecs;

fun cdecs_of (pkgName,(tys,tmdecs,contracts)) =
 let fun contract_consts contract =
          filter is_const_dec (tmdecs_of_contract contract)
 in
  List.concat
    (filter is_const_dec tmdecs :: map contract_consts contracts)
 end;

fun mk_constE pkglist =
 let val all_cdecs = List.concat (map cdecs_of pkglist)
     val all_const_decs = filter is_const_dec all_cdecs
     fun mk_const_bind (ConstDec(qid,ty,e)) = (snd qid,ty)
       | mk_const_bind otherwise = raise ERR "mk_constE" "expected a ConstDec"
     val alist = map mk_const_bind all_const_decs
 in assocFn alist
 end

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

(*
fun uses (A as AList (("name", String AName) ::
                           ("kind", String "AadlPackage") ::
                           ("public", AList publist):: _))
              (B as AList (("name", String BName) :: _)) =
          let val Auses = List.concat (mapfilter dest_with publist)
          in mem BName Auses
          end
       | uses other wise = false

val pkgs0 =
  case jpkg
   of List pkgs => pkgs
    | AList alist => dropList (assoc "modelUnits" alist)

val opkgs = rev (topsort uses pkgs0)
val [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7,pkg8,pkg9,pkg10,pkg11,pkg12,pkg13,pkg14,pkg15,
     pkg16,pkg17,pkg18,pkg19,pkg20,pkg21] = opkgs;

val modlist = mapfilter scrape
    [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7,pkg8,pkg9,pkg10,pkg11,pkg12,pkg13,pkg14];

scrape pkg9;
scrape pkg10;

val modlist = mapfilter scrape opkgs
val modlist' = replace_null_fields modlist
val modlist'' = map extend_recd_decs modlist'
val modlist''' = filter (not o empty_pkg) modlist''

*)

end
