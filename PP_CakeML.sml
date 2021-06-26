structure PP_CakeML :> PP_CakeML =
struct

open Lib Feedback MiscLib PPfns AST AADL;

type contig = ByteContig.contig;
type tyenvs = (id -> ty) * (qid -> ty) *  (qid -> ty)
type port = string * ty * string * string
type ivar = string * ty * exp
type guar = string * string * exp;

val ERR = mk_HOL_ERR "PP_CakeML";
fun unimplemented s = ERR s "unimplemented";

fun pp_qid ("",s) = s
  | pp_qid (s1,s2) = String.concat[s1,".",s2];

fun qid_string p = pp_qid p;

fun pp_pkg_qid pkgName (qid as (pkg,s)) =
 if pkg = "" then pp_qid qid else
 if pkgName="Defs" then pp_qid ("",s) else pp_qid ("Defs",s);

(*fun pp_pkg_qid pkgName (pkg,s) =
    if pkg=pkgName then pp_qid ("",s) else pp_qid (pkg,s);
 *)

fun AppExp elist = Fncall(("","App"), elist);
fun listLit elts = Fncall(("","List"), elts);
fun mk_tuple elts = Fncall(("","Tuple"), elts);
val boolTy = BaseTy BoolTy;
val dummyTy = NamedTy("","dummyTy");
fun mk_ite(b,e1,e2) = Fncall(("","IfThenElse"),[b,e1,e2]);
fun mk_assignExp v e = Fncall(("","AssignExp"),[v,e]);

fun letExp binds exp =
    let val eqs = map (fn (a,b) => Binop(Equal,a,b)) binds
    in Fncall(("","LET"),eqs@[exp])
    end;

(*---------------------------------------------------------------------------*)
(* Translate contig types into AST expressions                               *)
(*---------------------------------------------------------------------------*)

fun atom_to_exp atm =
 let open ByteContig
     fun mkC s = AST.ConstExp (AST.IdConst("",s))
 in case atm
     of Bool => mkC "bool"
      | Char => mkC "char"
      | Float => mkC "f32"
      | Double => mkC "f64"
      | Signed n => mkC ("i"^Int.toString (n * 8))
      | Unsigned n => mkC("u"^Int.toString (n * 8))
      | Blob => mkC"Blob"
 end

fun contig_to_exp decEnv contig =
 let open ByteContig
 in case contig
     of Void => ConstExp (IdConst("ByteContig","Void"))
      | Basic atm => atom_to_exp atm
      | Declared s => contig_to_exp decEnv (assoc s decEnv)
      | Raw (intLit n) => Fncall(("","mk_Raw"),[mk_uintLit n])
      | Raw other => raise ERR "contig_to_exp" "Raw expects integer literal"
      | Array (c,intLit n) =>
        Fncall(("","mk_Array"), [contig_to_exp decEnv c, mk_uintLit n])
      | Array other => raise ERR "contig_to_exp" "Array expects integer literal dimenstion"
      | Recd fields =>
         let fun mk_field(s,c) =
              mk_tuple [ConstExp (StringLit s),contig_to_exp decEnv c]
         in Fncall(("","mk_Recd"),[listLit(map mk_field fields)])
         end
      | Union choices => raise ERR "contig_to_exp" "Union not yet handled"
      | Assert b => raise ERR "contig_to_exp" "Assert not yet handled"
 end

(*---------------------------------------------------------------------------*)
(* CakeML Prettyprinters for AST                                             *)
(*---------------------------------------------------------------------------*)

fun base_ty_name BoolTy   = "bool"
  | base_ty_name CharTy   = "char"
  | base_ty_name StringTy = "string"
  | base_ty_name FloatTy  = "Double.double"
  | base_ty_name DoubleTy  = "Double.double"
  | base_ty_name (IntTy _) = "int"

fun pp_cake_ty depth pkgName ty =
 let open PolyML
 in if depth = 0 then PrettyString "<ty>"
   else
   case ty
    of BaseTy bty => PrettyString (base_ty_name bty)
     | NamedTy nty => PrettyString (pp_pkg_qid pkgName nty)
     | ArrayTy(eltype,dims) =>
         PrettyBlock(2,true,[],
            [PrettyString"(",
             pp_cake_ty (depth-1) pkgName eltype,
             PrettyBreak (1,0), PrettyString "array)"])
     | RecdTy(qid,fields) =>
       let fun pp_field(s,ty) = PrettyBlock(2,true,[],
                 [PrettyString s, Space, PrettyString ": ",
                  pp_cake_ty (depth-1) pkgName ty])
       in PrettyBlock(3,true,[],
           [PrettyString ("("^qid_string qid^")"), Line_Break,
            PrettyString "{",
            PrettyBlock(1,true,[],
                 [pp_list_with_style false Line_Break [emptyBreak] pp_field fields]),
            PrettyString"}"])
       end
 end

(*---------------------------------------------------------------------------*)
(* The pkgName parameter is used to suppress printing of the current package *)
(* name when inside the package. The env parameter is used to help compute   *)
(* types so that different code can be generated for ints and floats.        *)
(*---------------------------------------------------------------------------*)

fun stub _ = raise ERR"triv_env" "";

val triv_env = (stub,stub,stub);

fun ty_of env = Lib.total (AST.expTy env);

fun is_float env e =
 case ty_of env e
   of SOME (BaseTy FloatTy) => true
    | SOME (BaseTy DoubleTy) => true
    | otherwise => false;

fun pp_cake_exp depth pkgName env exp =
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
      | ConstExp (FloatLit r) =>
          if Real.sign r < 0 then
            PrettyString (String.concat
              ["(Double.~(Double.fromString ",
               Lib.quote (Real.toString (Real.abs r)), "))"])
          else
            PrettyString (String.concat
              ["(Double.fromString ", Lib.quote (Real.toString r), ")"])
      | Unop(Not,e) => PrettyBlock(2,true,[],
           [PrettyString"not",PrettyBreak(0,1),
            PrettyString"(",pp_cake_exp (depth-1) pkgName env e,PrettyString")"])
      | Unop(UMinus,ConstExp(FloatLit r)) =>
           PrettyString (String.concat
              ["(Double.~(Double.fromString ",
               Lib.quote (Real.toString (Real.abs r)), "))"])
      | Unop(UMinus,ConstExp(IntLit{value,...})) => PrettyString ("~"^Int.toString value)
      | Unop(UMinus,e) =>
         if is_float env e then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.~"),[e]))
         else
           PrettyBlock(2,true,[],
            [PrettyString"~(", pp_cake_exp (depth-1) pkgName env e, PrettyString")"])
      | Binop(Or,e1,e2) => pp_infix depth pkgName env ("orelse",e1,e2)
      | Binop(And,e1,e2) => pp_infix depth pkgName env ("andalso",e1,e2)
      | Binop(Equal,e1,e2) => pp_infix depth pkgName env ("=",e1,e2)
      | Binop(NotEqual,e1,e2) => pp_infix depth pkgName env ("<>",e1,e2)
      | Binop(Greater,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.>"),[e1,e2]))
         else
            pp_infix depth pkgName env (">",e1,e2)
      | Binop(GreaterEqual,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.>="),[e1,e2]))
         else
            pp_infix depth pkgName env (">=",e1,e2)
      | Binop(Less,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.<"),[e1,e2]))
         else
            pp_infix depth pkgName env ("<",e1,e2)
      | Binop(LessEqual,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.<="),[e1,e2]))
         else
            pp_infix depth pkgName env ("<=",e1,e2)
      | Binop(Minus,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.-"),[e1,e2]))
         else
            pp_infix depth pkgName env ("-",e1,e2)
      | Binop(Multiply,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.*"),[e1,e2]))
         else
            pp_infix depth pkgName env ("*",e1,e2)
      | Binop(Plus,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double.+"),[e1,e2]))
         else
            pp_infix depth pkgName env ("+",e1,e2)
      | Binop(Divide,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Double./"),[e1,e2]))
         else
             pp_cake_exp depth pkgName env (Fncall (("","Int.div"),[e1,e2]))
      | Binop(Modulo,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
           raise ERR "pp_cake_exp" "mod: not implemented for doubles"
         else
	  pp_cake_exp depth pkgName env (Fncall (("","Int.mod"),[e1,e2]))
      | Binop(Fby,e1,e2) => pp_infix depth pkgName env ("->",e1,e2)
      | ArrayExp elist =>
          pp_cake_exp depth pkgName env
              (Fncall (("","Array.fromList"),[listLit elist]))
      | ArrayIndex(A,dims) =>
         let fun trans exp [] = exp
               | trans exp (d::dims) =
                 let val dsub1 = Binop(Minus,d,mk_uintLit 1)
                 in trans (Fncall (("","Array.sub"),[exp,dsub1])) dims
                 end
         in pp_cake_exp depth pkgName env (trans A dims)
         end
      | Fncall ((_,"App"),elist) =>
         if null elist then PrettyString "<APP(empty)>"
         else
          PrettyBlock(2,false,[],
           [PrettyString"(",
            pp_list_with_style false Space [emptyBreak]
                   (pp_cake_exp (depth-1) pkgName env) elist,
            PrettyString")"])
      | Fncall ((_,"List"),elist) => PrettyBlock(0,true,[],
          [PrettyString"[",
            pp_list_with_style false Comma [emptyBreak]
               (pp_cake_exp (depth-1) pkgName env) elist,
            PrettyString"]"])
      | Fncall ((_,"Comment"),elist) =>
            gen_pp_list emptyString [Line_Break]
                   (pp_cake_exp (depth-1) pkgName env) elist
      | Fncall ((_,"unitExp"),[]) => PrettyString "()"
      | Fncall ((_,"IfThenElse"),[e1,e2,e3]) =>
          PrettyBlock(2,true,[],
            [PrettyString"if ", pp_cake_exp (depth-1) pkgName  env e1,
             PrettyString" then", Space,
             pp_cake_exp (depth-1) pkgName  env e2, Space,
             PrettyString"else ", pp_cake_exp (depth-1) pkgName env e3])
      | Fncall ((_,"LET"),eqlist) =>
	let val (binds,res) = front_last eqlist
        in PrettyBlock(5,true,[],
              [PrettyString"let ",
               PrettyBlock(0,true,[],
                 [gen_pp_list emptyString [Line_Break]
                    (pp_valbind (depth-1) pkgName env) binds]),
               Space, PrettyString"in",
               Space, pp_cake_exp (depth-1) pkgName env res,
               Line_Break, PrettyString "end"])
	end
      | Fncall(("","raise"),list) =>
         PrettyBlock(2,true,[],
              [PrettyString"raise ",
               gen_pp_list emptyString [Line_Break]
                      (pp_cake_exp (depth-1) pkgName env) list])
      | Fncall ((_,"CASE"),elist) =>
        if length elist < 2 then
           PrettyString "<MALFORMED CASE EXPRESSION>"
        else
	let fun dest_clause exp =
		case exp
                 of Fncall(("","App"),[e1,e2]) => (e1,e2)
                  |  otherwise  =>  raise ERR "pp_cake_exp" "CASE badly formed"
            val scrutinee = hd elist
            val clauses = enumerate 1 (map dest_clause (tl elist))
        in PrettyBlock(3,true,[],
              [PrettyString"case ", pp_cake_exp (depth-1) pkgName env scrutinee,
               Line_Break,
               PrettyBlock(0,true,[],
                 [gen_pp_list emptyString [Line_Break]
                      (pp_case_clause (depth-1) pkgName env) clauses])])
	end
      | Fncall(("","Tuple"),list) =>
          if null list then
            PrettyString "()"
          else if length list = 1 then
             pp_cake_exp (depth-1) pkgName env (hd list)
          else PrettyBlock(1,false,[],
                 List.concat [[PrettyString "("],
                  iter_pp Comma [emptyBreak] (pp_cake_exp (depth-1) pkgName env) list,
                  [PrettyString")"]])
      | Fncall(("","Lambda"),list) =>
         (case list
           of [v,e] =>
                PrettyBlock(2,true,[],
                  [PrettyString"(fn ", pp_cake_exp (depth-1) pkgName env v,
		   PrettyString" =>", Space,
                   pp_cake_exp (depth-1) pkgName env e,
                   PrettyString")"])
            | otherwise => PrettyString "!!<Lambda-as-Fncall needs 2 args>!!")
      | Fncall(("","Array_Forall"),list) =>
         (case list
           of [v,arry,P] =>
                pp_cake_exp (depth-1) pkgName env
                   (Fncall(("","Array.all"), [Fncall(("","Lambda"),[v,P]),arry]))
            | otherwise => PrettyString "!!<Array_Forall needs 3 args>!!")
      | Fncall(("","Array_Exists"),list) =>
         (case list
           of [v,arry,P] =>
                pp_cake_exp (depth-1) pkgName env
                   (Fncall(("","Array.exists"), [Fncall(("","Lambda"),[v,P]),arry]))
            | otherwise => PrettyString "!!<Array_Exists needs 3 args>!!")
      | Fncall(("","AssignExp"),[v,e]) => pp_infix (depth-1) pkgName env (":=",v,e)
      | Fncall (qid,args) => PrettyBlock(2,false,[],
           [PrettyString"(",
            PrettyString(pp_pkg_qid pkgName qid), PrettyString" ",
            if null args then PrettyString "()" else
            pp_list_with_style false Space [emptyBreak]
               (pp_cake_exp (depth-1) pkgName env) args,
            PrettyString")"])
      | ConstrExp(tyqid, constr,args) =>
         PrettyBlock(2,true,[],
          if null args then
	      [PrettyString(pp_pkg_qid pkgName (fst qid,constr))]
          else
	    [PrettyString"(",
             PrettyString(pp_pkg_qid pkgName (fst qid,constr)),
             PrettyString" ",
             pp_list_with_style false Space [emptyBreak]
                 (pp_cake_exp (depth-1) pkgName env) args,
            PrettyString")"])
      | RecdExp (qid,fields) => PrettyBlock(2,true,[],
           [PrettyString("("),PrettyString(pp_pkg_qid pkgName qid), Space,
            PrettyBlock(0,false,[],
              [pp_space_list (pp_cake_exp (depth-1) pkgName env) (map snd fields)]),
            PrettyString")"])
      | RecdProj(recd,field) => PrettyBlock(0,false,[],
           [pp_cake_exp (depth-1) pkgName env recd,
            PrettyString".",PrettyString field])
      | other => PrettyString "<UNKNOWN AST NODE>!?"
  end
and pp_infix d pkgName env (str,e1,e2) =
    let open PolyML
    in PrettyBlock(2,true,[],
        [PrettyString"(",pp_cake_exp (d-1) pkgName env e1,
         Space, PrettyString str, Space,
         pp_cake_exp (d-1) pkgName env e2,PrettyString")"])
    end
and pp_valbind d pkgName env (Binop(Equal,e1,e2)) =
    let open PolyML
    in case e1
        of Fncall(("","FUN"), VarExp fName::args) =>
           PrettyBlock(5,true,[],
             [PrettyString ("fun "^fName^" "),
              gen_pp_list Space [emptyBreak] (pp_cake_exp (d-1) pkgName env) args,
              PrettyString" =", Space, pp_cake_exp (d-1) pkgName env e2])
         | otherwise =>
           case e2
             of Fncall(("","Comment"),_) => pp_cake_exp (d-1) pkgName env e2
              | _ => PrettyBlock(5,true,[],
                       [PrettyString "val ",
                        pp_cake_exp (d-1) pkgName env e1,
                        PrettyString " =", Space,
                        pp_cake_exp (d-1) pkgName env e2])
    end
  | pp_valbind _ _ _ _ = PolyML.PrettyString"!!<MALFORMED LET BINDING>!!"
and
   pp_case_clause d pkgName env (n,(e1,e2)) =
    let open PolyML
    in PrettyBlock(3,true,[],
        [if n = 1 then PrettyString "of " else PrettyString " | ",
         pp_cake_exp (d-1) pkgName env e1,
         PrettyString " =>", Space, pp_cake_exp (d-1) pkgName env e2])
    end
;

(*---------------------------------------------------------------------------*)
(* Translate record declarations to datatype declarations. Generate          *)
(* projection function declarations for each field of each record. This      *)
(* supports CakeML code generation.                                          *)
(*---------------------------------------------------------------------------*)

fun pp_tydec depth pkgName tydec =
 let open PolyML
     fun pp_datatype d (id,constrs) =
       let fun pp_constr d (id,tys) =
               PrettyBlock(3,false,[],
                  [PrettyString id,Space,
                   pp_space_list (pp_cake_ty (d-1) pkgName) tys])
              fun pp_constr_list d list =
               let fun iter [] = []
                 | iter [x] = [pp_constr (d-1) x]
                 | iter (h::t) =
                     pp_constr (d-1) h :: PrettyString" |" :: Space::iter t
               in
                 PrettyBlock(0,true,[],iter list)
                end
       in PrettyBlock(2,true,[],
            [PrettyString "datatype ", PrettyString id, PrettyString " =",
             Space,
             pp_constr_list (depth-1) constrs,
             PrettyString";"])
       end
 in
   if depth = 0 then PrettyString "<decl>"
   else
   case tydec
    of EnumDec(qid,enums) =>
         pp_datatype depth (snd qid, map (fn e => (e,[])) enums)
     | RecdDec(qid,fields) =>
        let val tyName = snd qid
            val tys = map snd fields
        in pp_datatype depth (tyName,[(tyName,tys)])
        end
     | UnionDec(qid,constrs) =>
        let val tyName = snd qid
            val constrs' = map (fn (id,ty) => (id, [ty])) constrs
        in pp_datatype depth (tyName, constrs')
        end
     | ArrayDec(qid,ty) =>
         PrettyBlock(0,true,[],
           [PrettyString "type ",
            PrettyString (snd qid),
            PrettyString " =", Space,
            pp_cake_ty (depth-1) pkgName ty,
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

fun recd_projFn_name tyName fieldName = "proj_"^fieldName^"_"^tyName

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
  let val gargle = pp_cake_exp 72 "<PKG>" triv_env : exp -> pretty
      val pretty = gargle exp
      val buf = ref []
      fun addbuf s = buf := s :: !buf
      val _ = PolyML.prettyPrint (addbuf,72) pretty
      val expString = String.concat (rev (!buf))
  in raise wrap_exn "PP_CakeML" ("proj_intro on expression : "^expString)  e
  end;

fun empty_varE _ = NONE;

fun assocFn alist x =
 case assoc1 x alist
  of NONE => NONE
   | SOME (a,b) => SOME b;

fun extendE env (v,u) x =
 case env x
  of SOME y => SOME y
   | NONE => if x = v then SOME u else NONE;

fun mergeE env1 env2 x =
  case env1 x
   of SOME y => SOME y
    | NONE => env2 x;

fun dest_varExp (VarExp id) = id
  | dest_varExp otherwise = raise ERR "dest_varExp" "expected a VarExp";

fun transRval E e =
 case e
  of ConstExp _ => e
   | Unop (uop,e')     => Unop(uop,transRval E e')
   | Binop (bop,e1,e2) => Binop (bop,transRval E e1, transRval E e2)
   | ArrayExp elist    => ArrayExp (map (transRval E) elist)
   | ConstrExp(qid,id,elist) => ConstrExp(qid,id,map (transRval E) elist)
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

fun transRval_decl E tmdec =
 case tmdec
  of ConstDec (qid,ty,exp)
       => ConstDec (qid,ty,transRval (E,empty_varE) exp)
   | FnDec (qid,params,ty,exp)
       => FnDec (qid,params,ty, transRval (E,assocFn params) exp)
;

(*---------------------------------------------------------------------------*)
(* Superseded by code in splat.sml                                           *)
(*---------------------------------------------------------------------------*)

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

fun cdecs_of (Pkg(pkgName,(tys,tmdecs,filters,monitors))) =
 let fun filter_consts (FilterDec(_,_,tmdecs,_,_)) =
         filter is_const_dec tmdecs
     fun monitor_consts (MonitorDec(_,_,_,tmdecs,_,_)) =
           filter is_const_dec tmdecs
 in
  List.concat
    [filter is_const_dec tmdecs,
     List.concat (map filter_consts filters),
     List.concat (map monitor_consts monitors)]
 end;

fun mk_constE pkglist =
 let val all_cdecs = List.concat (map cdecs_of pkglist)
     val all_const_decs = filter is_const_dec all_cdecs
     fun mk_const_bind (ConstDec(qid,ty,e)) = (snd qid,ty)
       | mk_const_bind otherwise = raise ERR "mk_constE" "expected a ConstDec"
     val alist = map mk_const_bind all_const_decs
 in assocFn alist
 end

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
 let fun is_recd_proj_name s = Lib.mem s ["record-projection","Record-Projection"]
 in
 case tmdec
  of FnDec(qid,[("recd", NamedTy tyqid)], ty, Fncall(("",s),var::vars)) =>
       if is_recd_proj_name s then SOME(qid,tyqid,var,vars) else NONE
   | otherwise => NONE
 end
;

fun pp_projFn depth pkgName (qid,tyqid,var,vars) =
 let open PolyML
 in if null vars then
       PrettyString "<BADLY FORMED PROJECTION FN!>"
    else
      PrettyBlock(2,true,[],
        [PrettyString "fun ",
         PrettyString (snd qid), PrettyString " recd =",Space,
         PrettyString "case recd", Line_Break,
         PrettyString "  of ", PrettyString (snd tyqid), PrettyString " ",
         pp_list_with_style false Space [emptyBreak]
                (pp_cake_exp (depth-1) pkgName triv_env) vars,
         PrettyString " => ", (pp_cake_exp (depth-1) pkgName triv_env) var,
         Semicolon])
 end;

fun pp_tmdec depth pkgName env tmdec =
 let open PolyML
     val (varE,tyE,tmE) = env
 in if depth = 0 then PrettyString "<decl>"
    else
  case tmdec
   of ConstDec (qid,ty,exp) =>
      PrettyBlock(3,true,[],
        [PrettyString "val ",
         PrettyString (snd qid),
         PrettyString " =", Space,
         pp_cake_exp (depth-1) pkgName env exp,
         Semicolon])
    | FnDec (qid,params,ty,exp) =>
       let fun pp_param (s,ty) = PolyML.PrettyString s
           fun add (id,ty) E = fn x => if x=id then ty else E(x)
           val varE' = itlist add params varE
           val env' = (varE',tyE,tmE)
       in case dest_recd_projnFn tmdec
           of NONE =>
                PrettyBlock(0,true,[],
                  [PrettyString "fun ",
                   PrettyString (snd qid), PrettyString " ",
                   if null params then PrettyString"()" else
                   gen_pp_list Space [emptyBreak] pp_param params,
                   PrettyString " =", Space,
                   pp_cake_exp (depth-1) pkgName env' exp,
                   Semicolon])
           | SOME data => pp_projFn depth pkgName data
       end
 end;


(*---------------------------------------------------------------------------*)
(* Write out :                                                               *)
(*                                                                           *)
(*   - atom_width def                                                        *)
(*   - env def                                                               *)
(*   - contig support defs                                                   *)
(*   - contig defs                                                           *)
(*   - decoder support defs                                                  *)
(*   - decoder defs                                                          *)
(*   - parser defs                                                           *)
(*---------------------------------------------------------------------------*)

val boilerplate1 = String.concatWith "\n"
 ["(*---------------------------------------------------------------------------*)",
  "(* Set up parsing environment                                                *)",
  "(*---------------------------------------------------------------------------*)",
  "\n",
  "fun atom_width atom =",
  " case atom",
  "  of ByteContig.Bool       => 1",
  "   | ByteContig.Char       => 1",
  "   | ByteContig.Float      => 4",
  "   | ByteContig.Double     => 8",
  "   | ByteContig.Signed n   => n",
  "   | ByteContig.Unsigned n => n",
  "   | other => raise Utils.ERR \"atomic_width\" \"Blob: unknown width\"",
  "\n",
  "val parseEnv =",
  "  ([],[],atom_width,ByteContig.valFnLE,ByteContig.dvalFnLE);",
  "\n",
   "fun is_event byteA =",
   "  0 < Word8Array.length byteA andalso",
   "  Word8Array.sub byteA 0 = Word8.fromInt 1;",
   "\n",
  "fun eventParse p byteA =",
  " if not(is_event byteA) then",
  "    None",
  " else",
  "  let val (contig,mk_data) = p",
  "  in case ByteContig.parseFn",
  "            parseEnv byteA (ByteContig.VarName\"root\") contig",
  "              ([],1,ByteContig.empty_lvalMap())",
  "      of Some([ptree],_,_) => Some (Utils.total mk_data ptree)",
  "       | otherwise => Some None",
  "  end;",
  "\n",
  "(*---------------------------------------------------------------------------*)",
  "(* Contig stuff                                                              *)",
  "(*---------------------------------------------------------------------------*)",
  "\n",
  "fun intLit i   = ByteContig.IntLit i;",
  "fun unsigned n = ByteContig.Basic(ByteContig.Unsigned n);",
  "fun signed n   = ByteContig.Basic(ByteContig.Signed n);",
  "fun mk_Array c n = ByteContig.Array c (intLit n);",
  "fun mk_Recd list   = ByteContig.Recd list;",
  "fun mk_Union list  = ByteContig.Union list;",
  "\n",
  "val bool = ByteContig.Basic ByteContig.Bool;",
  "val u8   = unsigned 1;",
  "val char = unsigned 1;",
  "val u16  = unsigned 2;",
  "val u32  = unsigned 4;",
  "val i32  = signed 4;",
  "val i64  = signed 8;",
  "val f32  = ByteContig.Basic(ByteContig.Float);",
  "val f64  = ByteContig.Basic(ByteContig.Double);",
  "\n"];

val boilerplate2 = String.concatWith "\n"
 [ "val mk_intLE   = ByteContig.mk_intLE;",
   "val mk_floatLE = ByteContig.mk_floatLE;",
   "val mk_array   = ByteContig.mk_array;"
 ];

fun is_in_event_data_port (name,ty,dir,kind) = (dir = "in" andalso kind = "EventDataPort");
fun is_in_data_port (name,ty,dir,kind) = (dir = "in" andalso kind = "DataPort");
fun is_in_event_port (name,ty,dir,kind) = (dir = "in" andalso kind = "EventPort");

fun pp_parser_struct (structName,inports,contig_binds,decode_decs) =
 let open PolyML
     val contig_exps = map (I##contig_to_exp []) contig_binds
     fun mk_contig_dec (qid,exp) = ConstDec (("","contig_"^snd qid),dummyTy,exp)
     val contig_decs = map mk_contig_dec contig_exps
     val in_edps = filter is_in_event_data_port inports
     val in_dps = filter is_in_data_port inports
     val in_eps = filter is_in_event_port inports
     fun mk_parseFn_dec (pName,ty,_,_) =
      case ty
       of NamedTy(_,tyName) =>
           ConstDec(("","parse_"^tyName),dummyTy,
                Fncall(("","eventParse"),
                  [mk_tuple[VarExp ("contig_"^tyName),VarExp("decode_"^tyName)]]))
        | other =>  raise ERR "pp_parser" "expected type of inport to be named"
     val parseFn_decs = map mk_parseFn_dec in_edps
     val depth = ~1
 in
    PrettyBlock(0,true,[],
        [PrettyString ("structure "^structName^" = "), Line_Break,
         PrettyString "struct", Line_Break_2,
         PrettyString boilerplate1,
         end_pp_list Line_Break Line_Break
              (pp_tmdec  (depth-1) "Parse" triv_env) contig_decs,
         Line_Break,
	 Line_Break,
         PrettyString boilerplate2,
	 Line_Break,
	 Line_Break,
         end_pp_list Line_Break Line_Break
             (pp_tmdec (depth-1) "Parse" triv_env) decode_decs,
	 Line_Break,
	 Line_Break,
         end_pp_list Line_Break Line_Break
              (pp_tmdec (depth-1) "Parse" triv_env) parseFn_decs,
	 Line_Break,
	 Line_Break,
         PrettyString "end"
      ])
 end;

fun pp_defs_struct env (structName,tydecs,tmdecs) =
 let open PolyML
     val depth = ~1
 in
    PrettyBlock(0,true,[],
        [PrettyString ("structure "^structName^" = "), Line_Break,
         PrettyString "struct", Line_Break_2,
         end_pp_list Line_Break Line_Break (pp_tydec depth "Defs") tydecs,
         Line_Break,
	 Line_Break,
         end_pp_list Line_Break Line_Break
                 (pp_tmdec depth "Defs" env) tmdecs,
	 Line_Break,
	 Line_Break,
         PrettyString "end"
      ])
 end;

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

val unitExp = Fncall(("","unitExp"),[]);
val emptyString = VarExp(Lib.quote"")

fun localFnExp (name,args,body) = (Fncall(("","FUN"),VarExp name :: args),body)

val NoneExp = ConstExp(IdConst("","None"));
fun mk_Some e = Fncall(("","Some"),[e])
fun mk_isSome e = Fncall(("","Option.isSome"),[e])
fun mk_valOf e = Fncall(("","valOf"),[e])

fun mk_boolOpt e = mk_ite(e,mk_Some unitExp,NoneExp)

fun mk_comment slist = Fncall(("","Comment"), map VarExp slist);

fun mk_ref e = Fncall(("","Ref"),[e]);
fun mk_deref e = Fncall(("","!"),[e]);
fun mk_condExp(b,e1,e2) = Fncall(("","IfThenElse"),[b,e1,e2]);

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

datatype portsy = EventData of string * ty | Data of string * ty | Event of string;

fun portname (Event s) = s
  | portname (Data(s,ty)) = s
  | portname (EventData(s,ty)) = s;

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

(*---------------------------------------------------------------------------*)
(* Looking for:                                                              *)
(*                                                                           *)
(*  event port <=> e, or                                                     *)
(*                                                                           *)
(*  if e1 then event(port) and port = e2 else not(event port)                *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun outCode_target (gName,docstring,codeG) =
 case codeG
  of Binop(Equal,e1,e2) =>
      (case e1
        of Fncall(("","event"),[VarExp p]) => p
         | VarExp p => p
         | otherwise =>
             case e2
              of Fncall(("","event"),[VarExp p]) => p
              | _ => raise ERR "outCode_target" "unexpected syntax")
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


fun mk_monFn mondec =
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
    FnDec((fst qid,"monFn"), [], dummyTy, bodyExp)
 end

val comment1 =
  mk_comment ["",
	      "(*--------------------------*)",
              "(* Compute new state values *)",
              "(*--------------------------*)",""];

val comment2 =
  mk_comment ["",
	      "(*-----------------------*)",
              "(* Compute output values *)",
              "(*-----------------------*)", ""];

fun ivar_ty (s,ty,exp) = ty;
fun ivar_name (s,ty,exp) = s;
fun port_name (s,ty,dir,kind) = s;

fun ppBind ppleft ppright =
   PrettyBlock(2,true,[],
     [PrettyString "val ", ppleft, PrettyString " =",
      Space, PrettyBlock(0,false,[], [ppright])]);

fun valBind (left,right) = ppBind (ppExp left) (ppExp right)

fun valBinds vblist = end_pp_list Line_Break Line_Break valBind vblist;

fun letBinds (binds,exp) =
   PrettyBlock(0,true,[],
     [PrettyString "let ",
      PrettyBlock(4,true,[],[valBinds binds]),
      Space, PrettyString "in", Space, PrettyString "  ",
      ppExp exp, Space,
      PrettyString "end"]);

fun ppCond(ppB,pp_e1,pp_e2) =
  PrettyBlock(0,true,[],
     [PrettyString "if ",
      PrettyBlock(0,false,[],[ppB]),
      Space, PrettyString "then", Space,
      pp_e1,
      Space, PrettyString "else", Space, pp_e2]);

val gadget_struct_boilerplate = String.concatWith "\n"
 [ "fun pre x = x;",
   "val valOf = Option.valOf;"
 ];

fun pp_gadget_struct env (structName,ports,ivars,guars) =
 let open PolyML
     val ppExp = pp_cake_exp ~1 structName env
     val depth = ~1
     val inports = filter is_in_port ports
     val eiports = filter is_event inports
     val outports = filter is_out_port ports

     val initState_dec =
       let val initStateTuple = mk_tuple(intervalWith (K NoneExp) 1 (length ivars))
           val state_tys = map ivar_ty ivars
           fun pp_ty_option ty =
             PrettyBlock(0,true,[],[pp_cake_ty ~1 "" ty, PrettyString" option"])
           val state_ty_tuple = PrettyBlock(2,true,[],
               [gen_pp_list (PrettyString " *") [Space] pp_ty_option state_tys])
       in
         PrettyBlock(2,true,[],
           [PrettyString "val ",
            pp_cake_exp ~1 "" triv_env initStateVar,
            PrettyString " =", Space,
            pp_cake_exp ~1 "" triv_env initStateTuple,
            Space, PrettyString ": ",
            state_ty_tuple,
            PrettyString ";"])
       end

     val inputBind =
       let val inTuple = mk_tuple (map (VarExp o port_name) inports)
           val inputsVar = VarExp "inputs"
       in (inTuple,inputsVar)
       end

     val stateVarExps = map (VarExp o ivar_name) ivars
     val stateVarTuple = mk_tuple stateVarExps
     val stateVars = VarExp "stateVars"
     val newStateVars = VarExp "newStateVars"

     val stepFn_dec =
       let val stateBind = (stateVarTuple,stateVars)
           val event_varBinds =
             let fun mk_event_varBind id =
                  (VarExp ("event_"^id), mk_isSome(VarExp id))
             in map (mk_event_varBind o port_name) eiports
             end
           fun split (s,ty,exp) =
             let val (e1,e2) = split_fby exp
             in ((VarExp s,e1),(VarExp s,e2))
             end
           val (initBinds,stepBinds) = unzip (map split ivars)
           val initStep_False =
             (unitExp,
              mk_assignExp (VarExp"initStep")
                           (ConstExp(BoolLit false)))
           val initExp = letBinds(initBinds @ [initStep_False],stateVarTuple)
           val step_startVals =
             (stateVarTuple,mk_tuple(map mk_valOf stateVarExps))
           val stepExp = letBinds(step_startVals::stepBinds,stateVarTuple)
           val stepBind =
             ppBind (ppExp newStateVars)
                    (ppCond(PrettyString"!initStep",initExp, stepExp))
           val reBind = (stateVarTuple, newStateVars)
           val newOpts =
             (VarExp"newStateVarOpts", mk_tuple (map mk_Some stateVarExps))

           val outBinds =
             let val outIds = map outCode_target guars
                 val outVars = map VarExp outIds
             in zip outVars (map mk_outExp guars)
             end
       in
         PrettyBlock(2,true,[],
           [PrettyString "fun stepFn inputs stateVars = ", Line_Break,
            Line_Break,
            valBinds (inputBind::stateBind::event_varBinds),
            Line_Break,
            ppExp comment1,
            stepBind,
            Line_Break,
            valBind reBind,
            Line_Break,
            valBind newOpts,
            Line_Break,
            ppExp comment2,
            Line_Break,
            valBinds outBinds
          ])
       end

(*
TextIO.print (pp_string it);
*)

     val gadgetFn_dec =
        PrettyBlock(2,true,[],
        [PrettyString (String.concat["fun ", structName, "Fn () = ()"])
         ])
 in
    PrettyBlock(0,true,[],
        [PrettyString ("structure "^structName^" = "), Line_Break,
         PrettyString "struct", Line_Break_2,
         PrettyString gadget_struct_boilerplate,
         Line_Break_2,
         initState_dec,
         Line_Break,
         PrettyString"val theState = Ref initState;",
	 Line_Break,
         PrettyString"val initStep = Ref True;",
         Line_Break_2,
         stepFn_dec,
	 Line_Break_2,
         gadgetFn_dec,
 	 Line_Break_2,
         PrettyString "end"
      ])
 end;

(*
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
*)

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
  let val NoneExp = ConstrExp(("","Option"),"None",[])
      val nexpList = map (K NoneExp) (upto 1 n)
      val Some_True_Exp = ConstrExp(("","Option"),"Some",[ConstExp(BoolLit true)])
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
(*
fun pp_monitor depth mondec =
 let val MonitorDec(qid,ports,latched,decs,ivardecs,guars) = mondec
     val stepFn = mk_mon_stepFn mondec
     val monFn = mk_monFn mondec
     val dataports = filter is_data_port ports
     val iobufdecs = map (mk_buf (fst qid)) dataports
     val infiller_dec = mk_fillFn (filter is_inport dataports)
     val stateVars_dec = mk_stateVardecs (length ivardecs)
     val decs1 = iobufdecs @ [infiller_dec,stateVars_dec] @ decs @ [stepFn,monFn]
     val decs2 = stateVars_dec :: (decs @ [stepFn])
 in
  end_pp_list Line_Break Line_Break (pp_tmdec (depth-1) (fst qid)) decs2
 end
*)

fun pp_api (structName,inbufs,fillFns,sendFns,logInfo) =
 let open PolyML
     val depth = ~1
     fun pp_inbuf d (bufName,n) =
         PrettyBlock(2,true,[],
           [PrettyString "val ", PrettyString bufName, PrettyString " = " ,
            PrettyString "Word8Array.array ", PrettyString (Int.toString n),
            PrettyString " Utils.w8zero;"
           ])
     fun pp_fillFn d (bufName,api_call) =
         PrettyBlock(2,true,[],
           [PrettyString"fun ", PrettyString ("fill_"^bufName), PrettyString " () = " ,
            Line_Break,
            PrettyBlock(0,true,[],
               [PrettyString "let val () = Utils.clear_buf ",
                PrettyString bufName, Line_Break,
                 PrettyString "in ", PrettyString api_call, Line_Break,
                 PrettyString "end;"])
           ])
     fun pp_sendFn d (portName,api_call) =
         PrettyBlock(2,true,[],
           [PrettyString"fun ", PrettyString ("send_"^portName), PrettyString " string = " ,
            PrettyString api_call
           ])
 in
    PrettyBlock(0,true,[],
        [PrettyString ("structure "^structName^" = "), Line_Break,
         PrettyString "struct", Line_Break_2,
         end_pp_list Line_Break Line_Break (pp_inbuf  depth) inbufs,  Line_Break,
	 Line_Break,
         end_pp_list Line_Break Line_Break (pp_fillFn depth) fillFns, Line_Break,
	 Line_Break,
         end_pp_list Line_Break Line_Break (pp_sendFn depth) sendFns, Line_Break,
	 Line_Break,
         PrettyString logInfo,
         Line_Break,
	 Line_Break,
         PrettyString "end"
        ])
 end

(*---------------------------------------------------------------------------*)
(* Add in projection functions, and tranform expressions with field          *)
(* projections.                                                              *)
(*---------------------------------------------------------------------------*)
(*

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
         end_pp_list Line_Break Line_Break (pp_monitor (depth-1)) monitors,      Line_Break,
         PrettyString "end"
        ])
 end
*)

val _ = PolyML.addPrettyPrinter (fn i => fn () => fn ty => pp_cake_ty i "<pkg>" ty);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn e => pp_cake_exp  i "<pkg>" triv_env e);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tydec => pp_tydec i "<pkg>" tydec);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tmdec => pp_tmdec i "<pkg>" triv_env tmdec);
(*
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn mon => pp_monitor i mon);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn pkg => pp_pkg i pkg);
*)



end (* PP_CakeML *)
