(*---------------------------------------------------------------------------*)
(* Print various info extractable from a gadget into CakeML source text.     *)
(* Note. We assume that ivar equations are sorted into dependency order.     *)
(*---------------------------------------------------------------------------*)

structure PP_CakeML :> PP_CakeML =
struct

open Lib Feedback MiscLib PPfns AST AADL;

type contig = ByteContig.contig;
type tyenvs = (id -> ty) * (qid -> ty) *  (qid -> ty)
type port = string * ty * string * string
type ivar = string * ty * exp

val ERR = mk_HOL_ERR "PP_CakeML";
fun unimplemented s = ERR s "unimplemented";

fun splice x [] = []
  | splice x [y] = [y]
  | splice x (h::t) = h::x::splice x t;

fun pp_qid ("",s) = s
  | pp_qid (s1,s2) = String.concat[s1,".",s2];

fun qid_string p = pp_qid p;

(*---------------------------------------------------------------------------*)
(* Important decisions made here. All type and fun definitions made in       *)
(* various source AADL packages and annexes are swept into the "Defs" CakeML *)
(* structure. So, when the current structure is Defs, then don't print the   *)
(* struct name.  Otherwise, if the package name is "", then that's a sign    *)
(* that a builtin of some kind is being used, and so don't print the package *)
(* name.                                                                     *)
(*                                                                           *)
(* That leaves all other cases. This means pp_pkg_qid is being invoked on    *)
(* a qid not "in" the Defs package, and it also means we aren't doing        *)
(* systemsy things, so it must mean that we are in the actual code           *)
(* specified in the gadget body, so all remaining struct names are referring *)
(* back to the Defs structure.                                               *)
(*---------------------------------------------------------------------------*)

fun pp_pkg_qid pkgName (qid as (pkg,s)) =
 if pkg = "" then
    pp_qid qid else
 if pkgName="Defs" then
    pp_qid ("",s)
 else pp_qid ("Defs",s);

val boolTy = BaseTy BoolTy;
val dummyTy = NamedTy("","dummyTy");

val unitExp = Fncall(("","unitExp"),[]);
fun mk_intLit i = ConstExp(IntLit{value=i, kind=AST.Int NONE});
fun mk_stringLit s = ConstExp(StringLit s);
fun listLit elts = Fncall(("","List"), elts);
fun mk_tuple elts = Fncall(("","Tuple"), elts);

fun mk_ite(b,e1,e2) = Fncall(("","IfThenElse"),[b,e1,e2]);
fun mk_condExp(b,e1,e2) = Fncall(("","IfThenElse"),[b,e1,e2]);
fun mk_assignExp v e = Fncall(("","AssignExp"),[v,e]);
fun mk_apiCall (s,args) = Fncall(("","API."^s),args);
fun mk_encodeCall (tyName,arg) = Fncall(("","Encode."^tyName),arg);

fun letExp binds exp =
    let val eqs = map (fn (a,b) => Binop(Equal,a,b)) binds
    in Fncall(("","LET"),eqs@[exp])
    end;

val emptyStringVar = VarExp(Lib.quote"");

fun localFnExp (name,args,body) = (Fncall(("","FUN"),VarExp name :: args),body)

val NoneExp = ConstExp(IdConst("","None"));
fun mk_Some e = Fncall(("","Some"),[e])
fun mk_isSome e = Fncall(("","Option.isSome"),[e])
fun mk_valOf e = Fncall(("","valOf"),[e])


fun mk_comment slist = Fncall(("","Comment"), map VarExp slist);

fun mk_ref e = Fncall(("","Ref"),[e]);
fun mk_deref e = Fncall(("","!"),[e]);

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
      | ConstExp (IntLit{kind,value}) => PrettyString (Int.toString value)
      | ConstExp (FloatLit r) =>
          if Real.sign r < 0 then
            PrettyString (String.concat
              ["(Utils.double_negate(Double.fromString ",
               Lib.quote (Real.toString (Real.abs r)), "))"])
          else
            PrettyString (String.concat
              ["(Double.fromString ", Lib.quote (Real.toString r), ")"])
      | Unop(Not,e) => PrettyBlock(2,true,[],
           [PrettyString"not",PrettyBreak(0,1),
            PrettyString"(",pp_cake_exp (depth-1) pkgName env e,PrettyString")"])
      | Unop(UMinus,ConstExp(FloatLit r)) =>
           PrettyString (String.concat
              ["(Utils.double_negate(Double.fromString ",
               Lib.quote (Real.toString (Real.abs r)), "))"])
      | Unop(UMinus,ConstExp(IntLit{value,...})) => PrettyString ("~"^Int.toString value)
      | Unop(UMinus,e) =>
         if is_float env e then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_negate"),[e]))
         else
           PrettyBlock(2,true,[],
            [PrettyString"~(", pp_cake_exp (depth-1) pkgName env e, PrettyString")"])
      | Binop(Or,e1,e2) => pp_infix depth pkgName env ("orelse",e1,e2)
      | Binop(And,e1,e2) => pp_infix depth pkgName env ("andalso",e1,e2)
      | Binop(Equal,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_eq"),[e1,e2]))
         else
           pp_infix depth pkgName env ("=",e1,e2)
      | Binop(Imp,e1,e2) =>
         let val node = Fncall(("","IfThenElse"),[e1,e2,ConstExp(BoolLit true)])
         in pp_cake_exp depth pkgName env node
         end
      | Binop(NotEqual,e1,e2) => pp_cake_exp depth pkgName env (Unop(Not,Binop(Equal,e1,e2)))
      | Binop(Greater,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_gt"),[e1,e2]))
         else
            pp_infix depth pkgName env (">",e1,e2)
      | Binop(GreaterEqual,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_gte"),[e1,e2]))
         else
            pp_infix depth pkgName env (">=",e1,e2)
      | Binop(Less,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_lt"),[e1,e2]))
         else
            pp_infix depth pkgName env ("<",e1,e2)
      | Binop(LessEqual,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_lte"),[e1,e2]))
         else
            pp_infix depth pkgName env ("<=",e1,e2)
      | Binop(Minus,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_sub"),[e1,e2]))
         else
            pp_infix depth pkgName env ("-",e1,e2)
      | Binop(Multiply,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_mult"),[e1,e2]))
         else
            pp_infix depth pkgName env ("*",e1,e2)
      | Binop(Plus,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_add"),[e1,e2]))
         else
            pp_infix depth pkgName env ("+",e1,e2)
      | Binop(Divide,e1,e2) =>
         if is_float env e1 orelse is_float env e2 then
             pp_cake_exp (depth-1) pkgName env (Fncall (("","Utils.double_div"),[e1,e2]))
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
            [PrettyString"(if ", pp_cake_exp (depth-1) pkgName  env e1,
             PrettyString" then", Space,
             pp_cake_exp (depth-1) pkgName  env e2, Space,
             PrettyString"else ", pp_cake_exp (depth-1) pkgName env e3,
             PrettyString")"])
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
      | Fncall(("","Array_Forall_Indices"),list) =>
         (case list
           of [v,arry,P] =>
               pp_cake_exp (depth-1) pkgName env
                    (Fncall(("","Utils.array_allI"), [Fncall(("","Lambda"),[v,P]),arry]))
            | otherwise => PrettyString "!!<Array_Forall_Indices needs 3 args>!!")
      | Fncall(("","Array_Exists_Indices"),list) =>
         (case list
           of [v,arry,P] =>
               pp_cake_exp (depth-1) pkgName env
                     (Fncall(("","Utils.array_existsI"),
                             [Fncall(("","Lambda"),[v,P]),arry]))
            | otherwise => PrettyString "!!<Array_Exists_Indices needs 3 args>!!")
      | Fncall(("","Array_Foldr"),list) =>
	 (case list
           of [eltVar,accVar,body,arry,init] =>
               let val foldFn = Fncall(("","Lambda"),[eltVar,
                                Fncall(("","Lambda"),[accVar,body])])
                   val exp = Fncall(("","Array.foldr"),[foldFn,init,arry])
               in
                 pp_cake_exp depth pkgName env exp
               end
            | otherwise => PrettyString "!!<Array_Foldr needs 5 args>!!")
      | Fncall(("","Array_Foldl"),list) =>
	 (case list
           of [eltVar,accVar,body,arry,init] =>
               let val foldFn = Fncall(("","Lambda"),[eltVar,
                                Fncall(("","Lambda"),[accVar,body])])
                   val exp = Fncall(("","Array.foldl"),[foldFn,init,arry])
               in
                 pp_cake_exp depth pkgName env exp
               end
            | otherwise => PrettyString "!!<Array_Foldl needs 5 args>!!")
      | Fncall(("","Array_Foldr_Indices"),list) =>
	 (case list
           of [eltVar,accVar,body,arry,init] =>
               let val foldFn = Fncall(("","Lambda"),[eltVar,
                                Fncall(("","Lambda"),[accVar,body])])
                   val exp = Fncall(("","Utils.array_foldrI"),[foldFn,init,arry])
               in
                 pp_cake_exp depth pkgName env exp
               end
            | otherwise => PrettyString "!!<Array_Foldr_Indices needs 5 args>!!")
      | Fncall(("","Array_Foldl_Indices"),list) =>
	 (case list
           of [eltVar,accVar,body,arry,init] =>
               let val foldFn = Fncall(("","Lambda"),[eltVar,
                                Fncall(("","Lambda"),[accVar,body])])
                   val exp = Fncall(("","Utils.array_foldlI"),[foldFn,init,arry])
               in
                 pp_cake_exp depth pkgName env exp
               end
            | otherwise => PrettyString "!!<Array_Foldl_Indices needs 5 args>!!")
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
	      [PrettyString(pp_pkg_qid pkgName (fst tyqid,constr))]
          else
	    [PrettyString"(",
             PrettyString(pp_pkg_qid pkgName (fst tyqid,constr)),
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
      | other => PretteyString "<UNKNOWN AST NODE>!?"
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

fun dest_recd_projnFn tmdec =
 let fun is_recd_proj_name s = Lib.mem s ["record-projection","Record-Projection"]
 in
 case tmdec
  of FnDec(qid,[("recd", NamedTy tyqid)], ty, Fncall(("",s),var::vars)) =>
       if is_recd_proj_name s then SOME(qid,tyqid,var,vars) else NONE
   | otherwise => NONE
 end
;

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
  "val u64  = unsigned 8;",
  "val i16  = signed 2;",
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
(*---------------------------------------------------------------------------*)

fun split_fby exp =
  case exp
   of Binop(Fby,e1,e2) => (e1,e2)
    | otherwise => (exp,exp);

val stateVal_comment =
 (VarExp "foo",
  mk_comment ["",
	      "(*--------------------------*)",
              "(* Compute new state values *)",
              "(*--------------------------*)",""]);

val outVal_comment =
 (VarExp "foo",
  mk_comment ["",
	      "(*-----------------------*)",
              "(* Compute output values *)",
              "(*-----------------------*)", ""]);

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

(*---------------------------------------------------------------------------*)
(* Map an outdec to an expression which, when eval'd, will create the value  *)
(* that will be used to make the output FFI call on the port.                *)
(*---------------------------------------------------------------------------*)

fun eventOpt e = mk_ite(e,mk_Some unitExp,NoneExp)

fun outdecExp (Out_Data(s,ty,e)) =
     Fncall(("Utils","Out_Data"),[mk_stringLit s,e])
  | outdecExp (Out_Event_Only(s,ty,b)) =
     Fncall(("Utils","Out_Event_Only"),[mk_stringLit s,b])
  | outdecExp (Out_Event_Data(s,ty,b,e)) =
     Fncall(("Utils","Out_Event_Data"),[mk_stringLit s,b,e])

(*
fun mk_outExp (Out_Data(s,ty,e)) = e
  | mk_outExp (Out_Event_Only(s,ty,b)) = eventOpt b
  | mk_outExp (Out_Event_Data(s,ty,b,e)) = mk_ite (b,mk_Some e,NoneExp)
*)

val stateVar = VarExp "state";
val initStepVar = VarExp "initStep";

fun ivar_ty (s,ty,exp) = ty;
fun ivar_name (s,ty,exp) = s;

fun ty_name ty =
 case ty
  of NamedTy(_,tyName) => tyName
   | otherwise => raise ERR "ty_name" "Expected a named type";

fun ppBind ppleft ppright =
 let open PolyML
 in
   PrettyBlock(2,true,[],
     [PrettyString "val ", ppleft, PrettyString " =",
      Space, PrettyBlock(0,false,[], [ppright])])
 end;

fun ppCond(ppB,pp_e1,pp_e2) =
 let open PolyML
 in
  PrettyBlock(0,true,[],
     [PrettyString "if ",
      PrettyBlock(0,false,[],[ppB]),
      Space, PrettyString "then", Space,
      pp_e1,
      Space, PrettyString "else", Space, pp_e2])
 end;


val gadget_struct_boilerplate = String.concatWith "\n"
 [ "fun pre x = x;",
   "val valOf = Option.valOf;"
 ];

fun pp_gadget_struct env (structName,ports,ivars,outdecs) =
 let open PolyML
     val depth = ~1
     val ppExp = pp_cake_exp depth structName env
     fun valBind (left,right) = ppBind (ppExp left) (ppExp right)
     fun valBinds vblist = end_pp_list Line_Break Line_Break valBind vblist
     fun letBinds (binds,exp) =
        PrettyBlock(0,true,[],
         [PrettyString "let ",
          PrettyBlock(4,true,[],[valBinds binds]),
          Space, PrettyString "in", Space, PrettyString "  ",
          ppExp exp, Space,
          PrettyString "end"])
     val inports = filter is_in_port ports
     val eiports = filter is_event inports
     val outports = filter is_out_port ports

     val gadgetFnId = "gadgetFn"
     val inportIds = map port_name inports
     val inportTyNames = map (ty_name o port_ty) inports

     val initState_dec =
       let val initStateTuple = mk_tuple(intervalWith (K NoneExp) 1 (length ivars))
           val state_tys = map ivar_ty ivars
           fun pp_ty_option ty =
             PrettyBlock(0,true,[],[pp_cake_ty ~1 "" ty, PrettyString" option"])
           val state_ty_tuple =
              if null ivars then
                 PrettyString "unit"
              else PrettyBlock(2,true,[],
               [gen_pp_list (PrettyString " *") [Space] pp_ty_option state_tys])
       in
         PrettyBlock(2,true,[],
           [PrettyString "val ",
            pp_cake_exp ~1 "" triv_env (VarExp"initState"),
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

     (* Output port values and alist binding vars to them *)
     val outIds = map AADL.outdecName outdecs
     val outVars = map VarExp outIds
     val outBinds = zip outVars (map outdecExp outdecs)

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

           val outTuple = mk_tuple[VarExp"newStateVarOpts",mk_tuple outVars]
       in
         PrettyBlock(2,true,[],
           [PrettyString "fun stepFn inputs stateVars = ", Line_Break,
            PrettyString"let ",
            PrettyBlock(4,true,[],
             [valBinds (inputBind::stateBind::event_varBinds), Line_Break,
              ppExp comment1, Line_Break,
              stepBind,       Line_Break,
              valBind reBind, Line_Break,
              valBind newOpts,Line_Break,
              ppExp comment2, Line_Break,
              valBinds outBinds]),
            Space,
            PrettyString "in",
            Space, PrettyString "   ", ppExp outTuple,
            Space,
            PrettyString"end"
          ])
       end

     val parseFn_decs =
       let fun inportParser_dec portId tyName = String.concat
              ["fun ", "parse_"^portId, " () =\n",
               "  let val () = API.fill_", portId, "_buffer ()\n",
               "      val inOpt2 = Parse.parse_", tyName, " API.",portId, "_buffer\n",
               "  in\n",
               "     Utils.dropOpt \"Parsing of ", portId, "port failed.\" inOpt2\n",
	       "  end;"]
           val strings = map2 inportParser_dec inportIds inportTyNames
       in
         PrettyString (String.concatWith "\n\n" strings)
       end

     val gadgetFn_dec =
       let val inportIds = map port_name inports
           val inportVars = map VarExp inportIds
           fun mk_Opt s = s^"Opt"
           fun mk_inOpt id = String.concat
                               ["val ", mk_Opt id, " = parse_", id, " ()"]
           val inOpt_decs = splice Line_Break
                              (map (PrettyString o mk_inOpt) inportIds)
           val inOptIds = map mk_Opt inportIds
           val inOptVars = map VarExp inOptIds

	   fun is_valof ("","Option.valOf") = true
             | is_valof ("","valOf") = true
             | is_valof otherwise = false

           fun pp_outdec_effect outdec =
             case outdec
	      of Out_Data(p,ty,e)
                  => ppExp (mk_apiCall("send_"^p,[mk_encodeCall(ty,e)])),
               | Out_Event_Only (p,ty,b)
                  => ppExp
                       (mk_condExp
                          (b,
                           mk_apiCall("send_"^p,[emptyStringVar]),
                           unitExp))
               | Out_Event_Data (p,ty,b,e)
                  => ppExp
                       (mk_condExp
                          (b,
                           mk_apiCall("send_"^p,[mk_encodeCall(ty,e)]),
                           unitExp))

           val spacer = PrettyBlock(0,true,[], [Line_Break, PrettyString";", Line_Break_2])
           val outputCalls =
             PrettyBlock(2,true,[], splice spacer (map pp_outdec_effect outdecs))

       in
	   PrettyBlock(2,true,[],
           [PrettyString (String.concat["fun ", gadgetFnId, "() = "]),
            Line_Break,
            PrettyString"let ",
            PrettyBlock(4,true,[],
             (inOpt_decs
               @
              [Line_Break,
               valBind (VarExp"inputs", mk_tuple inOptVars),
               Line_Break,
               PrettyString "val (newState,outputs) = stepFn inputs (!theState)",
               Line_Break,
               PrettyString "val () = (theState := newState)",
               Line_Break,
               valBind(mk_tuple outVars, VarExp"outputs")])),
            Space,
            PrettyString "in", Space,
            PrettyString"  ",
            outputCalls, Space,
            PrettyString"end", Space,
            PrettyString "handle _ => (API.logInfo \"gadgetFn: exception raised (and caught); continuing\"; ());"
          ])
       end
 in
    PrettyBlock(0,true,[],
       ([PrettyString ("structure Gadget = "), Line_Break,
         PrettyString "struct", Line_Break_2,
         PrettyString gadget_struct_boilerplate, Line_Break_2,
         initState_dec, Line_Break,
         PrettyString"val theState = Ref initState;", Line_Break,
         PrettyString"val initStep = Ref True;", Line_Break_2,
         stepFn_dec,   Line_Break_2,
         parseFn_decs, Line_Break_2,
         gadgetFn_dec, Line_Break_2,
         PrettyString "end"])
      )
 end;

val _ = PolyML.addPrettyPrinter (fn i => fn () => fn ty => pp_cake_ty i "<pkg>" ty);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn e => pp_cake_exp  i "<pkg>" triv_env e);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tydec => pp_tydec i "<pkg>" tydec);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tmdec => pp_tmdec i "<pkg>" triv_env tmdec);


end (* PP_CakeML *)
