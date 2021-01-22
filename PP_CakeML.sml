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
  | base_ty_name FloatTy  = "double"
  | base_ty_name DoubleTy  = "double"
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
      | ConstExp (BoolLit b) => PrettyString (Bool.toString b)
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
      | Binop(Greater,e1,e2) => pp_infix depth pkgName (">",e1,e2)
      | Binop(GreaterEqual,e1,e2) => pp_infix depth pkgName (">=",e1,e2)
      | Binop(Less,e1,e2) => pp_infix depth pkgName ("<",e1,e2)
      | Binop(LessEqual,e1,e2) => pp_infix depth pkgName ("<=",e1,e2)
      | Binop(Minus,e1,e2) => pp_infix depth pkgName ("-",e1,e2)
      | Binop(Multiply,e1,e2) => pp_infix depth pkgName ("*",e1,e2)
      | Binop(Plus,e1,e2) => pp_infix depth pkgName ("+",e1,e2)
      | Binop(Divide,e1,e2) => pp_exp depth "" (Fncall (("Int","div"),[e1,e2]))
      | Binop(Modulo,e1,e2) => pp_exp depth "" (Fncall (("Int","mod"),[e1,e2]))
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
               Space, pp_exp (depth-1) pkgName  res,
               Line_Break, PrettyString "end"])
	end
      | Fncall(("","Tuple"),list) =>
          if null list then
            PrettyString "!!<EMPTY TUPLE FAILURE>!!"
          else if length list = 1 then
             pp_exp (depth-1) pkgName (hd list)
          else PrettyBlock(2,true,[],
                 [PrettyString"(",
                  PrettyBlock(0,false,[],
                     [gen_pp_list Comma [emptyBreak] (pp_exp (depth-1) pkgName ) list]),
                  PrettyString")"])
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
      | Fncall (qid,args) => PrettyBlock(2,true,[],
           [PrettyString"(",PrettyString(pp_pkg_qid pkgName qid), Space,
            PrettyBlock(0,false,[],
               [gen_pp_list Space [emptyBreak] (pp_exp (depth-1) pkgName ) args]),
            PrettyString")"])
      | ConstrExp(qid, constr,argOpt) =>
         PrettyBlock(2,true,[],
           [PrettyString(pp_pkg_qid pkgName qid), Space,
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
    in PrettyBlock(5,true,[],
        [PrettyString "val ",
         pp_exp (d-1) pkgName e1,
         PrettyString " =", Space,
         pp_exp (d-1) pkgName e2])
    end
  | pp_valbind other input stuff = PolyML.PrettyString"!!<MALFORMED LET BINDING>!!"
;

(*
      | Binop(Exponent,e1,e2) => pp_infix depth ("exp",e1,e2)
      | Binop(LogicalLShift,e1,e2) => pp_infix depth ("<<",e1,e2)
      | Binop(LogicalRShift,e1,e2) => pp_infix depth ("l>>",e1,e2)
      | Binop(CastWidth,e1,e2) => pp_infix depth ("width",e1,e2)
      | Binop(RegexMatch,e1,e2) => pp_exp depth (Fncall(("","match"),[e1,e2]))
      | Binop(Since,e1,e2) => pp_exp depth (Fncall(("","Since"),[e1,e2]))
      | Binop(Trigger,e1,e2) => pp_exp depth (Fncall(("","Trigger"),[e1,e2]))
      | Binop(Fby,e1,e2) => pp_infix depth ("->",e1,e2)
      | Binop(Imp,e1,e2) => pp_infix depth ("==>",e1,e2)
      | Binop(ArithmeticRShift,e1,e2) => pp_infix depth ("a>>",e1,e2)
      | Binop(BitAnd,e1,e2) => pp_infix depth ("&",e1,e2)
      | Binop(BitOr,e1,e2) => pp_infix depth ("|",e1,e2)
      | Binop(BitXOR,e1,e2) => pp_infix depth ("^",e1,e2)
      | Unop(BitNot,e) => PrettyBlock(2,true,[],
           [PrettyString"not",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Unop(Signed,e) => PrettyBlock(2,true,[],
           [PrettyString"signed",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Unop(Unsigned,e) => PrettyBlock(2,true,[],
           [PrettyString"unsigned",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Unop(Unbounded,e) => PrettyBlock(2,true,[],
           [PrettyString"unbounded",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Unop(Yesterday,e) => PrettyBlock(2,true,[],
           [PrettyString"Yesterday",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Unop(ZYesterday,e) => PrettyBlock(2,true,[],
           [PrettyString"ZYesterday",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Unop(Historically,e) => PrettyBlock(2,true,[],
           [PrettyString"Historically",
            PrettyString"(",pp_exp (depth-1) pkgName  e,PrettyString")"])
      | Quantified (quant,bvars,body) =>
          PrettyBlock(2,true,[],
           [PrettyString(case quant of Forall => "forall " | Exists => "exists "),
            PrettyBlock(0,false,[],
               [gen_pp_list Space [] (pp_ty_field (depth-1)) bvars]),
                pp_exp (depth-1) pkgName  body])
*)

(*         PrettyBlock(2,true,[],
           [PrettyString (pp_qid qid), PrettyBreak(0,0),
            PrettyString "{",
            pp_comma_list (pp_ty_field (depth-1)) fields,
            PrettyString "}"])
*)

(*
fun pp_vdec_semi d (id,ty) =
 let open PolyML
 in PrettyBlock(0,true,[],
     [PrettyString id, PrettyString":",pp_ty (d-1) ty,PrettyString";"])
 end;


fun pp_param d param =
 let open PolyML
     fun ppp mpp d (id,ty) =
       PrettyBlock(2,false,[],
         [PrettyString id, Space, PrettyString":",
          Space, mpp, Space, pp_ty (d-1) ty])
 in case param
     of In vdec => ppp (PrettyString"in") d vdec
      | Out vdec => ppp (PrettyString"out") d vdec
      | InOut vdec => ppp (PrettyString"inout") d vdec
 end;

fun pp_stmt depth stmt =
 let open PolyML
 in if depth = 0 then PrettyString "<stmt>"
  else
   case stmt
    of Skip => PrettyString "Skip;"
     | Check e =>
         PrettyBlock(2,true,[],
            [PrettyString "check",Space,
             pp_exp (depth-1) pkgName  e, PrettyString";"])
     | Assign(e1,e2) =>
         PrettyBlock(2,true,[],
         [pp_exp (depth-1) pkgName  e1, PrettyString " :=",
          Space, pp_exp (depth-1) pkgName  e2, PrettyString";"])
     | Call((pkgName,fnName),elist) =>
          PrettyBlock(2,true,[],
            [PrettyString (pkgName^"."^fnName),PrettyBreak(0,0),
             PrettyString"(", pp_comma_list (pp_exp (depth-1) pkgName ) elist,
             PrettyString");"])
     | IfThenElse(e,s1,s2) =>
          PrettyBlock(2,true,[],
            [PrettyString"if ", pp_exp (depth-1) pkgName  e, Space,
             PrettyString"then ", pp_stmt (depth-1) s1,Space,
             PrettyString"else ", pp_stmt (depth-1) s2])
     | Case(e,rules) =>
        let fun pp_rule d (p,s) =
         PrettyBlock(2,true,[],
          [pp_exp (d-1) p, PrettyString" =>", Space,
           pp_stmt (d-1) s])
        in
          PrettyBlock(2,true,[],
           [PrettyString "match ", pp_exp (depth-1) pkgName  e,
            PrettyString " {", Line_Break,
            gen_pp_list emptyString [Space] (pp_rule (depth-1)) rules,
            Line_Break, PrettyString "}"])
        end
     | Block stmts =>
           PrettyBlock(0,true,[],
            [PrettyString"{", Line_Break,
             PrettyBlock(2,true,[],
              [gen_pp_list emptyString [Space] (pp_stmt (depth-1)) stmts]),
             PrettyBreak(0,0),PrettyString "}"])
     | For((id,ty),e1,e2,istmt,body) =>
          PrettyBlock(4,true,[],
            [PrettyString"for", PrettyString"(",
             PrettyBlock(2,false,[],
               [PrettyString id,Space,PrettyString":",
                Space, pp_ty (depth-1) ty, Space,
                PrettyString"=", Space, pp_exp (depth-1) pkgName  e1]),
              PrettyString";", Space,
             pp_exp (depth-1) pkgName  e2,
             PrettyString";", Space,
             pp_stmt (depth-1) istmt,
             PrettyString")", PrettyBreak(9999,0),
             pp_stmt (depth-1) body])
     | While(e,stmt) =>
          PrettyBlock(2,false,[],
            [PrettyString"while ", pp_exp (depth-1) pkgName  e, Line_Break,
             PrettyString"do ", pp_stmt (depth-1) stmt])

 end;
*)

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
            val dty = DatatypeDecl (tyName,[(tyName,tys)])
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

fun pp_tmdec depth pkgName tmdec =
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
    else
  case tmdec
   of ConstDec (qid,ty,exp) =>
      PrettyBlock(0,true,[],
        [PrettyString "val ",
         PrettyString (snd qid),
         PrettyString " =", Space,
         pp_exp (depth-1) pkgName exp,
         Semicolon])
    | FnDec (qid,params,ty,exp) =>
       let fun pp_param (s,ty) = PolyML.PrettyString s
       in
       PrettyBlock(0,true,[],
        [PrettyString "fun ",
         PrettyString (snd qid), PrettyString " ",
         gen_pp_list Space [emptyBreak] pp_param params,
         PrettyString " =", Space,
         pp_exp (depth-1) pkgName exp,
         Semicolon])
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

val initStepVar = ("initStep",boolTy);

fun split_fby exp =
  case exp
   of Binop(Fby,e1,e2) => (e1,e2)
    | otherwise => (exp,exp);

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

datatype moncode =
	 MonitorCode of qid * port list * port list
                            * (string * ty) list
                            * (exp * exp) list
                            * (exp * exp) list
;

fun mk_monitor_stepFn (MonitorDec(qid, ports, _, _, eq_stmts, _, _)) =
 let val stepFn_name = snd qid ^ "StepFn"
     val (inports,outports) = Lib.partition (fn (_,_,mode,_) => mode = "in") ports
     val inputs = map feature2port inports
     val outputs = map feature2port outports
     val stateVars = map (fn (name,ty,exp) => (name,ty)) eq_stmts
     val pre_stmts = map (fn (s,ty,exp) => (VarExp s, split_fby exp)) eq_stmts
     val init_code = map (fn (v,(e1,e2)) => (v, e1)) pre_stmts
     val step_code = map (fn (v,(e1,e2)) => (v, e2)) pre_stmts
 in
   MonitorCode (qid, inputs, outputs, initStepVar::stateVars, init_code, step_code)
 end

val False_initStep = ConstExp(BoolLit false)

fun mk_tuple list = Fncall(("","Tuple"),list)

fun letExp binds exp =
    let val eqs = map (fn (a,b) => Binop(Equal,a,b)) binds
    in Fncall(("","LET"),eqs@[exp])
    end;

fun pp_mon_stepFn depth (MonitorCode(qid,inputs, outputs, stateVars, init, step)) =
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
    else
    let val stepFn_name = snd qid ^ "stepFn"
        val inportBs  = (mk_tuple(map (VarExp o portname) inputs),VarExp"inports")
        val outportBs = (mk_tuple(map (VarExp o portname) outputs),VarExp"outports")
        val stateBs   = (mk_tuple(map (VarExp o fst) stateVars),VarExp"stateVars")
        val stateExps = False_initStep::map (fn (s,ty) => VarExp s) (tl stateVars)
        val retTuple  = mk_tuple stateExps
        val initExp   = letExp init retTuple
        val stepExp   = letExp step retTuple
        val condExp   = Fncall(("","IfThenElse"),[VarExp"initStep",initExp,stepExp])
        val bodyExp   = letExp [inportBs,outportBs,stateBs] condExp
    in
      PrettyBlock(2,true,[],
        [PrettyString ("fun "^stepFn_name^" inports outports stateVars = "),
         Line_Break, PrettyString " ",
         pp_exp (depth - 1) (fst qid) bodyExp
        ])
    end
 end;

fun pp_monitor depth mondec =
 let val moncode = mk_monitor_stepFn mondec
 in pp_mon_stepFn depth moncode
 end

fun pp_pkg depth (Pkg(pkgName,(types,consts,filters,monitors))) =
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
   else
    PrettyBlock(2,true,[],
        [PrettyString ("structure "^pkgName^" = "), Line_Break,
         PrettyString "struct", Line_Break_2,
         end_pp_list Line_Break Line_Break (pp_tydec (depth-1) pkgName) types, Line_Break,
         end_pp_list Line_Break Line_Break (pp_tmdec (depth-1) pkgName) consts, Line_Break,
         end_pp_list Line_Break Line_Break (pp_filter (depth-1)) filters, Line_Break,
         end_pp_list Line_Break Line_Break (pp_monitor (depth-1)) monitors, Line_Break,
         PrettyString "end"
        ])
 end

val _ = PolyML.addPrettyPrinter (fn i => fn () => fn ty => pp_ty i "<pkg>" ty);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn e => pp_exp i "<pkg>" e);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tydec => pp_tydec i "<pkg>" tydec);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn tmdec => pp_tmdec i "<pkg>" tmdec);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn mon => pp_mon_stepFn i mon);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn pkg => pp_pkg i pkg);

(* val _ = PolyML.addPrettyPrinter (fn i => fn () => fn stmt => pp_stmt i "<pkg>" stmt); *)

end (* PP_CakeML *)
