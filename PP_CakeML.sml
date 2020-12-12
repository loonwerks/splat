structure PP_CakeML =
struct

open Lib Feedback MiscLib PPfns AST;

val ERR = mk_HOL_ERR "PP_CakeML";
fun unimplemented s = ERR s "unimplemented";

fun pp_qid ("",s) = s
  | pp_qid (s1,s2) = String.concat[s1,".",s2];

fun qid_string p = Lib.quote(pp_qid p);

(*---------------------------------------------------------------------------*)
(* CakeML Prettyprinters for AST                                             *)
(*---------------------------------------------------------------------------*)

fun base_ty_name (BaseTy BoolTy)   = "bool"
  | base_ty_name (BaseTy CharTy)   = "char"
  | base_ty_name (BaseTy StringTy) = "string"
  | base_ty_name (BaseTy FloatTy)  = "float"
  | base_ty_name (BaseTy DoubleTy)  = "double"
  | base_ty_name (BaseTy (IntTy _))= "int"
  | base_ty_name (NamedTy args) = pp_qid args
  | base_ty_name (BaseTy RegexTy)  = raise ERR "base_ty_name" "regex"

fun pp_ty depth ty =
 let open PolyML
 in if depth = 0 then PrettyString "<ty>"
   else
   case ty
    of BaseTy _ => PrettyString (base_ty_name ty)
     | NamedTy _ => PrettyString (base_ty_name ty)
     | RecdTy(qid,fields) =>
         PrettyBlock(2,true,[],
           [PrettyString (pp_qid qid), PrettyBreak(0,0),
            PrettyString "{",
            pp_comma_list (pp_ty_field (depth-1)) fields,
            PrettyString "}"])
     | ArrayTy(eltype,dims) =>
         PrettyBlock(2,true,[],
            [pp_ty (depth-1) eltype, PrettyBreak (1,0),
             PrettyString "[", pp_comma_list (pp_exp (depth-1)) dims,
             PrettyString "]"])
 end
 and pp_exp depth exp =
  let open PolyML
  in if depth = 0 then PrettyString "<exp>"
    else
    case exp
     of VarExp id => PrettyString id
      | ConstExp (IdConst qid) => PrettyString (pp_qid qid)
      | ConstExp (BoolLit b) => PrettyString (Bool.toString b)
      | ConstExp (CharLit c) => PrettyString ("'#"^Char.toString c^"'")
      | ConstExp (StringLit s) => PrettyString (Lib.quote(String.toString s))
      | ConstExp (IntLit{kind, value}) => PrettyString (Int.toString value)
      | ConstExp (FloatLit r) => PrettyString (Real.toString r)
      | ConstExp (RegexLit r) => PrettyString ("`"^r^"`")
      | Unop(Not,e) => PrettyBlock(2,true,[],
           [PrettyString"not",PrettyBreak(0,1),
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(BitNot,e) => PrettyBlock(2,true,[],
           [PrettyString"not",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(UMinus,e) => PrettyBlock(2,true,[],
           [PrettyString"~",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(ChrOp,e) => PrettyBlock(2,true,[],
           [PrettyString"chr",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(OrdOp,e) => PrettyBlock(2,true,[],
           [PrettyString"ord",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(Signed,e) => PrettyBlock(2,true,[],
           [PrettyString"signed",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(Unsigned,e) => PrettyBlock(2,true,[],
           [PrettyString"unsigned",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(Unbounded,e) => PrettyBlock(2,true,[],
           [PrettyString"unbounded",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(Yesterday,e) => PrettyBlock(2,true,[],
           [PrettyString"Yesterday",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(ZYesterday,e) => PrettyBlock(2,true,[],
           [PrettyString"ZYesterday",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Unop(Historically,e) => PrettyBlock(2,true,[],
           [PrettyString"Historically",
            PrettyString"(",pp_exp (depth-1) e,PrettyString")"])
      | Binop(And,e1,e2) => pp_binop depth ("and",e1,e2)
      | Binop(Imp,e1,e2) => pp_binop depth ("==>",e1,e2)
      | Binop(ArithmeticRShift,e1,e2) => pp_binop depth ("a>>",e1,e2)
      | Binop(BitAnd,e1,e2) => pp_binop depth ("&",e1,e2)
      | Binop(BitOr,e1,e2) => pp_binop depth ("|",e1,e2)
      | Binop(BitXOR,e1,e2) => pp_binop depth ("^",e1,e2)
      | Binop(Equal,e1,e2) => pp_binop depth ("=",e1,e2)
      | Binop(Exponent,e1,e2) => pp_binop depth ("exp",e1,e2)
      | Binop(Greater,e1,e2) => pp_binop depth (">",e1,e2)
      | Binop(GreaterEqual,e1,e2) => pp_binop depth (">=",e1,e2)
      | Binop(Divide,e1,e2) => pp_binop depth ("/",e1,e2)
      | Binop(Less,e1,e2) => pp_binop depth ("<",e1,e2)
      | Binop(LessEqual,e1,e2) => pp_binop depth ("<=",e1,e2)
      | Binop(LogicalLShift,e1,e2) => pp_binop depth ("<<",e1,e2)
      | Binop(LogicalRShift,e1,e2) => pp_binop depth ("l>>",e1,e2)
      | Binop(Minus,e1,e2) => pp_binop depth ("-",e1,e2)
      | Binop(Modulo,e1,e2) => pp_binop depth ("%",e1,e2)
      | Binop(Multiply,e1,e2) => pp_binop depth ("*",e1,e2)
      | Binop(NotEqual,e1,e2) => pp_binop depth ("!=",e1,e2)
      | Binop(Or,e1,e2) => pp_binop depth ("or",e1,e2)
      | Binop(Plus,e1,e2) => pp_binop depth ("+",e1,e2)
      | Binop(CastWidth,e1,e2) => pp_binop depth ("width",e1,e2)
      | Binop(RegexMatch,e1,e2) => pp_exp depth (Fncall(("","match"),[e1,e2]))
      | Binop(Since,e1,e2) => pp_exp depth (Fncall(("","Since"),[e1,e2]))
      | Binop(Trigger,e1,e2) => pp_exp depth (Fncall(("","Trigger"),[e1,e2]))
      | Binop(Fby,e1,e2) => pp_binop depth ("->",e1,e2)
      | ArrayExp elist => PrettyBlock(0,true,[],
           [PrettyString"[",
            pp_list_with_style false Comma [emptyBreak] (pp_exp (depth-1)) elist,
            PrettyString"]"])
      | ArrayIndex(A,dims) => PrettyBlock(0,false,[],
           [pp_exp (depth-1) A, PrettyString"[",
            gen_pp_list Comma [emptyBreak] (pp_exp (depth-1)) dims,
            PrettyString"]"])
      | ConstrExp(qid, constr,argOpt) =>
         PrettyBlock(2,true,[],
           [PrettyString(pp_qid qid^"'"^constr),
            PrettyBlock(0,false,[],
             case argOpt of NONE => []
               | SOME vexp => [PrettyString"(", pp_exp (depth-1) vexp,
                               PrettyString")"])])
      | Fncall (qid,args) => PrettyBlock(2,true,[],
           [PrettyString(pp_qid qid), PrettyString"(",
            PrettyBlock(0,false,[],
               [gen_pp_list Comma [emptyBreak] (pp_exp (depth-1)) args]),
            PrettyString")"])
      | Quantified (quant,bvars,body) =>
          PrettyBlock(2,true,[],
           [PrettyString(case quant of Forall => "forall " | Exists => "exists "),
            PrettyBlock(0,false,[],
               [gen_pp_list Space [] (pp_ty_field (depth-1)) bvars]),
                pp_exp (depth-1) body])
      | RecdExp (qid,fields) => PrettyBlock(2,true,[],
           [PrettyString(pp_qid qid), PrettyString("["),
            PrettyBlock(0,false,[],
                        [pp_comma_list (pp_exp_field (depth-1)) fields]),
            PrettyString"]"])
      | RecdProj(recd,field) => PrettyBlock(0,false,[],
           [pp_exp (depth-1) recd,PrettyString".",PrettyString field])
  end
and pp_binop d (str,e1,e2) =
    let open PolyML
    in PrettyBlock(2,true,[],
        [PrettyString"(",pp_exp (d-1) e1,
         Space,PrettyString str, Space,
         pp_exp (d-1) e2,PrettyString")"])
    end
and pp_exp_field d (id,exp) =
 let open PolyML
 in PrettyBlock(0,true,[],
     [PrettyString id, PrettyString":",pp_exp (d-1) exp])
 end
and pp_ty_field d (id,ty) =
 let open PolyML
 in PrettyBlock(0,true,[],
     [PrettyString id, PrettyString":",pp_ty (d-1) ty])
 end
;

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
             pp_exp (depth-1) e, PrettyString";"])
     | Assign(e1,e2) =>
         PrettyBlock(2,true,[],
         [pp_exp (depth-1) e1, PrettyString " :=",
          Space, pp_exp (depth-1) e2, PrettyString";"])
     | Call((pkgName,fnName),elist) =>
          PrettyBlock(2,true,[],
            [PrettyString (pkgName^"."^fnName),PrettyBreak(0,0),
             PrettyString"(", pp_comma_list (pp_exp (depth-1)) elist,
             PrettyString");"])
     | IfThenElse(e,s1,s2) =>
          PrettyBlock(2,true,[],
            [PrettyString"if ", pp_exp (depth-1) e, Space,
             PrettyString"then ", pp_stmt (depth-1) s1,Space,
             PrettyString"else ", pp_stmt (depth-1) s2])
     | Case(e,rules) =>
        let fun pp_rule d (p,s) =
         PrettyBlock(2,true,[],
          [pp_exp (d-1) p, PrettyString" =>", Space,
           pp_stmt (d-1) s])
        in
          PrettyBlock(2,true,[],
           [PrettyString "match ", pp_exp (depth-1) e,
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
                PrettyString"=", Space, pp_exp (depth-1) e1]),
              PrettyString";", Space,
             pp_exp (depth-1) e2,
             PrettyString";", Space,
             pp_stmt (depth-1) istmt,
             PrettyString")", PrettyBreak(9999,0),
             pp_stmt (depth-1) body])
     | While(e,stmt) =>
          PrettyBlock(2,false,[],
            [PrettyString"while ", pp_exp (depth-1) e, Line_Break,
             PrettyString"do ", pp_stmt (depth-1) stmt])

 end;


fun pp_decl depth decl =
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
  else
   case decl
    of TyAbbrevDecl(id,ty)
       => PrettyBlock(2,true,[],
           [PrettyString "type ", PrettyString id, PrettyString " = ",
            pp_ty (depth-1) ty, PrettyString";"])
     | RecdDecl(id,flds)
       => let in
          PrettyBlock(2,true,[],
             [PrettyString "type ", PrettyString id, PrettyString " =", Space,
              PrettyString "[", pp_comma_list (pp_ty_field (depth-1)) flds,
              PrettyString"];"])
          end
     | DatatypeDecl(id,constrs)
       => let fun pp_constr d (id,tys) =
               PrettyBlock(0,true,[],
                  [PrettyString id,
                   if not(null tys) then PrettyString":" else PrettyString"",
                   pp_comma_list (pp_ty (d-1)) tys])
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
     | VarDecl vdec
       => PrettyBlock(0,true,[],
             [PrettyString "var", Space, pp_ty_field (depth-1) vdec,
              PrettyString";"])
     | ConstDecl(id,ty,exp)
       => PrettyBlock(2,true,[],
             [PrettyString "const ",
              pp_ty_field (depth-1) (id,ty),
              PrettyString" = ", Space,
              pp_exp (depth-1) exp, PrettyString";"])
     | FnDecl(id,params,retvalOpt,locals,stmts)
       => let fun pp_params() = PrettyBlock (2,true,[],
                   [PrettyString id,Space,
                    PrettyString"(",
                    PrettyBlock(0,false,[],
                         [pp_comma_list (pp_param(depth-1)) params]),
                    PrettyString")",
                    PrettyBlock (2,true,[],
                         case retvalOpt
                          of NONE => []
                           | SOME vdec => [PrettyString" returns ",
                                           pp_ty_field (depth-1) vdec])])
             fun pp_body() = PrettyBlock(0,true,[],
                    iter_pp emptyString  [Line_Break] (pp_stmt (depth-1)) stmts)
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
     | SpecDecl(id,vdecs,stmts)
        => PrettyBlock(2,true,[],
             [PrettyString "spec ", PrettyString id,
              PrettyString " = {", PrettyBreak(999,2),
              PrettyBlock(4,true,[],
                case vdecs
                 of [] => []
                  | otherwise =>
                      [PrettyString"var", Line_Break,
                       gen_pp_list emptyString [Line_Break] (pp_vdec_semi (depth-1)) vdecs,
                       Line_Break, PrettyString"in ",Line_Break]),
                         gen_pp_list emptyString [Line_Break] (pp_stmt (depth-1)) stmts,
              Line_Break, PrettyString"}"])
     | CommentDecl lines
        => PrettyBlock(0,true,[],
           [PrettyString "/*-----------------------------------------------------------------",
            Line_Break, PrettyString"-- ",
            gen_pp_list Line_Break [PrettyString"--"] PrettyString lines,
            Line_Break,
            PrettyString "-----------------------------------------------------------------*/"])
     | NumTyDecl nkind
       => PrettyBlock(0,true,[],
           [PrettyString "numeral type = ",
            pp_ty (depth-1) (BaseTy(IntTy nkind)), PrettyString";"])
     | GraphDecl(id,nty,ety)
       => PrettyBlock(2,true,[],
             [PrettyString ("graphtype "^id), Space, PrettyString"= (",
              PrettyString "nodeLabel = ", pp_ty (depth-1) nty, Comma,Space,
              PrettyString "edgeLabel = ", pp_ty (depth-1) ety,PrettyString");"])
     | SizedDataDecl(id,ty,e1,NONE)
       => PrettyBlock(2,true,[],
             [PrettyString "sized ",
              pp_ty_field (depth-1) (id,ty),
              PrettyString" (", pp_exp (depth-1) e1, PrettyString");"])
     | SizedDataDecl(id,ty,e1,SOME e2)
       => PrettyBlock(2,true,[],
             [PrettyString "sized ",
              pp_ty_field (depth-1) (id,ty),
              PrettyString" (", pp_exp (depth-1) e1, PrettyString") :=",
              Space, pp_exp (depth-1) e2, PrettyString ";"])
     | SizedGraphDecl(id,ty,e1,e2)
       => PrettyBlock(2,true,[],
             [PrettyString "sized ",
              pp_ty_field (depth-1) (id,ty),
              PrettyString" (", pp_exp (depth-1) e1, Comma,
                                pp_exp (depth-1) e2, PrettyString");"])
     | EfnDecl(id,params,retvalOpt)
       => PrettyBlock(2,true,[],
             [PrettyString "imported function", Space,
              PrettyString id,Space,
              PrettyString"(", pp_comma_list (pp_param (depth-1)) params,
              PrettyString")",
              PrettyBlock(2,true,[],
                case retvalOpt
                 of NONE => []
                  | SOME vdec => [PrettyString" returns ",
                                  pp_ty_field (depth-1) vdec]),
              PrettyString";"])

 end

fun dest_inout (InOut p) = p
  | dest_inout otherwise = raise ERR "dest_inout" "";
fun dest_in (In p) = p
  | dest_in otherwise = raise ERR "dest_in" "";


datatype port
  = Event of string
  | Data of string * ty
  | EventData of string * ty;

fun portname (Event s) = s
  | portname (Data(s,ty)) = s
  | portname (EventData(s,ty)) = s;

datatype monitor_code
  = MonitorCode of qid
                 * port list
                 * port list
                 * (string * ty) list
                 * (exp * exp) list  (* init *)
                 * (exp * exp) list  (* step *)

fun pp_bind depth (v,e) =
 let open PolyML
 in PrettyBlock(0,true,[],
    [PrettyString "val ",
     pp_exp (depth-1) v,
     PrettyString " = ",
     pp_exp (depth-1) e])
 end

fun pp_lets depth (binds,exp) =
 let open PolyML
 in  PrettyBlock(4,true,[],
    case binds
     of [] => [pp_exp (depth-1) exp]
      | otherwise =>
         [PrettyString"let", Space,
          gen_pp_list emptyString [Line_Break] (pp_bind (depth-1)) binds,
          Line_Break, PrettyString"in ",Line_Break, pp_exp (depth-1) exp,
          Line_Break, PrettyString "end"])
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

fun pp_mon_stepFn depth (MonitorCode(qid,inputs, outputs, stateVars, init, step)) -
 let open PolyML
 in if depth = 0 then PrettyString "<decl>"
    else
    let val stepFn_name = snd qid ^ "stepFn"
        val inportVars = map portname inputs
        val outportVars = map portname outputs
        fun pp_unpack() = PrettyBlock (2,true,[],
                   [PrettyString let,Space,
                    PrettyString"(",
                    PrettyBlock(0,false,[],
                         [pp_comma_list (pp_param(depth-1)) params]),
                    PrettyString")",
                    PrettyBlock (2,true,[],
                         case retvalOpt
                          of NONE => []
                           | SOME vdec => [PrettyString" returns ",
                                           pp_ty_field (depth-1) vdec])])
             fun pp_init() = PrettyBlock(0,true,[],
                    iter_pp emptyString  [Line_Break] (pp_lets (depth-1)) init)
             fun pp_step() = PrettyBlock(0,true,[],
                    iter_pp emptyString  [Line_Break] (pp_lets (depth-1)) step)
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
             [PrettyString ("fun "^stepFn_name^" inports outports stateVars = "),
              Line_Break, PrettyString " ",
              pp_unpacking()
              (* if-then-else *)
              PrettyBlock(2,true,[],
                [PrettyString"if initStep", Space,
                 PrettyString"then ", pp_init(),Space,
                 PrettyString"else ", pp_step()])
              Line_Break,
              PrettyString"end"])
          end
 end;


val _ = PolyML.addPrettyPrinter (fn i => fn () => fn mon => pp_mon_stepFn i mon);

val _ = PolyML.addPrettyPrinter (fn i => fn () => fn ty => pp_ty i ty);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn e => pp_exp i e);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn stmt => pp_stmt i stmt);
val _ = PolyML.addPrettyPrinter (fn i => fn () => fn decl => pp_decl i decl);

end (* PP_CakeML *)
