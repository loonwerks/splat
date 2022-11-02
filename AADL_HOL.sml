(*
 val abstract_model_nums : decls -> decls

 val mk_pkg_defs
    : string
        -> tyEnv
          -> decls
            -> tyEnv * thm list (* types *)
                     * thm list (* constant defns *)
                     * ((string * string) * thm) list (* filters *)
                     * ((string * string) * thm) list (* monitors *)

 val pkgs2hol
      : string
         -> decls list
           -> tyEnv * thm list (* types *)
                    * thm list (* constant defns *)
                    * ((string * string) * thm) list (* filters *)
                    * ((string * string) * thm) list (* monitors *)

 val export_cakeml_filters : string -> (string * exp) list -> filter list -> unit

 datatype port
    = Event of string
    | Data of string * ty
    | EventData of string * ty;

*)

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

val pkg = last opkgs;  (* SW *)
val pkg = el 7 opkgs;  (* CMASI *)
val pkg = el 13 opkgs;  (* SW *)
val pkg = el 14 opkgs;  (* CASE_Proxies *)

val pkg_adsb = el 8 opkgs;  (* adsb-types *)
val pkg_case_props = el 10 opkgs;  (* case_props *)
val vpm = last opkgs;  (* VPM *)

val modlist = mapfilter scrape opkgs
val modlist' = replace_null_fields modlist
val modlist'' = map extend_recd_decs modlist'
val modlist''' = filter (not o empty_pkg) modlist'';
val pkgs = modlist''';

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

(*===========================================================================*)
(* AST to AST                                                                *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Lift all integer-like numbers to unbounded integers                       *)
(*---------------------------------------------------------------------------*)

fun amn_ty ty =
 let open AST
 in case ty
     of BaseTy (IntTy _)     => BaseTy  (IntTy (Int NONE))
      | RecdTy (qid, fldtys) => RecdTy  (qid, map (I##amn_ty) fldtys)
      | ArrayTy (ty,dims)    => ArrayTy (amn_ty ty,dims)
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
      | ConstrExp(qid,id,elist) => ConstrExp(qid,id, map amn_exp elist)
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
     fun amn_eq_stmt (s,ty,e) = (s,amn_ty ty,amn_exp e)
     fun amn_cprop (s1,s2,e) = (s1,s2,amn_exp e)
 in case fdec
     of FilterDec(qid, ports, decs,eq_stmts,guars) =>
        FilterDec(qid, map amn_port ports,
                   map amn_tmdec decs,
                   map amn_eq_stmt eq_stmts,
                   map amn_cprop guars)
 end
;

fun amn_monitor_dec fdec =
 let fun amn_port (s1,ty,s2,s3) = (s1,amn_ty ty,s2,s3)
     fun amn_eq_stmt (s,ty,e) = (s,amn_ty ty,amn_exp e)
     fun amn_cprop (s1,s2,e) = (s1,s2,amn_exp e)
 in case fdec
     of MonitorDec(qid, ports, latched, decs, eq_stmts, cprops) =>
        MonitorDec(qid, map amn_port ports, latched,
                   map amn_tmdec decs,
                   map amn_eq_stmt eq_stmts,
		   map amn_cprop cprops)
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
     of Not => boolSyntax.mk_neg t
      | UMinus =>
         if mem ty [intSyntax.int_ty,i8,i16,i32,i64] then
            lift intSyntax.mk_negated else
         if ty = real_ty then
           lift realSyntax.mk_negated
         else raise ERR "unop (UMinus)"
                   "expected type of operand to be int\
                   \ (either fixed width or unbounded)"
 end;

fun binop (bop,e1,_) t1 t2 =
 let open AST
     fun lift f = f (t1,t2)
     val ty1 = type_of t1
     val ty2 = type_of t2
 in
  case bop
   of Equal => lift boolSyntax.mk_eq
    | NotEqual => raise ERR "binop" "NotEqual should already be translated away"
    | Or => mk_disj(t1,t2)
    | And => mk_conj(t1,t2)
    | Imp => mk_imp(t1,t2)
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
    | Fby => undef "Fby"
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

val mk_is_some =
 let val is_some_tm = optionSyntax.is_some_tm
 in fn tm =>
     mk_comb(inst[alpha |-> type_of tm] is_some_tm, tm)
 end

fun resolve_constName (pkgname,cname) =
  case Term.decls cname
   of [] => NONE
    | [const] => SOME const
    | consts => (* prefer one specified in theory=pkgname otherwise current theory *)
       let val currthy = current_theory()
       in
         SOME (Lib.first (fn c => #Thy (dest_thy_const c) = pkgname) consts)
         handle HOL_ERR _ =>
         SOME (Lib.first (fn c => #Thy (dest_thy_const c) = currthy) consts)
         handle HOL_ERR _
         => NONE
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
    | ConstrExp(qid,id, elist) =>
       (let val c = mk_constr_const pkgName qid id
           val args = map (transExp pkgName varE Unknown) elist
        in list_mk_comb(c,args)
        end handle e as HOL_ERR _ => raise wrap_exn "" "transExp (ConstrExp)" e)
    | Fncall (qid as (pkgname,cname),expl) =>
       (case resolve_constName (pkgname,cname)
         of NONE => raise ERR "transExp"
               ("unable to create HOL constant corresponding to "^qid_string qid)
          | SOME c =>
        let val args = map (transExp pkgName varE Unknown) expl
        in list_mk_comb(c,args)
        end handle e as HOL_ERR _ => raise wrap_exn "" "transExp (Fncall)" e)

    | Fncall ((_,"IfThenElse"),[e1,e2,e3]) => mk_cond(a,b,c)
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
         mk_is_some (transExp pkgName varE Unknown arg)
    | Fncall ((_,"Event"),_) => raise ERR "transExp" "Event: unexpected number of args"
    | Fncall (qid as (pkgname,cname),expl) =>
       (case resolve_constName (pkgname,cname)
         of NONE => raise ERR "transExp"
               ("unable to create HOL constant corresponding to "^qid_string qid)
          | SOME c =>
        let val args = map (transExp pkgName varE Unknown) expl
        in list_mk_comb(c,args)
        end handle e as HOL_ERR _ => raise wrap_exn "" "transExp (Fncall)" e)
    | ConstExp (IdConst qid) => undef "ConstExp: IdConst"
    | ArrayExp elist => undef "ArrayExp"
    | Quantified(quant,qvars,exp) => undef "Quantified"

(* TOPSORT GUNK : second thing mentions the first *)

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
(* Puts type alpha in place of null. Expects there to be at most one such    *)
(* field. There is an assumption that all declarations of records, enums,    *)
(* etc, are taking place in the current theory, so the pkgName is ignored.   *)
(*---------------------------------------------------------------------------*)

fun ty2pretype tyEnv ty =
 let open Datatype ParseDatatype
 in if is_null_ty ty then dVartype "'a" else dAQ (transTy tyEnv ty)
 end;

fun declare_hol_record tyEnv ((_,recdName),fields) =
 let open ParseDatatype ParseDatatype_dtype
     fun mk_field(s,ty) = (s,ty2pretype tyEnv ty)
 in
    if length (filter is_null_ty (map snd fields)) > 1 then
      raise ERR "declare_hol_record" "multiple null fields not handled"
    else
    if null fields then  (* Empty records get mapped to a trivial datatype *)
     Datatype.astHol_datatype
          [(recdName,Constructors[(recdName,[dAQ oneSyntax.one_ty])])]
    else
     Datatype.astHol_datatype [(recdName,Record (map mk_field fields))]
   ; stdErr_print ("Declared record "^Lib.quote recdName^"\n")
 end

fun declare_hol_union tyEnv (qid,choices) =
 let open ParseDatatype
     val tyName = snd qid
     fun mk_constr (s,ty) = (tyName^s,[ty2pretype tyEnv ty])
 in
   Datatype.astHol_datatype [(tyName,Constructors (map mk_constr choices))]
   ; stdErr_print ("Declared union type "^Lib.quote tyName^"\n")
 end

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

fun declare_hol_term tyEnv dec =
  let val (qid,params,ty,body) =
         (case dec
           of ConstDec (qid,ty,exp) => (qid,[],ty,exp)
            | FnDec arg => arg)
      val name = snd qid
      fun mk_hol_param (s,ty) = (s, mk_var(s,transTy tyEnv ty))
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
    handle HOL_ERR _ => raise ERR "declare_hol_term"
           ("failed to define "^Lib.quote (snd(tmdec_qid dec)))

fun mk_filter_spec (thyName,tyEnv,fn_defs)
		   (FilterDec ((pkgName,fname), ports, decs, eq_stmts, cprops)) =
    let val outport = Lib.first (fn (_,_,dir,_) => (dir = "out")) ports
	val inport = Lib.first (fn (_,_,dir,_) => (dir = "in")) ports
        val iname = #1 inport
        val oname = #1 outport
        val ty = transTy tyEnv (#2 outport)
        val varIn = (iname,mk_var(iname,ty))
        val varOut = (oname,mk_var(oname,ty))
        val prop = end_itlist mk_and (map #3 cprops)
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
    handle e => raise wrap_exn "AADL"
    ("mk_filter_spec (on "^qid_string (pkgName,fname)^")") e;
;

fun is_event kind = mem kind ["EventPort","EventDataPort"];
fun is_event_port (_,_,_,kind) = is_event kind;

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

fun mapFail f list =
 let fun mapf [] acc = (rev acc,[])
       | mapf (h::t) acc =
          case (SOME (f h) handle _ => NONE)
           of NONE => (rev acc,h::t)
            | SOME x => mapf t (x::acc)
 in mapf list []
 end
;

fun mk_pkg_defs thyName tyEnv (pkgName,(tydecs,tmdecs,filters,monitors)) =
 let val (tyEnv',rst) = revitFail declare_hol_type tydecs tyEnv
 in if not(null rst) then
       raise ERR "mk_pkg_defs" "failure to define a declared type"
    else
 let val tydecls = List.filter (is_datatype o snd) (theorems thyName)
     val tmdecs' = op_mk_set same_tmdec tmdecs
     val tmdecs'' = topsort called_by tmdecs'
(*
val (fn_defs,rst) = mapFail (declare_hol_term tyEnv') tmdecs''
 *)
     val fn_defs = mapfilter (declare_hol_term tyEnv') tmdecs''
     val _ = if length fn_defs < length tmdecs'' then
               HOL_MESG (String.concat
                  [pkgName," : some constants or functions not defined. Continuing ..."])
             else ()
     val info = (thyName,tyEnv',fn_defs)
     val filter_specs = map (mk_filter_spec info) filters
     val monitor_specs = map (mk_monitor_spec info) monitors
 in
      (tyEnv', map snd tydecls, fn_defs, filter_specs, monitor_specs)
 end end;

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
val thyName = "UAS";

val pkgs as [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6] = scrape_pkgs jpkg;
val (pkgName,(tydecs,tmdecs,fdecs,mondecs)) = pkg5;
val [mondec1,mondec2] = mondecs;

val MonitorDec(qid,features,latched,decs,eq_stmts,guars) = mondec1;
val MonitorDec(qid,features,latched,decs,eq_stmts,guars) = mondec2;

val stepFn1 = mk_monitor_stepFn mondec1;
val stepFn2 = mk_monitor_stepFn mondec2;

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

local
(*---------------------------------------------------------------------------*)
(* Read in the template file "splat/codegen/filter-template"                 *)
(*---------------------------------------------------------------------------*)
val filter_template_ss =
    let val istrm = TextIO.openIn "codegen/filter-template"
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
(*           chunk0 . input-buf-decl .                                       *)
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
 let val (chunk0,suff0) = locate "<<INPUT-BUF-DECL>>" filter_template_ss
     val (chunk1,suff1) = locate "<<FILL-INPUT-BUF>>" suff0
     val (chunk2,suff2) = locate "<<FFI-OUTPUT-CALLS>>" suff1
     val (chunk3,suff3) = locate "<<SIZE-ORIGIN>>" suff2
     val (chunk4,suff4) = locate "<<BUF-SIZE>>" suff3
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

fun dest_namedTy (NamedTy qid) = qid
  | dest_namedTy other = raise ERR "dest_namedTy" "";

fun isIn (name,ty,"in",style) = true
  | isIn otherwise = false

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

val filterMap =
[(("CASEAgree","WELL_FORMED_OPERATING_REGION"),
  "CMASI_Contig.fullOperatingRegionMesg")
 ,
 (("CASEAgree","WELL_FORMED_LINE_SEARCH_TASK"),
  "CMASI_Contig.fullLineSearchTaskMesg")
 ,
 (("CASEAgree","WELL_FORMED_AUTOMATION_REQUEST"),
  "CMASI_Contig.fullAutomationRequestMesg")
 ,
 (("CASEAgree","WELL_FORMED_AUTOMATION_RESPONSE"),
  "CMASI_Contig.fullAutomationResponseMesg")
 ,
 (("CASEAgree","WELL_FORMED_POINT"),
  "CMASI_Contig.location3D")
 ,
 (("CASEAgree","WELL_FORMED_WAYPOINT"),
  "CMASI_Contig.location3D")
 ,
 (("CASEAgree","WELL_FORMED_VIEWANGLE"),
  "CMASI_Contig.wedge")
];

(* -------------------------------------------------------------------------- *)
(* Map a filter declaration to a CakeML file. Assumes filter has only one     *)
(* input port but could have multiple outputs.                                *)
(* -------------------------------------------------------------------------- *)

fun numBytes n = 1 + Int.div(n,8);

fun classify ports =
  case List.partition isIn ports
   of (desired as ([inp],_::_)) => desired
    | otherwise => raise ERR "inst_filter_template" "unexpected port structure";

fun mk_inbuf_decl (pkg,cName) bytesize_string =
 let val origin_string = (pkg^"."^cName)
 in
   String.concat
     ["(*---------------------------------------------------------------------------*)\n",
      "(* Size computed from ",origin_string, "                  *)\n",
      "(*---------------------------------------------------------------------------*)\n\n",
      "val input_buffer = Word8Array.array ", bytesize_string, " Utils.w8zero;"]
 end;

fun mk_fill_input_buffer portName = String.concatWith "\n"
["(*---------------------------------------------------------------------------*)",
 "(* Clear buffer, read port into buffer, copy buffer to string                *)",
 "(*---------------------------------------------------------------------------*)",
 "",
 "fun fill_input_buffer () =",
 "  let val () = Utils.clear_buf input_buffer",
 "      val () = #(api_get_"^portName^") \"\" input_buffer",
 "   in",
 "      Utils.buf2string input_buffer",
 "   end;"
];

(*---------------------------------------------------------------------------*)
(* Expect prop to be of form "if event(in) and well-formed(in) then ... "    *)
(* and we expect to pull out the qid for "well-formed"                       *)
(*---------------------------------------------------------------------------*)

fun wf_of_code_guar code_guar =
 case code_guar
  of Fncall(("","IfThenElse"),
         [Binop(And,p1,Fncall(wf,args)),_,_]) => wf
   | otherwise => raise ERR "wf_of_code_guar"
			"unable to find well-formedness predicate";

fun inst_filter_template targetDir const_alist dec =
 let open Substring
 in
 case dec
  of FilterDec (qid, ports as _::_, _,_, props as _::_) =>
    (let val () = stdErr_print ("-> "^qid_string qid^"\n")
         val ([(inportName,ty,dir,style)], outports) = classify ports
         val (pname,tyName) = dest_namedTy ty
         val sizeName = tyName^"_Bit_Codec_Max_Size"
         val bitsize_exp = assoc sizeName const_alist
         val bitsize = dest_intLit bitsize_exp
         val byte_size_string = Int.toString (1 + numBytes bitsize) (* for event byte *)
         val () = stdErr_print (String.concat
             ["    Buffer size (bits/bytes) : ",
              Int.toString bitsize,"/",byte_size_string,"\n"])
         val inbufName = "input_buffer"
         val inbuf_decl = mk_inbuf_decl (pname,sizeName) byte_size_string
         val bufsize_origin = pname^"."^sizeName
         val fill_input_decl = mk_fill_input_buffer inportName
         val outFns = mk_output_calls outports
         val wf_qid = wf_of_code_guar (#3(hd props))
         val () = stdErr_print (String.concat
             ["    Well-formedness predicate : ",qid_string wf_qid, "\n"])
         val contig_qid = assoc wf_qid filterMap
         val () = stdErr_print (String.concat
             ["    Associated contig type : ",contig_qid, "\n\n"])
         val filter_string =
              replace (full inbuf_decl)
                      (full fill_input_decl)
                      (full outFns)
                      (full bufsize_origin)
                      (full byte_size_string)
                      (full inportName)
                      (full contig_qid)
         val fileName = String.concat [targetDir, "/", snd qid, ".cml"]
         val ostrm = TextIO.openOut fileName
     in
         TextIO.output(ostrm,filter_string);
         TextIO.closeOut ostrm
     end
     handle e => raise wrap_exn "AADL" "inst_filter_template" e)
   | otherwise => raise ERR "inst_filter_template" "expected a FilterDec"
 end
 handle e => raise wrap_exn "inst_filter_template" "" e

fun export_cakeml_filters dir const_alist filterdecs =
  if null filterdecs then
     ()
  else
  let val qids = map filtdec_qid filterdecs
      val names = map qid_string qids
      val _ = stdErr_print (String.concat
         ["Creating CakeML filter implementation(s) for:\n   ",
          String.concatWith "\n   " names, "\n\n"])
  in
     List.app (inst_filter_template dir const_alist) filterdecs
   ; stdErr_print " ... Done.\n\n"
  end
