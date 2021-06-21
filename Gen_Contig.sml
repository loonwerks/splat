structure Gen_Contig =
struct

open Lib Feedback MiscLib AST;
open ByteContig;

local open PP_CakeML in end;


val ERR = mk_HOL_ERR "Gen_Contig";

val default_num_width = 32;  (* bits *)

val () = defaultNumKind := Nat (SOME default_num_width);

fun bits_to_bytes bits =
  if bits mod 8 = 0 then
     bits div 8
  else raise ERR "bits_to_bytes" "expected a mulitple of 8";

fun current_default_num_width () =
    case !defaultNumKind
     of Nat (SOME bits) => bits_to_bytes bits
      | Int (SOME bits) => bits_to_bytes bits
      | otherwise       => default_num_width
;

fun dest_dim (ConstExp(IntLit{value=i,kind})) = i
  | dest_dim otherwise = raise ERR "dest_dim" "";

fun contig_of env ty =
 let open ByteContig
 in case ty
     of BaseTy BoolTy => Basic Bool
      | BaseTy CharTy => Basic Char
      | BaseTy (IntTy (Nat (SOME bits))) => Basic (Unsigned (bits_to_bytes bits))
      | BaseTy (IntTy (Int (SOME bits))) => Basic (Signed (bits_to_bytes bits))
      | BaseTy (IntTy (Nat NONE)) => Basic (Unsigned (current_default_num_width()))
      | BaseTy (IntTy (Int NONE)) => Basic (Signed (current_default_num_width()))
      | BaseTy FloatTy  => Basic Float
      | BaseTy DoubleTy => Basic Double
      | BaseTy other    => raise ERR "contig_of" "unhandled base type"
      | NamedTy qid =>
          (case env qid
            of NONE => raise ERR "contig_of" ("unknown type: "^qid_string qid)
             | SOME ty => contig_of env ty)
      | RecdTy (qid, fields) => Recd (map (I##contig_of env) fields)
      | ArrayTy (elty,[dim]) => Array (contig_of env elty, intLit (dest_dim dim))
      | ArrayTy (elty,otherdims) => raise ERR "contig_of" "only single-dimension arrays handled"
 end

fun sumlist [] = 0
  | sumlist (h::t) = h + sumlist t;

fun maxlist [] = 0
  | maxlist (h::t) = Int.max(h, maxlist t);

fun size_of (env as (Consts,Decls,atomWidth)) contig =
let open ByteContig
 in case contig
     of Void => 0
      | Assert _ => 0
      | Basic atom => atomWidth atom
      | Declared s => size_of env (assoc s Decls)
      | Raw (intLit i) => i
      | Raw otherwise => raise ERR "size_of" "Raw: expected constant arg"
      | Recd fields => sumlist (map (size_of env o snd) fields)
      | Array (c,intLit i) => size_of env c * i
      | Array otherwise => raise ERR "size_of" "Array: expected constant arg"
      | Union choices => maxlist (map (size_of env o snd) choices)
end;

val mk_bool_node = VarExp"mk_bool"
val mk_char_node = VarExp "mk_char"
val mk_intLE_node = VarExp "mk_intLE"
val mk_floatLE_node = VarExp "mk_floatLE"
fun mk_array_node eltFn = Fncall(("","mk_array"),[eltFn]);

(*---------------------------------------------------------------------------*)
(* The decoder will be given a parse tree where the leaves are annotated     *)
(* with atoms telling what kind of interpretation to give.                   *)
(*---------------------------------------------------------------------------*)

fun decoder_of tyE decodeE ty =
 case ty
  of BaseTy BoolTy    => mk_bool_node
   | BaseTy CharTy    => mk_char_node
   | BaseTy (IntTy _) => mk_intLE_node
   | BaseTy FloatTy   => mk_floatLE_node
   | BaseTy DoubleTy  => mk_floatLE_node
   | BaseTy other => raise ERR "decoder_of" "unhandled base type"
   | ArrayTy (elty,dims) => mk_array_node (decoder_of tyE decodeE elty)
   | NamedTy qid =>
       (case tyE qid
         of NONE => raise ERR "decoder_of" ("unknown type: "^qid_string qid)
          | SOME ty' => decoder_of tyE decodeE ty')
   | RecdTy (qid, fields) =>
       (case decodeE qid
         of NONE => raise ERR "decoder_of" ("unknown type: "^qid_string qid)
          | SOME decoder => decoder)
;

fun uptoFn f lo hi =
  let fun iter i = if i > hi then [] else f i::iter (i+1)
  in iter lo
  end

val AppExp = PP_CakeML.AppExp;

(*---------------------------------------------------------------------------*)
(*  fun decode_X ptree =                                                     *)
(*    case ptree                                                             *)
(*     of RECD [a,...,k] => X (decode1 (snd a) ... (decodek (snd k))         *)
(*      | otherwise => raise Utils.ERR "decode_X" "expected a RECD"          *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun mk_decoder_def tyE decodeE ty =
 let val dummyTy = NamedTy("","dummyTy")
 in
 case ty
  of RecdTy (qid, fields) =>
     let val decoderName = "decode_"^snd qid
         val field_decoders = map (decoder_of tyE decodeE o snd) fields
         val vars = uptoFn (fn i => VarExp("v"^Int.toString i)) 1 (length fields)
         val varspat = listLit vars
         val recdpat = Fncall(("","ByteContig.RECD"),[varspat])
         val recdName = snd qid
         fun mk_recd elist = Fncall(("Defs",recdName^"Recd"),elist)
         fun mk_decode_app d v = AppExp [d, Fncall(("","snd"),[v])]
         val case_rhs = mk_recd (map2 mk_decode_app field_decoders vars)
         val main_clause = (recdpat,case_rhs)
         val errpat = VarExp"otherwise"
         val err_rhs = Fncall(("","raise"),
                       [VarExp"Utils.ERR",ConstExp(StringLit decoderName),
                        ConstExp(StringLit "unexpected parse tree")])
         val ptreeVar = VarExp "ptree"
         val case_exp = Fncall(("","CASE"),
                         [ptreeVar,AppExp[recdpat,case_rhs],AppExp[errpat,err_rhs]])
     in
        AADL.FnDec(("",decoderName),[("ptree",dummyTy)],NamedTy qid,case_exp)
     end
  | otherwise => raise ERR "recd_decoder_def" "expected a RecdTy"
 end;

val tydec_to_ty = PP_CakeML.tydec_to_ty;
val assocFn = PP_CakeML.assocFn;

fun qid_of_recdTy (RecdTy(qid,_)) = qid
  | qid_of_recdTy other = raise ERR "qid_of_recdTy" "";

val is_recd_ty = Lib.can qid_of_recdTy;

fun mk_decodeE tylist =
  let fun munge (qid as(pkgName,tyName)) =
         (qid,ConstExp(IdConst("","decode_"^tyName)))
  in mapfilter (munge o qid_of_recdTy) tylist
  end;

fun decoders tyE tylist =
 let val decodeE = assocFn(mk_decodeE tylist)
     fun itFn ty defs =
       if is_recd_ty ty then
          mk_decoder_def tyE decodeE ty::defs
       else defs
 in
   List.rev(rev_itlist itFn tylist [])
 end


(*
fun atomic_width atom =
let open ByteContig
 in case atom
     of Bool => 1
      | Signed i => i
      | Unsigned i => i
      | Blob => raise ERR "atomic_width" "Blob"
end;

val trivEnv = ([],[],atomic_width);

val i32 = Basic (Signed 4);

val coord = Recd [
  ("lat", i32),
  ("lon", i32),
  ("alt", i32)
 ];

val Map = Array(coord, intLit 2);

size_of trivEnv (Basic (Unsigned 4));
size_of trivEnv Map;
*)

end
