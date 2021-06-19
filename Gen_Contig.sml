structure Gen_Contig =
struct

open Lib Feedback MiscLib AST;
open ByteContig;


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

(*
val indty = Type.ind;
val _ = new_type("ptree",0);
val ptree = mk_type("ptree",[]);

fun mk_array_term eltFn_term =
 let val mk_array = mk_var("mk_array", (ptree --> ind) --> ptree --> ind)
 in mk_comb(mk_array,eltFn_term)
 end;

val mk_bool_term = mk_var ("mk_bool", ptree --> ind)
val mk_char_term = mk_var ("mk_char", ptree --> ind)
val mk_intLE_term = mk_var ("mk_intLE", ptree --> ind)
val mk_floatLE_term = mk_var ("mk_floatLE", ptree --> ind);
*)
val mk_bool_node = ConstExp(IdConst("Decode","mk_bool"));
val mk_char_node = ConstExp(IdConst("Decode","mk_char"));
val mk_intLE_node = ConstExp(IdConst("Decode","mk_intLE"));
val mk_floatLE_node = ConstExp(IdConst("Decode","mk_floatLE"));
fun mk_array_node eltFn = Fncall(("Decode","mk_array"),[eltFn]);

(*---------------------------------------------------------------------------*)
(* The decoder will be given a parse tree where the leaves are annotated     *)
(* with atoms telling what kind of interpretation to give.                   *)
(*---------------------------------------------------------------------------*)

fun decoder_of decodeE ty =
 case ty
  of BaseTy BoolTy    => mk_bool_node
   | BaseTy CharTy    => mk_char_node
   | BaseTy (IntTy _) => mk_intLE_node
   | BaseTy FloatTy   => mk_floatLE_node
   | BaseTy DoubleTy  => mk_floatLE_node
   | BaseTy other => raise ERR "decoder_of" "unhandled base type"
   | ArrayTy (elty,dims) => mk_array_node (decoder_of decodeE elty)
   | NamedTy qid =>
       (case decodeE qid
         of NONE => raise ERR "decoder_of" ("unknown type: "^qid_string qid)
          | SOME decoder => decoder)
   | RecdTy (qid, fields) =>
       (case decodeE qid
         of NONE => raise ERR "decoder_of" ("unknown type: "^qid_string qid)
          | SOME decoder => decoder)
;

(*---------------------------------------------------------------------------*)
(*  (qid,[f1:ty1, ..., fn:tyn]) => mk_qid [|ty1|] ...  [|tyn|]               *)
(*---------------------------------------------------------------------------*)

fun ptrees_of_recd ptree =
 case ptree
  of RECD fields => map snd fields
   | otherwise => raise ERR "ptrees_of_RECD" "expected a RECD";

fun appFn f x = f x;

val decodeE = PP_CakeML.assocFn [] : qid -> AST.exp option;

fun listLit elts = Fncall(("","List"), elts);

fun recd_decoder_def ty decodeE =
 let open listSyntax
 in
 case ty
  of RecdTy (qid, fields) =>
     let val field_decoders = map (decoder_of decodeE o snd) fields
         val recdName = snd qid
         fun recd_constr e = Fncall(("Decode",recdName^"Recd"),[e])
         val ptreeVar = VarExp "ptree"
         val decoder_LHS = Fncall(("Decode","decode_"^snd qid),[ptreeVar])
         val ptrees_app = Fncall(("Decode","ptrees_of_recd"),[ptreeVar])
         val appFn_node = ConstExp(IdConst("Utils","appFn"))
         val map2node =
	     Fncall(("Utils","map2"),
                    [appFn_node, listLit field_decoders,ptrees_app])
     in
       Binop(Equal,decoder_LHS, recd_constr map2node)
     end
  | otherwise => raise ERR "recd_decoder_def" "expected a RecdTy"
 end;

val tydec_to_ty = PP_CakeML.tydec_to_ty;

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
