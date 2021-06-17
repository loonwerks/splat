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
      | BaseTy CharTy => Basic (Unsigned 1)
      | BaseTy (IntTy (Nat (SOME bits))) => Basic (Unsigned (bits_to_bytes bits))
      | BaseTy (IntTy (Int (SOME bits))) => Basic (Signed (bits_to_bytes bits))
      | BaseTy (IntTy (Nat NONE)) => Basic (Unsigned (current_default_num_width()))
      | BaseTy (IntTy (Int NONE)) => Basic (Signed (current_default_num_width()))
      | BaseTy FloatTy  => raise ERR "FloatTy" "not handled yet"
      | BaseTy DoubleTy => raise ERR "DoubleTy" "not handled yet"
      | BaseTy other    => raise ERR "contig_of" "unhandled base type"
      | NamedTy qid => assoc qid env
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
