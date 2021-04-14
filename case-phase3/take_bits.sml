val ERR = mk_HOL_ERR "take_bits";

(*---------------------------------------------------------------------------*)
(* Break number up into a base-k representation. Big-endian.                 *)
(*---------------------------------------------------------------------------*)

fun wordNlistBE k ii =
 let fun accFn ii acc =
  if ii < k then
       ii::acc
  else let val (d,m) = IntInf.divMod(ii,k)
       in accFn d (m::acc)
       end
 in accFn ii []
 end;

(*---------------------------------------------------------------------------*)
(* Little-endian version.                                                    *)
(*---------------------------------------------------------------------------*)

fun wordNlist k ii = List.rev(wordNlistBE k ii);

val ii_0 = IntInf.fromInt 0;
val ii_2 = IntInf.fromInt 2;
val ii_256 = IntInf.fromInt 256;

val bits_of = wordNlist ii_2;
val bytes_of = wordNlist ii_256;

fun ii_byte ii = Word8.fromInt(IntInf.toInt ii);
fun byte_ii byte = IntInf.fromInt(Word8.toInt byte);

(*---------------------------------------------------------------------------*)
(* Map a LE byte array B = [b0,b1,...,b(n-1)] to N = b0 + 256 * (b1 + ...)   *)
(*---------------------------------------------------------------------------*)

fun w8array_to_ii bytes =
  let open IntInf
      fun step (byte,ii) = byte_ii byte + ii_256 * ii
  in Word8Array.foldr step ii_0 bytes
  end

fun ii_to_w8array ii = Word8Array.fromList (List.map ii_byte (bytes_of ii));

(*---------------------------------------------------------------------------*)
(* Take n bits off an ii. Return a pair (bits,N') where N' is the remaining  *)
(* number and bits is the big-endian list of bits.                           *)
(*---------------------------------------------------------------------------*)

fun ncopies x n = if n<1 then [] else x::ncopies x (n-1);

fun zeroPadR n bits = bits @ ncopies ii_0 (n - length bits);

fun take_bits nbits N =
 let val (d,m) = IntInf.divMod(N, IntInf.pow(ii_2,nbits))
 in (zeroPadR nbits (bits_of m), d)
 end;

(*---------------------------------------------------------------------------*)
(* Tests                                                                     *)
(*---------------------------------------------------------------------------*)

fun string_to_w8array s =
  Word8Array.fromList
      (List.map Byte.charToByte (String.explode s));

fun w8array_to_string A = Byte.bytesToString (Word8Array.vector A);

val N = w8array_to_ii (string_to_w8array "100");
val s = w8array_to_string(ii_to_w8array N);

val N = w8array_to_ii
        (string_to_w8array "rumblefishrumblefishrumblefishrumblefishrumblefish");
val s = w8array_to_string(ii_to_w8array N);

(*---------------------------------------------------------------------------*)
(* Map a LE list L = [b0,b1,...,b(n-1)] to N = b0 + 256 * (b1 + ...)         *)
(*---------------------------------------------------------------------------*)

fun bitsVal blist = itlist (fn bit => fn acc => bit + ii_2 * acc) blist 0;

fun chunkBy n list =
 let fun chunk list =
      if length list = n then [list]
      else let val (c,rst) = Option.valOf (take_drop n list)
           in c::chunk rst
           end
 in if n < 1 orelse null list orelse
       length list mod n <> 0 then
         raise ERR "chunkBy" "malformed input"
    else chunk list
 end;

fun bytesVal blist =
  List.map bitsVal (chunkBy 8 blist)
  handle e => raise wrap_exn "take_bits" "bytesVal" e;
