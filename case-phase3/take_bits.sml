val ERR = mk_HOL_ERR "take_bits";

fun assert b s = if b then () else raise ERR s "assertion failure";

fun take_drop n list =
    SOME(List.take(list, n),List.drop(list, n)) handle _ => NONE;

fun divmod i n = (Int.div(i,n), Int.mod(i,n));

val pow2 = Array.fromList [1,2,4,8,16,32,64,128,256];

fun twoExp n = Array.sub(pow2,n);

fun grab_bits n N =  (* should use dnc *)
 if n <= 0 then []
 else
 let val (i1,b1) = divmod N 2
  in if n = 1 then [b1]
 else let val (i2,b2) = divmod i1 2
  in if n = 2 then [b2,b1]
 else let val (i3,b3) = divmod i2 2
  in if n = 3 then [b3,b2,b1]
 else let val (i4,b4) = divmod i3 2
  in if n = 4 then [b4,b3,b2,b1]
 else let val (i5,b5) = divmod i4 2
  in if n = 5 then [b5,b4,b3,b2,b1]
 else let val (i6,b6) = divmod i5 2
  in if n = 6 then [b6,b5,b4,b3,b2,b1]
 else let val (i7,b7) = divmod i6 2
  in if n = 7 then [b7,b6,b5,b4,b3,b2,b1]
 else [i7,b7,b6,b5,b4,b3,b2,b1]
 end end end end end end end;

fun bytes2bits nlist = List.concat (List.map (grab_bits 8) nlist);

fun byteInterval A i j =
   if i <= j then
      Word8Array.sub(A,i)::byteInterval A (i+1) j
   else [];

(*---------------------------------------------------------------------------*)
(* Chop interval in bits [i..i+width] from byte                              *)
(*---------------------------------------------------------------------------*)

fun byteSegment byte i width =
 let val _ = assert (i + width <= 8) "byteSegment"
     val shift = Word.fromInt (8 - (i + width))
     val byte' = Word8.>>(byte, shift)
     val N = Int.mod(Word8.toInt byte',twoExp width)
 in grab_bits width N
 end;

(*---------------------------------------------------------------------------*)
(* Extract bits [lo..lo+width-1] from A. Bit endianess = BE.                 *)
(*---------------------------------------------------------------------------*)

fun bits_of A lo width =
 let val len = Word8Array.length A
     val (loIndex,i) = divmod lo 8
     val (hiIndex,j) = divmod (lo + width) 8
     val _ = assert (0 <= lo andalso lo + width <= len * 8) "bits_of"
     val lbyte = Word8Array.sub(A,loIndex)
 in
  if width + i <= 8 then
     byteSegment lbyte i width
  else
  let val lbits = byteSegment lbyte i (8 - i)
      val (cbytes,rbyte) = front_last (byteInterval A (loIndex+1) hiIndex)
      val cbits = bytes2bits (List.map Word8.toInt cbytes)
      val shift = Word.fromInt (8 - j)
      val rbyte' = Word8.>>(rbyte, shift)
      val rbits = grab_bits j (Word8.toInt rbyte')
  in
    lbits @ cbits @ rbits
  end
 end;


(*---------------------------------------------------------------------------*)
(* Map from bit lists to N                                                   *)
(*---------------------------------------------------------------------------*)

val ii_0 = IntInf.fromInt 0;
val ii_2 = IntInf.fromInt 2;
val ii_256 = IntInf.fromInt 256;

fun bitsValBE blist =
 let open IntInf
 in rev_itlist (fn bit => fn acc => IntInf.fromInt(bit) + ii_2 * acc) blist 0
 end;

fun unsigned blist = IntInf.toInt(bitsValBE blist)

fun twos_comp blist =
 let val U = IntInf.pow(ii_2, length blist)
     val halfU = IntInf.div(U,ii_2)
     val n = IntInf.fromInt(unsigned blist)
  in
    IntInf.toInt(if IntInf.<(n,halfU) then n else IntInf.-(n,U))
 end;

fun chunkBy n list =
 let fun chunk list =
      if length list <= n then [list]
      else let val (c,rst) = Option.valOf (take_drop n list)
           in c::chunk rst
           end
 in if n < 1 orelse null list then
         raise ERR "chunkBy" "malformed input"
    else chunk list
 end;

fun bytesValBE blist =
  List.map bitsValBE (chunkBy 8 blist)
  handle e => raise wrap_exn "take_bits" "bytesVal" e;

fun stringVal blist =
  String.implode (List.map (Char.chr o IntInf.toInt) (bytesValBE blist));

fun boolVal 0 = false
  | boolVal 1 = true
  | boolVal otherwise = raise ERR "boolVal" "";
