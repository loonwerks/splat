structure testUtils :> testUtils =
struct

fun inc x = x := !x + 1;
fun reset x = x := 0;

fun store32 A i j =
 PackWord32Little.update
    (A,i,LargeWord.fromInt j)

(*---------------------------------------------------------------------------*)
(* top 32 bits of w32big are 0, since we've come from 4 bytes, so we need to *)
(* do some work to recover negative numbers.                                 *)
(*---------------------------------------------------------------------------*)

local
  val top32 = 4294967296
  val half32 = top32 div 2
in
fun fetch32 A i =
 let val w32big = PackWord32Little.subArr(A,i)
     val n = LargeWord.toInt w32big
 in if n < half32 then
      n
    else ~(top32 - n)
 end
end

datatype result = EOS | SHORT of string | EXACT of string;

fun getchars (istrm,n) =
 let open TextIO
     val V = inputN (istrm,n)
     val k = String.size V
 in if k = 0 then
      EOS else
    if k = n then EXACT V else SHORT V
 end


end
