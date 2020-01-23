structure testUtils :> testUtils =
struct

fun store32 A i j =
 PackWord32Little.update
    (A,i,LargeWord.fromInt j)

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
