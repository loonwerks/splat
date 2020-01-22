(*---------------------------------------------------------------------------*)
(* top 32 bits of w32big are 0, since we've come from 4 bytes, so we need to *)
(* do some work to recover negative numbers.                                 *)
(*---------------------------------------------------------------------------*)

val B = Word8Array.array(12, Word8.fromInt 0);

fun fill (B,s) = Byte.packString(B,0,Substring.full s)

local
  val top32 = 4294967296
  val half32 = top32 div 2
in
fun fetch B i =
 let val w32big = PackWord32Little.subArr(B,i)
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

fun main() =
 let open TextIO
  fun get_mesg istrm =
    case getchars(istrm,12)
     of EXACT V =>
        let val _ = fill (B,V)
            val i = fetch B 0
            val j = fetch B 1
            val k = fetch B 2
        in
          output(stdOut,
            String.concat["Target received : ", Int.toString i,", ",
                          Int.toString j,", ",Int.toString k,"\n\n"])
          ; flushOut stdOut
        end
      | SHORT V => output(stdOut, String.concat["\n\nShort message!\n\n"])
      | EOS => (output(stdErr, String.concat["\nTarget: end of input, terminating.\n"])
                ; OS.Process.terminate OS.Process.success)

in
    while true
    do get_mesg stdIn
end
