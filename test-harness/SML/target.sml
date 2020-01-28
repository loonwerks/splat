(*---------------------------------------------------------------------------*)
(* top 32 bits of w32big are 0, since we've come from 4 bytes, so we need to *)
(* do some work to recover negative numbers.                                 *)
(*---------------------------------------------------------------------------*)

open testUtils;

val B = Word8Array.array(12, Word8.fromInt 0);

fun fill (B,s) = Byte.packString(B,0,Substring.full s)

fun main() =
 let open TextIO
  fun get_mesg istrm =
    case getchars(istrm,12)
     of EXACT V =>
        let val _ = fill (B,V)
            val i = fetch32 B 0
            val j = fetch32 B 1
            val k = fetch32 B 2
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
