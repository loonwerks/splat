open Regexp_Type regexpLib Regexp_Numerics;

val _ = Regexp_Type.set_intervalFn (twos_comp_interval LSB 4);

val DFA =
  #matchfn
    (regexpLib.gen_dfa SML
       (Regexp_Type.fromQuote `\i{~90,90}\i{~180,180}\i{0,15000}`));

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
     fun handler V =
      if DFA V then
          (output(stdErr, "Filter: pass\n");
           output(stdOut,V);  (* pass it on *)
           flushOut stdOut
          )
      else
          output(stdErr,"Filter Rejects :\n\n  "^V^"\n\n")
     fun filter istrm =
      case getchars(istrm,12)
       of EOS => (output(stdErr, String.concat["\nFilter: end of input, terminating.\n"])
                  ; OS.Process.terminate OS.Process.success)
        | SHORT V => handler V  (* expected to be false, cuz short, but still check *)
        | EXACT V => handler V
in
  while true
  do filter stdIn
end
