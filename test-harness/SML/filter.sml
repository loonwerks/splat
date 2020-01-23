open Regexp_Type regexpLib Regexp_Numerics testUtils;

val _ = Regexp_Type.set_intervalFn (twos_comp_interval LSB 4);

val DFA =
  #matchfn
    (regexpLib.gen_dfa SML
       (Regexp_Type.fromQuote `\i{~90,90}\i{~180,180}\i{0,15000}`));

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
