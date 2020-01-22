open Regexp_Type regexpLib Regexp_Numerics;

val _ = Regexp_Type.set_intervalFn (twos_comp_interval LSB 4);

val regexp = Regexp_Type.fromQuote `\i{~90,90}\i{~180,180}\i{0,15000}`;

val DFA = regexpLib.gen_dfa SML regexp;

val test = #matchfn DFA;

fun drop_nl s =
 let val n = String.size s
 in
   if n = 0 then s else
   if String.sub(s,n-1) = #"\n" then
     String.substring(s,0,n-1)
   else s
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

let open TextIO
    val istrm = openIn "input.bin"
    fun checkFile () =
      case getchars(istrm,12)
       of EOS => true
        | SHORT V => test V  (* expected to be false, cuz short, but still check *)
        | EXACT V => if test V then checkFile() else false
    val result = time checkFile()
in
    closeIn istrm;
    result
end

(*
    print ("Input size (bytes): "^Int.toString (String.size s)^"\n\n");
*)

(*
fun CLOSED_INST theta th =
 let val bvars = fst (strip_forall (concl th))
     val domvars = map #redex theta
     val bvars' = filter (not o C (op_mem aconv) domvars) bvars
 in GENL bvars' (INST theta (SPEC_ALL th))
 end
*)
