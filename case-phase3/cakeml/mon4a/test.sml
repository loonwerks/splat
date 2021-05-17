val ERR = Feedback.mk_HOL_ERR "mon4a test harness";

val EventByte = Word8.fromInt 1;

fun crlf ch = (ch = #"\n") orelse (ch = #"\r");

fun inputLines strm = String.tokens crlf (TextIO.inputAll strm);

fun chunk2 list =
 case list
  of [] => []
   | a::b::t => (a,b)::chunk2 t
   | otherwise => raise ERR "chunk2" "odd length input"

fun hexchar2int ch =
 case ch
  of #"0" => 0
   | #"1" => 1
   | #"2" => 2
   | #"3" => 3
   | #"4" => 4
   | #"5" => 5
   | #"6" => 6
   | #"7" => 7
   | #"8" => 8
   | #"9" => 9
   | #"A" => 10
   | #"B" => 11
   | #"C" => 12
   | #"D" => 13
   | #"E" => 14
   | #"F" => 15
   | #"a" => 10
   | #"b" => 11
   | #"c" => 12
   | #"d" => 13
   | #"e" => 14
   | #"f" => 15
   | otherwise => raise ERR "hexchar2int" "Domain";

(*---------------------------------------------------------------------------*)
(* Expecting CSV file                                                        *)
(*---------------------------------------------------------------------------*)

fun get_rows fileName =
 let val instrm = TextIO.openIn fileName
     val rows = inputLines instrm
 in
     TextIO.closeIn instrm;
     rows
 end;

fun byte_of (a,b) = Word8.fromInt (hexchar2int a * 16 + hexchar2int b);

fun mk_bytes row = EventByte::List.map byte_of (chunk2 (String.explode row));

fun row2w8array row =
   Word8Array.vector
     (Word8Array.fromList
       (mk_bytes row));

fun csv2byteA fileName = List.map row2w8array (get_rows fileName);

(* Byte.bytesToString
fun csv2strings fileName = List.map row2string (get_rows fileName);
 *)

fun convert file1 file2 =
 let val byteArrays = csv2byteA file1
     val ostrm = BinIO.openOut file2
     val () = List.app (curry BinIO.output ostrm) byteArrays
 in BinIO.closeOut ostrm
 end;

(*---------------------------------------------------------------------------*)
(* Try it on an example.                                                     *)
(*---------------------------------------------------------------------------*)

val _ = convert "data.csv" "test-1";

use "../../BitFns.sml";
use "../../BitContig.sig";
use "../../BitContig.sml";
open BitContig;

use "../../adsb.contig";

val instrm = TextIO.openIn "test-1";
val row1 = TextIO.inputN(instrm,4387);
val _ = TextIO.closeIn instrm;

debug;
