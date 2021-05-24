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
(*
val _ = convert "data.csv" "test-1";

use "../../BitFns.sml";
use "../../BitContig.sig";
use "../../BitContig.sml";
open BitContig;

use "../../adsb.contig";

fun phase3_atom_width atm =
 case atm
  of Bool       => 1
   | Signed i   => i
   | Unsigned i => i
   | Blob => raise ERR "atom_width" "unknown width of Raw";

(*---------------------------------------------------------------------------*)
(* Valuation functions                                                       *)
(*---------------------------------------------------------------------------*)

fun valFn atm bits =
 case atm
  of Signed i => SOME (BitFns.twos_comp bits)
   | otherwise => SOME (BitFns.unsigned bits);

fun dvalFn atm bits = raise ERR "dvalFn" "undefined";

val theEnv = ([],[],phase3_atom_width,valFn,dvalFn);

(*---------------------------------------------------------------------------*)
(* Takes a contig and a decoder and combines them into a parser.             *)
(*---------------------------------------------------------------------------*)

fun genParse env p A =
 case p
  of (contig,mk_data)
 =>
 case parseFn env A (VarName"root") contig
                 ([],0,empty_lvalMap)
  of SOME ([ptree],_,_) => total mk_data ptree
   | otherwise => NONE;

fun adsbParse p A = genParse theEnv p A;


fun is_event byteA =
  0 < Word8Array.length byteA andalso
  Word8Array.sub(byteA,0) = Word8.fromInt 1;

fun eventParse p byteA =
 if not(is_event byteA) then
    NONE
 else
  let val (contig,mk_data) = p
  in case BitContig.parseFn
            theEnv byteA (BitContig.VarName"root") contig
              ([],1,BitContig.empty_lvalMap())
      of Some([ptree],_,_) => Some (Utils.total mk_data ptree)
       | otherwise => Some None
  end;


val instrm = TextIO.openIn "test-1";
val row1 = TextIO.inputN(instrm,4387);
val _ = TextIO.closeIn instrm;

val char2byte = Word8.fromInt o Char.ord;

val rowA =
 Word8Array.tabulate
   (String.size row1,
    fn i => char2byte (String.sub(row1,i)));

val PASS(pos, theta) = predFn theEnv rowA ([(VarName"root",adsb_messages)],8,empty_lvalMap);
Redblackmap.listItems theta;

val Heartbeat = BitFns.total_bits_of rowA 8 56;
val Ownship_messageID = BitFns.total_bits_of rowA 57 8;

BitFns.total_bits_of rowA 76 4;
BitFns.total_bits_of rowA 80 24;
valFn (Unsigned 24) (Option.valOf (BitFns.total_bits_of rowA 80 24));

(root.Ownship.addrType, (u4, (76, 4))),
(root.Ownship.address, (u24, (80, 24))),

val blist =
    [1, 0, 1, 0,  1, 0, 1, 1,
     1, 1, 0, 0,  1, 1, 0, 1,
     1, 1, 1, 0,  1, 1, 1, 1];

10, 11, 12, 13, 14, 15
 A,  B,  C,  D,  E,  F

*)