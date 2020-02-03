(*===========================================================================*)
(* Provides a source for the filter to filter.                               *)
(*===========================================================================*)

open testUtils;

(*---------------------------------------------------------------------------*)
(* Note: SML provides a few flavours of integer. We assume here that an int  *)
(* is 32 bits, in accordance with the assumption made by today's C compilers.*)
(*---------------------------------------------------------------------------*)

val A = Word8Array.array(12, Word8.fromInt 0);

val gn = Random.newgen();

val randFns =
  map Random.range
      [(~90,90), (~180,180), (0,15000), (0,4294967296)];

val [seg1RandElt,seg2RandElt,seg3RandElt,arb32] = randFns;

fun arb_mesg() =
 let val i = arb32 gn
     val j = arb32 gn
     val k = arb32 gn
 in
     store32 A 0 i
   ; store32 A 1 j
   ; store32 A 2 k
   ; (Byte.bytesToString(Word8Array.vector A),(i,j,k))
 end

fun mesg () =
 let val i = seg1RandElt gn
     val j = seg2RandElt gn
     val k = seg3RandElt gn
 in
     store32 A 0 i
   ; store32 A 1 j
   ; store32 A 2 k
   ; (Byte.bytesToString(Word8Array.vector A), (i,j,k))
 end

fun int3string (i,j,k) =
 String.concat
     [Int.toString i,", ", Int.toString j,", ",Int.toString k,"\n"];


fun main () =
 let open TextIO
   val counter = ref 0
   fun next_mesg() =
     (inc counter;
      if !counter mod 10 = 0 then
         (reset counter; arb_mesg())
      else mesg())
 in
   while true
   do let val (msg,(i,j,k)) = next_mesg()
       in
          output(stdErr, String.concat["Src: ", int3string(i,j,k)])
        ; output(stdOut,msg)
        ; flushOut stdOut
        ; Posix.Process.sleep (Time.fromReal 0.2)
       end
 end
