(*===========================================================================*)
(* Provides a source for the filter to filter.                               *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Note: SML provides a few flavours of integer. We assume, for now, that an *)
(* int is 32 bits, in accordance with typical C compilers (for now).         *)
(*---------------------------------------------------------------------------*)

val A = Word8Array.array(12, Word8.fromInt 0);

fun store A i j =
 PackWord32Little.update
    (A,i,LargeWord.fromInt j)

val gn = Random.newgen();
val randFns =
  map Random.range
      [(~90,90), (~180,180), (0,15000), (0,4294967296)];
val [seg1RandElt,seg2RandElt,seg3RandElt,arbElt] = randFns;

fun arb_mesg() =
 let val i = arbElt gn
     val j = arbElt gn
     val k = arbElt gn
     val _ = store A 0 i
     val _ = store A 1 j
     val _ = store A 2 k
 in
   (Byte.bytesToString(Word8Array.vector A),(i,j,k))
 end

fun mesg () =
 let val i = seg1RandElt gn
     val j = seg2RandElt gn
     val k = seg3RandElt gn
     val _ = store A 0 i
     val _ = store A 1 j
     val _ = store A 2 k
 in
   (Byte.bytesToString(Word8Array.vector A), (i,j,k))
 end

fun main () =
 let open TextIO
     val counter = ref 0
     fun inc x = x := !x + 1
 in
   while true
   do let val _ = inc counter
          val (s,(i,j,k)) =
              if !counter mod 10 = 0 then
                 (counter := 0; arb_mesg())
              else mesg()
           val _ = output(stdErr,
                     String.concat["Src: ", Int.toString i,", ",
                         Int.toString j,", ",Int.toString k,"\n"])
          val _ = output(stdOut,s)
          val _ = flushOut stdOut
          val _ = Posix.Process.sleep (Time.fromReal 0.5)
       in ()
       end
 end;
