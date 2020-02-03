signature testUtils =
sig

   val inc : int ref -> unit
   val reset : int ref -> unit

   val store32 : Word8Array.array -> int -> int -> unit
   val fetch32 : Word8Array.array -> int -> int


   datatype result = EOS | SHORT of string | EXACT of string

   val getchars : TextIO.instream * int -> result

end
