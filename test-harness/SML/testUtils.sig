signature testUtils =
sig

    val store32 : Word8Array.array -> int -> int -> unit
    val fetch32 : Word8Array.array -> int -> int

    datatype result = EOS | SHORT of string | EXACT of string

    val getchars : TextIO.instream * int -> result

end
