signature splatLib =
sig
 include Abbrev

  type regexp = Regexp_Type.regexp

  datatype width
    = BITWIDTH of int
    | BYTEWIDTH of int
  
  datatype fieldrep =
     Interval of 
       {span     : IntInf.int * IntInf.int,
        encoding : Regexp_Numerics.encoding,
        endian   : Regexp_Numerics.endian,
        width    : width,
        encoder  : IntInf.int -> string,
        decoder  : string -> IntInf.int,
        regexp   : regexp}
    | Enumset of 
       {enum_type    : hol_type,
        constr_codes : (term * int) list,
        elts         : term list,
        codec        : Enum_Encode.enum_codec,
        regexp       : regexp}
    | StringLit of 
       {strlit : string,
        regexp : regexp}
    | Raw of 
       {width  : width,
        regexp : regexp}


  type filter_info
   = {name : string,
      regexp : Regexp_Type.regexp,
      encode_def : thm, 
      decode_def : thm,
      inversion : term,
      correctness : term,
      receiver_correctness : term,
      implicit_constraints : thm option,
      manifest : (term * fieldrep) list};

  datatype shrink = Optimize of int | Uniform of int

  type int_format = shrink * Regexp_Numerics.endian * Regexp_Numerics.encoding
						      
  val gen_filter_artifacts : int_format -> string * thm -> filter_info

  val IN_CHARSET_NUM_TAC : tactic

  val pure_in_charset_conv : conv
  val in_charset_conv : conv
  val in_charset_conv_ss : simpLib.ssfrag
end
