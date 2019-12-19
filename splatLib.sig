signature splatLib =
sig
 include Abbrev

  type regexp = Regexp_Type.regexp
  type endian = Regexp_Numerics.endian
  type encoding = Regexp_Numerics.encoding

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
        regexp   : regexp,
      constraint : term}
    | Enumset of
       {enum_type    : hol_type,
        constr_codes : (term * int) list,
        elts         : term list,
        codec        : Enum_Encode.enum_codec,
        regexp       : regexp,
        constraint   : term}
    | StringLit of
       {strlit : string,
        regexp : regexp,
      constraint : term}
    | Raw of
       {width  : width,
        regexp : regexp,
      constraint : term}


  type filter_info
    = {name : string,
       regexp : Regexp_Type.regexp,
       manifest : (term * fieldrep) list,
       implicit_constraints : thm option,
       tv : term}

  val field_encoder : fieldrep -> term
  val field_decoder : fieldrep -> term

  datatype shrink = Optimize of int | Uniform of int

  type int_format = shrink * endian * encoding

  val gen_filter_artifacts : int_format -> (string * string) * thm -> filter_info

  val IN_CHARSET_NUM_TAC : tactic

  val pure_in_charset_conv : conv
  val in_charset_conv : conv
  val in_charset_conv_ss : simpLib.ssfrag

  val mesg_ss : simpLib.simpset
  val splat_ss : simpLib.simpset
  val TV_TAC : fieldrep list -> tactic
end
