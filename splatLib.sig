signature splatLib =
sig
 include Abbrev

  type regexp = Regexp_Type.regexp

  datatype width
    = BITWIDTH of int
    | BYTEWIDTH of int
  
  datatype atomic =
     Interval of 
       {span : IntInf.int * IntInf.int,
        encoding : Regexp_Numerics.encoding,
        endian : Regexp_Numerics.endian,
        width  : width,
        encoder : IntInf.int -> string,
        decoder : string -> IntInf.int,
        recog  : Regexp_Type.regexp}
    | Enumset of 
       {enum_type : hol_type,
        constr_codes : (term * int) list,
        logic : Enum_Encode.logic_info,
        recog : Regexp_Type.regexp}
    | StringLit of string
    | Raw of width


  datatype format
    = ATOM of atomic
    | CONCAT of format list
    | LIST of format
    | ARRAY of format * int
    | UNION of format * format
    | PACKED of format list * width


  type filter_info
   = {name : string,
      regexp : Regexp_Type.regexp,
      encode_def : thm, 
      decode_def : thm,
      inversion : term,
      correctness : term,
      receiver_correctness : term,
      implicit_constraints : thm option};

  val filter_correctness : string * thm -> filter_info

  val IN_CHARSET_NUM_TAC : tactic

end
