signature Enum_Encode =
sig
 
 include Abbrev

 type ('a,'b) fmap = ('a,'b) Redblackmap.dict

 type enum_codec
    = {enc : term,
       dec : term,
       enc_def : thm,
       dec_def : thm,
       dec_enc : thm}

 val define_enum_encoding : hol_type -> enum_codec

 type enumMap = (hol_type, ((term * int) list * enum_codec)) fmap

 val base_enumMap : enumMap
 val the_enumMap : unit -> enumMap
 val insert_enum_type : hol_type * term list * enum_codec -> unit

end
