signature Enum_Encode =
sig
 
 include Abbrev

 type ('a,'b) fmap = ('a,'b) Redblackmap.dict

 type logic_info 
    = {enc : term,
       dec : term,
       enc_def : thm,
       dec_def : thm,
       dec_enc : thm}

 val define_enum_encoding : hol_type -> logic_info

  type enumMap = (hol_type, ((term * int) list * logic_info)) fmap

  val base_enumMap : enumMap
  val the_enumMap : unit -> enumMap
  val insert_enum_type : hol_type * term list * logic_info -> unit

end
