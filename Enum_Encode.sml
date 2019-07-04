structure Enum_Encode :> Enum_Encode = 
struct

open HolKernel Parse boolLib bossLib MiscLib 

local open splatTheory in end;

 type logic_info 
    = {enc : term,
       dec : term,
       enc_def : thm,
       dec_def : thm,
       dec_enc : thm}

 type ('a,'b) fmap = ('a,'b) Redblackmap.dict

structure Finmap = Redblackmap;

type enumMap = (hol_type, ((term*int) list * logic_info)) fmap;

(*---------------------------------------------------------------------------*)
(* An enum type needs a formatting map from the enum constants to numbers.   *)
(* The domain of the map is the name of the enum type.                       *)
(*---------------------------------------------------------------------------*)

val bool_logic_info = 
    {enc = ``splat$enc_bool``,
     dec = ``splat$dec_bool``,
     enc_def = splatTheory.enc_bool_def,
     dec_def = splatTheory.dec_bool_def,
     dec_enc = splatTheory.dec_enc_bool}

val base_enumMap : enumMap =
  let open boolSyntax
  in 
    Finmap.fromList Type.compare [(Type.bool, ([(F,0), (T,1)], bool_logic_info))]
  end;

local
    val emap = ref base_enumMap
in 
 fun the_enumMap() = !emap
 fun insert_enum (k,v) = (emap := Finmap.insert (the_enumMap(), k,v))
end

fun insert_enum_type (ety,constrs,logic) =
    insert_enum(ety,(map swap (enumerate 0 constrs),logic));

fun define_enum_encoding ety =
 let val etyName = fst(dest_type ety)
     val clist = TypeBase.constructors_of ety
     val eclist = map swap (enumerate 0 clist)
     val teclist = map (I##numSyntax.term_of_int) eclist
     val ename = "num_of_"^etyName
     val dname = etyName^"_of_num"
     val efnvar = mk_var(ename,ety --> numSyntax.num)
     val dfnvar = mk_var(dname,numSyntax.num --> ety)
     fun enc_clause (constr,itm) = mk_eq(mk_comb(efnvar,constr),itm)
     val enc_clauses = map enc_clause teclist
     val num_of_enum = TotalDefn.Define `^(list_mk_conj enc_clauses)`
     val argvar = mk_var("n",numSyntax.num)
     fun cond_of (c,n) x = mk_cond(mk_eq(argvar,n),c,x)
     val (L,(b,_)) = front_last teclist
     val body = itlist cond_of L b
     val enum_of_num = TotalDefn.Define `^(mk_comb(dfnvar,argvar)) = ^body`
     val n_of_e_const = mk_const(dest_var(efnvar))
     val e_of_n_const = mk_const(dest_var(dfnvar))
     val enumvar = mk_var("c",ety)
     val stringvar = mk_var("s",stringSyntax.string_ty)
     val encoderName = "enc_"^etyName
     val decoderName = "dec_"^etyName
     val encvar = mk_var(encoderName,ety --> stringSyntax.string_ty)
     val decvar = mk_var(decoderName,stringSyntax.string_ty --> ety)
     val encoder = TotalDefn.Define `^(mk_comb(encvar,enumvar)) = enc 1 (^n_of_e_const ^enumvar)`
     val decoder = TotalDefn.Define `^(mk_comb(decvar,stringvar)) = ^e_of_n_const (dec ^stringvar)`
     val encoder_const = mk_const(dest_var(encvar))
     val decoder_const = mk_const(dest_var(decvar))
     val inversion_goal = 
       mk_forall(enumvar, 
		 mk_eq(mk_comb(decoder_const,mk_comb(encoder_const, enumvar)),
		       enumvar))
     val inversion = 
       prove (inversion_goal, 
           Cases >> rw_tac std_ss 
                      [encoder, decoder,splatTheory.dec_enc,
                       num_of_enum, enum_of_num])
     val coding = 
        {enc = encoder_const,
         dec = decoder_const,
         enc_def = encoder,
         dec_def = decoder,
         dec_enc = inversion}
 in
   coding
 end
 handle e => raise wrap_exn "Enum_Encode" "define_enum_encoding" e

end


