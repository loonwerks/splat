open HolKernel Parse boolLib bossLib splatLib;

(*---------------------------------------------------------------------------*)
(* Declare simple record and define wellformedness                           *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype
   `gps = <| lat:  int ;
             lon : int ;
             alt : int |>`
;

val good_gps_def =
 Define
  `good_gps recd <=>
          -90 <= recd.lat /\ recd.lat <= 90 /\
         -180 <= recd.lon /\ recd.lon <= 180 /\
            0 <= recd.alt /\ recd.alt <= 17999`
;

(*---------------------------------------------------------------------------*)
(* Regexp expressing corresponding interval constraints                      *)
(*---------------------------------------------------------------------------*)

val gps_regexp =
    Regexp_Match.normalize
        (Regexp_Type.fromQuote `\i{~90,90}\i{~180,180}\i{0,17999}`);

val gps_regexp_term = regexpSyntax.regexp_to_term gps_regexp;

val fieldreps =
 let open splatLib Regexp_Numerics
 in [Interval{span = (~90,90),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 1,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~180,180),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (0,17999),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T}
    ]
 end

Theorem gps_tv_thm :
  !s. s IN regexp_lang ^gps_regexp_term
      <=>
      s IN ({enci 1 i | -90 <= i /\ i <= 90} dot
            {enci 2 i | -180 <= i /\ i <= 180} dot
            {enci 2 i | 0 <= i /\ i <= 17999})
Proof
 splatLib.TV_TAC fieldreps
QED

(*===========================================================================*)
(* Larger example                                                            *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Regexp expressing corresponding interval constraints                      *)
(*---------------------------------------------------------------------------*)

val gps_regexp =
    Regexp_Match.normalize
        (Regexp_Type.fromQuote `(\i{~90,90}\i{~180,180}\i{0,17999}){4}`);

val gps_regexp_term = regexpSyntax.regexp_to_term gps_regexp;

val fieldreps =
 let open splatLib Regexp_Numerics
 in [Interval{span = (~90,90),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 1,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~180,180),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (0,17999),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~90,90),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 1,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~180,180),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (0,17999),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~90,90),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 1,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~180,180),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (0,17999),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~90,90),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 1,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (~180,180),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T},
     Interval{span = (0,17999),
              encoding = Twos_comp,
              endian = LSB, width = BYTEWIDTH 2,
              encoder = fn _ => raise ERR "" "",
              decoder = fn _ => raise ERR "" "",
              regexp = Regexp_Type.DOT,
              constraint = T}
    ]
 end

Theorem gps_tv_thm :
  !s. s IN regexp_lang ^gps_regexp_term
      <=>
      s IN ({enci 1 i | -90 <= i /\ i <= 90} dot
            {enci 2 i | -180 <= i /\ i <= 180} dot
            {enci 2 i | 0 <= i /\ i <= 17999} dot
            {enci 1 i | -90 <= i /\ i <= 90} dot
            {enci 2 i | -180 <= i /\ i <= 180} dot
            {enci 2 i | 0 <= i /\ i <= 17999} dot
            {enci 1 i | -90 <= i /\ i <= 90} dot
            {enci 2 i | -180 <= i /\ i <= 180} dot
            {enci 2 i | 0 <= i /\ i <= 17999} dot
            {enci 1 i | -90 <= i /\ i <= 90} dot
            {enci 2 i | -180 <= i /\ i <= 180} dot
            {enci 2 i | 0 <= i /\ i <= 17999})
Proof
 splatLib.TV_TAC fieldreps
QED
