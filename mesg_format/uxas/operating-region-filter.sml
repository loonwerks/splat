use "uxas.sml";
use "consts.sml";

(*---------------------------------------------------------------------------*)
(* AGREE filter requirement on Operating Region messages                     *)
(*                                                                           *)
(* fun WELL_FORMED_OPERATING_REGION(msg:CMASI::OperatingRegion.i) : bool =   *)
(*   msg.ID >= OPERATING_REGION_ID_MIN and                                   *)
(*   msg.ID <= OPERATING_REGION_ID_MAX and                                   *)
(*   (forall kiz in msg.KeepInAreas,                                         *)
(*        kiz >= KEEP_IN_ZONE_ID_MIN and kiz <= KEEP_IN_ZONE_ID_MAX) and     *)
(*   (forall koz in msg.KeepOutAreas,                                        *)
(*        koz >= KEEP_OUT_ZONE_ID_MIN and koz <= KEEP_OUT_ZONE_ID_MAX)       *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Mapping between AGREE types and contig types is required to bridge the    *)
(* gap between requirements-level data and message-level data.               *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Each element in a kizone or kozone is bounded by the specified constants. *)
(* This takes care of the "foralls in the reqt.                              *)
(*---------------------------------------------------------------------------*)

val kizoneElt = bounded u64 (KEEP_IN_ZONE_ID_MIN,KEEP_IN_ZONE_ID_MAX);
val kozoneElt = bounded u64 (KEEP_OUT_ZONE_ID_MIN,KEEP_OUT_ZONE_ID_MAX);

val operating_region = Recd [
  ("ID",             i64),
  ("keep_in_areas",  uxasBoundedArray kizoneElt 32),
  ("keep_out_areas", uxasBoundedArray kozoneElt 32)
 ];

(*---------------------------------------------------------------------------*)
(* Rqt: the source-entity-ID is within the min and max for operating-region  *)
(* ids.                                                                      *)
(*---------------------------------------------------------------------------*)

val attributes = Recd [
  ("contentType",      Scanner (scanTo "|")),
  ("descriptor",       Scanner (scanTo "|")),
  ("source_group",     Scanner (scanTo "|")),
  ("source_entity_ID", Scanner (scanTo "|")),
  ("source_entity_ID-bounds", Assert
   (Interval "source_entity_ID"
      (OPERATING_REGION_ID_MIN,OPERATING_REGION_ID_MAX))),
  ("source_service_ID", Scanner (scanTo "$"))
];

(*---------------------------------------------------------------------------*)
(* Address-attributed operating region message                               *)
(*---------------------------------------------------------------------------*)

val fullOperatingRegionMesg = Recd [
  ("address",       Scanner (scanTo "$")),
  ("attributes",    attributes),
  ("controlString", i32),  (* = 0x4c4d4350 = valueFn "LMCP" *)
  ("check",         Assert (Beq(Loc(VarName"controlString"),intLit 0x4c4d4350))),
  ("mesgSize",      u32),
  ("mesg",          mesgOption "OPERATINGREGION" operating_region),
  ("checksum",      u32)
];

(*---------------------------------------------------------------------------*)
(* Custom valFn for address-attributed OR messages. A hack!                  *)
(*---------------------------------------------------------------------------*)

fun dest_string s =
    SOME(String.sub(s,0),String.extract(s,1,NONE)) handle _ => NONE;

fun OR_valFn a s =
 uxas_valFn a s handle e =>
  (case a
    of Scanned =>
        (case Int.scan StringCvt.DEC dest_string s
          of NONE => raise ERR "OR_valFn" "Scanned: expected decimal integer string"
           | SOME (i,_) => i)
    | otherwise => raise e)
;

val OREnv =
 let val (Consts,Decls,atomicWidths,_) = uxasEnv
 in (Consts,Decls,atomicWidths,OR_valFn)
 end;

(*---------------------------------------------------------------------------*)
(* Check that a string meets the requirements embedded in                    *)
(* fullOperatingRegionMesg contig-type.                                      *)
(*---------------------------------------------------------------------------*)

fun check_OR_mesg s =
  predFn OREnv ([(VarName"root",fullOperatingRegionMesg)],s,empty_lvalMap);

(*---------------------------------------------------------------------------*)
(* Support for generating random well-formed operation region messages.      *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)
(* Special-case strings to be put into fields that result from guest         *)
(* scanners, when generating random message. This is highly specific to      *)
(* uxAS address-attributed messages.                                         *)
(*---------------------------------------------------------------------------*)

fun scanRandFn path =
 case path
  of RecdProj(lval,"address") => "<address>$"
   | RecdProj(RecdProj(lval,"attributes"),fName) =>
      (case fName
        of "contentType"       => "<contentType>|"
         | "descriptor"        => "<descriptor>|"
         | "source_group"      => "<source_group>|"
         | "source_entity_ID"  => "500|"
         | "source_service_ID" => "<source_service_ID$"
         | otherwise => "!!UNEXPECTED!!")
   | otherwise => "!!UNEXPECTED!!"
;

val randEnv =
 let val (Consts,Decls,atomicWidths,valFn) = OREnv
 in (Consts,Decls,atomicWidths,valFn,
     repFn,scanRandFn,Random.newgen())
 end;

(*---------------------------------------------------------------------------*)
(* Generate a full address-annotated operation region message                *)
(*---------------------------------------------------------------------------*)

fun gen_OR_mesg () =
  String.concat
    (randFn randEnv
        ([(VarName"root",fullOperatingRegionMesg)], empty_lvalMap, []));

(*---------------------------------------------------------------------------*)
(* Test                                                                      *)
(*---------------------------------------------------------------------------*)

val string = gen_OR_mesg();

check_OR_mesg string;

fun check_gen() = predFn OREnv
   ([(VarName"root",fullOperatingRegionMesg)],
    gen_OR_mesg(),empty_lvalMap);

fun is_pass (Lib.PASS _) = true
  | is_pass other = false;

val true = List.all is_pass (map (fn i => check_gen()) (upto 0 100));

fun filterFn (input:Word8Vector.vector option) =
 case input
  of NONE => NONE
  |  SOME bytes =>
       if check_OR_mesg (Byte.bytesToString bytes) then
         input
       else NONE;
