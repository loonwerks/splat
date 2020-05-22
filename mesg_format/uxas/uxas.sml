use "../contig.sml";
load "Regexp_Numerics";

(*---------------------------------------------------------------------------*)
(* uxAS constants                                                            *)
(*---------------------------------------------------------------------------*)

val SOME CMASISeriesID = LargeInt.fromString"4849604199710720000";

(*---------------------------------------------------------------------------*)
(* The above CMASISeriesID does not fit in 63 bits, which is what is used    *)
(* for an int in PolyML. Temporarily using a crap number so I don't have to  *)
(* deal with big ints everywhere just to accomodate this one number, which   *)
(* is only going to be compared against, anyway. Plus CakeML has bigints     *)
(* everywhere, so there won't be any problem in the generated system.        *)
(*---------------------------------------------------------------------------*)

val CMASISeriesID = ~1;
val CMASISeriesVersion = 3;

(*---------------------------------------------------------------------------*)
(* uxAS message types                                                        *)
(*---------------------------------------------------------------------------*)

val ABSTRACTGEOMETRY = 1
val KEYVALUEPAIR = 2
val LOCATION3D = 3
val PAYLOADACTION = 4
val PAYLOADCONFIGURATION = 5
val PAYLOADSTATE = 6
val VEHICLEACTION = 7
val TASK = 8
val SEARCHTASK = 9
val ABSTRACTZONE = 10
val ENTITYCONFIGURATION = 11
val FLIGHTPROFILE = 12
val AIRVEHICLECONFIGURATION = 13
val ENTITYSTATE = 14
val AIRVEHICLESTATE = 15
val WEDGE = 16
val AREASEARCHTASK = 17
val CAMERAACTION = 18
val CAMERACONFIGURATION = 19
val GIMBALLEDPAYLOADSTATE = 20
val CAMERASTATE = 21
val CIRCLE = 22
val GIMBALANGLEACTION = 23
val GIMBALCONFIGURATION = 24
val GIMBALSCANACTION = 25
val GIMBALSTAREACTION = 26
val GIMBALSTATE = 27
val GOTOWAYPOINTACTION = 28
val KEEPINZONE = 29
val KEEPOUTZONE = 30
val LINESEARCHTASK = 31
val NAVIGATIONACTION = 32
val LOITERACTION = 33
val LOITERTASK = 34
val WAYPOINT = 35
val MISSIONCOMMAND = 36
val MUSTFLYTASK = 37
val OPERATORSIGNAL = 38
val OPERATINGREGION = 39
val AUTOMATIONREQUEST = 40
val POINTSEARCHTASK = 41
val POLYGON = 42
val RECTANGLE = 43
val REMOVETASKS = 44
val SERVICESTATUS = 45
val SESSIONSTATUS = 46
val VEHICLEACTIONCOMMAND = 47
val VIDEOSTREAMACTION = 48
val VIDEOSTREAMCONFIGURATION = 49
val VIDEOSTREAMSTATE = 50
val AUTOMATIONRESPONSE = 51
val REMOVEZONES = 52
val REMOVEENTITIES = 53
val FLIGHTDIRECTORACTION = 54
val WEATHERREPORT = 55
val FOLLOWPATHCOMMAND = 56
val PATHWAYPOINT = 57
val STOPMOVEMENTACTION = 58
val WAYPOINTTRANSFER = 59
val PAYLOADSTOWACTION = 60
;

val uxas_constants_map =
 ("CMASISeriesID",CMASISeriesID)
 ::
[("CMASISeriesVersion",CMASISeriesVersion),
 ("ABSTRACTGEOMETRY",ABSTRACTGEOMETRY),
 ("KEYVALUEPAIR",KEYVALUEPAIR),
 ("LOCATION3D",LOCATION3D),
 ("PAYLOADACTION",PAYLOADACTION),
 ("PAYLOADCONFIGURATION",PAYLOADCONFIGURATION),
 ("PAYLOADSTATE",PAYLOADSTATE),
 ("VEHICLEACTION",VEHICLEACTION),
 ("TASK",TASK),
 ("SEARCHTASK",SEARCHTASK),
 ("ABSTRACTZONE",ABSTRACTZONE),
 ("ENTITYCONFIGURATION",ENTITYCONFIGURATION),
 ("FLIGHTPROFILE",FLIGHTPROFILE),
 ("AIRVEHICLECONFIGURATION",AIRVEHICLECONFIGURATION),
 ("ENTITYSTATE",ENTITYSTATE),
 ("AIRVEHICLESTATE",AIRVEHICLESTATE),
 ("WEDGE",WEDGE),
 ("AREASEARCHTASK",AREASEARCHTASK),
 ("CAMERAACTION",CAMERAACTION),
 ("CAMERACONFIGURATION",CAMERACONFIGURATION),
 ("GIMBALLEDPAYLOADSTATE",GIMBALLEDPAYLOADSTATE),
 ("CAMERASTATE",CAMERASTATE),
 ("CIRCLE",CIRCLE),
 ("GIMBALANGLEACTION",GIMBALANGLEACTION),
 ("GIMBALCONFIGURATION",GIMBALCONFIGURATION),
 ("GIMBALSCANACTION",GIMBALSCANACTION),
 ("GIMBALSTAREACTION",GIMBALSTAREACTION),
 ("GIMBALSTATE",GIMBALSTATE),
 ("GOTOWAYPOINTACTION",GOTOWAYPOINTACTION),
 ("KEEPINZONE",KEEPINZONE),
 ("KEEPOUTZONE",KEEPOUTZONE),
 ("LINESEARCHTASK",LINESEARCHTASK),
 ("NAVIGATIONACTION",NAVIGATIONACTION),
 ("LOITERACTION",LOITERACTION),
 ("LOITERTASK",LOITERTASK),
 ("WAYPOINT",WAYPOINT),
 ("MISSIONCOMMAND",MISSIONCOMMAND),
 ("MUSTFLYTASK",MUSTFLYTASK),
 ("OPERATORSIGNAL",OPERATORSIGNAL),
 ("OPERATINGREGION",OPERATINGREGION),
 ("AUTOMATIONREQUEST",AUTOMATIONREQUEST),
 ("POINTSEARCHTASK",POINTSEARCHTASK),
 ("POLYGON",POLYGON),
 ("RECTANGLE",RECTANGLE),
 ("REMOVETASKS",REMOVETASKS),
 ("SERVICESTATUS",SERVICESTATUS),
 ("SESSIONSTATUS",SESSIONSTATUS),
 ("VEHICLEACTIONCOMMAND",VEHICLEACTIONCOMMAND),
 ("VIDEOSTREAMACTION",VIDEOSTREAMACTION),
 ("VIDEOSTREAMCONFIGURATION",VIDEOSTREAMCONFIGURATION),
 ("VIDEOSTREAMSTATE",VIDEOSTREAMSTATE),
 ("AUTOMATIONRESPONSE",AUTOMATIONRESPONSE),
 ("REMOVEZONES",REMOVEZONES),
 ("REMOVEENTITIES",REMOVEENTITIES),
 ("FLIGHTDIRECTORACTION",FLIGHTDIRECTORACTION),
 ("WEATHERREPORT",WEATHERREPORT),
 ("FOLLOWPATHCOMMAND",FOLLOWPATHCOMMAND),
 ("PATHWAYPOINT",PATHWAYPOINT),
 ("STOPMOVEMENTACTION",STOPMOVEMENTACTION),
 ("WAYPOINTTRANSFER",WAYPOINTTRANSFER),
 ("PAYLOADSTOWACTION",PAYLOADSTOWACTION)
];


(*---------------------------------------------------------------------------*)
(* Value of a string as an MSB number                                        *)
(*---------------------------------------------------------------------------*)

fun uxas_valFn a s =
 let fun uvalFn w = IntInf.toInt
         (Regexp_Numerics.string2iint Regexp_Numerics.Unsigned
                                      Regexp_Numerics.MSB w)
     fun ivalFn w = IntInf.toInt
         (Regexp_Numerics.string2iint Regexp_Numerics.Twos_comp
                                      Regexp_Numerics.MSB w)
 in case a
  of Bool => uvalFn s
   | Char => uvalFn s
   | Enum _ => uvalFn s
   | Signed w => ivalFn s
   | Unsigned w => uvalFn s
   | otherwise  => raise ERR "uxas_valFn" "unexpected input"
 end
;

(*---------------------------------------------------------------------------*)
(* Environment of functions mapping ints to various representation strings   *)
(*---------------------------------------------------------------------------*)

fun uxas_repFn a i =
 let val u2string = Regexp_Numerics.iint2string
                        Regexp_Numerics.Unsigned Regexp_Numerics.MSB
     val i2string = Regexp_Numerics.iint2string
                        Regexp_Numerics.Twos_comp Regexp_Numerics.MSB
     val j = LargeInt.fromInt i
 in case a
  of Bool => u2string 1 j
   | Char => u2string 1 j
   | Enum s => u2string 1 j
   | Signed w => i2string w j
   | Unsigned w => u2string w j
   | Float => u2string 4 j  (* hack *)
   | Double => u2string 8 j  (* hack *)
   | otherwise => raise ERR "uxas_repFn" "unexpected case"
 end
;

(*---------------------------------------------------------------------------*)
(* Doubles                                                                   *)
(*---------------------------------------------------------------------------*)

fun dvalFn Double s = PackRealBig.fromBytes (Byte.stringToBytes s)
  | dvalFn other s = raise ERR "dvalFn" "expected Double"
;
fun drepFn Double r = Byte.bytesToString (PackRealBig.toBytes r)
  | drepFn other s = raise ERR "drepFn" "expected Double"
;

fun bounded c (i,j) = Recd [
  ("val", c),
  ("check", Assert (Interval "val" (i,j)))
 ];

fun add_contig_decl E (s,d) =
 let val (Consts,Decls,aW,vFn,dvFn) = E
 in (Consts,(s,d)::Decls,aW,vFn,dvFn)
 end

fun enumList elts = zip elts (upto 0 (length elts - 1));

val real32 = Basic Float;
val real64 = Basic Double;

(*---------------------------------------------------------------------------*)
(* Arrays in uxAS are preceded by a length field.                            *)
(*---------------------------------------------------------------------------*)

fun uxasArray contig = Recd [
  ("len", u16),
  ("elts", Array(contig, Loc (VarName"len")))
 ];

(*---------------------------------------------------------------------------*)
(* Enforce a given bound on array size                                       *)
(*---------------------------------------------------------------------------*)

fun uxasBoundedArray contig bound = Recd [
  ("len", u16),
  ("len-check",  Assert (Ble(Loc(VarName "len"), intLit bound))),
  ("elts", Array(contig, Loc (VarName"len")))
 ];

(*---------------------------------------------------------------------------*)
(* Option type                                                               *)
(*---------------------------------------------------------------------------*)

fun Option contig = Recd
 [("present", Basic Bool),
  ("contents", Union [
     (BLoc (VarName "present"), contig),
     (Bnot(BLoc (VarName "present")), SKIP)
     ])
 ];

(*---------------------------------------------------------------------------*)
(* Wrapper for a contig, with message type specified. Notice that we only    *)
(* check the message type. A more stringent check would also check the       *)
(* seriesID and seriesVersion, as follows.                                   *)
(*                                                                           *)
(*  ("check-mesg-numbers", Assert                                            *)
(*   (Band(Beq(Loc(VarName "seriesID"),ConstName "CMASISeriesID"),           *)
(*    Band(Beq(Loc(VarName "mesgType"),ConstName mesgtyName),                *)
(*         Beq(Loc(VarName "seriesVersion"),ConstName "CMASISeriesVersion")) *)
(*---------------------------------------------------------------------------*)

fun uxasMesg mesgtyName contig = Recd [
   ("seriesID", i64),
   ("mesgType", u32),
   ("check-mesg-type",
    Assert (Beq(Loc(VarName "mesgType"),ConstName mesgtyName))),
   ("seriesVersion",  u16),
   ("mesg",  contig)
 ];

fun mesgOption name = Option o uxasMesg name;

(*---------------------------------------------------------------------------*)
(* uxAS strings                                                              *)
(*---------------------------------------------------------------------------*)

val StringRecd = uxasArray (Basic Char);

val String = Declared "StringRecd";

(*---------------------------------------------------------------------------*)
(* pairs of strings                                                          *)
(*---------------------------------------------------------------------------*)

val KeyValuePairRecd =  (* pairs of varying length strings *)
  Recd [("key",   String),
        ("value", String)];

val KeyValuePair = Declared "KeyValuePair";

(*---------------------------------------------------------------------------*)
(* Enumerations                                                              *)
(*---------------------------------------------------------------------------*)

val altitude_type = ("AltitudeType", enumList ["AGL","MSL"]);
val speed_type    = ("SpeedType",    enumList ["AirSpeed","GroundSpeed"]);
val turn_type     = ("TurnType",     enumList ["TurnShort", "FlyOver"]);

val wavelength_band =
 ("WavelengthBand", enumList ["AllAny","EO","LWIR","SWIR","MWIR","Other"]);

val navigation_mode =
 ("NavigationMode",
  enumList ["Waypoint", "Loiter", "FlightDirector",
            "TargetTrack", "FollowLeader", "LostComm"]);

val command_status_type =
 ("CommandStatusType",
  enumList ["Pending", "Approved", "InProcess", "Executed", "Cancelled"]);

val AltitudeType   = Declared "AltitudeType"
val WavelengthBand = Declared "WavelengthBand"
val NavigationMode = Declared "NavigationMode"
val SpeedType      = Declared "SpeedType"
val TurnType       = Declared "TurnType"
val CommandStatusType = Declared "CommandStatusType";

(*---------------------------------------------------------------------------*)
(* Basic uxAS environment plus enumerations.                                 *)
(*---------------------------------------------------------------------------*)

val uxasEnv =
  (uxas_constants_map,[],atomic_widths,uxas_valFn,dvalFn)
     |> C add_contig_decl ("String",StringRecd)
     |> C add_contig_decl ("KeyValuePair", KeyValuePairRecd)
     |> C add_enum_decl altitude_type
     |> C add_enum_decl wavelength_band
     |> C add_enum_decl navigation_mode
     |> C add_enum_decl speed_type
     |> C add_enum_decl turn_type
     |> C add_enum_decl command_status_type
;

(*---------------------------------------------------------------------------*)
(* Messages                                                                  *)
(*---------------------------------------------------------------------------*)

val operating_region = Recd [
  ("ID",             i64),
  ("keep_in_areas",  uxasBoundedArray u64 32),
  ("keep_out_areas", uxasBoundedArray u64 32)
  ];

val automation_request = Recd [
  ("EntityList",        uxasBoundedArray i64 16),
  ("TaskList",          uxasBoundedArray i64 32),
  ("TaskRelationShips", String),
  ("OperatingRegion",   i64),
  ("RedoAllTasks",      Basic Bool)
  ];

val Wedge = Recd [
  ("AzimuthCenterline",  real32),
  ("VerticalCenterline", real32),
  ("AzimuthExtent",      real32),
  ("VerticalExtent",     real32)
 ];

val Location3D = Recd [
  ("Latitude",  real64),
  ("Longitude", real64),
  ("Altitude",  real32),
  ("AltitudeType", AltitudeType)
];

val Checked_Location3D = Recd [
  ("Latitude",  real64),
  ("Lat-check", Assert (
    Band(DleA(~90.0,Loc(VarName"Latitude")),
         DleB(Loc(VarName"Latitude"),90.0)))),
  ("Longitude", real64),
  ("Lon-check", Assert (
    Band(DleA(~180.0,Loc(VarName"Longitude")),
         DleB(Loc(VarName"Longitude"),180.0)))),
  ("Altitude",  real32),
  ("AltitudeType", AltitudeType),
  ("AltitudeType-check", Assert (
    Ble(Loc(VarName"AltitudeType"),intLit 1)))
];

val Location3D = Checked_Location3D;

(*---------------------------------------------------------------------------*)
(* LineSearchTask message                                                    *)
(*---------------------------------------------------------------------------*)

val linesearch_task = Recd [
  (* Task *)
  ("TaskID",           i64),
  ("Label",            String),
  ("EligibleEntities", uxasBoundedArray i64 32),
  ("RevisitRate",      real32),
  ("Parameters",       uxasBoundedArray (mesgOption "KEYVALUEPAIR" KeyValuePair) 8),
  ("Priority",         u8),
  ("Required",         Basic Bool),

  (* SearchTask *)
  ("DesiredWavelengthBands", uxasBoundedArray WavelengthBand 8),
  ("DwellTime",              i64),
  ("GroundSampleDistance",   real32),

  (* LineSearchTask *)
  ("PointList",     uxasBoundedArray (mesgOption "LOCATION3D" Location3D) 1024),
  ("ViewAngleList", uxasBoundedArray (mesgOption "WEDGE" Wedge) 16),
  ("UseInertialViewAngles", Basic Bool)
];


(*---------------------------------------------------------------------------*)
(* AutomationResponse message                                                *)
(*---------------------------------------------------------------------------*)

val VehicleAction = Recd [
  ("AssociatedTaskList", uxasBoundedArray i64 8)
];

val VehicleActionCommand = Recd [
  ("CommandID",         i64),
  ("VehicleID",         i64),
  ("VehicleActionList", uxasBoundedArray (mesgOption "VEHICLEACTION" VehicleAction) 8),
  ("Status",            CommandStatusType),
  ("check-status",      Assert (Ble(Loc(VarName"Status"),intLit 4)))
 ];

val Waypoint = Recd [
  ("Location",            Location3D),  (* Q: mesgOption this? A: Nope: extension base *)
  ("Number",              i64),
  ("NextWaypoint",        i64),
  ("Speed",               real32),
  ("SpeedType",           SpeedType),
  ("check-speed-type",    Assert (Ble(Loc(VarName"SpeedType"),intLit 1))),
  ("ClimbRate",           real32),
  ("TurnType",            TurnType),
  ("check-turn-type",     Assert (Ble(Loc(VarName"TurnType"),intLit 1))),
  ("VehicleActionList",   uxasBoundedArray (mesgOption "VEHICLEACTION" VehicleAction) 8),
  ("ContingencyWaypointA",i64),
  ("ContingencyWaypointB",i64),
  ("AssociatedTasks",     uxasBoundedArray i64 8)
 ];

val MissionCommand = Recd [
 ("VehicleActionCommand", VehicleActionCommand), (* Q: mesgOption this? Nope: extension base *)
 ("WaypointList",         uxasBoundedArray (mesgOption "WAYPOINT" Waypoint) 1024),
 ("FirstWaypoint",        i64)
];

val automation_response = Recd [
 ("MissionCommandList", uxasBoundedArray (mesgOption "MISSIONCOMMAND" MissionCommand) 16),
 ("VehicleCommandList", uxasBoundedArray (mesgOption "VEHICLEACTIONCOMMAND" VehicleActionCommand) 64),
 ("Info",               uxasBoundedArray (mesgOption "KEYVALUEPAIR" KeyValuePair) 8)
];

(*---------------------------------------------------------------------------*)
(* AirVehicleState message                                                   *)
(*---------------------------------------------------------------------------*)

val PayloadState = Recd [
 ("PayloadID",  i64),
 ("Parameters", uxasBoundedArray (mesgOption "KEYVALUEPAIR" KeyValuePair) 8)
];

val EntityState = Recd [
  ("ID",     i64),
  ("u",      real32),
  ("v",      real32),
  ("w",      real32),
  ("udot",   real32),
  ("vdot",   real32),
  ("wdot",   real32),
  ("Heading",real32),
  ("Pitch",  real32),
  ("Roll",   real32),
  ("p",      real32),
  ("q",      real32),
  ("r",      real32),
  ("Course", real32),
  ("Groundspeed",      real32),
  ("Location",         mesgOption "LOCATION3D" Location3D),
  ("EnergyAvailable",  real32),
  ("ActualEnergyRate", real32),
  ("PayloadStateList", uxasBoundedArray(mesgOption "PAYLOADSTATE" PayloadState) 8),
  ("CurrentWaypoint",  i64),
  ("CurrentCommand",   i64),
  ("Mode",             NavigationMode),
  ("AssociatedTasks",  uxasBoundedArray i64 8),
  ("Time",             i64),
  ("Info", uxasBoundedArray(mesgOption "KEYVALUEPAIR" KeyValuePair) 32)
];


val airvehicle_state = Recd [
  ("EntityState",   EntityState),
  ("Airspeed",      real32),
  ("VerticalSpeed", real32),
  ("WindSpeed",     real32),
  ("WindDirection", real32)
];

(*---------------------------------------------------------------------------*)
(* Full uxAS operating region message looks like the following               *)
(* (Eric Mercer dug this info out):                                          *)
(*                                                                           *)
(*  <address> $ <attributes> $ <mesg-object>                                 *)
(*                                                                           *)
(* where                                                                     *)
(*                                                                           *)
(*  <address> is e.g. uxas.project.isolate.IntruderAlert,                    *)
(*                    uxas.roadmonitor,  etc.                                *)
(*                                                                           *)
(*  <attributes> = <contentType>       ;; string of non "|" chars            *)
(*               | <descriptor>        ;; ditto                              *)
(*               | <source-group>      ;; ditto                              *)
(*               | <source-entity-ID>  ;; ditto                              *)
(*               | <source-service-ID> ;; ditto                              *)
(*                                                                           *)
(* (The vertical bars are included in the message text.)                     *)
(*                                                                           *)
(* Using some regexp-like notation, this is                                  *)
(*                                                                           *)
(*  (.* "$") (.* "|"){4} (.* "$") <mesg-object>                              *)
(*                                                                           *)
(* The mesg field is a mesgOption as above                                   *)
(*---------------------------------------------------------------------------*)

val attributes = Recd [
 ("contentType",       Scanner (scanTo "|")),
 ("descriptor",        Scanner (scanTo "|")),
 ("source_group",      Scanner (scanTo "|")),
 ("source_entity_ID",  Scanner (scanTo "|")),
 ("source_service_ID", Scanner (scanTo "$"))
 ];

fun full_mesg contig = Recd [
  ("address",      Scanner (scanTo "$")),
  ("attributes",   attributes),
  ("controlString",i32),  (* = 0x4c4d4350 = valueFn "LMCP" *)
  ("check",        Assert (Beq(Loc(VarName"controlString"),intLit 0x4c4d4350))),
  ("mesgSize",     u32),
  ("mesg",         contig),
  ("checksum",     u32)
 ];

(*---------------------------------------------------------------------------*)
(* Full messages for a few formats                                           *)
(*---------------------------------------------------------------------------*)

val fullOperatingRegionMesg =
  full_mesg (mesgOption "OPERATINGREGION" operating_region);

val fullAutomationRequestMesg =
  full_mesg (mesgOption "AUTOMATIONREQUEST" automation_request);

val fullLineSearchTaskMesg =
  full_mesg (mesgOption "LINESEARCHTASK" linesearch_task);

val fullAutomationResponseMesg =
  full_mesg (mesgOption "AUTOMATIONRESPONSE" automation_response);

val fullAirVehicleStateMesg =
  full_mesg (mesgOption "AIRVEHICLESTATE" airvehicle_state);


(*===========================================================================*)
(* Parsing. First define target datastructures.                              *)
(*===========================================================================*)

type i64 = Int.int;
type real32 = Real32.real;
type real64 = Real.real;
type KeyValPair = string * string;

(*---------------------------------------------------------------------------*)
(* Enumerations                                                              *)
(*---------------------------------------------------------------------------*)

datatype SpeedType = AirSpeed | GroundSpeed;
datatype TurnType = TurnShort | FlyOver;

datatype AltitudeType = AGL | MSL;

datatype WavelengthBand = AllAny | EO | LWIR | SWIR | MWIR | Other;

datatype NavigationMode =
	 WAYPOINT | Loiter | FlightDirector | TargetTrack | FollowLeader | LostComm;

datatype CommandStatusType = Pending | Approved | InProcess | Executed | Cancelled;

type Location3D =
     {Latitude  : real64,
      Longitude : real64,
      Altitude  : real32,
      AltitudeType : AltitudeType};

type Polygon = Location3D array;

type Waypoint =
  {Location    : Location3D,
   Number      : i64,
   NextWaypoint: i64,
   Speed       : real32,
   SpeedType   : SpeedType,
   ClimbRate   : real32,
   TurnType    : TurnType,
   VehicleActionList    : i64 array array,
   ContingencyWaypointA : i64,
   ContingencyWaypointB : i64,
   AssociatedTasks      : i64 array
 };

type MissionCommand =
 {CommandID         : i64,
  VehicleID         : i64,
  VehicleActionList : i64 array array,
  Status            : CommandStatusType,
  WaypointList      : Waypoint array,
  FirstWaypoint     : i64};


type VehicleAction = i64 array;

type VehicleActionCommand =
 {CommandID : i64,
  VehicleID : i64,
  VehicleActionList : VehicleAction array,
  Status : CommandStatusType}

type AutomationResponse =
     {MissionCommandList : MissionCommand array,
      VehicleCommandList : VehicleActionCommand array,
      Info : KeyValPair array}

(*---------------------------------------------------------------------------*)
(* Parsing                                                                   *)
(*---------------------------------------------------------------------------*)

val mk_i64   = uxas_valFn  (Signed 8);
fun mk_float s = Real32.fromInt 42;
fun mk_double s = dvalFn Double s;

fun mk_leaf f (LEAF(_,s)) = f s
  | mk_leaf f otherwise = raise ERR "mk_leaf" ""

fun mk_bounded_array eltFn ptree =
 case ptree
  of RECD [("len",_),("elts", ARRAY elts)] => Array.fromList (List.map eltFn elts)
   | otherwise  => raise ERR "mk_bounded_array" "";

fun dest_header ptree =
 case ptree
  of RECD [("seriesID",_),
           ("mesgType",_),
           ("seriesVersion",_),
           ("mesg", pt)] => pt
   | otherwise => raise ERR "dest_header" "";

fun mk_uxasOption eltFn ptree =
 case ptree
  of RECD [("present", _), ("contents", elt)] =>
        (case elt
          of RECD [] => NONE
           | contig  => SOME(eltFn contig))
   | otherwise => raise ERR "mk_uxasOption" "";

fun mk_bounded_mesgOption_array eltFn ptree =
 case ptree
  of RECD [("len",_),("elts", ARRAY elts)]
      => Array.fromList
           (List.mapPartial (mk_uxasOption (eltFn o dest_header)) elts)
   | otherwise  => raise ERR "mk_bounded_mesgOption_array" "";

fun decodeCommandStatusType s =
  let val i = uxas_valFn (Enum "CommandStatusType") s
  in if i = 0 then Pending else
     if i = 1 then Approved else
     if i = 2 then InProcess else
     if i = 3 then Executed else
     if i = 4 then Cancelled
     else raise ERR "decodeCommandStatusType" ""
  end;

fun decodeAltitudeType s =
  let val i = uxas_valFn (Enum "AltitudeType") s
  in if i = 0 then AGL else
     if i = 1 then MSL
     else raise ERR "decodeAltitudeType" ""
  end;

fun decodeSpeedType s =
  let val i = uxas_valFn (Enum "SpeedType") s
  in if i = 0 then AirSpeed else
     if i = 1 then GroundSpeed
     else raise ERR "decodeSpeedType" ""
  end;

fun decodeTurnType s =
  let val i = uxas_valFn (Enum "TurnType") s
  in if i = 0 then TurnShort else
     if i = 1 then FlyOver
     else raise ERR "decodTurnType" ""
  end;

fun mk_location3D ptree =
 case ptree
  of RECD [("Latitude", lat),
           ("Longitude", lon),
           ("Altitude",  alt),
           ("AltitudeType", alt_type)]
     => {Latitude  = mk_leaf mk_double lat,
         Longitude = mk_leaf mk_double lon,
         Altitude  = mk_leaf mk_float alt,
         AltitudeType = mk_leaf decodeAltitudeType alt_type}
   | otherwise => raise ERR "mk_location3D" "";


(*---------------------------------------------------------------------------*)
(* Geofence monitor input                                                    *)
(*---------------------------------------------------------------------------*)

val PhaseII_Polygon = Array(Location3D, intLit 2);

(*---------------------------------------------------------------------------*)
(* Decode polygon encoded with uxas encoding                                 *)
(*---------------------------------------------------------------------------*)

fun parse_uxas_polygon string =
 let fun contents_of ptree =
       (case ptree
         of RECD [("present", _), ("contents", RECD elts)] => elts
          | otherwise => raise ERR "contents_of" "")
      fun mesgs_of alist = map snd (filter (equal "mesg" o fst) alist)
 in
   case parseFn uxasEnv (VarName"root") Polygon ([],string,empty_lvalMap)
    of NONE => NONE
     | SOME ([ptree],remaining,theta) =>
         (case ptree
           of RECD [("BoundaryPointsList",
                    RECD[("len", _), ("elts", ARRAY recds)])] =>
                    let val contents = List.concat (map contents_of recds)
                        val mesgs = mesgs_of contents
                    in SOME (Array.fromList (map mk_location3D mesgs))
                    end
            | otherwise => NONE)
     | otherwise => NONE
 end;

fun mk_phase2_polygon ptree =
  case ptree
   of ARRAY recds => Array.fromList (map mk_location3D recds)
    | otherwise => raise ERR "mk_phase2_polygon" ""

fun parse_phase2_polygon string =
  case parseFn uxasEnv (VarName"root") PhaseII_Polygon ([],string,empty_lvalMap)
   of NONE => raise ERR "parse_phase2_polygon" ""
    | SOME ([ptree],remaining,theta) => mk_phase2_polygon ptree
    | otherwise => raise ERR "parse_phase2_polygon" ""

(*---------------------------------------------------------------------------*)
(* VehicleAction =                                                           *)
(*  Recd [("AssociatedTaskList", uxasBoundedArray i64 8)]                    *)
(*---------------------------------------------------------------------------*)

fun mk_VA ptree =
 case ptree
  of RECD [("AssociatedTaskList",RECD [("len", _),("elts",ARRAY elts)])]
       => Array.fromList (map (mk_leaf mk_i64) elts)
   | otherwise  => raise ERR "mk_VA" "";

(*---------------------------------------------------------------------------*)
(* VehicleActionCommand = Recd [                                             *)
(*  ("CommandID",         i64),                                              *)
(*  ("VehicleID",         i64),                                              *)
(*  ("VehicleActionList", uxasBoundedArray                                   *)
(*                            (mesgOption "VEHICLEACTION" VehicleAction) 8), *)
(*  ("Status",            CommandStatusType)                                 *)
(* ]                                                                         *)
(*---------------------------------------------------------------------------*)

fun mk_VAC ptree : VehicleActionCommand =
 case ptree
  of RECD [("CommandID",cid),
           ("VehicleID", vid),
           ("VehicleActionList", valist),
           ("Status", status)]
      => {CommandID         = mk_leaf mk_i64 cid,
          VehicleID         = mk_leaf mk_i64 vid,
          VehicleActionList = mk_bounded_mesgOption_array mk_VA valist,
          Status            = mk_leaf decodeCommandStatusType status}
   | otherwise  => raise ERR "mk_VAC" ""

(*---------------------------------------------------------------------------*)
(* Waypoint = Recd [                                                         *)
(*  ("Location",            Location3D),                                     *)
(*  ("Number",              i64),                                            *)
(*  ("NextWaypoint",        i64),                                            *)
(*  ("Speed",               real32),                                         *)
(*  ("SpeedType",           SpeedType),                                      *)
(*  ("check-speed-type",    Assert (Ble(Loc(VarName"SpeedType"),intLit 1))), *)
(*  ("ClimbRate",           real32),                                         *)
(*  ("TurnType",            TurnType),                                       *)
(*  ("check-turn-type",     Assert (Ble(Loc(VarName"TurnType"),intLit 1))),  *)
(*  ("VehicleActionList",   uxasBoundedArray                                 *)
(*                             (mesgOption "VEHICLEACTION" VehicleAction) 8),*)
(*  ("ContingencyWaypointA",i64),                                            *)
(*  ("ContingencyWaypointB",i64),                                            *)
(*  ("AssociatedTasks",     uxasBoundedArray i64 8)                          *)
(* ]                                                                         *)
(*---------------------------------------------------------------------------*)

fun mk_Waypoint ptree =
  case ptree
   of RECD [("Location", loc3d), ("Number", n),
            ("NextWaypoint",     next_wpt), ("Speed", speed),
            ("SpeedType", speed_type), ("ClimbRate",climbrate),
            ("TurnType",turn_type), ("VehicleActionList", valist),
            ("ContingencyWaypointA",cwptA), ("ContingencyWaypointB",cwptB),
            ("AssociatedTasks",  atasks)]
      => {Location     = mk_location3D loc3d,
          Number       = mk_leaf mk_i64 n,
          NextWaypoint = mk_leaf mk_i64 next_wpt,
          Speed        = mk_leaf mk_float speed,
          SpeedType    = mk_leaf decodeSpeedType speed_type,
          ClimbRate    = mk_leaf mk_float climbrate,
          TurnType     = mk_leaf decodeTurnType turn_type,
          VehicleActionList    = mk_bounded_mesgOption_array mk_VA valist,
          ContingencyWaypointA = mk_leaf mk_i64 cwptA,
          ContingencyWaypointB = mk_leaf mk_i64 cwptB,
          AssociatedTasks      = mk_bounded_array (mk_leaf mk_i64) atasks}
      | otherwise => raise ERR "mk_Waypoint" ""



(*---------------------------------------------------------------------------*)
(*  MissionCommand = Recd [                                                  *)
(* ("VehicleActionCommand", VehicleActionCommand),                           *)
(* ("WaypointList",                                                          *)
(*     uxasBoundedArray(mesgOption "WAYPOINT" Waypoint) 1024),               *)
(* ("FirstWaypoint", i64)                                                    *)
(* ]                                                                         *)
(*---------------------------------------------------------------------------*)

fun mk_MC ptree =
  case ptree
   of RECD [("VehicleActionCommand", vac),
            ("WaypointList", wpts),
            ("FirstWaypoint",fst_wpt)]
       => {VehicleActionCommand = mk_VAC vac,
           WaypointList = mk_bounded_mesgOption_array mk_Waypoint wpts,
           FirstWaypoint = mk_leaf mk_i64 fst_wpt}
    | otherwise => raise ERR "mk_mission_command" ""

(*---------------------------------------------------------------------------*)
(* automation_response = Recd [                                              *)
(*  ("MissionCommandList",                                                   *)
(*      uxasBoundedArray (mesgOption "MISSIONCOMMAND" MissionCommand) 16),   *)
(*  ("VehicleCommandList",                                                   *)
(*      uxasBoundedArray                                                     *)
(*           (mesgOption "VEHICLEACTIONCOMMAND" VehicleActionCommand) 64),   *)
(*  ("Info", uxasBoundedArray (mesgOption "KEYVALUEPAIR" KeyValuePair) 8)    *)
(* ]                                                                         *)
(*---------------------------------------------------------------------------*)

fun mk_automation_response ptree =
  case ptree
   of RECD [("MissionCommandList",mclist),
            ("VehicleCommandList",vaclist), ("Info", infolist)]
       => {MissionCommandList = mk_bounded_mesgOption_array mk_MC wpts mclist,
           VehicleCommandList = mk_bounded_mesgOption_array mk_VAC vaclist,
           Info = ilist}
    | otherwise => raise ERR "mk_automation_response" ""


(*---------------------------------------------------------------------------*)
(* Generate messages to test the parser on.                                  *)
(*---------------------------------------------------------------------------*)

fun scanRandFn (path:lval) = "!!UNEXPECTED!!"

val randEnv =
 let val (Consts,Decls,atomicWidths,valFn,dvalFn) = uxasEnv
 in (Consts,Decls,atomicWidths,valFn,dvalFn,
     uxas_repFn,scanRandFn,Random.newgen())
 end;

fun gen_phase2_polygon () =
  String.concat
    (randFn randEnv
        ([(VarName"root",PhaseII_Polygon)], empty_lvalMap, []));

parse_phase2_polygon (gen_phase2_polygon());

fun gen_VA () =
  String.concat
    (randFn randEnv
        ([(VarName"root",VehicleAction)], empty_lvalMap, []));

val (ptree,remaining,theta) = parse uxasEnv VehicleAction (gen_VA());
mk_VA ptree;

fun gen_VAC () =
  String.concat
    (randFn randEnv
        ([(VarName"root",VehicleActionCommand)], empty_lvalMap, []));

val (ptree,remaining,theta) = parse uxasEnv VehicleActionCommand (gen_VAC());
mk_VAC ptree;

fun gen_waypoint () =
  String.concat
    (randFn randEnv
        ([(VarName"root",Waypoint)], empty_lvalMap, []));

val (ptree,remaining,theta) = parse uxasEnv Waypoint (gen_waypoint());
mk_Waypoint ptree;


fun gen_MC () =
  String.concat
    (randFn randEnv
        ([(VarName"root",MissionCommand)], empty_lvalMap, []));

val (ptree,remaining,theta) = parse uxasEnv MissionCommand (gen_MC());
mk_MC ptree;

fun gen_keyvalpair () =
  String.concat
    (randFn randEnv
        ([(VarName"root",KeyValuePair)], empty_lvalMap, []));


val read_polygon = parse_polygon o Byte.bytesToString;
val read_automation_response = parse_automation_response o Byte.bytesToString;

val read_zone = parse_zone o Byte.bytesToString;
val read_mission = parse_mission o Byte.bytesToString;
