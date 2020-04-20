use "contig.sml";
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

fun valueFn s =
 let open Regexp_Numerics
 in IntInf.toInt(string2iint Unsigned MSB s)
 end

fun add_contig_decl E (s,d) =
 let val (Consts,Decls,aW,vFn) = E
 in (Consts,(s,d)::Decls,aW,vFn)
 end

fun enumList elts = zip elts (upto 0 (length elts - 1));

val real32 = Basic Float;
val real64 = Basic Double;

(*---------------------------------------------------------------------------*)
(* A way of expressing the language consisting of just the empty string      *)
(*---------------------------------------------------------------------------*)

val SKIP = Recd [];

(*---------------------------------------------------------------------------*)
(* Arrays in uxAS are preceded by a length field.                            *)
(*---------------------------------------------------------------------------*)

fun uxasArray contig = Recd [
  ("len", u16),
  ("elts", Array(contig, Loc (VarName"len")))
 ];

fun arrlenBound name i =
 Assert (Bleq(Loc(RecdProj(VarName name,"len")), intLit i));

(*---------------------------------------------------------------------------*)
(* Enforce a given bound on array size                                       *)
(*---------------------------------------------------------------------------*)

fun uxasBoundedArray contig bound = Recd [
  ("len", u16),
  ("len-check",  Assert (Bleq(Loc(VarName "len"), intLit bound))),
  ("elts", Array(contig, Loc (VarName"len")))
 ];

(*---------------------------------------------------------------------------*)
(* Wrapper for a contig, with message type specified. Essentially an option  *)
(*---------------------------------------------------------------------------*)

fun mesgOption mesgtyName contig = Recd [
 ("present", Basic Bool),
 ("contents", Union [
   (Bnot(BLoc (VarName "present")), SKIP),
   (BLoc (VarName "present"), Recd[
     ("seriesID", i64),
     ("mesgType", u32),
     ("version",  u16),
     ("check-mesg-numbers", Assert
       (Band(Beq(Loc(VarName "seriesID"),ConstName "CMASISeriesID"),
        Band(Beq(Loc(VarName "mesgType"),ConstName mesgtyName),
             Beq(Loc(VarName "seriesID"),ConstName "CMASISeriesVersion"))))),
     ("payload",  contig)])
   ])
 ];

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
(* Basic uxAS environment                                                    *)
(*---------------------------------------------------------------------------*)

val uxasEnv =
  (uxas_constants_map,[],atomic_widths,valueFn)
   |> C add_contig_decl ("String",StringRecd)
   |> C add_contig_decl ("KeyValuePair", KeyValuePairRecd)
;

(*---------------------------------------------------------------------------*)
(* Enumerations                                                              *)
(*---------------------------------------------------------------------------*)

val altitude_type = ("AltitudeType", enumList ["AGL","MSL"]);

val speed_type = ("SpeedType", enumList ["AirSpeed","GroundSpeed"]);

val turn_type = ("TurnType", enumList ["TurnShort", "FlyOver"]);

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
(* Add enumerations to environment                                           *)
(*---------------------------------------------------------------------------*)

val E = uxasEnv
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
  ("keep_in_areas",  uxasArray u64),
  ("keep_out_areas", uxasArray u64)
  ];

val automation_request = Recd [
  ("EntityList",           uxasBoundedArray i64 16),
  ("TaskList",             uxasBoundedArray i64 32),
  ("TaskRelationShips",    String),
  ("OperatingRegion",      i64),
  ("RedoAllTasks",         Basic Bool)
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
  ("Status",            CommandStatusType)
 ];

val Waypoint = Recd [
  ("Location",            Location3D),  (* Q: mesgOption this? A: Nope: extension base *)
  ("Number",              i64),
  ("NextWaypoint",        i64),
  ("Speed",               real32),
  ("SpeedType",           SpeedType),
  ("ClimbRate",           real32),
  ("TurnType",            TurnType),
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
  ("AssociatedTasks",  uxasArray i64),
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
 ("contentType",      Scanner (scanTo "|")),
 ("descriptor",       Scanner (scanTo "|")),
 ("source_group",     Scanner (scanTo "|")),
 ("source_entity_ID", Scanner (scanTo "|")),
 ("source_service_ID",Scanner (scanTo "$"))
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
