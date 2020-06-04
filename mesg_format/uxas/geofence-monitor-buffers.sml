(*===========================================================================*)
(* ML code for GeoFence monitor.                                             *)
(*===========================================================================*)
(* AGREE/AADL spec

  thread CASE_Monitor_Geo_thr
  features
    keep_in_zones  : in data port CMASI::Polygon.i;
    keep_out_zones : in data port CMASI::Polygon.i;
    observed       : in event data port CMASI::AutomationResponse.i;
    alert          : out event port;
    output         : out event data port CMASI::AutomationResponse.i;

  properties
    CASE_Properties::Component_Type => MONITOR; -- marks this component as a monitor

    -- monitor guarantee
    CASE_Properties::Component_Spec =>
         ("GeofenceMonitor_alert_event",
          "GeofenceMonitor_output_event", "GeofenceMonitor_output_data");
    CASE_Properties::Monitor_Latched => true; -- indicates if the monitor is latched
    Dispatch_Protocol => Periodic;
    Period => 500ms;
    Compute_Execution_Time => 2ms .. 2ms;

  annex agree {**
    -- a constant generated from the component property above, handy for
    -- expressing the monitor guarantee
    const is_latched : bool = Get_Property(this, CASE_Properties::Monitor_Latched);

    -- Monitor policy (models the expected behavior in terms of the input ports)
    -- property CASE_Monitor_Coord_policy =
         Historically
           (event(observed) =>
            (WAYPOINTS_IN_ZONE(GET_MISSION_COMMAND(observed), keep_in_zones) and
             WAYPOINTS_NOT_IN_ZONE(GET_MISSION_COMMAND(observed), keep_out_zones)));

    -- Monitor guarantee (guarantees on the output ports in terms of the input ports
    -- and monitor policy)
    guarantee GeofenceMonitor_alert_event
    "An alert is generated only when observed is invalid" :
      event(alert) <=> false -> (is_latched and pre(event(alert))) or not CASE_Monitor_Coord_policy;

    guarantee GeofenceMonitor_output_event
    "The output event fires only when observed is valid" :
      event(output) <=> event(observed) and not event(alert);

    guarantee GeofenceMonitor_output_data
    "Output is equal to observed when observed is valid" :
      event(observed) and not event(alert) => output = observed;

    fun GET_MISSION_COMMAND
          (automationResponse: CMASI::AutomationResponse.i) : CMASI::MissionCommand.i
        = automationResponse.MissionCommandList[0];

    fun WAYPOINTS_IN_ZONE
          (mission : CMASI::MissionCommand.i, zone : CMASI::Polygon.i) : bool
        = forall waypoint in mission.WaypointList, WAYPOINT_IN_ZONE_RECTANGLE(waypoint, zone);

    fun WAYPOINTS_NOT_IN_ZONE
          (mission : CMASI::MissionCommand.i, zone : CMASI::Polygon.i) : bool
        = forall waypoint in mission.WaypointList, not WAYPOINT_IN_ZONE_RECTANGLE(waypoint, zone);

    -- Assumes rectangle that is defined by two corners so it is aligned
    -- with the origin (not rotated in space)
    -- Assumes that the altitude is the same in all the coordinates
    -- Assumes zone[0] is the bottom left corner and zone[1] in the upper right corner

    fun WAYPOINT_IN_ZONE_RECTANGLE
          (waypoint : CMASI::Waypoint.i, zone : CMASI::Polygon.i) : bool
        = (waypoint.Latitude >= (zone.BoundaryPointsList[0]).Latitude)
           and (waypoint.Latitude <= (zone.BoundaryPointsList[1]).Latitude)
           and (waypoint.Longitude >= (zone.BoundaryPointsList[0]).Longitude)
           and (waypoint.Longitude <= (zone.BoundaryPointsList[1]).Longitude)
           and (waypoint.Altitude >= (zone.BoundaryPointsList[0]).Altitude);
  **};
 end CASE_Monitor_Geo_thr;

*)

(*---------------------------------------------------------------------------*)
(* NB. The notion of polygon used for the keep-in and keep-out zones is a    *)
(* 2-element array of Location3D items. The message format for polygon is    *)
(* "plain", ie. not in the uxas address-attributed coding. The contig type   *)
(* is therefore just                                                         *)
(*                                                                           *)
(*     Array(Location3D, intLit 2)                                           *)
(*                                                                           *)
(* The "observed" port is an address-attributed event port where the data is *)
(* an automation_response.                                                   *)
(*---------------------------------------------------------------------------*)


use "uxas.sml";
use "consts.sml";

val ERR = mk_HOL_ERR "geofence-monitor-buffers";

structure API =
struct
  (* A Location3D record is exactly 21 bytes *)
  val polygonSizeBytes = 48;

  (* The actual max size of an automation response is huge *)
  val automation_responseAASizeBytes = 10 * 1024

(*---------------------------------------------------------------------------*)
(* IO via faked-up CakeML FFI interface.                                     *)
(*---------------------------------------------------------------------------*)

exception FFI_CALL of string

val flyZoneDBKeepInZone_ints =
   [64, 70, 166, 115, 79, 130, 245, 18, 192, 94, 64, 242, 161, 114, 171, 239,
    68, 122, 0, 0, 0, 0, 0, 1, 64, 70, 172, 52, 59, 112, 239, 86, 192, 94,
    58, 101, 152, 225, 12, 246, 68, 122, 0, 0, 0, 0, 0, 1];

val flyZoneDBKeepOutZone_ints =
   [64, 70, 170, 161, 173, 100, 81, 185, 192, 94, 60, 9, 162, 64, 49, 72, 68,
    122, 0, 0, 0, 0, 0, 1, 64, 70, 170, 250, 13, 119, 183, 200, 192, 94, 59,
    202, 167, 88, 158, 254, 68, 122, 0, 0, 0, 0, 0, 1];

val isaacKeepInZone_ints =
   [64, 70, 166, 115, 127, 145, 88, 34, 192, 94, 64, 241, 85, 201, 92, 129,
    68, 122, 0, 0, 0, 0, 0, 1, 64, 70, 172, 51, 76, 52, 202, 88, 192, 94, 58,
    102, 184, 109, 250, 125, 68, 122, 0, 0, 0, 0, 0, 1];

val isaacKeepOutZone_ints =
   [64, 70, 170, 161, 177, 173, 198, 213, 192, 94, 60, 9, 194, 235, 166, 12,
    68, 122, 0, 0, 0, 0, 0, 1, 64, 70, 170, 250, 0, 133, 236, 185, 192, 94,
    59, 202, 243, 88, 129, 235, 68, 122, 0, 0, 0, 0, 0, 1];


fun toString list = String.implode (List.map Char.chr list);

val flyZoneDBKeepInZone = toString flyZoneDBKeepInZone_ints
val flyZoneDBKeepOutZone = toString flyZoneDBKeepOutZone_ints
val isaacKeepInZone = toString isaacKeepInZone_ints
val isaacKeepOutZone = toString isaacKeepOutZone_ints;

val automation_response_event_string =
 let val istrm = TextIO.openIn "ARE"
     val str = TextIO.inputAll istrm
     val _ = TextIO.closeIn istrm
 in
   str
 end;

fun copyVec s buf =
    Word8Array.copyVec {src = Byte.stringToBytes s, dst = buf, di = 0};

fun std_output s = TextIO.output(TextIO.stdOut,s);

fun callFFI fname istr obuf =
 if fname = "get_keep_in_zone" then
    let val inputLen = String.size flyZoneDBKeepInZone
        val bufLen = Word8Array.length obuf
    in if inputLen <= bufLen  then
         copyVec flyZoneDBKeepInZone obuf
       else raise FFI_CALL "get_keep_in_zone: input too large for buffer"
    end
 else
 if fname = "get_keep_out_zone" then
    let val inputLen = String.size flyZoneDBKeepOutZone
        val bufLen = Word8Array.length obuf
    in if inputLen <= bufLen  then
         copyVec flyZoneDBKeepOutZone obuf
       else raise FFI_CALL "get_keep_out_zone: input too large for buffer"
    end
 else
 if fname = "get_observed" then
    let val inputLen = String.size automation_response_event_string
        val bufLen = Word8Array.length obuf
    in if inputLen <= bufLen  then
         copyVec automation_response_event_string obuf
       else raise FFI_CALL "get_observed: input too large for buffer"
    end
 else
 if fname = "put_alert" then
     std_output "\nALERT!\n"
 else
 if fname = "put_output" then
     std_output "\nmoving observed input to output\n"
 else
 raise FFI_CALL "unknown IO request"


end  (* API *)

structure Geofence_Monitor =
struct

val w8zero = Word8.fromInt 0;

(*---------------------------------------------------------------------------*)
(* Declare input buffers as global variables.                                *)
(*---------------------------------------------------------------------------*)

val kizone_buffer   = Word8Array.array(API.polygonSizeBytes,w8zero)
val kozone_buffer   = Word8Array.array(API.polygonSizeBytes,w8zero)
val observed_buffer = Word8Array.array
                         (API.automation_responseAASizeBytes,w8zero)

val emptybuf = Word8Array.array(0,w8zero);

fun clear buffer =
 let val len = Word8Array.length buffer
     fun zero i = Word8Array.update(buffer,i, w8zero)
     fun loop j = if j < len then (zero j; loop (j+1)) else ()
 in
    loop 0
 end;

(*---------------------------------------------------------------------------*)
(* Globals from the "business logic" of the monitor                          *)
(*---------------------------------------------------------------------------*)

val alerted = ref false;  (* a pre(var) turns into a state-holding var *)
val dfaState = ref 14;    (* Computed from Thomas' MG *)


(*---------------------------------------------------------------------------*)
(* Observation functions                                                     *)
(*---------------------------------------------------------------------------*)

fun WAYPOINT_IN_ZONE_RECTANGLE (locn:Location3D) (zone:Polygon) =
 let open Real
     val {Latitude,Longitude,Altitude,AltitudeType} = locn
     val LL = Array.sub(zone,0)
     val UR = Array.sub(zone,1)
 in
    Latitude  >= #Latitude LL  andalso
    Latitude  <= #Latitude UR  andalso
    Longitude >= #Longitude LL andalso
    Longitude <= #Longitude UR andalso
    Real32.==(Altitude, #Altitude LL)
 end;

fun location_of (wpt: Waypoint) = #Location wpt;
fun waypoints_of (cmd: MissionCommand) = #WaypointList cmd;

fun WAYPOINTS_IN_ZONE missioncmd zone =
  Array.all (fn wpt => WAYPOINT_IN_ZONE_RECTANGLE (location_of wpt) zone)
            (waypoints_of missioncmd)
 ;

fun WAYPOINTS_NOT_IN_ZONE missioncmd zone =
  Array.all (fn wpt => not (WAYPOINT_IN_ZONE_RECTANGLE (location_of wpt) zone))
            (waypoints_of missioncmd)
 ;

(*---------------------------------------------------------------------------*)
(* Extra credit. All waypoints have distinct coords.                         *)
(*---------------------------------------------------------------------------*)

fun locnEq loc1 loc2 =
 let val {Latitude=lat1,Longitude=lon1,Altitude=alt1,AltitudeType=aty1} = loc1
     val {Latitude=lat2,Longitude=lon2,Altitude=alt2,AltitudeType=aty2} = loc2
 in
    Real.==(lat1,lat2) andalso
    Real.==(lon1,lon2) andalso
    Real32.==(alt1,alt2) (* Not checking altType equal *)
 end

fun waypointEq wp1 wp2 = locnEq (location_of wp1) (location_of wp2);

(*---------------------------------------------------------------------------*)
(* Different indices map to different elements, i.e., no duplicates          *)
(*---------------------------------------------------------------------------*)

fun arrayInjective equiv arr =
 let val len = Array.length arr
     fun look i elts =
       if i < len then
          let val elt = Array.sub(arr,i)
          in if List.exists (equiv elt) elts then false
             else look (i+1) (elt::elts)
          end
       else true
 in look 0 []
 end;

(*
val test = arrayInjective (equal:int->int->bool);
test (Array.fromList [1,2,3,4,5,6,7,8,9]);
test (Array.fromList [1,2,3,4,9,6,7,8,9]);
*)

fun WAYPOINTS_DISTINCT missioncmd =
    arrayInjective waypointEq (waypoints_of missioncmd);

fun GET_MISSION_COMMAND (AR : AutomationResponse) : MissionCommand
    = Array.sub(#MissionCommandList AR,0);

(*---------------------------------------------------------------------------*)
(* DFA generated from pLTL property. The property is violated when the DFA   *)
(* is no longer in an accept state.                                          *)
(*---------------------------------------------------------------------------*)

val DFA_Table =
  Array.fromList
   (map Array.fromList
     [[12, 11, 5, 4, 3, 2, 1, 0],
      [12, 11, 5, 4, 3, 2, 1, 0],
      [12, 11, 5, 4, 3, 2, 1, 0],
      [12, 11, 5, 4, 3, 2, 1, 0],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [10, 11, 5, 4, 9, 8, 7, 6],
      [12, 11, 5, 4, 3, 2, 1, 0],
      [13, 13, 13, 13, 13, 13, 13, 13],
      [12, 11, 5, 4, 3, 2, 1, 0]]);

val DFA_Accepts = Array.fromList
  [true, true, true,
   true, false, false,
   false, false, false,
   false, false, false,
   true, false, false];

fun goodState i = Array.sub(DFA_Accepts,i) = true;

fun subset A B = List.all (fn x => mem x B) A;

(*---------------------------------------------------------------------------*)
(* Map from a list of observations to a DFA alphabet symbol (a number)       *)
(* Generated from Thomas' MG.                                                *)
(*---------------------------------------------------------------------------*)

fun obs2symbol obslist =
 if subset ["obsVar_1", "obsVar_2","obsVar_3"] obslist then
    0 else
 if subset ["obsVar_1", "obsVar_2"] obslist then
    1 else
 if subset ["obsVar_1", "obsVar_3"] obslist then
    2 else
 if subset ["obsVar_1"] obslist then
    3 else
 if subset ["obsVar_2", "obsVar_3"] obslist then
    4 else
 if subset ["obsVar_2"] obslist then
    5 else
 if subset ["obsVar_3"] obslist then
    6
 else 7;

fun DFA_Transition (obsList,state) =
  let fun is_true_pair (b,s) = (b=true)
      val trueVars = map snd (filter is_true_pair obsList)
  in
     Array.sub (Array.sub(DFA_Table,state),obs2symbol trueVars)
  end

(*---------------------------------------------------------------------------*)
(* Take one DFA step. Compute the observations and collect the true ones,    *)
(* but only in case all "in-event-dataports" have data. If not, then each    *)
(* observation is just set to false, without attempting the computations.    *)
(*---------------------------------------------------------------------------*)

fun stepDFA kizone kozone responseOpt =
 let val V0 = Option.isSome responseOpt
     val V1 = V0 andalso
              WAYPOINTS_IN_ZONE
                  (GET_MISSION_COMMAND(Option.valOf responseOpt)) kizone
     val V2 = V0 andalso
              WAYPOINTS_NOT_IN_ZONE
                (GET_MISSION_COMMAND(Option.valOf responseOpt)) kozone
     val obsVals = [(V0,"obsVar_1"),(V1,"obsVar_2"),(V2,"obsVar_3")]
     val () = (dfaState := DFA_Transition(obsVals, !dfaState))
 in
   goodState (!dfaState)
end

(*---------------------------------------------------------------------------*)
(* The core monitor function has the following type:                         *)
(*                                                                           *)
(*   stepMon : inports -> outports                                           *)
(*                                                                           *)
(* A stepMon step does the following: make one DFA step, then set new values *)
(* for globals, then set the values of output ports.                         *)
(*                                                                           *)
(* Logic specification of stepMon behaviour follows. I'd dearly like to get  *)
(* this by AADL scraping. MON_SPEC relates the pre-state and inputs to the   *)
(* post-state (state') and outputs. The state is a record with fields        *)
(*                                                                           *)
(*  {dfaState : num, alerted : bool}                                         *)
(*                                                                           *)
(* MON_SPEC (state, inputs) (state',outputs) =                               *)
(*  state'.dfaState = stepDFA(state.dfaState,inputs) /\                      *)
(*  state'.alerted = (latched /\ state.alerted) \/ ~good(state'.dfaState) /\ *)
(*  ((state'.alerted  /\ outputs = {dataOut=NONE, alertOut = SOME()}) \/     *)
(*   (~state'.alerted /\ outputs = {dataOut=dataIn, alertOut = NONE}))       *)
(*                                                                           *)
(* Notice a slight subtlety: the last disjunct covers two cases. If the      *)
(* system hasn't yet entered an alert state, then dataOut is equal to        *)
(* dataIn, in case dataIn is NONE or in case it is SOME(-).                  *)
(*                                                                           *)
(* The code for stepMon can be improved by handling possible parse errors.   *)
(*---------------------------------------------------------------------------*)

val latched = true;   (* Obtained from architecture; can also be false *)

fun stepMon kizone kozone responseOpt =
 let val troubleFound = not (stepDFA kizone kozone responseOpt)
     val () = alerted := ((latched andalso !alerted) orelse troubleFound)
 in
   !alerted
 end

(*---------------------------------------------------------------------------*)
(* Move buf contents, less the first char (which represents eventishness),   *)
(* to string, which becomes the argument to the selected FFI output call.    *)
(* Would raise an exception if buf was of size 0, which we know isn't true.  *)
(*---------------------------------------------------------------------------*)

fun outFFI fname buf =
 let val vect = Word8Array.vector buf
     val event_string = Byte.bytesToString vect
     val string = String.extract(event_string,1,NONE)
 in
  API.callFFI fname string emptybuf
 end

fun inFFI fname buf = (clear buf ; API.callFFI fname "" buf);

fun fill_buffers() =
 let in
    inFFI "get_keep_in_zone"  kizone_buffer
  ; inFFI "get_keep_out_zone" kozone_buffer
  ; inFFI "get_observed"      observed_buffer
 end

(*---------------------------------------------------------------------------*)
(* Parse message buffers to datastructures                                   *)
(*---------------------------------------------------------------------------*)

fun parse_buf contig mk_data buf =
 let val string = Byte.bytesToString (Word8Array.vector buf)
 in
  case parseFn uxasEnv (VarName"root") contig ([],string,empty_lvalMap)
   of SOME ([ptree],remaining,theta) => mk_data ptree
    | otherwise => raise ERR "parse_buf" ""
 end

fun mk_kizone() : Polygon =
  parse_buf PhaseII_Polygon mk_phase2_polygon kizone_buffer

fun mk_kozone() : Polygon =
  parse_buf PhaseII_Polygon mk_phase2_polygon kozone_buffer

(*---------------------------------------------------------------------------*)
(* A SOME value returned means that there was an event, and that the buffer  *)
(* translated to an AutomationResponse.                                      *)
(*---------------------------------------------------------------------------*)

fun mk_automation_response_event () : AutomationResponse option =
   parse_buf (Option fullAutomationResponseMesg)
             mk_AR_event observed_buffer;


fun geofence_monitor () =
 let val _           = fill_buffers()
     val kizone      = mk_kizone()
     val kozone      = mk_kozone()
     val responseOpt = mk_automation_response_event()
     val alertHi     = stepMon kizone kozone responseOpt
 in
   if alertHi
    then API.callFFI "put_alert" "" emptybuf
    else outFFI "put_output" observed_buffer
 end


end (* Geofence_Monitor *)
