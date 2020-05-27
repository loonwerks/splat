(*===========================================================================*)
(* ML code for GeoFence monitor.                                             *)
(*===========================================================================*)
(* AGREE/AADL spec

  thread CASE_Monitor_Geo_thr
  features
    keep_in_zones: in data port CMASI::Polygon.i;
    keep_out_zones: in data port CMASI::Polygon.i;
    alert: out event port;
    observed: in event data port CMASI::AutomationResponse.i;
    output: out event data port CMASI::AutomationResponse.i;

  properties
    CASE_Properties::Component_Type => MONITOR; -- marks this component as a monitor
    CASE_Properties::Component_Spec =>
         ("GeofenceMonitor_alert_event",
          "GeofenceMonitor_output_event", "GeofenceMonitor_output_data"); -- monitor guarantee
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

 process CASE_Monitor_Geo
 features
    keep_in_zones: in data port CMASI::Polygon.i;
    keep_out_zones: in data port CMASI::Polygon.i;
    alert: out event port;
    observed: in event data port CMASI::AutomationResponse.i;
    output: out event data port CMASI::AutomationResponse.i;

properties
    CASE_Scheduling::Domain => 13;
end CASE_Monitor_Geo;
*)

use "uxas.sml";
use "consts.sml";

val ERR = mk_HOL_ERR "geofence-monitor";


(*---------------------------------------------------------------------------*)
(* Globals                                                                   *)
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
(* TODO: consider whether observations have just enough event-data-port info *)
(* for the computation to go through.                                        *)
(*---------------------------------------------------------------------------*)

fun stepDFA (kizone,kozone,observed) =
 let val V0 = Option.isSome observed
     val V1 = V0 andalso
              WAYPOINTS_IN_ZONE
                  (GET_MISSION_COMMAND(Option.valOf observed)) kizone
     val V2 = V0 andalso
              WAYPOINTS_NOT_IN_ZONE
                (GET_MISSION_COMMAND(Option.valOf observed)) kozone
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

type bytes = Word8Vector.vector;

type inports =
  {kizoneB : bytes,
   kozoneB : bytes,
   observedB : bytes option};

type outports =
  {alert  : unit option,
   outputB : bytes option};

fun stepMon {kizoneB,kozoneB,observedB} : outports =
 let val kizone = read_polygon kizoneB
     val kozone = read_polygon kozoneB
     val observed = Option.map read_automation_response observedB
     val troubleFound = not (stepDFA (kizone,kozone,observed))
 in
    alerted := ((latched andalso !alerted) orelse troubleFound)
  ;
    {alert   = if !alerted then SOME() else NONE,
     outputB = if !alerted then NONE else observedB}
 end

(*---------------------------------------------------------------------------*)
(* HAMR interface will provide implementations for getInputs and setOutputs  *)
(* below.                                                                    *)
(*---------------------------------------------------------------------------*)

fun HAMR s = failwith ("expected HAMR "^s^" call");

fun getInputs () : inports = HAMR "input";

fun setOutputs ({alert,outputB} : outports) =
 case (alert,outputB)
  of (NONE,NONE)   => ()
   | (NONE,SOME b) => HAMR "output" (* alert not raised, output sent onwards *)
   | (SOME(),NONE) => HAMR "output" (* alert event signalled, output stifled *)
   | (SOME(),SOME _) => raise ERR "setOutputs"
                         "attempt to forward data when alert is raised";


(*---------------------------------------------------------------------------*)
(* Get input, step monitor, set outputs                                      *)
(*---------------------------------------------------------------------------*)

val IO_stepFn = setOutputs o stepMon o getInputs;

(*---------------------------------------------------------------------------*)
(* Go forever. Does IO_stepFn get bracketed by a wait-release pair?          *)
(*---------------------------------------------------------------------------*)

val _ = while true do IO_stepFn();   (* will currently fail *)


(* Parsing tests  --- using MSB for numbers because it's what uxAS uses *)

local open Regexp_Numerics
in
fun mk_u16 i = iint2string Unsigned MSB 2 (IntInf.fromInt i)
fun mk_i32 i = iint2string Twos_comp MSB 4 (IntInf.fromInt i)
end;

fun waypoint_string (i,j,k) = String.concat[mk_i32 i,mk_i32 j,mk_i32 k];

val kizone_bytes = Byte.stringToBytes
 (String.concat
  [waypoint_string (0,0,9999),
   waypoint_string (75,175,9999)
  ]);

val kozone_bytes = Byte.stringToBytes
 (String.concat
  [waypoint_string (0,0,9999),
   waypoint_string (~35,~60,9999)
  ]);

val mission_bytes = Byte.stringToBytes
 (String.concat
  [mk_u16 5,
   waypoint_string (1,1,9999),
   waypoint_string (2,2,9999),
   waypoint_string (4,4,9999),
   waypoint_string (7,7,9999),
   waypoint_string (65,167,9999)
  ]);

val kizone = read_zone kizone_bytes 0;
val kozone = read_zone kozone_bytes 0;
val mission = read_mission mission_bytes 0;

WAYPOINTS_IN_ZONE mission kizone = true;
WAYPOINTS_NOT_IN_ZONE mission kozone = true;

val (NONE,SOME b) =
  stepMon{kizoneB = kizone_bytes,
          kozoneB = kozone_bytes,
          observedB = SOME mission_bytes};

true = (b = mission_bytes);
