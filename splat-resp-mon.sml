(*===========================================================================*)
(* Hand-rolled ML code for Respose-Request monitor.                          *)
(*===========================================================================*)

load "Regexp_Numerics";

val ERR = mk_HOL_ERR "splat-resp-mon";

(*---------------------------------------------------------------------------*)
(* Globals                                                                   *)
(*---------------------------------------------------------------------------*)

val alerted = ref false;  (* a pre(var) turns into a state-holding var *)
val dfaState = ref 14;    (* Computed from Thomas' MG *)

(*---------------------------------------------------------------------------*)
(* Observation functions                                                     *)
(*---------------------------------------------------------------------------*)

type waypoint =
  {latitude  : int,
   longitude : int,
   altitude  : int};

type zone = waypoint array;

type mission = waypoint array;

fun WAYPOINT_IN_ZONE_RECTANGLE (wpt:waypoint) (zone:zone) =
    #latitude wpt  >= #latitude(Array.sub(zone,0))  andalso
    #latitude wpt  <= #latitude(Array.sub(zone,1))  andalso
    #longitude wpt >= #longitude(Array.sub(zone,0)) andalso
    #longitude wpt <= #longitude(Array.sub(zone,1)) andalso
    #altitude wpt  >= #altitude(Array.sub(zone,0))
;

fun WAYPOINTS_IN_ZONE mission zone =
  Array.all (fn wpt => WAYPOINT_IN_ZONE_RECTANGLE wpt zone) mission
 ;

fun WAYPOINTS_NOT_IN_ZONE mission zone =
  Array.all (fn wpt => not (WAYPOINT_IN_ZONE_RECTANGLE wpt zone)) mission
 ;

(*---------------------------------------------------------------------------*)
(* Parsing. The data in this example is extremely simple; it is not worth it *)
(* to apply the contig-type machinery. Therefore we hand-roll byte buffer    *)
(* parsing.                                                                  *)
(*---------------------------------------------------------------------------*)

fun uvalueFn s =  (* make an unsigned number (MSB) from ASCII string *)
 let open Regexp_Numerics
 in IntInf.toInt(string2iint Unsigned MSB s)
 end

fun ivalueFn s =  (* make a signed number (2scomp, MSB) *)
 let open Regexp_Numerics
 in IntInf.toInt(string2iint Twos_comp MSB s)
 end

fun charAt bytes j =
  Char.chr (Word8.toInt (Word8Vector.sub(bytes,j)))

fun read_u16 bytes i =  (* read a u16 value starting at index i in bytes *)
 if i+2 <= Word8Vector.length bytes then
   uvalueFn (String.implode(List.map (charAt bytes) [i,i+1]))
  else
    raise ERR "read_u16" "";

fun read_i32 bytes (i:int) = (* read an i32 value starting at index i *)
 if i+4 <= Word8Vector.length bytes then
     ivalueFn (String.implode(List.map (charAt bytes) [i,i+1,i+2,i+3]))
 else
     raise ERR "read_i32" "";

fun read_waypoint bytes i =  (* (i32)^3 -> waypoint *)
  if i+12 <= Word8Vector.length bytes then
     {latitude =  read_i32 bytes i,
      longitude = read_i32 bytes (i+4),
      altitude =  read_i32 bytes (i+8)}
   else
       raise ERR "read_waypoint" "";

(*---------------------------------------------------------------------------*)
(* zone = waypoint[2]                                                        *)
(*---------------------------------------------------------------------------*)

fun read_zone bytes i =
  Array.fromList [read_waypoint bytes i, read_waypoint bytes (i+12)];

(*---------------------------------------------------------------------------*)
(* mission = {len  : u16                                                     *)
(*            elts : waypoint[len]}                                          *)
(*---------------------------------------------------------------------------*)

fun read_mission bytes i =
 let val len = read_u16 bytes i
 in Array.fromList
     (List.map (fn i => read_waypoint bytes (i*12+2))
               (upto 0 (len - 1)))
 end;

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
     val V1 = V0 andalso WAYPOINTS_IN_ZONE (Option.valOf observed) kizone
     val V2 = V0 andalso WAYPOINTS_NOT_IN_ZONE (Option.valOf observed) kozone
     val obsVals = [(V0,"V0"),(V1,"V1"),(V2,"V2")]
     val () = (dfaState := DFA_Transition(obsVals, !dfaState))
 in
   goodState (!dfaState)
end

(*---------------------------------------------------------------------------*)
(* The core monitor function has the following type:                         *)
(*                                                                           *)
(*   stepMon : inports -> outports                                           *)
(*                                                                           *)
(* stepMon takes one monitor step: make one DFA step, then set new values    *)
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
 let val kizone = read_zone kizoneB 0
     val kozone = read_zone kozoneB 0
     val observed = Option.map (C read_mission 0) observedB
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

stepMon{kizoneB = kizone_bytes,
        kozoneB = kozone_bytes,
        observedB = SOME mission_bytes};
