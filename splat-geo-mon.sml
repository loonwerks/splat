(*===========================================================================*)
(* Example ML code for GeoFence monitor. Note that input calls on            *)
(* event-data-ports are expected to return bytearray option. Thus            *)
(*                                                                           *)
(*    kizone : bytearray                                                     *)
(*    kozone : bytearray                                                     *)
(*    observed : bytearray option                                            *)
(*                                                                           *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Globals                                                                   *)
(*---------------------------------------------------------------------------*)

val alerted = ref false;  (* a pre(var) turns into a state-holding var *)
val dfaState = ref 14;    (* Computed from Thomas' MG *)

(*---------------------------------------------------------------------------*)
(* User defined types                                                        *)
(*---------------------------------------------------------------------------*)

type waypoint =
  {latitude  : Int32.int,
   longitude : Int32.int,
   altitude  : Int32.int};

type zone = waypoint array;

type mission = waypoint array;

(*---------------------------------------------------------------------------*)
(* Observation functions                                                     *)
(*---------------------------------------------------------------------------*)

fun WAYPOINT_IN_ZONE_RECTANGLE (wpt:waypoint) (zone:zone) =
 let open Int32 Array
 in #latitude wpt  >= #latitude(sub(zone,0))  andalso
    #latitude wpt  <= #latitude(sub(zone,1))  andalso
    #longitude wpt >= #longitude(sub(zone,0)) andalso
    #longitude wpt <= #longitude(sub(zone,1)) andalso
    #altitude wpt  >= #altitude(sub(zone,0))
 end

fun WAYPOINTS_IN_ZONE mission zone =
  Array.all (fn wpt => WAYPOINT_IN_ZONE_RECTANGLE wpt zone) mission
 ;

fun WAYPOINTS_NOT_IN_ZONE mission zone =
  Array.all (fn wpt => not (WAYPOINT_IN_ZONE_RECTANGLE wpt zone)) mission
 ;

(*---------------------------------------------------------------------------*)
(* DFA generated from pLTL property. The property is violated when the DFA   *)
(* enters an accept state.                                                   *)
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
  [true, true, true, true, false, false, false,
   false, false, false, false, false, true, false, false];

fun goodState i = Array.sub(DFA_Accepts,i) = true;

fun subset A B = List.all (fn x => mem x B) A;

(*---------------------------------------------------------------------------*)
(* Map from a list of observations to a DFA alphabet symbol (a number)       *)
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

fun DFA_transition (obsList,state) =
  let open Array
      val trueVars = map snd (filter (I o fst) obsList)
   in sub (sub(DFA_Table,state),obs2symbol trueVars)
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
     val () = (dfaState := DFA_transition(obsVals, !dfaState))
 in
   goodState (!dfaState)
end

(*---------------------------------------------------------------------------*)
(* One monitor cycle. Take one DFA step, then set new values for globals,    *)
(* then specify the values of output ports.                                  *)
(*---------------------------------------------------------------------------*)

val latched = true;

fun stepMon (kizone,kozone,observed) =
 let val troubleFound = not (stepDFA (kizone,kozone,observed))
 in
    alerted := ((latched andalso !alerted) orelse troubleFound)
  ;
    {dataOut  = if !alerted then NONE else observed,
     alertOut = if !alerted then SOME() else NONE}
 end

(*---------------------------------------------------------------------------*)
(* Interface with HAMR                                                       *)
(*---------------------------------------------------------------------------*)

type bytes = Word8Vector.vector;

type inports =
  {kizone : bytes,
   kozone : bytes,
   observed : bytes option};

type outports =
  {alert  : unit option,
   output : bytes option};

fun stub() = failwith "stub: not yet implemented";

fun getInputs () : inports =
  {kizone = stub(),
   kozone = stub(),
   observed = stub()};

fun setOutputs {alert,output} =
 case (alert,output)
  of (NONE,NONE)     => ()
   | (NONE,SOME b)   => stub()  (* alert not raised, output sent onwards *)
   | (SOME(),NONE)   => stub()  (* write alert port, output not passed   *)
   | (SOME(),SOME _) => failwith "setOutputs: attempt to forward data when alert is raised"


(*---------------------------------------------------------------------------*)
(* Get input, step monitor, set outputs                                      *)
(*---------------------------------------------------------------------------*)

fun IO_stepFn () = setOutputs(stepMon (getInputs()))


val _ = while true do IO_stepFn();



(*---------------------------------------------------------------------------*)
(* contig-types for the inputs                                               *)
(*---------------------------------------------------------------------------*)

use "mesg_format/contig.sml";

(*---------------------------------------------------------------------------*)
(* Option type via a boolean field and a Union.                              *)
(*---------------------------------------------------------------------------*)

fun Option contig = Recd
 [("present", Basic Bool),
  ("contents", Union [
     (BLoc (VarName "present"), contig),
     (Bnot(BLoc (VarName "present")), SKIP)
     ])
 ];

(*---------------------------------------------------------------------------*)
(* Waypoints. Altitude left unrestricted                                     *)
(*---------------------------------------------------------------------------*)

val waypoint = Recd [
   ("latitude", i32),
   ("longitude", i32),
   ("altitude", i32),
   ("wellformed", Assert (
      Band(Ble (intLit (~90),Loc(VarName"latitude")),
      Band(Ble (Loc(VarName"latitude"),intLit 90),
      Band(Ble (intLit (~180),Loc(VarName"longitude")),
           Ble (Loc(VarName"longitude"),intLit 180))))))
  ]

val all_data_in_one_buffer = Recd [
    ("kizone", Array(waypoint, intLit 2)),
    ("kozone", Array(waypoint, intLit 2)),
    ("mission",
      Option (Recd [("len", u8),
                    ("elts", Array(waypoint, Loc(VarName"len")))]))
   ];


(*---------------------------------------------------------------------------*)
(* OR (slight change of emphasis!) as a spec that needn't translate to a     *)
(* datastructure in order to check data validity.                            *)
(*---------------------------------------------------------------------------*)


val waypoint_that_respects_zones = Recd [ (* lots of "free" lvals" *)
   ("latitude", i32),
   ("longitude", i32),
   ("altitude", i32),
   ("check-inzone",Assert
     (Band(Ble (Loc(RecdProj(ArraySub(VarName"kizone",intLit 0),"latitude")),Loc(VarName"latitude")),
      Band(Ble (Loc(VarName"latitude"), Loc(RecdProj(ArraySub(VarName"kizone",intLit 1),"latitude"))),
      Band(Ble (Loc(RecdProj(ArraySub(VarName"kizone",intLit 0),"longitude")),Loc(VarName"longitude")),
      Band(Ble (Loc(VarName"longitude"), Loc(RecdProj(ArraySub(VarName"kizone",intLit 1),"longitude"))),
           Ble (Loc(RecdProj(ArraySub(VarName"kizone",intLit 0),"altitude")),
                Loc(VarName"altitude")))))))),
   ("check-outzone",Assert
     (Bnot
      (Band(Ble(Loc(RecdProj(ArraySub(VarName"kozone",intLit 0),"latitude")),Loc(VarName"latitude")),
       Band(Ble(Loc(VarName"latitude"), Loc(RecdProj(ArraySub(VarName"kozone",intLit 1),"latitude"))),
       Band(Ble(Loc(RecdProj(ArraySub(VarName"kozone",intLit 0),"longitude")),Loc(VarName"longitude")),
       Band(Ble(Loc(VarName"longitude"), Loc(RecdProj(ArraySub(VarName"kozone",intLit 1),"longitude"))),
        Ble(Loc(RecdProj(ArraySub(VarName"kozone",intLit 0),"altitude")),Loc(VarName"altitude")))))))))
  ];

val all_data_in_one_mesg = Recd [
    ("kizone", Array(waypoint, intLit 2)),
    ("kozone", Array(waypoint, intLit 2)),
    ("mission",
      Option (Recd [("len", u8),
                    ("elts", Array(waypoint_that_respects_zones, Loc(VarName"len")))]))
   ];
