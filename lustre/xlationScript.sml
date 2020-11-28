local open realLib intLib stringLib in end;

val _ = numLib.prefer_num();

(*
thread CASE_Monitor_Req_thr
  features
    observed: in event data port CMASI::AutomationResponse.i;
    reference_1: in event data port CMASI::AutomationRequest.i;
    alert: out event data port Base_Types::Boolean;

  properties
    CASE_Properties::Component_Type => MONITOR; -- marks this component as a monitor
    CASE_Properties::Monitor_Latched => false; -- indicates if the monitor is latched
    CASE_Properties::Component_Spec => ("Req002_ReqRespMonitorEvent"); -- monitor guarantee
    Dispatch_Protocol => Periodic;
    Period => 500ms;
    Compute_Execution_Time => 2ms .. 2ms;
    Stack_Size => CM_Property_Set::Stack_Size;

    annex agree {**
      -- a constant generated from the component property above, handy for expressing
      -- the monitor guarantee

      const is_latched : bool = Get_Property(this, CASE_Properties::Monitor_Latched);

      -- Monitor policy (models the expected behavior in terms of the input ports)
      -- AutomationResponse (observed) occurs within two scheduling cycles after
      -- AutomationRequest (reference_1)

      -- eq empty_day : bool = not event(observed) and not event(reference_1);

      -- property CASE_Monitor_Req_Resp_policy =
      --     Historically(event(reference_1) or
      --     (empty_day and Yesterday(event(reference_1) or
      --     (empty_day and Yesterday(event(reference_1))))) => event(observed));

      eq counter_increment : int =
         0 ->
         if (event(observed))
            then 0
         else if (event(reference_1))
            then 1
         else pre(counter_increment);

      eq count : int =
         0 ->
         if (event(reference_1) or event(observed))
            then 0
         else pre(count) + counter_increment;

      const nMonitorInvocations : int = 10; -- user-defined value for "days"

      eq response_received_in_time : bool = count < nMonitorInvocations;

      property CASE_Monitor_Req_Resp_policy = Historically(response_received_in_time);

      -- Monitor guarantee (guarantees on the output ports in terms of the input ports
      -- and monitor policy)

      guarantee Req002_ReqRespMonitorEvent
        "The monitor shall only output an alert when the monitor policy is false" :
        alert <=> false -> (is_latched and pre(event(alert))) or not CASE_Monitor_Req_Resp_policy;

      guarantee FOO
        "The monitor shall only output an alert when the monitor policy is false" :
        Event(alert) <=> alert

     **};

end CASE_Monitor_Req_thr;
*)

val _ = new_theory "xlation";

Datatype ‘SpeedType = Airspeed | Groundspeed’;

Datatype ‘TurnType = TurnShort | FlyOver’;

Datatype ‘CommandStatusType = Pending | Approved | InProcess | Executed | Cancelled’;

Datatype ‘AltitudeType = AGL | MSL’;

Datatype ‘KeyValuePair = <| Key : string ; Value : string |>’;

Datatype ‘VehicleAction = <| AssociatedTaskList : int list |>’;

Datatype ‘Waypoint =
      <| Latitude : real ;
         Longitude : real ;
         Altitude : real ;
         AltitudeType : AltitudeType ;
         Number : int ;
         NextWaypoint : int ;
         Speed : real ;
         SpeedType : SpeedType ;
         ClimbRate : real ;
         TurnType : TurnType ;
         VehicleActionList : VehicleAction list ;
         ContingencyWaypointA : int ;
         ContingencyWaypointB : int ;
         AssociatedTasks : int list |>’
;

Datatype ‘MissionCommand =
      <| CommandID :  int ;
         VehicleID : int ;
         VehicleActionList : VehicleAction list ;
         Status : CommandStatusType ;
         WaypointList : Waypoint list ;
         FirstWaypoint : int
      |>’
;


Datatype ‘VehicleActionCommand =
      <| CommandID : int ;
         VehicleID : int ;
         VehicleActionList : VehicleAction list ;
         Status : CommandStatusType
      |>’
;

Datatype ‘AutomationResponse =
      <| MissionCommandList : MissionCommand list ;
         VehicleCommandList : VehicleActionCommand list ;
         Info: KeyValuePair list
      |>’
;


Datatype ‘AutomationRequest =
      <| EntityList : int list ;
         TaskList : int list;
         TaskListSize : int ;
         TaskRelationships : string ;
         OperatingRegion : int ;
         RedoAllTasks : bool
      |>’
;

(*---------------------------------------------------------------------------*)
(* History TL primitive (semantic version). Also needs to be a programmatic  *)
(* version.                                                                  *)
(*---------------------------------------------------------------------------*)

Definition Historically_def :
 Historically P t ⇔ ∀i. i ≤ t ⇒ P i
End

(*---------------------------------------------------------------------------*)
(* Represent an event data port by a pair of streams. Event and Data are the *)
(* projections.                                                              *)
(*---------------------------------------------------------------------------*)

Definition Event_def :
 Event (A:num->bool,B:num->'a) = A
End

Definition Data_def :
 Data (A:num->bool,B:num->'a) = B
End

Definition nMonitorInvocations_def :
  nMonitorInvocations = 10n
End

Definition FAIL_def :
 FAIL = nMonitorInvocations + 1
End

Definition Inc_def :
 Inc x = if x < nMonitorInvocations then x+1 else FAIL
End

Definition ticks_def :
 (ticks (reqt,resp) 0 =
    if Event resp 0 then
       FAIL
    else if Event reqt 0 then 1 else 0) /\
  (ticks (reqt,resp) t =
   if Event reqt t /\ Event resp t then
      FAIL
   else
   if ~(Event reqt t \/ Event resp t) then
      (if ticks (reqt,resp) (t-1) = 0 then
         0
       else Inc (ticks (reqt,resp) (t-1)))
   else
   if Event resp t then
      (if (1 <= ticks (reqt,resp) (t-1)) then 0 else FAIL)
   else
      (if (ticks (reqt,resp) (t-1) = 0) then 1 else FAIL))
End

val ticks_thm = SIMP_RULE arith_ss [] ticks_def;

(* -------------------------------------------------------------------------- *)
(*    eq response_received_in_time : bool = ticks < nMonitorInvocations;      *)
(* -------------------------------------------------------------------------- *)

Definition response_received_in_time_def :
  response_received_in_time (reqt,resp) (t:num) <=>
     ticks (reqt,resp) t < nMonitorInvocations
End

(* --------------------------------------------------------------------------*)
(*  property CASE_Monitor_Reqt_Resp_policy =                                 *)
(*       Historically(response_received_in_time);                            *)
(*                                                                           *)
(* Same as saying count has, up to this point, always been less than         *)
(* nMonitorInvocations.                                                      *)
(* --------------------------------------------------------------------------*)

Definition CASE_Monitor_Reqt_Resp_policy_def :
  CASE_Monitor_Reqt_Resp_policy (reqt,resp)
   <=>
  Historically (response_received_in_time (reqt,resp))
End

(* --------------------------------------------------------------------------*)
(*  guarantee Req002_ReqRespMonitorEvent                                     *)
(*  "Monitor shall only output an alert when the monitor policy is false"    *)
(*   alert <=> false -> (is_latched and pre(event(alert)))                   *)
(*                      or                                                   *)
(*                      not CASE_Monitor_Req_Resp_policy;                    *)
(*  guarantee FOO : ""                                                       *)
(*    Event(alert) <=> alert                                                 *)
(*                                                                           *)
(* OR, if alert was a mere event port (no data):                             *)
(*                                                                           *)
(*   Event(alert) <=> false -> (is_latched and pre(event(alert)))            *)
(*                             or                                            *)
(*                             not CASE_Monitor_Req_Resp_policy;             *)
(* --------------------------------------------------------------------------*)
(*
Definition Monitor_Spec_def :
  Monitor_Spec (reqt,resp,alert,is_latched) <=>
   ∀t. (Data alert t =
         if t = 0n then
            F
         else
         ((is_latched ∧ Event alert (t-1))
         ∨
         ~CASE_Monitor_Reqt_Resp_policy (reqt,resp) t))
      ∧
      (Event alert t ⇔ Data alert t)
End
*)

(*============================================================================*)
(* Code generation.                                                           *)
(*                                                                            *)
(* Suppose there is a collection of definitions made as part of the           *)
(* monitor declaration. The idea is that they all get evaluated on the        *)
(* current inputs, setting state variables if necessary, and then the         *)
(* monitor specification is checked against those updated variables.          *)
(*============================================================================*)

val ERR = mk_HOL_ERR "xlationScript";

datatype 'a edport = EDPORT of bool * 'a;

fun Event (EDPORT (a,b)) = a;
fun Data (EDPORT (a,b)) = b;

(*---------------------------------------------------------------------------*)
(* constants                                                                 *)
(*---------------------------------------------------------------------------*)

val is_latched = true;

val nMonitorInvocations = 10;

val FAILURE = nMonitorInvocations + 1;

fun Inc x = if x < nMonitorInvocations then x+1 else FAILURE;

type state = {time : int,
	      H : bool,
              alert : bool,
              ticks : int};

val stateVars : state ref =
    ref {time = 0,
	 H = false,
         alert = false,
         ticks = ~42};

(*---------------------------------------------------------------------------*)
(* Take a step of the monitor. First, run all input-dependent local          *)
(* functions. This requires evaluating them in dependency order. Then        *)
(* calculate alert.                                                          *)
(*---------------------------------------------------------------------------*)
(*   alert <=> false -> (is_latched and pre(event(alert)))                   *)
(*                      or                                                   *)
(*                      not CASE_Monitor_Req_Resp_policy;                    *)
(*---------------------------------------------------------------------------*)

fun stepFn (reqt,resp) state =
 case state
  of {time,H,alert,ticks} =>
     if time = 0 then
        let val ticks = (if Event resp then FAILURE
                         else if Event reqt then 1 else 0)
            val timely = ticks < nMonitorInvocations
            val H = timely
	    val alert = not H
        in
          {time = time + 1, H = H, alert = alert, ticks = ticks}
        end
     else (* t > 0 *)
        let val ticks =
             (case (Event reqt,Event resp)
               of (true,true)   => FAILURE
                | (false,false) => (if ticks = 0 then 0 else Inc ticks)
                | (false,true)  => (if 1 <= ticks then 0 else FAILURE)
                | (true,false)  => (if ticks = 0 then 1 else FAILURE))
            val timely = ticks < nMonitorInvocations
            val H = timely andalso H
	    val alert = (is_latched andalso alert) orelse not H
        in
           {time = time + 1, H = H, alert = alert, ticks = ticks}
        end
;

fun getReqt() : bool edport = raise ERR "getReqt" "stub";
fun getResp() : bool edport = raise ERR "getResp" "stub";
fun putAlert x = raise ERR "putAlert" "stub";

val alertHi = EDPORT(true,true);
val alertLo = EDPORT(true,false);

fun stepMon () =
 let val (rqt,rsp) = (getReqt(),getResp())
     val state = !stateVars
     val state' = stepFn (rqt,rsp) state
     val _ = stateVars := state'
 in
   if #alert(!stateVars) then putAlert alertHi else putAlert alertLo
 end
