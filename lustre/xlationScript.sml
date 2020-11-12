local open ptltlTheory realLib intLib stringLib in end;

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
(* Represent an event data port by a pair of streams. Event and Data are the *)
(* projections.                                                              *)
(*---------------------------------------------------------------------------*)

Definition Event_def :
 Event (a,b) = a
End

Definition Data_def :
 Data (a,b) = b
End

(* -------------------------------------------------------------------------- *)
(*        eq counter_increment : int =                                        *)
(*         0 ->                                                               *)
(*         if (event(observed))                                               *)
(*            then 0                                                          *)
(*         else if (event(reference_1))                                       *)
(*            then 1                                                          *)
(*         else pre(counter_increment);                                       *)
(* -------------------------------------------------------------------------- *)

Definition counter_increment_def :
  counter_increment (reqt,resp) (t:num) =
    if t = 0 then
       0n
    else if Event resp t then
       0
    else if Event reqt t then
       1
    else counter_increment (reqt,resp) (t-1)
End

(* -------------------------------------------------------------------------- *)
(*      eq count : int =                                                      *)
(*         0 ->                                                               *)
(*         if (event(reference_1) or event(observed))                         *)
(*            then 0                                                          *)
(*         else pre(count) + counter_increment;                               *)
(* -------------------------------------------------------------------------- *)

Definition count_def :
  count (reqt,resp) (t:num) =
    if t = 0 then
       0n
    else if Event resp t ∨ Event reqt t then
       0
    else count (reqt,resp) (t-1) +
         counter_increment (reqt,resp) t
End

Definition nMonitorInvocations_def :
  nMonitorInvocations = 10n
End

(* -------------------------------------------------------------------------- *)
(*    eq response_received_in_time : bool = count < nMonitorInvocations;      *)
(* -------------------------------------------------------------------------- *)

Definition response_received_in_time_def :
  response_received_in_time (reqt,resp) (t:num) <=>
     count (reqt,resp) t < nMonitorInvocations
End

(* --------------------------------------------------------------------------*)
(*  property CASE_Monitor_Reqt_Resp_policy =                                 *)
(*       Historically(response_received_in_time);                            *)
(*                                                                           *)
(* Same as saying count has, up to this point, always been less than         *)
(* nMonitorInvocations?                                                      *)
(* --------------------------------------------------------------------------*)

Definition CASE_Monitor_Reqt_Resp_policy_def :
  CASE_Monitor_Reqt_Resp_policy (reqt,resp) t <=>
     ∀t'. t' ≤ t ⇒ response_received_in_time (reqt,resp) t'
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
(*                      or                                                   *)
(*                      not CASE_Monitor_Req_Resp_policy;                    *)
(* --------------------------------------------------------------------------*)

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

(*============================================================================*)
(* Code generation.                                                           *)
(*                                                                            *)
(* Suppose there is a collection of definitions made as part of the           *)
(* monitor declaration. The idea is that they all get evaluated on the        *)
(* current inputs, setting state variables if necessary, and then the         *)
(* monitor specification is checked against those variables.                  *)
(*============================================================================*)

fun event(a,b) = a;
fun data(a,b) = b;

(*---------------------------------------------------------------------------*)
(* pre is invoked on a value (expression?) accessed before variable(s)       *)
(* are updated.                                                              *)
(*---------------------------------------------------------------------------*)

fun pre x = !x;

val counter_increment = ref 0;
val count = ref 0;

fun step_counter_increment(rqt,rsp) =
  if event(rsp)      then (counter_increment := 0)
  else if event(rqt) then (counter_increment := 1)
  else (counter_increment := pre counter_increment);

fun step_count(rqt,rsp) =
  if event(rqt) orelse event(rsp) then
       count := 0
  else count := pre count + !counter_increment

fun response_received_in_time (rqt,resp) = !count < 10;

val policyVar := ref true;

fun CASE_Monitor_Req_Resp_policy(rqt,rsp) =
    policyVar := (!policyVar) andalso response_received_in_time (rqt,resp);


(*---------------------------------------------------------------------------*)
(* How does HAMR want init value of alert set up on output port?  Check      *)
(* filter code.                                                              *)
(*---------------------------------------------------------------------------*)

val latched = true;

(* imperative representation of an event-data-port as a pair of streams *)

val alert = (ref false, ref ());

(*---------------------------------------------------------------------------*)
(* Take a step of the monitor. First, run all input-dependent local          *)
(* functions. This requires evaluating them in dependency order. Then        *)
(* calculate alert.                                                          *)
(*---------------------------------------------------------------------------*)
(*   alert <=> false -> (is_latched and pre(event(alert)))                   *)
(*                      or                                                   *)
(*                      not CASE_Monitor_Req_Resp_policy;                    *)
(*---------------------------------------------------------------------------*)

fun step_monitor (rqt,rsp,alert) =
 let val _ = step_counter_increment(rqt,rsp)
     val _ = step_count(rqt,rsp)
     val Policy = CASE_Monitor_Req_Resp_policy(rqt,rsp)
 in
   if (latched andalso pre(event(alert)) orelse not Policy then
       alert := (true,())
   else ()
 end


(*---------------------------------------------------------------------------

 Now follows the deprecated formalization wherein we modelled event data
 ports as stream of options. That would hamper syntax-directed translation
 of AGREE lustre.

Definition Event_def :
 Event = IS_SOME
End

(* -------------------------------------------------------------------------- *)
(*        eq counter_increment : int =                                        *)
(*         0 ->                                                               *)
(*         if (event(observed))                                               *)
(*            then 0                                                          *)
(*         else if (event(reference_1))                                       *)
(*            then 1                                                          *)
(*         else pre(counter_increment);                                       *)
(* -------------------------------------------------------------------------- *)

Definition counter_increment_def :
  counter_increment (resp,reqt) (t:num) =
    if t = 0 then
       0n
    else if Event (resp t) then
       0
    else if Event (reqt t) then
       1
    else counter_increment (resp,reqt) (t-1)
End

(* -------------------------------------------------------------------------- *)
(*      eq count : int =                                                      *)
(*         0 ->                                                               *)
(*         if (event(reference_1) or event(observed))                         *)
(*            then 0                                                          *)
(*         else pre(count) + counter_increment;                               *)
(* -------------------------------------------------------------------------- *)

Definition count_def :
  count (resp,reqt) (t:num) =
    if t = 0 then
       0n
    else if Event (resp t) ∨ Event (reqt t) then
       0
    else count (resp,reqt) (t-1) +
         counter_increment (resp,reqt) t
End

Definition nMonitorInvocations_def :
  nMonitorInvocations = 10n
End

(* -------------------------------------------------------------------------- *)
(*    eq response_received_in_time : bool = count < nMonitorInvocations;      *)
(* -------------------------------------------------------------------------- *)

Definition response_received_in_time_def :
  response_received_in_time (resp,reqt) (t:num) <=>
     count (resp,reqt) t < nMonitorInvocations
End

(* --------------------------------------------------------------------------*)
(*  property CASE_Monitor_Reqt_Resp_policy =                                  *)
(*       Historically(response_received_in_time);                            *)
(*                                                                           *)
(* Same as saying count has, up to this point, always been less than         *)
(* nMonitorInvocations?                                                      *)
(* --------------------------------------------------------------------------*)

Definition CASE_Monitor_Req_Resp_policy_def :
  CASE_Monitor_Req_Resp_policy (resp,reqt) t <=>
     ∀t'. t' ≤ t ⇒ response_received_in_time (resp,reqt) t'
End

(* --------------------------------------------------------------------------*)
(*  guarantee Req002_ReqRespMonitorEvent                                     *)
(*  "Monitor shall only output an alert when the monitor policy is false"    *)
(*   alert <=> false -> (is_latched and pre(event(alert)))                   *)
(*                      or                                                   *)
(*                      not CASE_Monitor_Req_Resp_policy;                    *)
(*                                                                           *)
(* OR, if alert was a mere event port (no data):                             *)
(*                                                                           *)
(*   Event(alert) <=> false -> (is_latched and pre(event(alert)))            *)
(*                      or                                                   *)
(*                      not CASE_Monitor_Req_Resp_policy;                    *)
(* --------------------------------------------------------------------------*)

Definition Monitor_Spec_def :
  Monitor_Spec (resp,reqt,alert,is_latched) <=>
   ∀t. alert(t) =
         if t = 0n then
            NONE
         else
         if is_latched ∧ Event(alert (t-1)) then
           SOME T
         else
         if ~CASE_Monitor_Reqt_Resp_policy (resp,reqt) t then
          SOME T
         else NONE
End
*)
