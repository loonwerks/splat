use "uxas.sml";
use "consts.sml";

(*---------------------------------------------------------------------------
thread CASE_AttestationGate_thr
features

  trusted_ids: in data port CMASI::Address
                   {Data_Model::Data_Representation => Array;
                    Data_Model::Dimension => (3);};

  AutomationRequest_in  : in event data port  CMASI::AddressAttributedMessage.i;
  AutomationRequest_out : out event data port CMASI::AutomationRequest.i;
  OperatingRegion_in    : in event data port  CMASI::AddressAttributedMessage.i;
  OperatingRegion_out   : out event data port CMASI::OperatingRegion.i;
  LineSearchTask_in     : in event data port  CMASI::AddressAttributedMessage.i;
  LineSearchTask_out    : out event data port CMASI::LineSearchTask.i;

properties
  CASE_Properties::Component_Type => MONITOR;
  CASE_Properties::Component_Spec => ("CASE_AttestationGate_policy");

annex agree {**

  fun IS_TRUSTED(src_id : CMASI::Address) : bool = exists id in trusted_ids, id = src_id;

  guarantee CASE_AttestationGate_policy "Only messages from trusted sources shall be forwarded" :
    if event(AutomationRequest_in) and IS_TRUSTED(AutomationRequest_in.id) then
         event(AutomationRequest_out)
          and not (event(OperatingRegion_out) or event(LineSearchTask_out))
          and AutomationRequest_out = AutomationRequest_in.payload.AutomationRequest
    else
    if event(OperatingRegion_in) and IS_TRUSTED(OperatingRegion_in.id) then
         event(OperatingRegion_out)
          and not (event(AutomationRequest_out) or event(LineSearchTask_out))
          and OperatingRegion_out = OperatingRegion_in.payload.OperatingRegion
    else
    if event(LineSearchTask_in) and IS_TRUSTED(LineSearchTask_in.id) then
         event(LineSearchTask_out)
          and not (event(AutomationRequest_out) or event(OperatingRegion_out))
          and LineSearchTask_out = LineSearchTask_in.payload.LineSearchTask
    else
      not (event(AutomationRequest_out)
           or event(OperatingRegion_out)
           or event(LineSearchTask_out));

end CASE_AttestationGate_thr;
-----------------------------------------------------------------------------*)

(*
val AAmesg = Recd [
   ("address",           Scanner (scanTo "$")),
   ("contentType",       Scanner (scanTo "|")),
   ("descriptor",        Scanner (scanTo "|")),
   ("source_group",      Scanner (scanTo "|")),
   ("source_entity_ID",  Scanner (scanTo "|")),
   ("source_service_ID", Scanner (scanTo "$")),
   ("all_the_rest",      Scanner (fn s => SOME(s,"")))
 ];

val trusted_ids = Array(i32,intLit 3);
*)

(*---------------------------------------------------------------------------*)
(* Parsing. Break input into A$B|C|D|E|F$G                                   *)
(*---------------------------------------------------------------------------*)

fun seekFrom V w8 i =
 let val K = Word8Vector.length V
     fun seek j =
       if j < K then
          (if Word8Vector.sub(V,j) = w8 then SOME j else seek (j+1))
       else NONE
 in seek i
 end;

fun seekFrom S c i =
 let val K = String.size S
     fun seek j =
       if j < K then
          (if String.sub(S,j) = c then SOME j else seek (j+1))
       else NONE
 in seek i
 end;

fun scan S =
 case seekFrom S #"$" 0
  of NONE => NONE
   | SOME i1 =>
 case seekFrom S #"|" (i1+1)
  of NONE => NONE
   | SOME i2 =>
 case seekFrom S #"|" (i2+1)
  of NONE => NONE
   | SOME i3 =>
 case seekFrom S #"|" (i3+1)
  of NONE => NONE
   | SOME i4 =>
 case seekFrom S #"|" (i4+1)
  of NONE => NONE
   | SOME i5 =>
 case seekFrom S #"$" (i5+1)
  of NONE => NONE
   | SOME i6 =>
     SOME(String.substring(S,0,i1+1),
          String.substring(S,i1+1,i2-i1),
          String.substring(S,i2+1,i3-i2),
          String.substring(S,i3+1,i4-i3),
          String.substring(S,i4+1,i5-i4),
          String.substring(S,i5+1,i6-i5),
          String.extract(S,i6+1,NONE))
;

fun fromDecimal s =
 let val s' = String.substring(s,0,String.size s - 1) (* drop vertical bar *)
 in Int.fromString s'
 end

fun getID S =
 case scan S
  of NONE => NONE
   | SOME (address,contentType,descriptor,
           source_group, source_entity_ID,
           source_service_ID, all_the_restxp) => fromDecimal source_entity_ID
;

val readID = getID o Byte.bytesToString;

(* Tests *)

val SOME 500 = getID "A$B|C|D|500|F$G";
val SOME 500 = getID "A$B||D|500|F$G";
val SOME 500 = getID "199.0.0.1$p--q--r|foo|A!D!CD|500|FRED$GHIJ";

(*---------------------------------------------------------------------------*)
(* Map 3 adjacent 4-byte chunks to 3 ints                                    *)
(*---------------------------------------------------------------------------*)

fun get_trusted_ids s =
 if String.size s = 12 then
   let val s1 = String.substring(s,0,4)
       val s2 = String.substring(s,4,4)
       val s3 = String.substring(s,8,4)
   in case Int.fromString s1
       of NONE => NONE
        | SOME i1 =>
      case Int.fromString s2
       of NONE => NONE
        | SOME i2 =>
      case Int.fromString s3
       of NONE => NONE
        | SOME i3 =>
      SOME(Array.fromList[i1,i2,i3])
   end
 else NONE

val readTIDs = get_trusted_ids o Byte.bytesToString;

(*---------------------------------------------------------------------------*)
(* The actual check being made.                                              *)
(*---------------------------------------------------------------------------*)

fun check tids bytes =
 case readID bytes
  of NONE => NONE
   | SOME ID =>
      if Array.exists (equal ID) tids
      then SOME bytes
      else NONE

type inports
   = Word8Vector.vector *
     Word8Vector.vector option *
     Word8Vector.vector option *
     Word8Vector.vector option;

type outports
   = Word8Vector.vector option *
     Word8Vector.vector option *
     Word8Vector.vector option;

(*---------------------------------------------------------------------------*)
(* Look at all events in an ordered manner: OpRegion; LST; AutoRqt. Pass     *)
(* only the first one that meets the criterion.                              *)
(*                                                                           *)
(* NB! att_gate_seq in att-gate-cakeml has a better version of this function *)
(*---------------------------------------------------------------------------*)

val Att_Gate_Single_Ordered : inports -> outports =
fn (trusted_id_bytes,OpRegion,LST,AutoRqt) =>
  case readTIDs trusted_id_bytes
   of NONE => (NONE,NONE,NONE)
    | SOME tids =>
  case OpRegion
   of SOME bytes => (check tids bytes,NONE,NONE)
    | NONE =>
  case LST
   of SOME bytes => (NONE,check tids bytes,NONE)
    | NONE =>
  case AutoRqt
   of SOME bytes => (NONE,NONE,check tids bytes)
    | NONE       => (NONE,NONE,NONE)
;

(*---------------------------------------------------------------------------*)
(* Look at all events in an unordered manner. Pass along all that meet the   *)
(* criterion.                                                                *)
(*---------------------------------------------------------------------------*)

fun Att_Gate_Multi (trusted_id_bytes,OpRegion,LST,AutoRqt) =
 case readTIDs trusted_id_bytes
   of NONE => (NONE,NONE,NONE)
    | SOME tids =>
      let val checkFn = Option.mapPartial (check tids)
      in
        (checkFn AutoRqt,checkFn OpRegion,checkFn LST)
      end;
