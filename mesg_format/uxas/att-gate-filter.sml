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

(*---------------------------------------------------------------------------*)
(* Parsing                                                                   *)
(*---------------------------------------------------------------------------*)

fun dest_string s =
    SOME(String.sub(s,0),String.extract(s,1,NONE)) handle _ => NONE;

fun getID ptree =
 case ptree
  of RECD [("address",           LEAF(Scanned, _)),
           ("contentType",       LEAF(Scanned, _)),
           ("descriptor",        LEAF(Scanned, _)),
           ("source_group",      LEAF(Scanned, _)),
           ("source_entity_ID",  LEAF(Scanned, ssID)),
           ("source_service_ID", LEAF(Scanned, _)),
           ("all_the_rest",      LEAF(Scanned, _))]
     => (case Int.scan StringCvt.DEC dest_string ssID
          of NONE => raise ERR "getID" "expected decimal integer string"
           | SOME (i,_) => i)
   | otherwise => raise ERR "getID" "";

fun parse_AAmesg_ID string =
 let val (ptree,_,_) = parse uxasEnv AAmesg string
 in getID ptree
 end

val readID = parse_AAmesg_ID o Byte.bytesToString;

fun parse_trusted_ids string =
 let fun parse_leaf (LEAF (tg, s)) = uxas_valFn tg s
       | parse_leaf otherwise = raise ERR "parse_leaf" ""
 in case parse uxasEnv trusted_ids string
     of (ARRAY ptrees,_,_) => Array.fromList (map parse_leaf ptrees)
      | otherwise => raise ERR "parse_trusted_ids" ""
 end;

fun check (trusted_id_bytes,bytes) =
 let val trusted_array = parse_trusted_ids trusted_id_bytes
     val ID = readID bytes
 in if Array.exists (equal ID) trusted_array then
      SOME bytes
    else NONE
 end;

fun Att_Gate (trusted_ids,AutoRqt,OpRegion,LST) =
  case (AutoRqt,OpRegion,LST)
   of (SOME bytes, NONE, NONE) => (check(trusted_ids,bytes),NONE,NONE)
    | (NONE, SOME bytes, NONE) => (NONE,check(trusted_ids,bytes),NONE)
    | (NONE, NONE, SOME bytes) => (NONE,NONE,check(trusted_ids,bytes))
    | (NONE, NONE, NONE)       => (NONE,NONE,NONE)
    | otherwise                => (NONE,NONE,NONE);
