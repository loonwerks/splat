(*===========================================================================*)
(* thread CASE_Filter_LST_thr
   features
     filter_in: in event data port CMASI::LineSearchTask.i;
     filter_out: out event data port CMASI::LineSearchTask.i;

   properties
     CASE_Properties::Component_Type => FILTER;
     CASE_Properties::Component_Spec => ("Req_Filter_LST");
     Dispatch_Protocol => Periodic;
     Period => 500ms;
     Compute_Execution_Time => 2ms .. 2ms;

   annex agree {**
     guarantee Req_Filter_LST "Well-formed Line Search Task message"
        : CASEAgree::WELL_FORMED_LINE_SEARCH_TASK(filter_out);
     **};
   end CASE_Filter_LST_thr;

   fun WELL_FORMED_LINE_SEARCH_TASK(msg : CMASI::LineSearchTask.i) : bool =
       msg.TaskID >= TASK_ID_MIN and msg.TaskID <= TASK_ID_MAX and
       (forall point in msg.PointList, WELL_FORMED_POINT(point));

   fun WELL_FORMED_POINT(point : CMASI::Location3D.i) : bool =
      point.Latitude >= LATITUDE_MIN and point.Latitude <= LATITUDE_MAX and
      point.Longitude >= LONGITUDE_MIN and point.Longitude <= LONGITUDE_MAX and
      point.Altitude >= ALTITUDE_MIN and point.Altitude <= ALTITUDE_MAX;
 *)
(*===========================================================================*)

use "uxas.sml";
use "consts.sml";

val ERR = mk_HOL_ERR "line-search-task-filter";

structure API =
struct

val linesearch_taskAASizeBytes = 3709;   (* actual size of example message *)
val linesearch_taskAASizeBytes = 10 * 1024;

(*---------------------------------------------------------------------------*)
(* IO via faked-up CakeML FFI interface.                                     *)
(*---------------------------------------------------------------------------*)

exception FFI_CALL of string

val linesearch_task_event_string =
 let val istrm = TextIO.openIn "LSTE"
     val str = TextIO.inputAll istrm
     val _ = TextIO.closeIn istrm
 in
   str
 end;

fun copyVec s buf =
    Word8Array.copyVec {src = Byte.stringToBytes s, dst = buf, di = 0};

fun std_output s = TextIO.output(TextIO.stdOut,s);

fun callFFI fname istr obuf =
 if fname = "get_filter_in" then
    let val inputLen = String.size linesearch_task_event_string
        val bufLen = Word8Array.length obuf
    in if inputLen <= bufLen  then
         copyVec linesearch_task_event_string obuf
       else raise FFI_CALL "get_filter_in: input too large for buffer"
    end
 else
 if fname = "put_filter_out" then
     std_output "\nmoving filter input to output\n"
 else
 raise FFI_CALL "unknown IO request"

end  (* API *)

structure LST_Filter =
struct

val w8zero = Word8.fromInt 0;
val emptybuf = Word8Array.array(0,w8zero);

(*---------------------------------------------------------------------------*)
(* Declare input buffers as global variables.                                *)
(*---------------------------------------------------------------------------*)

val filter_in_buffer = Word8Array.array(API.linesearch_taskAASizeBytes,w8zero)

fun clear buffer =
 let val len = Word8Array.length buffer
     fun zero i = Word8Array.update(buffer,i, w8zero)
     fun loop j = if j < len then (zero j; loop (j+1)) else ()
 in
    loop 0
 end;

fun outFFI fname buf =
 let val vect = Word8Array.vector buf
     val event_string = Byte.bytesToString vect
     val string = String.extract(event_string,1,NONE)
 in
    API.callFFI fname string emptybuf
 end

fun filter_step () =
 let val () = clear filter_in_buffer
     val () = API.callFFI "get_filter_in" "" filter_in_buffer
     val string = Byte.bytesToString (Word8Array.vector filter_in_buffer)
 in
    if wellformed uxasEnv (Option fullLineSearchTaskMesg) string then
       outFFI "put_filter_out" filter_in_buffer
    else ()
 end

end (* LST_Filter *)
