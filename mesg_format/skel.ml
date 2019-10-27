(*===========================================================================*)
(* Message skeleton format.                                                  *)
(*                                                                           *)
(* A message skeleton is simply a description of all fields in a message,    *)
(* associating with each field in the message its width in bits.             *)
(*                                                                           *)
(* For static messages with a fixed format, the skeleton description is      *)
(* straightforward. But there are messages the skeleton of which is          *)
(* determined dynamically, by the message contents already seen. For         *)
(* example, a message might have a "len" field which specifies the size of   *)
(* an array occurring elsewhere in the mesg. Different lengths therefore     *)
(* lead to different skeletons. Similarly, a field can be used to select     *)
(* from a collection of skeletons, enabling a single message format to       *)
(* compactly implement a set of message formats.                             *)
(*===========================================================================*)

datatype skel = Span of string * int;

(*---------------------------------------------------------------------------*)
(* This says that mesg has 3 segments, of length 4, 12, and 8, respectively. *)
(*---------------------------------------------------------------------------*)

val mesg = [Span ("A", 4), Span ("B", 12), Span("C", 8)]

(*---------------------------------------------------------------------------*)
(* The key to handling dynamic skeletons is to incorporate a notion of beta- *)
(* redex. For example, the following says that the width of field B is       *)
(* computed from the value of field A.                                       *)
(*---------------------------------------------------------------------------*)

val mesg = [Span ("A", 4), 
            Span ("B", ((lambda x. 8 * x) (Val "A")), 
            Span ("C", 8)];

(*---------------------------------------------------------------------------*)
(* So we need to extract the *value* of field A before the width of field B  *)
(* is computed. Recall that beta-redexes can be rendered as "lets". So we    *)
(* can imagine the following equivalent description, where "Val" interprets  *)
(* bitstrings as unsigned numbers. (The description is in HOL syntax for     *)
(* my convenience.) In this notation, A needs to bear at least 2 meanings:   *)
(* (1) the width of the field named A and (2) an arbitrary bitstring of that *)
(* length.                                                                   *)
(*---------------------------------------------------------------------------*)

val mesg = 
 ``let A = 4 ;
       B = 8 * Val(A) ;
       C = 8
   in [A ; B ; C]``;
       
(*---------------------------------------------------------------------------*)
(* I think I can interpret (many, but maybe not all) bitCodec descriptions   *)
(* to this. It raises the question about what expressions can appear in the  *)
(* rhs of let-bindings. For now, I am just interested in doing a good job on *)
(* widths. To be actually useful, we also need to have per-field well-formed-*)
(* ness specifications. Thus, if a field is a specific (numeric or string)   *)
(* literal, that becomes a wellformedness predicate. A field-specific        *)
(* predicate will be given the field width as parameter.                     *)
(*---------------------------------------------------------------------------*)

val wf_mesg =
 ``well_formed list = 
    ?A B C. (list = [A;B;C] /\
            wfA (A, 4) /\
            wfB (B, 8 * Val(A)) /\
            wfC (C, 8)``

datatype iexp 
    = Var of string
    | Const of int
    | Add of iexp * iexp
    | Mult of iexp * iexp
    | Diff of iexp * iexp

datatype segments
    = Segs of string list
    | Cseg of (string * iexp) * segments
    | Choice of iexp * (int -> segments)


(*---------------------------------------------------------------------------*)
(* CASE example                                                              *)
(*                                                                           *)
(* The example builds on the a sequence of declarations, resulting in a      *)
(* filter on a connection of type RF_Msg. Following are the record           *)
(* declarations.                                                             *)
(*---------------------------------------------------------------------------*)

app load ["intLib"; "fcpLib"];

Hol_datatype 
   `Coordinate = <| lat : int; lon : int; alt : int |>`;

Hol_datatype 
   `FlightPattern = ZigZag | StraightLine | Perimeter`;

Hol_datatype 
   `CASE_MsgHeader = <| src : int; dst : int; trusted : bool; HMAC : bool |>`;

Hol_datatype 
   `Command = <| map : Coordinate [4]; pattern : FlightPattern |>`;

Hol_datatype 
   `RF_Msg = <| header  : CASE_MsgHeader; payload : Command |>`;

(*---------------------------------------------------------------------------*)
(* This is completely static, but shows how hierarchy can be supported.      *)
(*---------------------------------------------------------------------------*)

``let header = 
         (let src = 32; 
              dst = 32; 
              trusted = 8;
	      HMAC = 8;
          in [src ; dst ; trusted ; HMAC])
         ;
      payload = 
         (let map = 4 * sizeof(Coordinate); 
              pattern = 8; 
          in [map ; pattern])
         ;
 in header ++ payload``;


(*---------------------------------------------------------------------------*)
(* Wellformedness.                                                           *)
(*---------------------------------------------------------------------------*)

Definition CASE_UAV_ID_def : 
 CASE_UAV_ID = 42i
End
 
Definition VALID_MESSAGE_def : 
  VALID_MESSAGE (msg: RF_Msg) <=>
      msg.header.src > 0i /\ 
      (msg.header.dst = CASE_UAV_ID) /\
      msg.header.HMAC
End

Definition good_coordinate_def :
  good_coordinate (coord:Coordinate) <=> 
    (coord.lat >= (-90i) /\ coord.lat <= 90i) /\
    (coord.lon >= (-180i) /\ coord.lon <= 180i) /\
    (coord.alt >= 0i /\ coord.alt <= 15000i)
End
    
Definition good_map_def :
  good_map map <=> FCP_EVERY good_coordinate map
End
  
Definition good_pattern_def :
 good_pattern pattern 
  <=>
  pattern = ZigZag \/ pattern = StraightLine \/ pattern = Perimeter
End


(*---------------------------------------------------------------------------*)
(* The filter specification is a predicate on the output connection          *)
(* (filter_out) of the filter.                                               *)
(*---------------------------------------------------------------------------*)

Definition filter_output_spec_def :
 filter_output_spec (filter_out:RF_Msg) <=>
       VALID_MESSAGE filter_out /\
       good_map filter_out.payload.map /\
       good_pattern filter_out.payload.pattern
End
       
The filter.
-----------

When looking at the message as a sequence of bytes, the fields will be
laid out in order as the header fields followed by the payload fields, namely

  [src,dest,trusted,HMAC,map,pattern]

where

  - src is a signed int > 0
  - dest is a signed int = 42
  - trusted is boolean but not specified, so could be true or false
  - HMAC is boolean and must be true
  - map is a 4 element array of good coordinates
  - pattern is any of the three possible patterns

and a good coordinate is a triple

  - lat  (signed int between -90 and 90)
  - lon (signed int between -180 and 180)
  - alt  (signed int between 0 and 15000)

The default signed ints are 32 bits wide (4 bytes, little-endian) and
enumerations fit into a byte.  The encoding fits intervals into the
smallest possible number of bytes. Thus the layout skeleton is 28
bytes in length:

  - src     : 4
  - dest    : 1
  - trusted : 1
  - HMAC    : 1
  - map     : 4 elements * 5 bytes per element 
               (lat fits in 1 byte, lon, and alt each fit in 2)
  - pattern : 1

Yet more detail:

  - the boolean encoding: false = 0, true = 1


val gps_recd = 
 ``let lat = sizeof int ;
       lon = sizeof int ;
       alt = sizeof int
   in (lat,lon,alt)``;

val case_mesg =
``let A = 1 ;
      B = 1 ;
      C = 4 * sizeof gps_recd ;
      D = 2
  in 
  (A,B,C,D)``;

(* val wf_case_mesg = 
``wf_case_mesg (A,B,C,D) =
*)

datatype 
 iexp 
   = Var of string
   | Const of int
   | Add of iexp * iexp
   | Mult of iexp * iexp
   | Diff of iexp * iexp;
  
fun V E iexp = p
 case iexp
  of Var s => E s
   | Const i => i
   | Add  (e1,e2) => V E e1 + V E e2
   | Mult (e1,e2) => V E e1 * V E e2
   | Diff (e1,e2) => V E e1 - V E e2

datatype segments
  = Eseg of string list
  | Cseg of (string * iexp) * segments
  | Choice of iexp * (int -> segments);

``let A = 3 ;
      B = 4 ;
      C = Val A * Val B;
  in if Val A = 0 
     then let D = 4; E = 5; 
          in [A; B; D; E]
     else [A;B;C]``
