structure Code_Gen :> Code_Gen =
struct

open Lib MiscLib Feedback;

type dfa =
  {name       : string,
   src_regexp : string,
   finals     : bool list,
   table      : int list list}

fun get_filter_name s = last (String.tokens (equal #".") s)

fun export_dfa codegen (name,suffix) regexp finals table =
 let open TextIO
     val rstring = PP.pp_to_string 72 Regexp_Type.pp_regexp regexp
     val dfa = {name=name,src_regexp=rstring, finals=finals,table=table}
     val filename = get_filter_name name
     val ostrm = openOut (filename^suffix)
 in
    codegen dfa ostrm
  ; closeOut ostrm
 end

fun spread s [] = []
  | spread s [x] = [x]
  | spread s (h::t) = h::s::spread s t;

fun spreadlnWith {sep:string, ln:string, width:int} f =
 let fun spr n [] = []
       | spr n [x] = [f x]
       | spr n (h::t) =
          let val hstring = f h
           in if n <= 0
               then hstring::sep::ln::spr width t
               else hstring::sep::spr (n-1) t
           end
 in
  spr width
 end;

(*---------------------------------------------------------------------------*)
(* Slang code.                                                               *)
(*---------------------------------------------------------------------------*)

local
fun boolString true = "T"
  | boolString false = "F"
fun indexString i = String.concat ["t\"",Int.toString i, "\""]

fun finalsString list =
 let val spreadList =
       spreadlnWith {sep=",", ln="\n       ", width=20} boolString list
 in
   String.concat (spreadList @ [")"])
 end;

fun row2string (rowName,intList) =
 let val prefix =
        String.concat["  @strictpure def ", rowName,
                      ": IS[U8, State] = IS[U8, State](\n     "]
     val spreadList =
       spreadlnWith {sep=",", ln="\n     ", width=12} indexString intList
 in
   String.concat (prefix :: spreadList @ [")"])
 end

in
fun Slang {name=aadl_path, src_regexp,finals,table} ostrm =
 let val _ = MiscLib.stdErr_print "Generating Slang code.\n"
     val filter_name = get_filter_name aadl_path
     val nstates = List.length finals
     val rowNames = map (fn i => "row"^Int.toString i) (upto 0 (nstates-1))
     val row_defs = map row2string (zip rowNames table)
     val row_defList = String.concat (spread "\n\n" row_defs)
     val rowList = String.concat(spreadlnWith {sep=",", ln="\n      ", width=10} I rowNames)
 val string = String.concat
 ["// #Sireum\n\n",
  "/*---------------------------------------------------------------------------\n",
  " -- DFA ", filter_name, " is the compiled form of regexp\n",
  " --\n",
  " --   ", src_regexp, "\n",
  " --\n",
  " -- Number of states in DFA: ",Int.toString nstates, "\n",
  " --\n",
  " *---------------------------------------------------------------------------*/\n",
  "\n\n",
  "package ", aadl_path, "\n\n",
  "import org.sireum._\n\n",
  "object State {\n\n",
  "  @range(min = 0, max = ", Int.toString (nstates - 1),
           ") class T // max is the number of DFA states - 1\n}\n\n",
  "import State.T._\n\n",
  "object Filter {\n",
  "  type State = State.T\n\n",
  "  val isAccepting : IS[State, B] = IS[State, B](\n       ",
  finalsString finals, "\n",
  "\n",
  row_defList,
  "\n\n",
  "  val DELTA: IS[State, IS[U8, State]] =\n",
  "    IS[State, IS[U8, State]](\n      ", rowList,")\n\n",
  "  @pure def filter(s: ISZ[U8]): B = {\n",
  "    var state = t\"0\"\n",
  "    for (i <- 0 until s.size) {\n",
  "      state = DELTA(state)(s(i));\n",
  "    }\n\n",
  "    return isAccepting(state);\n",
  "    }\n",
  "}\n"
 ]
 in
  TextIO.output(ostrm,string)
 end
end;

end
