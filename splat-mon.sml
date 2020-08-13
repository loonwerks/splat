(*---------------------------------------------------------------------------*)
(* Maps from Json representation of AADL to AST and then to HOL. Solely      *)
(* aimed at extracting monitor properties, plus support definitions.          *)
(*---------------------------------------------------------------------------*)

open Lib Feedback HolKernel boolLib MiscLib bossLib;

local open AADL ptltlSyntax regexpLib regexpSyntax realLib realSyntax in end

val ERR = Feedback.mk_HOL_ERR "splat-mon";

fun printHelp() =
  stdErr_print
    ("Usage: splat-mon <name>.json\n")

fun fail() = (printHelp(); MiscLib.fail())

fun failwithERR e =
  (stdErr_print (Feedback.exn_to_string e^"\n\n"); MiscLib.fail());


fun check_suffix id s =
 let val filename = FileSys.fullPath s
            handle e => (stdErr_print (Feedback.exn_to_string e); fail())
 in case String.tokens (equal #".") filename
     of [file,x] => if x=id then filename else fail()
      | otherwise => fail()
 end

fun parse_args args =
 if null args then fail()
 else
 let val (flags,file) = front_last args
     val jfile = check_suffix "json" file
 in
    jfile
 end

(* From Thomas' synthesize.sml file

  val top_form_term = (PtltlTree.to_hol_form form)

  val relational_data_term = (
    ``mk_relational_data (^top_form_term) T``
  ) |> EVAL |> concl |> rhs

  val table_data_term = (
    ``mk_table_data (^relational_data_term)``
  ) (* |> EVAL |> concl |> rhs ---- TODO: figure out problem with early stage evaluation *)

*)

fun synthesize_monitor monitor =
 let fun small_step (_,def) =
       let val tm = rhs(snd(strip_forall(concl def)))
           val exec_tm = ptltlSyntax.mk_smallstep1 tm
       in
          EVAL exec_tm
       end
    fun monitor_data ((s1,s2),def) =
      let val tm = rhs(snd(strip_forall(concl def)))
          val exec_tm = ptltlSyntax.mk_table_data1
                            (ptltlSyntax.mk_relational_data(tm,T))
      in save_thm(s1^"_"^s2,EVAL exec_tm)
      end
 in
   monitor_data monitor
 end

val args = ["examples/UAS.json"];

(*
HAMR::Bit_Codec_Max_Size: It is attached to the types declared for the channel.

val args = ["examples_monitor/req_resp_monitor.json"];
val args = ["examples_monitor/geo_monitor.json"];
val args = ["examples_monitor/Coord-Mon.json"];
val args = ["examples_monitor/Resp-Mon.json"];
val args = ["examples_monitor/Coord-Mon.json"];
val args = ["examples_monitor/SW-Mon-1.json"];
val args = ["examples_monitor/SW-Mon.json"];
val args = ["examples_monitor/RunTimeMonitor_Simple_Example_V1.json"];
val args = ["examples_monitor/Datacentric_monitor.json"];
*)

fun extract_filter (pkgName,(tydecs,fndecs,filtdecs,mondecs)) = filtdecs;

fun extract_consts ("CM_Property_Set",(tydecs,fndecs,filtdecs,mondecs)) =
     let open AADL
         fun dest_const_dec (ConstDec ((_,cname),ty,i)) = (cname,i)
     in mapfilter dest_const_dec fndecs
     end
  | extract_consts otherwise = raise ERR "extract_consts" "looking for package CM_Property_Set"


fun main () =
 let val _ = stdErr_print "splat-mon: \n"
     val args = CommandLine.arguments()
     val jsonfile = parse_args args
     val ([jpkg],ss) = apply_with_chatter Json.fromFile jsonfile
	   ("Parsing "^jsonfile^" ... ") "succeeded.\n"
     val pkgs = apply_with_chatter AADL.scrape_pkgs jpkg
                  "Converting Json to AST ... " "succeeded.\n"
     val filter_decs = List.concat (map extract_filter pkgs)
     val const_alist = tryfind extract_consts pkgs
     val filter_CakeML_files = map (AADL.inst_filter_template "." const_alist) filter_decs
     val thyName = fst (last pkgs)
     val _ = new_theory thyName
     val logic_defs = apply_with_chatter (AADL.pkgs2hol thyName) pkgs
	   "Converting AST to logic ...\n" "---> succeeded.\n"
     val filters = #4 logic_defs
     val filter_thms = []
     val monitors = #5 logic_defs
     val monitor_thms = apply_with_chatter (List.map synthesize_monitor) monitors
	   "Synthesizing monitors ...\n" "---> succeeded.\n"
     val _ = export_theory()
  in
    MiscLib.succeed()
 end
 handle e =>
    let open MiscLib
    in stdErr_print "\n\nSPLAT-MON FAILED!!\n\n";
       failwithERR e
    end
