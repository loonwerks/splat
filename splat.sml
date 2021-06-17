(*---------------------------------------------------------------------------*)
(* Maps from Json representation of AADL to AST and then to CakeML code.     *)
(*---------------------------------------------------------------------------*)

open Lib Feedback HolKernel boolLib MiscLib bossLib;

(*
load "intrealSyntax";
*)

local open
   AADL regexpLib regexpSyntax realLib realSyntax intrealSyntax PP_CakeML Gen_Contig
in end

val ERR = Feedback.mk_HOL_ERR "splat";

fun printHelp() =
  MiscLib.stdErr_print
    ("Usage: splat [-target (hamr | standalone)]\n\
     \             [-outdir <dirname>]\n\
     \             [-intwidth <int>]\n\
     \             [-endian (LSB | MSB)]\n\
     \             <name>.json\n")

fun fail() = (printHelp(); MiscLib.fail())

fun failwithERR e =
  (MiscLib.stdErr_print (Feedback.exn_to_string e^"\n\n"); MiscLib.fail());

val FLAGS =
  {target   = ref NONE : string option ref,
   codegen  = ref NONE : string option ref,
   outDir   = ref NONE : string option ref,
   intwidth = ref NONE : int option ref,
   endian   = ref NONE : Regexp_Numerics.endian option ref,
   encoding = ref NONE : Regexp_Numerics.encoding option ref,
   preserve_model_nums = ref NONE : bool option ref};

(*---------------------------------------------------------------------------*)
(* If directory does not exist, create it. Also check that dir has rwe       *)
(* permissions.                                                              *)
(*---------------------------------------------------------------------------*)

fun set_target s =
  case !(#target FLAGS)
    of NONE => (#target FLAGS := SOME "Standalone")
     | SOME "standalone" => ()
     | SOME "hamr" => ()
     | SOME other => fail()

fun set_codegen lang =
 let val _ =
    if mem lang ["CakeML"] then () else fail()
 in case !(#codegen FLAGS)
     of NONE => (#codegen FLAGS := SOME lang)
      | SOME _ => ()
 end

fun set_outDir d =
 let open FileSys
     fun fpath s =
      let val path = fullPath s handle _ => (mkDir s ; fullPath s)
                                handle _ => fail()
      in if isDir path andalso access(path,[A_EXEC,A_READ,A_WRITE])
          then path else fail()
      end
 in
   case !(#outDir FLAGS)
    of NONE => (#outDir FLAGS := SOME (fpath d))
     | SOME _ => ()
 end

fun set_intwidth s =
 case !(#intwidth FLAGS)
  of NONE =>
      (case Int.fromString s
        of SOME i =>
           if i < 8 orelse not (i mod 8 = 0)
              then fail()
              else (#intwidth FLAGS := SOME i)
         |  NONE => fail())
   | SOME _ => ()
;

fun set_preserve_model_nums b =
 case !(#preserve_model_nums FLAGS)
  of NONE => (#preserve_model_nums FLAGS := SOME b)
   | SOME _ => ()

fun s2endian s =
 let open Regexp_Numerics
 in case s
     of "LSB" => LSB
      | "MSB" => MSB
      | other => fail()
 end

fun set_endian e =
 case !(#endian FLAGS)
  of NONE => (#endian FLAGS := SOME (s2endian e))
   | SOME _ => ()

fun s2encoding s =
 let open Regexp_Numerics
 in case s
     of "Unsigned"  => Unsigned
      | "Twos_comp" => Twos_comp
      | "Sign_mag"  => Sign_mag
      | "ZigZag"    => Zigzag
      | "Zigzag"    => Zigzag
      | other       => fail()
 end

fun set_encoding enc =
 case !(#encoding FLAGS)
  of NONE => (#encoding FLAGS := SOME (s2encoding enc))
   | SOME _ => ()

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
     fun set_flags list =
       case list
        of [] =>
           let in
              set_target "Standalone";
              set_codegen "CakeML";
              set_outDir "./splat_outputs";
              set_intwidth "32";
              set_endian "MSB";
              set_encoding "Twos_comp";
              set_preserve_model_nums false
            end
         | "-target"   :: d :: t => (set_target d;   set_flags t)
         | "-codegen"  :: d :: t => (set_codegen d;  set_flags t)
         | "-outdir"   :: d :: t => (set_outDir d;   set_flags t)
         | "-intwidth" :: d :: t => (set_intwidth d; set_flags t)
         | "-endian"   :: d :: t => (set_endian d;   set_flags t)
         | "-encoding" :: d :: t => (set_encoding d; set_flags t)
         | "-preserve_model_nums"::t => (set_preserve_model_nums true; set_flags t)
         | otherwise => fail()
 in
     set_flags flags
   ; jfile
 end

fun extract_consts ("CM_Property_Set",(tydecs,fndecs,filtdecs,mondecs)) =
     let open AADL
         fun dest_const_dec (ConstDec ((_,cname),ty,i)) = (cname,i)
     in mapfilter dest_const_dec fndecs
     end
  | extract_consts otherwise = raise ERR "extract_consts" "unable to find package CM_Property_Set"

fun extract_filters (pkgName,(tydecs,fndecs,filtdecs,mondecs)) = filtdecs;
fun extract_monitors (pkgName,(tydecs,fndecs,filtdecs,mondecs)) = mondecs;

(*
fun decls_qids decls =
 let val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = decls
     val supplied_qids = Lib.union (supplied_tydec_qids tydecs) (supplied_tmdec_qids tmdecs)
     val mentioned_qids = MiscLib.bigU [mentioned_tydec_qids, mentiond_tmdec_qids,
                                        mentioned_filter_qids, mentioned_monitor_qids]
 in
*)

(*---------------------------------------------------------------------------*)
(* Transform to a set of "components", each of the form                      *)
(*                                                                           *)
(*  ([pkg_1,...,pkg_n],dec)                                                  *)
(*                                                                           *)
(*  where the pkg_i are packages used in dec, and dec is a filter, monitor,  *)
(*  or gate. The pkg_i can be trimmed to be minimal.                         *)
(*---------------------------------------------------------------------------*)

open AST AADL;

type port = string * ty * string * string;  (* (id,ty,dir,kind) *)

type ivardec = string * ty * exp

type guar = string * string * exp;

type decs = tydec list * tmdec list;

type support = (string * decs) list;

datatype gadget =
 Gadget of qid
           * support
           * tydec list
           * tmdec list
           * (port list * bool * ivardec list * guar list);


fun elim_monitor support (MonitorDec mondec) =
 let val (qid,ports,latched,tmdecs,ivardecs,guars) = mondec
     val tydecs = []  (* Will change *)
 in Gadget (qid, support, tydecs, tmdecs, (ports,latched,ivardecs,guars))
 end;

fun elim_filter support (FilterDec filtdec) =
 let val (qid,ports,tmdecs, ivardecs, guars) = filtdec
     val latched = false
     val tydecs = []
 in Gadget (qid, support, tydecs, tmdecs, (ports,latched,ivardecs,guars))
 end;

(*---------------------------------------------------------------------------*)
(* A "decls" thing represents an AADL package (roughly).                     *)
(*---------------------------------------------------------------------------*)

fun configure decls (support,gadgets) =
 let val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = decls
     val support' = (pkgName,(tydecs,tmdecs)) :: support
     val filter_gadgets = List.map (elim_filter support') filtdecs
     val monitor_gadgets = List.map (elim_monitor support') mondecs
 in
     (support',
      filter_gadgets @ monitor_gadgets @ gadgets)
end

fun mk_gadgets pkgs = snd (rev_itlist configure pkgs ([],[]));

val empty_varE = PP_CakeML.empty_varE;
val assocFn = PP_CakeML.assocFn;
val transRval = PP_CakeML.transRval;
val transRval_decl = PP_CakeML.transRval_decl;
val mk_tyE = PP_CakeML.mk_tyE;
val mk_constE = PP_CakeML.mk_constE;
val mk_recd_projns = PP_CakeML.mk_recd_projns;

fun catE env1 env2 x =
  case env1 x
   of NONE => env2 x
    | SOME y => SOME y;

fun transRval_dec E tmdec =
 case tmdec
  of ConstDec (qid,ty,exp) => ConstDec (qid,ty,transRval (E,empty_varE) exp)
   | FnDec (qid,params,ty,exp) =>
     FnDec (qid,params,ty, transRval (E,assocFn params) exp)
;

fun trans_ivardec E (s,ty,e) = (s,ty,transRval E e)
fun trans_guar E (s1,s2,e) = (s1,s2,transRval E e)

fun trans_support E support = map (I##(I##map (transRval_decl E))) support;

fun portE ports =
 let fun dest_port (id,ty,_,_) = (id,ty)
 in assocFn (map dest_port ports)
 end

fun ivarE ivars =
 let fun dest_ivar (id,ty,_) = (id,ty)
 in assocFn (map dest_ivar ivars)
 end

(*---------------------------------------------------------------------------*)
(* Add synthesized projn fn defs after eliminating record projections. This  *)
(* is currently needed because the projection eliminator doesn't handle the  *)
(* case syntax properly.                                                     *)
(*---------------------------------------------------------------------------*)

fun transRval_gadget E gadget =
 let val Gadget (qid,support, tydecs, tmdecs,
                 (ports,latched,ivardecs,guars)) = gadget
     val support' = trans_support E support
     val projFn_decs = mk_recd_projns tydecs
     val tmdecs' = projFn_decs @ map (transRval_decl E) tmdecs
     val varE = catE (portE ports) (ivarE ivardecs)
     val ivardecs' = map (trans_ivardec (E,varE)) ivardecs
     val guars' = map (trans_guar (E,varE)) guars
 in
    Gadget (qid, support', tydecs, tmdecs', (ports,latched,ivardecs',guars'))
 end

fun elim_projections pkgs gdts =
 let val tyE = mk_tyE pkgs
     val constE = mk_constE pkgs
 in
   map (transRval_gadget (tyE,constE)) gdts
 end

fun atomic_width atom =
let open ByteContig
 in case atom
     of Bool => 1
      | Signed i => i
      | Unsigned i => i
      | Blob => raise ERR "atomic_width" "Blob"
end;

val trivEnv = ([],[],atomic_width);

fun gadget_qid (Gadget(qid,supp,tydecs,tmdecs,(ports,latched,ivars,guars))) = qid;
fun ports_of (Gadget(qid,supp,tydecs,tmdecs,(ports,latched,ivars,guars))) = ports;

fun foo env (id,ty,dir,kind) =
 let val

fun add_APIs gdts =
let fun api_of gdt =
     let val qid = gadget_qid gdt
         val ports = ports_of gdt

         val contigs = map (Gen_Contig.contig_of env)

in
end;
fun CakeML_names pkgs = pkgs;

fun process_model jsonFile =
 let val ([jpkg],ss) = Json.fromFile jsonFile
     val pkgs = scrape_pkgs jpkg
     val gdts1 = mk_gadgets pkgs
     val gdts2 = elim_projections (map Pkg pkgs) gdts1
     val gdts3 = add_API gdts2
     val gdts4 = CakeML_names gdts3
 in
    gdts4
 end;

(*
val jsonFile = "examples/SW.json";
val args = [jsonFile];
val thyName = "SW";
val dir = ".";

val ([jpkg],ss) = Json.fromFile (parse_args args)

val gadgets = process_model "examples/SW.json";

val [gadget1, gadget2, gadget3] = gdts1;


open AADL;

val [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7] = pkgs;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg7;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg5;
val [mondec1,mondec2,mondec3] = mondecs;
val [filtdec1,filtdec2,filtdec3,filtdec4] = filtdecs;
*)

(*
fun process_filter intformat flags ((pkgName,fname),thm) =
 let open FileSys
     val _ = stdErr_print ("\nProcessing filter "^Lib.quote fname^".\n")
     val wDir = getDir()
     val filterDir = String.concat[wDir,"/",pkgName,"_",fname]
     val _ = ((mkDir filterDir handle _ => ()); chDir filterDir)
     val (checkprops,codegen,testgen,alevel) = flags
     val filter_artifacts =
         apply_with_chatter
           (splatLib.gen_filter_artifacts intformat) ((pkgName,fname),thm)
           "Defining filter artifacts ... " "succeeded.\n"

     val _ = if checkprops = true then
               apply_with_chatter
                  prove_filter_props filter_artifacts
                  "Proving translation validation property ... " "succeeded.\n"
             else ()

    val {regexp,...} = filter_artifacts

    val regexp_compiler =
         case alevel
          of Basic => regexpLib.SML
	   | HOL   => regexpLib.HOL
	   | other => failwithERR
             (ERR "splat" "Cake regexp compilation not handled at present")

    val DFA as (certificate, start, finals, table) =
        deconstruct (regexpLib.gen_dfa regexp_compiler regexp)

    val (match_state_thm, match_def) = mk_matcher fname certificate

    val (langGen,suffix) =
     case codegen
      of "C" => (DFA_Codegen.C,".c")
       | "SML" => (DFA_Codegen.SML,".sml")
       | "Ada" => (DFA_Codegen.Ada,".ada")
       | "Java" => (DFA_Codegen.Java,".java")
       | "Slang" => (Code_Gen.Slang,".scala")
       | other    => raise ERR "process_filter" "unsupported target language"

    (* Smuggling architecture info through the name. To be handled (so far)
       only in Slang code generation, which wants the AADL path to the filter
    *)
    val slang_path_name =
     if codegen = "Slang" then
       String.concat[pkgName,".",fname]
     else fname
 in
     Code_Gen.export_dfa langGen (slang_path_name,suffix) regexp finals table
   ;
     stdErr_print ("End processing filter "^Lib.quote fname^".\n\n")
   ;
     chDir wDir
   ;
     filter_artifacts
 end
*)

(*

val args = ["examples/uxaslite.json"];
val thyName = "uxaslite";
val dir = ".";

val args = ["examples/gate.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/mon3a.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/mon4a.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/mon5a.json"];
val thyName = "VPM";
val dir = ".";

val args = ["examples/UAS.json"];
val thyName = "UAS";
val dir = ".";

val jsonfile = parse_args args;
val ([jpkg],ss) = Json.fromFile jsonfile;
open AADL;

val pkgs = scrape_pkgs jpkg;

val [pkg1,pkg2,pkg3,pkg4,pkg5,pkg6,pkg7] = pkgs;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg7;

val (pkgName,(tydecs,tmdecs,filtdecs,mondecs)) = pkg5;
val [mondec1,mondec2,mondec3] = mondecs;
val [filtdec1,filtdec2,filtdec3,filtdec4] = filtdecs;

val const_alist = tryfind extract_consts pkgs

val MonitorDec(qid,features,latched,decs,eq_stmts,outCode) = mondec1;
val MonitorDec(qid,features,latched,decs,eq_stmts,outCode) = mondec2;
val MonitorDec(qid,features,latched,decs,eq_stmts,outCode) = mondec3;

val plist = map Pkg pkgs;
val plist' = transRval_pkglist plist ;
*)

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

fun main () =
 let val _ = stdErr_print "splat-mon: \n"
     val args = CommandLine.arguments()
     val jsonfile = parse_args args
     val ([jpkg],ss) = apply_with_chatter Json.fromFile jsonfile
	   ("Parsing "^jsonfile^" ... ") "succeeded.\n"
     val pkgs = apply_with_chatter AADL.scrape_pkgs jpkg
                  "Converting Json to AST ... " "succeeded.\n"
     val thyName = "SPLAT"  (* Need something better: get it from modelUnits from jpkg *)

     val filter_decs = List.concat (map extract_filters pkgs)
     val monitor_decs = List.concat (map extract_monitors pkgs)
     val _ = stdErr_print ("Found "^Int.toString (List.length filter_decs)^" filter declarations.\n")
     val _ = stdErr_print ("Found "^Int.toString (List.length monitor_decs)^" monitor declarations.\n")
     val const_alist = tryfind extract_consts pkgs

(*
     val _ = AADL.export_cakeml_monitors dir const_alist monitor_decs
     val _ = AADL.export_cakeml_filters dir const_alist filter_decs
*)
  in
    MiscLib.succeed()
 end
 handle e =>
    let open MiscLib
    in stdErr_print "\n\nSPLAT-MON FAILED!!\n\n";
       failwithERR e
    end
