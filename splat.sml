(*---------------------------------------------------------------------------*)
(* Maps from Json representation of AADL to AST and then to CakeML code.     *)
(*---------------------------------------------------------------------------*)

open Lib Feedback HolKernel boolLib MiscLib bossLib;

local
  open AADL Gadget Gen_Contig PP_CakeML agree_fullSyntax
in end

val ERR = Feedback.mk_HOL_ERR "splat";

fun printHelp() =
  MiscLib.stdErr_print
    ("Usage: splat [-target (Hamr | Standalone)]\n\
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
    of NONE => (#target FLAGS := SOME "Hamr")
     | SOME "Hamr" => (#target FLAGS := SOME "Hamr")
     | SOME "Standalone" => (#target FLAGS := SOME "Standalone")
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

fun get_outDir() =
 case !(#outDir FLAGS)
  of NONE => raise ERR "get_outDir" "no default outdir"
   | SOME dir => dir

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
              set_endian "LSB";
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

(*---------------------------------------------------------------------------*)
(* Gadget Processing                                                         *)
(*---------------------------------------------------------------------------*)

fun atomic_width atom =
 let open ByteContig
 in case atom
     of Bool => 1
      | Char => 1
      | Float => 4
      | Double => 8
      | Signed i => i
      | Unsigned i => i
      | Blob => raise ERR "atomic_width" "Blob"
 end;

val trivEnv = ([],[],atomic_width);

fun defs_struct_of gdt =
 let open Gadget
     val tyEnvs = gadget_tyEnvs gdt
     val fodder = ("Defs",gadget_tydecs gdt,gadget_tmdecs gdt)
     val pretty = PP_CakeML.pp_defs_struct tyEnvs fodder
in
  pretty
end

fun API_of (orig_gdt,gdt) =
let open Gadget
    val qid = gadget_qid gdt
    val (inports, outports) = get_ports gdt
    val tyE = assocFn (gadget_tyE gdt)
     fun mk_inport_buf (iport as (id,ty,dir,kind)) =
      let val contig = Gen_Contig.contig_of tyE ty
          val size = Gen_Contig.size_of trivEnv contig
          val esize = if kind = "EventDataPort" then size+1 else size
      in
       (id^"_buffer", esize)
      end
    val inport_bufs = map mk_inport_buf inports

    val (orig_inports, orig_outports) = get_ports orig_gdt

    fun mk_fillFn ((iport as (id,ty,dir,kind)),(orig_id,_,_,_)) =
     let val bufName = id^"_buffer"
         val api_call = String.concat ["#(api_get_",orig_id,") \"\" ", bufName]
     in (bufName, api_call)
     end
    val fillFns = map mk_fillFn (zip inports orig_inports)

    fun mk_sendFn ((oport as (id,ty,dir,kind)),(orig_id,_,_,_)) =
      let val api_call = String.concat["#(api_send_",orig_id,") string Utils.emptybuf;"]
      in (id, api_call)
      end
    val sendFns = map mk_sendFn (zip outports orig_outports)

    val logInfo = "fun logInfo s = #(api_logInfo) s Utils.emptybuf;"
    val fodder = ("API",inport_bufs,fillFns,sendFns,logInfo)
    val pretty = PP_CakeML.pp_api fodder
 in
   pretty
 end;

fun parser_struct_of gdt =
 let open Gadget
     val qid = gadget_qid gdt
     val tydecs = gadget_tydecs gdt
     val ports = gadget_ports gdt
     val inports = filter AADL.is_in_port ports
     val tyEalist = gadget_tyE gdt
     val tyE = assocFn tyEalist
     val contig_binds = map (I##Gen_Contig.contig_of tyE) tyEalist
     val decoder_defs = Gen_Contig.decoders tyE tydecs
     val fodder = ("Parse",inports,contig_binds,decoder_defs)
     val pretty = PP_CakeML.pp_parser_struct fodder
 in
   pretty
 end

fun gadget_struct_of gdt =
let open AST Gadget
    val Gadget (qid,tydecs,tmdecs,ports,ivars,odecs) = gdt
    val fodder = (snd qid,ports,ivars,odecs)
    val env = gadget_tyEnvs gdt
    val pretty = PP_CakeML.pp_gadget_struct env fodder
in
  pretty
end

fun apply gdts [] = gdts
  | apply gdts (f::t) = apply (f gdts) t;

fun process_model jsonFile =
 let open Gadget
     val ([jpkg],ss) = apply_with_chatter Json.fromFile jsonFile
	   ("Parsing "^jsonFile^" ... ") "succeeded.\n"
     val pkgs = AADL.scrape_pkgs jpkg
     val gdts1 = Gadget.mk_gadgets pkgs
     val tyE = AADL.mk_tyE pkgs
     val tmE = AADL.mk_constE pkgs
     val gdts = apply gdts1
                 [map corral_rogue_vars,
                  map set_type_constrs,
                  map set_sig_lower_case,
                  map set_ports_and_ivars_lower_case,
                  map (elim_projections tyE tmE),
                  map set_Defs_struct,
                  map add_inport_data_projns]
     val apis = map API_of (zip gdts1 gdts)
     val parser_structs = map parser_struct_of gdts
     val defs_structs = map defs_struct_of gdts
     val gadget_structs = map gadget_struct_of gdts
 in
    (apis, parser_structs, defs_structs, gadget_structs, gdts)
 end;

(*---------------------------------------------------------------------------*)
(* Map from a gadget to a deep embedding, called a "component", which is     *)
(* formalized in agree/agree_fullScript.sml.                                 *)
(*                                                                           *)
(* Unfortunately, for now, gadgets do not carry the assumptions and guars    *)
(* from the source AGREE, so the corresponding component fields are left     *)
(* empty.                                                                    *)
(*---------------------------------------------------------------------------*)

fun mk_expr e =  (* AST.exp -> term *)
 let open AST agree_fullSyntax stringSyntax
     fun not_handled s =
         raise ERR "mk_expr" (Lib.quote s^" not handled")
 in case e
     of VarExp s => mk_Var (fromMLstring s)
      | ConstExp (IdConst qid) => not_handled "identifiers denoting constants"
      | ConstExp(BoolLit b) => mk_BoolLit (if b then T else F)
      | ConstExp(CharLit c) => not_handled "character literals"
      | ConstExp(StringLit s) => not_handled "string literals"
      | ConstExp(IntLit{value, kind}) =>
          mk_IntLit (intSyntax.term_of_int (Arbint.fromInt value))
      | ConstExp(FloatLit r) => not_handled "floating point types"
      | Unop(Not,e) => mk_Not(mk_expr e)
      | Unop(UMinus,e) => mk_Sub(intSyntax.zero_tm,mk_expr e)
      | Binop(Or,e1,e2) => mk_Or(mk_expr e1, mk_expr e2)
      | Binop(And,e1,e2) => mk_And (mk_expr e1, mk_expr e2)
      | Binop(Equal,e1,e2) => mk_Eq(mk_expr e1, mk_expr e2)
      | Binop(Divide,e1,e2) => mk_Div(mk_expr e1, mk_expr e2)
      | Binop(Exponent,e1,e2) => not_handled "exponent"
      | Binop(Imp,e1,e2) => mk_Imp(mk_expr e1, mk_expr e2)
      | Binop(Greater,e1,e2) => mk_Lt(mk_expr e2, mk_expr e1)
      | Binop(GreaterEqual,e1,e2) => mk_Leq(mk_expr e2, mk_expr e1)
      | Binop(Less,e1,e2) => mk_Lt(mk_expr e1, mk_expr e2)
      | Binop(LessEqual,e1,e2) => mk_Leq(mk_expr e1, mk_expr e2)
      | Binop(Plus,e1,e2) => mk_Add(mk_expr e1, mk_expr e2)
      | Binop(Minus,e1,e2) => mk_Sub(mk_expr e1, mk_expr e2)
      | Binop(Modulo,e1,e2) => mk_Mod(mk_expr e1, mk_expr e2)
      | Binop(Multiply,e1,e2) => mk_Mult(mk_expr e1, mk_expr e2)
      | Binop(NotEqual,e1,e2) => mk_expr (Unop(Not,Binop(Equal,e1,e2)))
      | Binop(Fby,e1,e2) => mk_Fby(mk_expr e1, mk_expr e2)
      | ArrayExp elist => mk_Array (listSyntax.mk_list(map mk_expr elist,expr_ty))
      | ArrayIndex (e1,[e2]) => mk_ArraySub(mk_expr e1, mk_expr e2)
      | ArrayIndex otherwise => not_handled "multiple array indices"
      | RecdExp (qid,fields) =>
         let fun mk_field(s,e) = pairSyntax.mk_pair (fromMLstring s, mk_expr e)
         in
           mk_Recd (listSyntax.mk_list(map mk_field fields, “:string # expr”))
          end
      | RecdProj (e,s) => mk_RecdProj(mk_expr e, fromMLstring s)
      | Fncall (("","pre"),[e]) => mk_Pre(mk_expr e)
      | Fncall (("","Port.event"),[p]) => mk_PortEvent(mk_expr p)
      | Fncall (("","Port.dataOf"),[p]) => mk_PortData(mk_expr p)
      | Fncall (("","IfThenElse"),[e1,e2,e3]) => mk_Cond(mk_expr e1,mk_expr e2,mk_expr e3)
      | Fncall (("Defs","historically"),[p]) => mk_Hist(mk_expr p)
      | Fncall (qid,elist) => not_handled ("function call on "^qid_string qid)
      | ConstrExp (tyqid,s,elist) => not_handled "constructor expressions"
      | otherwise => not_handled "unexpected AST.exp"
 end


fun gadget_to_component gdt =
 let open AST AADL Gadget agree_fullSyntax stringSyntax
     val gdt' = elim_defs gdt
     val Gadget (qid,tydecs,tmdecs,ports,ivars,outdecs) = gdt'
     val inportNames = map #1 (filter AADL.is_in_port ports)
     fun mk_var_def (s,ty,e) = mk_stmt(fromMLstring s, mk_expr e)
     fun mk_out_def (Out_Data (s,ty,e)) = mk_output_data(fromMLstring s,mk_expr e)
       | mk_out_def (Out_Event_Only(s,ty,e)) = mk_output_event (fromMLstring s, mk_expr e)
       | mk_out_def (Out_Event_Data(s,ty,e1,e2)) =
           mk_output_event_data (fromMLstring s, mk_expr e1,mk_expr e2)
 in
   agree_fullSyntax.mk_component
      [("inports",  listSyntax.mk_list (map fromMLstring inportNames,string_ty)),
       ("var_defs", listSyntax.mk_list(map mk_var_def ivars,“:stmt”)),
       ("out_defs", listSyntax.mk_list(map mk_out_def outdecs,“:ostmt”)),
       ("assumptions", listSyntax.mk_nil “:expr”),
       ("guarantees",  listSyntax.mk_nil “:expr”)]
 end


fun getFile path =
  let val istrm = TextIO.openIn path
      val vector = TextIO.inputAll istrm
      val () = TextIO.closeIn istrm
  in
    vector
  end;

val Utils_Src      = getFile "Lego/Utils.cml";
val ByteContig_Src = getFile "Lego/ByteContig.cml";
val basis_ffi_Src  = getFile "Lego/basis_ffi.c";
val Makefile_Src   = getFile "Lego/Makefile";
val Control_Src    = getFile "Lego/Control";
val Make_Sh_Src    = getFile "Lego/make.sh";
(* val Cake_Src       = getFile "Lego/cake.S"; *)

fun export_implementation dir (api,parser,defs,pp_gdt,gdt) =
 let open FileSys Gadget AST
     val (pkgName,compName) = gadget_qid gdt
     val gadgetName = pkgName^"_"^compName
     val _ = stdErr_print ("\nProcessing "^qid_string (gadget_qid gdt)^".\n")
     val invocDir = getDir()
     val () = stdErr_print ("Invocation dir: "^ invocDir ^ "\n")
     val gadgetDir = String.concat[dir,"/",gadgetName]
     val _ = ((mkDir gadgetDir handle _ => ()); chDir gadgetDir)

     val _ = stdErr_print ("  Writing basis_ffi.c\n")
     val () = let val ostrm = TextIO.openOut "basis_ffi.c"
              in TextIO.output(ostrm,basis_ffi_Src);
                 TextIO.closeOut ostrm
              end

     val _ = stdErr_print ("  Writing Makefile\n")
     val () = let val ostrm = TextIO.openOut "Makefile"
              in TextIO.output(ostrm, Makefile_Src);
                 TextIO.closeOut ostrm
              end

     val _ = stdErr_print ("  Writing make.sh\n")
     val () = let val ostrm = TextIO.openOut "make.sh"
              in TextIO.output(ostrm, Make_Sh_Src);
                 TextIO.closeOut ostrm
              end
     val _ = OS.Process.system "chmod +x make.sh" handle _ => OS.Process.failure

     val gadget_src = gadgetName^".cml"
     val _ = stdErr_print ("  Writing "^gadget_src^"\n")
     val ostrm = TextIO.openOut gadget_src
     fun put s = TextIO.output(ostrm,s)
     fun add s = (put s; put "\n\n")
     fun add_pp pp = (PPfns.pp_ostrm ostrm pp; put "\n\n")
 in
    add Utils_Src;
    add ByteContig_Src;
    add_pp defs;
    add_pp parser;
    add_pp api;
    add_pp pp_gdt;
    add Control_Src;
    TextIO.closeOut ostrm;
    stdErr_print ("Code written to directory: "^gadgetDir ^ "\n");
    stdErr_print "Done.\n";
    chDir invocDir
 end

(*---------------------------------------------------------------------------*)
(* Generate HOL script file defining a gadget in the logic. (Could           *)
(* alternatively create a theory at runtime and do an "export_theory" at     *)
(* the end.                                                                  *)
(*---------------------------------------------------------------------------*)

val component_script_prefix =
 String.concatWith "\n"
   ["open HolKernel Parse boolLib bossLib BasicProvers",
    "     pred_setLib stringLib intLib finite_mapTheory",
    "     arithmeticTheory listTheory pred_setTheory",
    "     agree_fullTheory;\n",
    "val _ = intLib.prefer_int();"];

val component_script_suffix = "val _ = export_theory();"


fun export_formal_model dir gdt =
 let open FileSys Gadget AST
     val invocDir = getDir()
     val (pkgName,compName) = gadget_qid gdt
     val gadgetName = pkgName^"_"^compName
     val gadgetDir = String.concat[dir,"/",gadgetName]
     val gadgetFile = gadgetName^"Script.sml"
     val _ = stdErr_print (String.concat
              ["\nProcessing ", qid_string (gadget_qid gdt),
               " to generate formal model.\n"])
     val _ = stdErr_print ("Invocation dir: "^ invocDir ^ "\n")
     val _ = ((mkDir gadgetDir handle _ => ()); chDir gadgetDir)
     val component_tm = gadget_to_component gdt
     val component_tm_string = Parse.term_to_string component_tm
     val component_def = String.concatWith "\n"
           ["Definition "^gadgetName^"_def:",
            gadgetName^" = ",
            "   "^component_tm_string,
            "End"]
     val new_theory_dec = ("val _ = new_theory "^Lib.quote gadgetName^";")

     val () = stdErr_print ("  Writing "^gadgetFile^"\n")
     val ostrm = TextIO.openOut gadgetFile
     fun put s = TextIO.output(ostrm,s)
     fun add s = (put s; put "\n\n")
 in
    add component_script_prefix;
    add new_theory_dec;
    add component_def;
    add component_script_suffix;
    TextIO.closeOut ostrm;
    stdErr_print ("Component spec written to directory: "^gadgetDir ^ "\n");
    stdErr_print "Done.\n";
    chDir invocDir
 end


(*
val jsonFile = "examples/uxaslite.json";
val (apis,parsers,defs,gdt_pps,gdts) = process_model jsonFile;
val [gdt1, gdt2] = gdts;
export_formal_model "tmp" gdt1; (* Fails cuz support defs not handled *)
export_formal_model "tmp" gdt2;


val comp2 = gadget_to_component gdt2;

val jsonFile = "examples/SW.json";
val jsonFile = "examples/UAS.json";
val jsonFile = "examples/uxaslite.json";
val jsonFile = "examples/SimpleFFA.json";
val jsonFile = "examples/WatchWordServer.json";

val (apis,parsers,defs,gdt_pps,gdts) = process_model jsonFile;
val [gdt1, gdt2] = gdts;
val [api1,api2] = apis;
val [p1,p2] = parsers;
val [defs1,defs2] = defs;
val [gpp1,gpp2] = gdt_pps;

export_implementation "tmp" (api1,p1,defs1,gpp1,gdt1);
export_implementation "tmp" (api2,p2,defs2,gpp2,gdt2);


val [gdt1, gdt2, gdt3] = gdts;
val [api1,api2,api3] = apis;
val [p1,p2,p3] = parsers;
val [defs1,defs2,defs3] = defs;
val [gpp1,gpp2,gpp3] = gdt_pps;
export_implementation "tmp" (api3,p3,defs3,gpp3,gdt3);

listBinds 10 "ivars" "vdec" ;
*)

fun zip5 (h1::t1) (h2::t2) (h3::t3) (h4::t4) (h5::t5) =
     (h1,h2,h3,h4,h5)::zip5 t1 t2 t3 t4 t5
  | zip5 [] [] [] [] [] = []
  | zip5 a b c d e = raise ERR "zip5" "not all lists have equal length";

fun main () =
 let val _ = stdErr_print "splat: \n"
     val args = CommandLine.arguments()
     val jsonFile = parse_args args
     val (apis,parsers,defs,gdt_pps,gdts) = process_model jsonFile
     val _ = stdErr_print
             (String.concat
               ["Found ",
                Int.toString (List.length gdts),
                " CASE security components.\n"])
     val inputs = zip5 apis parsers defs gdt_pps gdts
     val dir = get_outDir()
     val () = List.app (export_implementation dir) inputs
  in
    MiscLib.succeed()
 end
 handle e =>
    let open MiscLib
    in stdErr_print "\n\nSPLAT FAILURE!!\n\n";
       failwithERR e
    end
