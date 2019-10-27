(*---------------------------------------------------------------------------*)
(* Maps from Json representation of AADL to AST and then to HOL. Solely      *)
(* aimed at extracting filter properties, plus support definitions.          *)
(*---------------------------------------------------------------------------*)

open Lib Feedback HolKernel boolLib MiscLib;
open AADL;

val ERR = Feedback.mk_HOL_ERR "splat";

fun printHelp() = 
  stdErr_print
    ("Usage: splat [basic | cake | hol | full]\n\
     \             [-checkprops]\n\
     \             [-outdir <dirname>]\n\
     \             [-intwidth <int> [optimize]]\n\
     \             [-endian (LSB | MSB)]\n\
     \             [-encoding (Unsigned | Twos_comp | Sign_mag | ZigZag)]\n\
     \             <name>.json\n")

fun fail() = (printHelp(); MiscLib.fail())

fun failwithERR e =
  (stdErr_print (Feedback.exn_to_string e); MiscLib.fail());

(*---------------------------------------------------------------------------*)
(* Assurance levels.                                                         *)
(*                                                                           *)
(*   Basic: PolyML regexp compiler (generated from HOL model) builds DFA,    *)
(*        from which {C,Ada,Java,SML} can be generated. Currently produces   *)
(*        C source code.                                                     *)
(*                                                                           *)
(*   Cake: Input regexp constructed by splat frontend; then passed via       *)
(*        hol2deep sexp interface. Then off-the-shelf cake binary loaded     *)
(*        with compiled regexp compiler applied to regexp to get DFA and     *)
(*        then binary.                                                       *)
(*                                                                           *)
(*   HOL: HOL regexp compiler run inside logic to get DFA. DFA then pushed   *)
(*        through hol2deep, generating DFA.sexp, then CakeML binary invoked. *)
(*                                                                           *)
(*   Full: As in HOL, except that the CakeML compiler is applied inside-     *)
(*        the-logic so that correctness of regexp compilation can be joined  *)
(*        to the ML compiler correctness theorem to get an end-to-end        *)
(*        correctness theorem. So no invocation of hol2deep or generation of *)
(*        .sexp version or invocation of off-the-shelf compilers.            *)
(*                                                                           *)
(* Basic will be fast, and Cake should be decent as well. HOL can be slow    *)
(* on larger messages, and Full will definitely take the most time.          *)
(*---------------------------------------------------------------------------*)

datatype assurance = Basic | Cake | HOL | Full;

val FLAGS = 
  {checkprops = ref NONE : bool option ref,
   alevel     = ref NONE : assurance option ref,
   outDir     = ref NONE : string option ref,
   intwidth   = ref NONE : splatLib.shrink option ref,
   endian     = ref NONE : Regexp_Numerics.endian option ref,
   encoding   = ref NONE : Regexp_Numerics.encoding option ref};
   
fun set_checkprops b =
 case !(#checkprops FLAGS)
  of NONE => (#checkprops FLAGS := SOME b)
   | SOME _ => ()

fun alevel "basic" = Basic 
  | alevel "cake"  = Cake 
  | alevel "hol"   = HOL 
  | alevel "full"  = Full
  | alevel otherwise = fail();

fun set_alevel alevel =
 case !(#alevel FLAGS)
  of NONE => (#alevel FLAGS := SOME alevel)
   | SOME _ => ()


(*---------------------------------------------------------------------------*)
(* If directory does not exist, create it. Also check that dir has rwe       *)
(* permissions.                                                              *)
(*---------------------------------------------------------------------------*)

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

fun set_intwidth s b =
 let open splatLib 
 in case !(#intwidth FLAGS)
     of NONE => 
        (case Int.fromString s
          of SOME i => 
              if i < 8 orelse not (i mod 8 = 0)
                then fail() 
              else (#intwidth FLAGS := SOME
                      (if b then Optimize i else Uniform i))
          |  NONE => fail())
   | SOME _ => ()
 end

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
        of [] => (set_checkprops false; 
                  set_alevel Basic; 
                  set_outDir "./splat_outputs";
                  set_intwidth "32" false;
                  set_endian "LSB";
                  set_encoding "Twos_comp")
         | "basic"::t => (set_alevel Basic; set_flags t)
         | "cake"::t  => (set_alevel Cake; set_flags t)
         | "hol"::t   => (set_alevel HOL; set_flags t)
         | "full"::t  => (set_alevel Full; set_flags t)
         | "-checkprops"::t => (set_checkprops true; set_flags t)
         | "-outdir"   :: d :: t => (set_outDir d; set_flags t)
         | "-intwidth" :: d :: "optimize" :: t => (set_intwidth d true; set_flags t)
         | "-intwidth" :: d :: t => (set_intwidth d false; set_flags t)
         | "-endian"   :: d :: t => (set_endian d; set_flags t)
         | "-encoding" :: d :: t => (set_encoding d; set_flags t)
         | otherwise => fail()
 in
     set_flags flags
   ; jfile
 end

fun prove_filter_props {name,regexp,encode_def,decode_def,
                        inversion, correctness, receiver_correctness, 
                        implicit_constraints,manifest} =
 let in
     store_thm(name^"_inversion",inversion,shortcut);
     store_thm(name^"_correctness",correctness,shortcut);
     store_thm(name^"_receiver_correctness",receiver_correctness,shortcut);
     ()
 end;

fun deconstruct {certificate, final, matchfn, start, table,aux} =
 let fun toList V = List.map (curry Vector.sub V) (upto 0 (Vector.length V - 1))
 in (certificate,start, toList final, toList (Vector.map toList table))
 end;

fun export_dfa codegen
         {name,regexp,encode_def,decode_def,
          inversion, correctness, receiver_correctness, 
          implicit_constraints,manifest} = 
 let open TextIO
     val (result as (_,_,finals,table)) = 
                 deconstruct (regexpLib.gen_dfa regexpLib.SML regexp)
     val rstring = PP.pp_to_string 72 Regexp_Type.pp_regexp regexp 
     val dfa = {name=name,src_regexp=rstring, finals=finals,table=table}
     val ostrm = openOut (name^".c")
 in
    codegen dfa ostrm
  ; closeOut ostrm
 end

fun process_filter iformat (checkprops,alevel) (fname,thm) = 
 let open FileSys
     val _ = stdErr_print ("Processing filter "^Lib.quote fname^".\n")
     val wDir = getDir()
     val filterDir = wDir^"/"^fname
     val _ = ((mkDir filterDir handle _ => ()); chDir filterDir)
     val filter_artifacts = 
         apply_with_chatter
           (splatLib.gen_filter_artifacts iformat) (fname,thm)
           "Defining filter artifacts ... " "succeeded.\n"
  in
     if checkprops = true then
         apply_with_chatter
            prove_filter_props filter_artifacts
            "Proving filter properties ... " "succeeded.\n"
      else ()
   ;
    (case alevel 
      of Basic => export_dfa DFA_Codegen.C filter_artifacts
       | Cake  => failwithERR (ERR "splat" "Cake compilation not supported")
       | HOL   => failwithERR (ERR "splat" "HOL compilation not supported")
       | Full  => failwithERR (ERR "splat" "Full compilation-by-proof not supported")
    )
   ; 
     stdErr_print ("End processing filter "^Lib.quote fname^".\n")
   ;
     chDir wDir
   ;
     filter_artifacts
 end

fun main () =
 let val _ = stdErr_print "splat: \n"
     val args = CommandLine.arguments()
     val jsonfile = parse_args args
     val {alevel,checkprops,outDir,intwidth,endian,encoding} = FLAGS
     val invocDir = FileSys.getDir()
     val _ = stdErr_print 
               (String.concat ["splat invoked in directory ", invocDir, ".\n"])
     val workingDir = valOf(!outDir)
     val _ = stdErr_print 
               (String.concat ["output directory is ", workingDir, ".\n"])
     val _ = FileSys.chDir workingDir
     val ([jpkg],ss) = apply_with_chatter Json.fromFile jsonfile
	   ("Parsing "^jsonfile^" ... ") "succeeded.\n"
     val pkgs = apply_with_chatter AADL.scrape_pkgs jpkg
                  "Converting Json to AST ... " "succeeded.\n"
     val thyName = fst (last pkgs)
     val _ = new_theory thyName
     val logic_defs = apply_with_chatter (AADL.pkgs2hol thyName) pkgs
	   "Converting AST to logic ...\n" "---> succeeded.\n"
     fun filters_of (a,b,c,d) = d
     val filter_spec_thms = filters_of logic_defs
     val intformat = (valOf(!intwidth),valOf(!endian),valOf(!encoding))
     val otherflags = (valOf(!checkprops),valOf(!alevel))
     val results = map (process_filter intformat otherflags) filter_spec_thms
     val _ = Theory.export_theory()
     val _ = if invocDir = workingDir then ()
             else stdErr_print ("Returning to "^invocDir^".\n")
     val _ = FileSys.chDir invocDir
     val _ = stdErr_print "Finished.\n"
  in 
    MiscLib.succeed()
 end;
