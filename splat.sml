(*---------------------------------------------------------------------------*)
(* Maps from Json representation of AADL to AST and then to HOL. Originallly *)
(* aimed at extracting filter properties, plus support definitions. Has      *)
(* evolved to also generate code and test harnesses.                         *)
(*---------------------------------------------------------------------------*)

open Lib Feedback HolKernel boolLib MiscLib;

open AADL;

val ERR = Feedback.mk_HOL_ERR "splat";

fun printHelp() =
  stdErr_print
    ("Usage: splat [-alevel (basic | cake | hol | full)]\n\
     \             [-codegen (C | SML | Ada | Slang | Java)]\n\
     \             [-checkprops]\n\
     \             [-outdir <dirname>]\n\
     \             [-intwidth <int> [optimize]]\n\
     \             [-endian (LSB | MSB)]\n\
     \             [-encoding (Unsigned | Twos_comp | Sign_mag | ZigZag)]\n\
     \             [-preserve_model_nums]\n\
     \             <name>.json\n")

fun fail() = (printHelp(); MiscLib.fail())

fun failwithERR e =
  (stdErr_print (Feedback.exn_to_string e^"\n\n"); MiscLib.fail());

(*---------------------------------------------------------------------------*)
(* Assurance levels.                                                         *)
(*                                                                           *)
(*   Basic: PolyML regexp compiler (generated from HOL model) builds DFA,    *)
(*        from which {C,Ada,Java,SML,...} can be generated. Defaults to C    *)
(*        source code being generated.                                       *)
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
   codegen    = ref NONE : string option ref,
   testgen    = ref NONE : bool option ref,
   outDir     = ref NONE : string option ref,
   intwidth   = ref NONE : splatLib.shrink option ref,
   endian     = ref NONE : Regexp_Numerics.endian option ref,
   encoding   = ref NONE : Regexp_Numerics.encoding option ref,
   preserve_model_nums = ref NONE : bool option ref};

fun set_checkprops b =
 case !(#checkprops FLAGS)
  of NONE => (#checkprops FLAGS := SOME b)
   | SOME _ => ()

fun set_testgen b =
 case !(#testgen FLAGS)
  of NONE => (#testgen FLAGS := SOME b)
   | SOME _ => ()

fun s2alevel "basic" = Basic
  | s2alevel "cake"  = Cake
  | s2alevel "hol"   = HOL
  | s2alevel "full"  = Full
  | s2alevel otherwise = fail();

fun set_alevel alevel =
 case !(#alevel FLAGS)
  of NONE => (#alevel FLAGS := SOME (s2alevel alevel))
   | SOME _ => ()

fun set_codegen lang =
 let val _ =
    if mem lang ["C","SML","Ada","Java","Slang"]
    then () else fail()
 in case !(#codegen FLAGS)
     of NONE => (#codegen FLAGS := SOME lang)
      | SOME _ => ()
 end

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
              set_alevel "basic";
              set_codegen "C";
              set_testgen false;
              set_checkprops false;
              set_outDir "./splat_outputs";
              set_intwidth "32" false;
              set_endian "LSB";
              set_encoding "Twos_comp";
              set_preserve_model_nums false
            end
         | "-checkprops" :: t => (set_checkprops true; set_flags t)
         | "-testgen"    :: t => (set_testgen true;    set_flags t)
         | "-alevel"   :: d :: t => (set_alevel d;     set_flags t)
         | "-codegen"  :: d :: t => (set_codegen d;    set_flags t)
         | "-outdir"   :: d :: t => (set_outDir d;     set_flags t)
         | "-intwidth" :: d :: "optimize" :: t => (set_intwidth d true; set_flags t)
         | "-intwidth" :: d :: t => (set_intwidth d false; set_flags t)
         | "-endian"   :: d :: t => (set_endian d; set_flags t)
         | "-encoding" :: d :: t => (set_encoding d; set_flags t)
         | "-preserve_model_nums"::t => (set_preserve_model_nums true; set_flags t)
         | otherwise => fail()
 in
     set_flags flags
   ; jfile
 end

fun prove_filter_props {name,regexp,implicit_constraints,manifest,tv} =
 let val fieldreps = map snd manifest
 in store_thm(name^"_TV",tv,splatLib.TV_TAC fieldreps)
  ; ()
 end;

fun deconstruct {certificate, final, matchfn, start, table,aux} =
 let fun toList V = List.map (curry Vector.sub V) (upto 0 (Vector.length V - 1))
 in (certificate,start, toList final, toList (Vector.map toList table))
 end;

fun mk_matcher name certificate =
 let open numSyntax stringSyntax bossLib
     val SOME thm = certificate
     val eqn = snd(dest_forall(concl thm))
     val (exec_dfa,[finals,table,start,s]) = strip_comb(lhs eqn)
     val finals_name = name^"_finals"
     val table_name = name^"_table"
     val start_name = name^"_start"
     val finals_var = mk_var(finals_name,type_of finals)
     val table_var  = mk_var(table_name,type_of table)
     val start_var  = mk_var(start_name,type_of start)
     val finals_def = Define `^finals_var = ^finals`
     val table_def  = Define `^table_var = ^table`
     val start_def  = Define `^start_var = ^start`
     val thm' = CONV_RULE
        (BINDER_CONV
          (LHS_CONV
            (REWRITE_CONV [GSYM finals_def, GSYM table_def, GSYM start_def]))) thm
     val CT = current_theory()
     val finals_const = prim_mk_const{Thy=CT,Name=finals_name}
     val table_const = prim_mk_const{Thy=CT,Name=table_name}
     val start_const = prim_mk_const{Thy=CT,Name=start_name}

     val match_stateName = name^"_match_state"
     val match_stateVar = mk_var(match_stateName, num --> string_ty --> bool)
     val match_state_def =
            Define `^match_stateVar = exec_dfa ^finals_const ^table_const`
     val match_state_const = prim_mk_const{Thy=CT, Name=match_stateName}
     (* translate this, not match_state_def *)
     val match_state_thm = Q.store_thm
      (match_stateName^"_thm",
       `^match_state_const n s =
          if s="" then
            sub ^finals_const n
          else case sub (sub ^table_const n) (ORD (HD s)) of
                 | NONE => F
                 | SOME k => ^match_state_const k (TL s)`,
      rw_tac list_ss [match_state_def]
       >- rw_tac list_ss [regexp_compilerTheory.exec_dfa_def]
       >- (`?h t. s = h::t` by metis_tac [listTheory.list_CASES]
	    >> rw_tac list_ss [Once regexp_compilerTheory.exec_dfa_def]))
     val matchName = name^"_match"
     val v = mk_var(matchName, string_ty --> bool)
     val match_def = Define `^v = ^match_state_const ^start_const`
 in
    (match_state_thm, match_def)
 end
 handle _ => (TRUTH,TRUTH);

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

fun main () =
 let val _ = stdErr_print "splat: \n"
     val args = CommandLine.arguments()
     val jsonfile = parse_args args
     val {alevel,checkprops,outDir,testgen,codegen,
          intwidth,endian,encoding,preserve_model_nums} = FLAGS
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
     val pkgs1 = if valOf(!preserve_model_nums) = true then
                    pkgs
                 else map AADL.abstract_model_nums pkgs
     val thyName = fst (last pkgs1)
     val _ = new_theory thyName
     val logic_defs = apply_with_chatter (AADL.pkgs2hol thyName) pkgs1
	   "Converting AST to logic ...\n" "---> succeeded.\n"
     fun filters_of (a,b,c,d) = d
     val filter_spec_thms = filters_of logic_defs
     val intformat = (valOf(!intwidth),valOf(!endian),valOf(!encoding))
     val otherflags = (valOf(!checkprops),valOf(!codegen),
                       valOf(!testgen),valOf(!alevel))
     val results = map (process_filter intformat otherflags) filter_spec_thms
     val _ = Theory.export_theory()
     val _ = if invocDir = workingDir then ()
             else stdErr_print ("Returning to "^invocDir^".\n")
     val _ = FileSys.chDir invocDir
     val _ = stdErr_print "Finished.\n"
  in
    MiscLib.succeed()
 end
 handle e =>
    let open MiscLib
    in stdErr_print "\n\nSPLAT FAILED!!\n\n";
       failwithERR e
    end
val args = ["-codegen", "SML", "examples/Producer_Consumer.json"];
