open CCommon
open JS2JSIL_Preprocessing
open JS2JSIL_Compiler
open JS_PreParser
open JSIL_PostParser

let file = ref "" 

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
      (* file to compile *)
      "-file", Arg.String(fun f -> file := f), "file to run";
      (* harnessing *)
      "-harness", Arg.Unit(fun _ -> js2jsil_harnessing := true), "ES6 harness";
      (* show line numbers *)
      "-line_numbers", Arg.Unit(fun () -> js2jsil_line_numbers := true), "show line numbers";
      (* one procedure per file *)
      "-sep_procs", Arg.Unit(fun () -> js2jsil_sep_procs := true), "one procedure per file";
      (* output for logic verification  *)
      "-logic", Arg.Unit(fun () -> verification := true), "output for logic verification";
      (* cosette *)
      "-cosette", Arg.Unit(fun () -> symb_testing := true; SCommon.cosette := true), "output for cosette testing";
      (* bi *)
      "-bi", Arg.Unit(fun () -> symb_testing := true; SCommon.cosette := true; SCommon.bi := true), "output for cosette bi-abductive testing";
      (* unfolds *)
      "-unfolds", Arg.Unit(fun () -> unfolding := true), "insert unfolds";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let create_output ext_proc path =
  let content = EProc.str ext_proc in
  let path = path ^ "/" ^ ext_proc.name ^ ".jsil" in
  let oc = open_out path in
  output_string oc content;
  close_out oc

let process_file path =
  try
  let e_str = IO_Utils.load_js_file path in
    let e_str = if (!symb_testing) then JS_PreParser.stringify_assume_and_assert e_str else e_str in 
  let offset_converter = JS_Utils.memoized_offsetchar_to_offsetline e_str in
  let e = JSParserMain.exp_from_string ~force_strict:true e_str in
  let (ext_prog : EProg.t), _, _ = js2jsil e offset_converter (!verification) in
  let ext_prog = if (!unfolding) then post_parse_eprog ext_prog else ext_prog in 
  let ext_prog = if (!SCommon.bi) then bi_post_parse_eprog ext_prog JS2JSIL_Compiler.cc_tbl JS2JSIL_Compiler.vis_tbl else ext_prog in

  let file_name = Filename.chop_extension path in
  (if (not (!js2jsil_sep_procs))
    then (
      let jsil_prog_str = EProg.str ext_prog in
        IO_Utils.save_file (file_name ^ ".jsil") jsil_prog_str
      ) else (
        let folder_name = file_name in
      IO_Utils.safe_mkdir folder_name;
      Hashtbl.iter (fun p_name p_body -> create_output p_body folder_name) ext_prog.procs));
  
  if (!js2jsil_line_numbers)
    then (
      let e_line_numbers = EProg.line_info ext_prog in
      let file_numbers_name = file_name ^ JS2JSIL_Constants.line_numbers_extension in
      IO_Utils.save_file file_numbers_name (Annot.line_info_to_str e_line_numbers)
    ) else ()
  with
  | JSParser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1
  | JS2JSIL_Preprocessing.EarlyError e -> Printf.printf "\nParser post-processing threw an EarlyError: %s\n" e; exit 1


let main () =
  arguments ();
  JSParserMain.init ();
  JSParserMain.verbose := false;
  process_file !file

let _ = main()
