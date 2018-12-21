open CCommon
open Lexing
open JS2JSIL_Constants


let file    = ref ""
let js      = ref false
let compile = ref false
let test262 = ref false


  let arguments () =
    let usage_msg="Usage: -file <path>" in
    Arg.parse
      [
        (* file to compile *)
        "-file", Arg.String(fun f -> file := f), "file to run";

        (* access debugging information *)
        "-debug", Arg.Unit(fun () -> debug := true), "debug information";

        (* it is a compiled js program *)
        "-js", Arg.Unit(fun () -> js := true), "input is a compiled js program";

        (* no outputs *)
        "-noheap",  Arg.Unit(fun () -> CCommon.no_heap := true), "suppress heap output";

        (* compile and run *)
        "-js2jsil", Arg.Unit(fun () -> js := true; compile := true), "compile and run";

        (* use test262 harness *)
        "-test262",  Arg.Unit(fun () -> js := true; compile := true; test262 := true), "use test262 harness";

        (* no outputs *)
        "-silent",  Arg.Unit(fun () -> Logging.silent := true), "suppress output";
      ]
      (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
      usage_msg


let return_to_exit (ret_ok : bool) : unit =
  match ret_ok with
  | false -> exit 1
  | true  -> ()

let string_of_ret_val (heap : CHeap.t) (ret_flag : Flag.t) (v : Literal.t) : string =
  match ret_flag with
  | Normal -> Literal.str v
  | Error -> if (!js) then CInterpreter.M.string_of_js_error heap v else ""

let run (prog : Prog.t) : unit = 
  let prog    = UP.init_prog prog in 
  let prog    = (match prog with | Ok prog -> prog | _ -> raise (Failure "Program could not be initialised")) in 
  let ret     = CInterpreter.M.evaluate_prog prog in
  let ret_str = CInterpreter.M.string_of_result ret in 
  if (!debug) then Printf.printf "Final state: \n%s\n" ret_str;
  return_to_exit (CInterpreter.M.valid_concrete_result ret)

let main () =
  arguments ();
  JSParserMain.init ();
  
  if (!compile) then (
    try
      JSParserMain.verbose := false;
      let main : string = IO_Utils.load_file (!file) in
      let all  = if (!test262) then (IO_Utils.load_file "harness.js") ^ "\n" ^ main else main in
      let offset_converter = JS_Utils.memoized_offsetchar_to_offsetline all in
      let e    = JSParserMain.exp_from_string ~force_strict:true all in
      let (ext_prog, cc_tbl, vis_tbl) = JS2JSIL_Compiler.js2jsil e offset_converter false in
        let prog = Parsing_Utils.eprog_to_prog ext_prog in
          run prog
        with
          | JSParser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1
          | JS2JSIL_Preprocessing.EarlyError e -> Printf.printf "\nParser post-processing threw an EarlyError: %s\n" e; exit 1
          | _ -> Printf.printf "Uncaught parser exception.\n"; exit 1)
  else (
    let ext_prog = Parsing_Utils.parse_eprog_from_file !file in
    Printf.printf "Program:\n%s\n" (EProg.str ext_prog);
    let prog = Parsing_Utils.eprog_to_prog ext_prog in
    Printf.printf "De-labeled program:\n";
    run prog 
  );
  Logging.wrap_up ()

let _ = main ()