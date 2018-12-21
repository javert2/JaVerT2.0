open CCommon
open SCommon

let file    = ref ""
let js2jsil = ref false

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
  	  (* file containing the program to symbolically execute *)
  	  "-file", Arg.String(fun f -> file := f), "file to run";
  	  (* *)
  	  "-js2jsil", Arg.Unit (fun () -> js2jsil := true), "js2jsil output";

      (* no outputs *)
      "-noheap",  Arg.Unit(fun () -> CCommon.no_heap := true), "suppress heap output";
      
      (* *)
      "-silent",  Arg.Unit(fun () -> Logging.silent := true), "suppress output";

      (* *)
      "-stats",  Arg.Unit(fun () -> CCommon.stats := true), "display statistics";

      (* *)
      "-mthread",  Arg.Int(fun n -> CCommon.max_threads := n), "multi-threading";

      (* *)
      "-bi", Arg.Unit (fun () -> SCommon.bi := true), "bi-abduction active";

      (* *)
      "-js", Arg.Unit (fun () -> SCommon.js := true), "bi-abduction active";

      (* *)
      "-bug_propagation",  Arg.Unit (fun () -> CCommon.bug_specs_propagation := true), "Propagate bug specs";

       (* *)
       "-output_verification",  Arg.Unit (fun () -> CCommon.output_verification := true), "Output for verification";
	  ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg


let process_file (path : string) : unit =

  SCommon.cosette := true;
  
  (** Step 1: PARSING                                            *)
  (*  -----------------------------------------------------------*)
  L.log L.Normal (lazy "\n***Stage 1: Parsing program. ***\n");
  let e_prog     = Parsing_Utils.parse_eprog_from_file path in
  let proc_names = e_prog.proc_names in 
	
  (** Step 2: Syntactic Checks + Program transformation          *)
  (*  -----------------------------------------------------------*)
  L.log L.Normal (lazy "*** Stage 2: Transforming the program.\n");
  let prog = Parsing_Utils.eprog_to_prog e_prog in
  EProg.perform_syntax_checks e_prog prog;
  L.log L.Normal (lazy "\n*** Stage 2: DONE transforming the program.\n");
  
  (** Step 3: Symbolic Execution                                 *)
  (*  -----------------------------------------------------------*)	
  L.log L.Normal (lazy "*** Stage 3: Symbolic Execution.\n");

  if (!SCommon.bi) then (
    (** bi-abduction active *)
    SCommon.unfolding := false; 
    let prog = LogicPreprocessing.preprocess prog true in
    (match UP.init_prog prog with
    | Error _ -> raise (Failure "Creation of unification plans failed.")
    | Ok prog' -> 
        AbsBiAbduction.test_procs prog' proc_names; 
        if (!CCommon.output_verification) then (
          EProg.update_specs e_prog prog'.prog;
          let e_prog = { e_prog with preds = Hashtbl.create CCommon.small_tbl_size } in 
          let eprog_final_str = EProg.str e_prog in
          let fname = Filename.basename path in 
          let folder_path = Filename.dirname path in 
          let fname' = "BI_" ^ fname in 
          let path' = folder_path ^ "/" ^ fname' in 
          IO_Utils.save_file path' eprog_final_str 
        )
        (* BiAbduction.test_procs prog' *))
  ) else (
    (match UP.init_prog prog with
    | Error _ -> raise (Failure "Creation of unification plans failed.")
    | Ok prog' -> 
      let rets : (SInterpreter.M.result_t) list = 
        SInterpreter.M.evaluate_proc (fun x -> x) prog' "main" [] (SState.M.init None) in
      ())
  )
  

let main () =
		arguments ();
    let pid = Unix.getpid() in 
    let start_time = Sys.time () in 
		process_file !file;
    let end_time = Sys.time () in 
    if (!stats) then print_statistics ();
    Logging.wrap_up();
    act_threads := !act_threads - 1

let _ = main()