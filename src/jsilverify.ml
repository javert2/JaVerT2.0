open CCommon
open SCommon
open Verification
open LogicPreprocessing
open MakeAbsState

module L = Logging

let file    = ref ""
let js2jsil = ref false
let unfold  = ref true 


let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
	  (* file containing the program to symbolically execute *)
	  "-file", Arg.String(fun f -> file := f), "file to run";
	  (* *)
	  "-js2jsil", Arg.Unit (fun () -> js2jsil := true), "js2jsil output";
	  (* *)
	  "-stats",  Arg.Unit (fun () -> stats := true), "stats";
    (* *)
    "-nounfold", Arg.Unit (fun () -> unfold := false), "no automatic unfolding of non-recursive predicates"; 
    (* *)
    "-silent",  Arg.Unit(fun () -> Logging.silent := true), "suppress output";
    (* *)
    "-stats",  Arg.Unit(fun () -> CCommon.stats := true), "display statistics";
    (* *)
    "-manual",  Arg.Unit(fun () -> CCommon.manual_proof := true), "no automatic unfolding of pred assertions";
	]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg


let process_file (path : string) =
  
  (** Step 1: PARSING                                            *)
  (*  -----------------------------------------------------------*)
  L.log L.Verbose (lazy "\n*** Stage 1: Parsing program. ***\n");
  let e_prog = Parsing_Utils.parse_eprog_from_file path in

  (** Step 2: Syntactic Checks + Program transformation          *)
  (*  -----------------------------------------------------------*)
  L.log L.Verbose (lazy "\n*** Stage 2: Transforming the program.\n");
  let prog = Parsing_Utils.eprog_to_prog e_prog in
  EProg.perform_syntax_checks e_prog prog;
  L.log L.Verbose (lazy "\n*** Stage 2: DONE transforming the program.\n");
  
  (** Step 3: Logic Preprocessing                                *)
  (*  -----------------------------------------------------------*)
  L.log L.Verbose (lazy "\n*** Stage 3: Logic Preprocessing.\n");
  let prog = LogicPreprocessing.preprocess prog !unfold in
  L.log L.Verbose (lazy "\n*** Stage 3: DONE Logic Preprocessing.\n");

  (** Step 4: Verification                                       *)
  (*  -----------------------------------------------------------*)	
  L.log L.Verbose (lazy "\n*** Stage 4: Verification.\n");
  Verification.verify_procs prog


let main () =
		arguments ();
		process_file !file;
    if (!stats) then print_statistics ();
    Logging.wrap_up()

let _ = main()