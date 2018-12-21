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
      "-silent",  Arg.Unit(fun () -> Logging.silent := true), "suppress output";

    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg


let process_file (path : string) : unit =
 
  (** Step 1: PARSING                                            *)
  (*  -----------------------------------------------------------*)
  L.log L.Normal (lazy "\n***Stage 1: Parsing query. ***\n");
  let left_side, right_side = Parsing_Utils.parse_fo_query path in
	
  (** Step 2:                                                    *)
  (*  -----------------------------------------------------------*)
  L.log L.Normal (lazy "*** Stage 2: Questioning the tool.\n");
  let prog = Parsing_Utils.eprog_to_prog e_prog in
  EProg.perform_syntax_checks e_prog prog;
  L.log L.Normal (lazy "\n*** Stage 2: DONE transforming the program.\n");
  

let main () =
		arguments ();
    let pid = Unix.getpid() in 
    let start_time = Sys.time () in 
		process_file !file;
    let end_time = Sys.time () in 
    if (pid = Unix.getpid()) then print_endline (Printf.sprintf "Finished in %f%!" (end_time -. start_time));
    if (!stats) then print_statistics ();
    Logging.wrap_up();
    act_threads := !act_threads - 1

let _ = main()