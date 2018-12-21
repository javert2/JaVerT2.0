open CCommon

module L              = Logging
module BiSState       = BiSState.M
module BiSInterpreter = BiSInterpreter.M
module AbsSState      = AbsSState.M


type t = {
  name          : string; 
  params        : string list; 
  state         : BiSState.t
}

type result_t = BiSInterpreter.result_t


let testify (bi_spec : BiSpec.t) : t option = 
  let params = SS.of_list bi_spec.params in 
  match Normaliser.normalise_assertion None None (Some params) bi_spec.pre with 
    | None              -> None
    | Some (ss_pre, _)  -> 
      let state, safe = AbsSState.deabstract ss_pre in 
      if (not safe) then Printf.printf "UNSAFE DEABSTRACTION: testify_with_spec"; 
        Some {
          name   = bi_spec.name; 
          params = bi_spec.params; 
          state  = BiSState.initialise state None
        } 

let run_test (prog : UP.prog) (test : t) : result_t list =  
  let state = BiSState.copy test.state in 
  try (
    let rets : result_t list = BiSInterpreter.evaluate_proc prog test.name test.params state in 
    rets 
  ) with (Failure msg) -> (
    Printf.printf "ERROR in proc %s with message:\n%s\n" test.name msg; 
    []   
  ) 

let test_procs (prog : UP.prog) : unit = 
  (* Printf.printf "Starting bi-abductive testing\n"; *)
  
  let process_spec (name, params, state_pre, state_post, flag, errs) : Spec.t option = 
     if (name <> "main")
        then (
          let _ = BiSState.simplify state_pre in
          let _ = BiSState.simplify state_post in
          Some (BiSState.make_spec prog name params state_pre state_post flag)
        ) else None in 

  let specs, bugs = 
    List.split 
      (List.map 
        (fun test -> 
          let rets = run_test prog test in 
          let ret_succs, ret_fails = List.partition (fun x -> match (x : result_t) with | RSucc _ -> true | _ -> false) rets in 
          let ret_succs = List.map (fun x -> match (x : result_t) with | RSucc (fl, _, state_f) -> Some (test.name, test.params, BiSState.copy test.state, state_f, fl, None) | _ -> None) ret_succs in 
          let ret_succs = CCommon.get_list_somes ret_succs in 
          let ret_fails = List.map (fun x -> match (x : result_t) with | RFail (state_f, errs)  -> Some (test.name, test.params, BiSState.copy test.state, state_f, Flag.Error, Some errs) | _ -> None) ret_fails in 
          let ret_fails = CCommon.get_list_somes ret_fails in 
          ret_succs, ret_fails)
        (get_list_somes (List.map testify (UP.get_bispecs prog)))) in 
  
  let specs = List.concat specs in 
  let bugs  = List.concat bugs in 
  
  let specs = get_list_somes (List.map process_spec specs) in 
  let bugs  = get_list_somes (List.map process_spec bugs)  in 

  print_to_all (Printf.sprintf "BUG SPECS:\n%s\n" (String.concat "\n" (List.filter (fun x -> x <> "") (List.map (UP.string_of_spec prog.preds) bugs))));

  print_to_all (Printf.sprintf "SUCCESSFUL SPECS:\n%s\n" (String.concat "\n" (List.filter (fun x -> x <> "") (List.map (UP.string_of_normal_spec prog.preds) specs))));
