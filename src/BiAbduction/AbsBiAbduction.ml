open CCommon

module L                 = Logging
module BiAbsSState       = BiAbsSState.M
module BiAbsSInterpreter = BiAbsSInterpreter.M
module AbsSState         = AbsSState.M
module SSubst            = SVal.SSubst
module SVal              = SVal.M
module SError            = SError.M
module JSCleanUp         = MakeJSCleanUp.M(SVal)(SSubst)(SStore)(SError)(AbsSState)

type bi_state_t = BiAbsSState.t
type abs_state  = AbsSState.t 

type t = {
  name          : string; 
  params        : string list; 
  state         : bi_state_t
}

type result_t = BiAbsSInterpreter.result_t


let make_id_subst (a : Asrt.t) : SSubst.t =
  let lvars = Asrt.lvars a in 
  let alocs = Asrt.alocs a in 
  let lvar_bindings = List.map (fun x -> (x, Expr.LVar x)) (SS.elements lvars) in 
  let aloc_bindings = List.map (fun x -> (x, Expr.ALoc x)) (SS.elements alocs) in 
  let bindings  = lvar_bindings @ aloc_bindings in 
  let bindings' = 
    List.map 
      (fun (x, e) ->
        match SVal.from_expr e with 
          | Some v -> (x, v)
          | _ -> raise (Failure "DEATH. make_id_subst"))
      bindings in 
  SSubst.init bindings' 

let make_spec 
        (prog       : UP.prog) 
        (name       : string) 
        (params     : string list) 
        (bi_state_i : bi_state_t)  
        (bi_state_f : bi_state_t) 
        (fl         : Flag.t) : Spec.t * Spec.t = 
    
    (* let start_time = time() in *)

    let _                 = BiAbsSState.simplify ~kill:true bi_state_f in 
    let state_i, _        = BiAbsSState.get_components bi_state_i in 
    let state_f, state_af = BiAbsSState.get_components bi_state_f in 
    let pvars             = SS.of_list (Flag.return_variable :: params) in 

    L.log L.Verbose (lazy (
      Printf.sprintf "Going to create a spec for %s(%s)\nAF:\n%s\nFinal STATE:\n%s"
        name (String.concat ", " params) (AbsSState.str state_af) (AbsSState.str state_f)
    )); 

    let post, spost = 
      if ((name <> "main") && !SCommon.js) then (
        let state_f'  = AbsSState.copy state_f in 
        let state_f'  = JSCleanUp.exec prog state_f' name false in  
        let post  = Asrt.star (List.sort Asrt.compare (AbsSState.to_assertions ~to_keep:pvars state_f)) in 
        let spost = Asrt.star (List.sort Asrt.compare (AbsSState.to_assertions ~to_keep:pvars state_f')) in
        post, spost 
      ) else (
        let post = Asrt.star (List.sort Asrt.compare (AbsSState.to_assertions ~to_keep:pvars state_f)) in 
        post, post 
      ) in 
  
    let pre, spre  =
      if ((name <> "main") && !SCommon.js) then (
        let af_asrt  = Asrt.star (AbsSState.to_assertions state_af) in 
        let af_subst = make_id_subst af_asrt in  
        match AbsSState.produce state_i af_subst af_asrt with 
          | Some state_i' -> 
              let _ = AbsSState.simplify ~kill:true state_i' in 
              let state_i'' = AbsSState.copy state_i' in 
              let state_i'' = JSCleanUp.exec prog state_i'' name true in  
              let pre  = Asrt.star (AbsSState.to_assertions ~to_keep:pvars state_i') in 
              let spre = Asrt.star (AbsSState.to_assertions ~to_keep:pvars state_i'') in 
              pre, spre
          | _ -> raise (Failure "DEATH. make_spec")
      ) else (
        let pre = 
          Asrt.star 
            (List.sort Asrt.compare 
              ((AbsSState.to_assertions ~to_keep:pvars state_i) @ (AbsSState.to_assertions state_af))) in
        pre, pre
      ) in 
    
    let make_spec_aux pre post = 
      let post_clocs = Asrt.clocs post in 
      let pre_clocs  = Asrt.clocs pre in 
      let new_clocs  = SS.diff post_clocs pre_clocs in 
      let subst      = Hashtbl.create CCommon.medium_tbl_size in
      List.iter (fun cloc -> Hashtbl.replace subst cloc (Expr.ALoc (SCommon.fresh_aloc ()))) (SS.elements new_clocs);  
      let subst_fun  = (fun cloc -> match Hashtbl.find_opt subst cloc with | Some e -> e | None -> Lit (Loc cloc)) in 
      let new_post   = Asrt.subst_clocs subst_fun post in 

      let spec : Spec.t = { 
        name   = name; 
        params = params;
        sspecs = [ { 
          pre       = pre; 
          posts     = [ new_post ]; 
          flag      = fl; 
          to_verify = false;
          label     = None 
        }]; 
        normalised = true; 
        to_verify  = false
      } in 
      spec in 
   
   let spec  = make_spec_aux pre post in 
   let sspec = make_spec_aux spre spost in 

    L.log L.Verbose (lazy (
      Printf.sprintf "Created a spec for %s(%s) successfully. Here is the spec:\n%s"
        name (String.concat ", " params) (Spec.str spec))); 
   (* update_statistics "make_spec_AbsBi" (time() -. start_time); *)

   sspec, spec 


let testify (prog : UP.prog) (bi_spec : BiSpec.t) : t option = 
  let procs      = Prog.get_procs prog.prog in 
  let proc_names = List.map (fun (proc : Proc.t) -> proc.name) procs in 
  let params     = SS.of_list bi_spec.params in 
  match Normaliser.normalise_assertion ~pred_defs:prog.preds None None (Some params) bi_spec.pre with 
    | None              -> None
    | Some (ss_pre, _)  -> 
        Some {
          name   = bi_spec.name; 
          params = bi_spec.params; 
          state  = BiAbsSState.initialise (SS.of_list proc_names) ss_pre (Some prog.preds)
        } 

let run_test 
    (ret_fun : result_t -> Spec.t * bool) 
    (prog    : UP.prog) 
    (test    : t) : (Spec.t * bool) list =  
  let state = BiAbsSState.copy test.state in 
  try (
    let specs : (Spec.t * bool) list = BiAbsSInterpreter.evaluate_proc ret_fun prog test.name test.params state in 
    specs 
  ) with (Failure msg) -> (
    print_to_all (Printf.sprintf "ERROR in proc %s with message:\n%s\n" test.name msg); 
    []   
  ) 

let test_procs (prog : UP.prog) (proc_names : string list) : unit = 
  (* Printf.printf "Starting bi-abductive testing\n"; *)

  JSIL_PostParser.populate (); 
  
  let bispecs = get_list_somes (List.map (fun name -> Prog.get_bispec prog.prog name) proc_names) in 
  let tests   = get_list_somes (List.map (testify prog) bispecs) in 

  let process_spec name params state_pre state_post flag errs : Spec.t * Spec.t = 
    let _ = BiAbsSState.simplify ~kill:true state_pre in
    let _ = BiAbsSState.simplify ~kill:true state_post in
    make_spec prog name params state_pre state_post flag in 

  let process_symb_exec_result 
      (name    : string) 
      (params  : string list) 
      (state_i : bi_state_t)
      (result  : result_t) : Spec.t * bool = 
    
    let state_i = BiAbsSState.copy state_i in 
    (match result with 
      | RFail (_, _, state_f, errs) -> 
          let sspec, spec = process_spec name params state_i state_f Flag.Error (Some errs) in 
          if (!CCommon.bug_specs_propagation) 
            then (
              L.log L.Verbose (lazy (Printf.sprintf "Trying to build UP from BUG SPEC for %s\n" name)); 
              (try UP.add_spec prog spec
                with Failure inner_msg ->
                  (let msg =  Printf.sprintf "when trying to build UP for %s, died with msg: %s!\n" name inner_msg in 
                  L.log L.Verbose (lazy msg)))  
            ); 
          sspec, false 
      | RSucc (fl, _, state_f) -> 
          let sspec, spec = process_spec name params state_i state_f fl  None in 
          L.log L.Verbose (lazy (Printf.sprintf "Trying to build UP from SUCC SPEC for %s\n" name)); 
          (try UP.add_spec prog spec 
            with Failure inner_msg ->
              (let msg =  Printf.sprintf "when trying to build UP for %s, died with msg: %s!\n" name inner_msg in 
               L.log L.Verbose (lazy msg)));  
          sspec, true) in 
          
  let bug_specs, succ_specs =
    List.split
      (List.map 
        (fun test : (Spec.t list * Spec.t list)  -> 
          (* Printf.printf "Running Biabduction on function %s\n" test.name; *)
          let rets = run_test (process_symb_exec_result test.name test.params test.state) prog test in 
          let succ_specs, bug_specs = List.partition (fun (_, b) -> b) rets in 
          let succ_specs = List.map (fun (spec, _) -> spec) succ_specs in 
          let bug_specs  = List.map (fun (spec, _) -> spec) bug_specs in 
          bug_specs, succ_specs)  
      tests) in 
  
  let succ_specs : Spec.t list = List.concat succ_specs in 
  let bug_specs  : Spec.t list = List.concat bug_specs in 

  let succ_specs, error_specs = 
    List.partition 
      (fun (spec : Spec.t) -> 
         match spec.sspecs with 
           | [ sspec ] -> (sspec.flag = Flag.Normal)
           | _  -> false 
      ) succ_specs in 

  print_to_all (Printf.sprintf "BUG SPECS:\n%s\n" (String.concat "\n" (List.filter (fun x -> x <> "") (List.map (UP.string_of_spec prog.preds) bug_specs))));
  
  print_to_all (Printf.sprintf "SUCCESSFUL SPECS:\n%s\n" (String.concat "\n" (List.filter (fun x -> x <> "") (List.map (UP.string_of_spec ~preds_printer:JSCleanUp.js_preds_printer prog.preds) succ_specs))));

  (* This is a hack to not count auxiliary functions that are bi-abduced *)
  let len_succ = List.length succ_specs in 
  let auxiliaries = List.fold_left (fun ac (spec : Spec.t) -> ac || (match spec.name with "assumeType" -> true | _ -> false)) false succ_specs in 
  let offset = if auxiliaries then 12 else 0 in 
  let len_succ = len_succ - offset in 

  print_to_all (Printf.sprintf "SUCCESS SPECS: %d\nERROR SPECS: %d\nBUG SPECS: %d" len_succ (List.length error_specs) (List.length bug_specs))

