open CCommon 
open SCommon 
open SInterpreter

module SSubst    = SVal.SSubst 
module Error     = MakeError.M(SVal.M)(SVal.SSubst)
module L         = Logging

type t = {
  name          : string; 
  id            : int; 
  params        : string list; 
  pre_state     : AbsSState.M.t; 
  post_up       : UP.t; 
  flag          : Flag.t option; 
  spec_vars     : SS.t
}


let global_results = Hashtbl.create medium_tbl_size 


let testify 
    (preds : (string, Pred.t) Hashtbl.t) (name : string) (params : string list) 
    (id : int) (pre : Asrt.t) (posts : Asrt.t list) (flag : Flag.t option) : t option * (Asrt.t * Asrt.t list) option =   
  
  (** Step 1 - normalise the precondition *)
  try (match Normaliser.normalise_assertion None None (Some (SS.of_list params)) pre with 
    | None -> None, None 
    | Some (ss_pre, subst) -> 
      (** Step 2 - spec_vars = lvars(pre)\dom(subst) -U- alocs(range(subst)) *)
      let lvars     = Asrt.lvars pre in 
      let subst_dom = SSubst.domain subst None in
      let get_aloc  = fun x -> match (x : Expr.t) with | ALoc loc -> Some loc | _ -> None in 
      let alocs     = SS.of_list (get_list_somes (List.map get_aloc (SSubst.range subst))) in 
      let spec_vars = SS.union (SS.diff lvars subst_dom) alocs in
     
      (** Step 3 - postconditions to symbolic states *)
      L.log L.Verboser (lazy (Printf.sprintf "Creating unification plan for one postcondition of %s with spec_vars: %s" 
        name (String.concat ", " (SS.elements spec_vars))));
      let posts    = List.map (fun p -> Asrt.substitution subst true p) posts in
      (* the following line is horrific - and suggests bad design - mea culpa - JFS *)
      let known_post_vars = match flag with | Some _ -> SS.singleton Flag.return_variable | None -> SS.empty in 
      let ss_posts = List.map (Normaliser.normalise_assertion None None (Some known_post_vars)) posts in 
      let ss_posts = List.map (fun (ss, _) -> ss) (get_list_somes ss_posts) in 
      let posts'   = List.map (fun post -> Asrt.star (AbsSState.M.to_assertions post)) ss_posts in 

      (** Step 4 - create a unification plan for the postconditions and s_test *)
      let known_vars    = SS.add Flag.return_variable (SS.union (SS.of_list params) spec_vars) in 
      let simple_posts  = List.map (fun post -> post, (None, None)) posts' in 
      let post_up       = UP.init known_vars SS.empty preds simple_posts in
      (match post_up with 
      | Error errs -> None, None
      | Ok post_up -> 
        let test = { name = name; id = id; params = params; pre_state = ss_pre; post_up = post_up; flag = flag; spec_vars = spec_vars } in 
        let pre' = Asrt.star (AbsSState.M.to_assertions ss_pre) in 
        Some test, Some (pre', posts')))
    with e -> None, None 


let testify_sspec 
    (preds : (string, Pred.t) Hashtbl.t) (name : string) 
    (params : string list) (id : int) (sspec : Spec.st) : t option * Spec.st option = 
  let stest, sspec' = testify preds name params id sspec.pre sspec.posts (Some sspec.flag) in 
  let sspec' = Option.map (fun (pre, posts) -> { sspec with pre = pre; posts = posts }) sspec' in 
  if (sspec.to_verify) then stest, sspec' else None, sspec' 


let testify_spec (preds : (string, Pred.t) Hashtbl.t) (spec : Spec.t) : t list * Spec.t =  
  match spec.to_verify with 
    | false -> [], spec
    | true -> 
        L.log L.Verbose (lazy ("-------------------------------------------------------------------------\n" ^ 
                        (Printf.sprintf "Creating symbolic tests for procedure %s: %d cases\n" spec.name (List.length spec.sspecs)) ^ 
                        "-------------------------------------------------------------------------"));
        let tests, sspecs = List.split (List.mapi (testify_sspec preds spec.name spec.params) spec.sspecs) in
        let tests         = get_list_somes tests in 
        let sspecs        = get_list_somes sspecs in 
        let new_spec      = { spec with sspecs = sspecs } in 
        L.log L.Verboser (lazy (Printf.sprintf "Simplified SPECS:\n%s\n" (Spec.str new_spec))); 
        tests, new_spec 

let testify_lemma (preds : (string, Pred.t) Hashtbl.t) (lemma : Lemma.t) : t list * Lemma.t =
  let test, sspec = testify preds lemma.name lemma.params 0 lemma.pre lemma.posts None in 
  let tests = Option.map_default (fun test -> [ test ]) [] test in 
  match sspec with 
      | Some (pre, posts) -> tests, { lemma with pre = pre; posts = posts }
      | None -> raise (Failure (Printf.sprintf "Could not simplify lemma %s" lemma.name)) 

let analyse_result (subst : SSubst.t) (test : t) (state : AbsSState.M.t) : bool =
  let _      = AbsSState.M.simplify state in 
  let ostat  = AbsSState.M.copy state in
  let subst  = SSubst.copy subst in 

  (* Adding spec vars in the post to the subst - these are effectively the existentials of the post *)
  List.iter 
    (fun x -> 
      if (not (SSubst.mem subst x)) then 
        SSubst.add subst x (Expr.LVar x))
    (Var.Set.elements (AbsSState.M.get_spec_vars state)); 

  (* TODO: Understand if this should be done: setup all program variables in the subst *)
  SStore.iter (AbsSState.M.get_store state) 
    (fun v value -> if (not (SSubst.mem subst v)) then SSubst.put subst v value); 
  (* Option.may (fun v_ret -> SSubst.put subst Flag.return_variable v_ret)  
    (SStore.get (SState.get_store state) Flag.return_variable); *)

  L.log L.Verbose (lazy (Printf.sprintf "Analyse result: About to unify one postcondition of %s. post: %s" test.name (UP.str test.post_up)));  
  (match AbsSState.M.unify state  subst test.post_up with 
    | true ->  
        L.log L.Verbose (lazy "Analyse result: Postcondition unified successfully");
        Hashtbl.replace global_results (test.name, test.id) true; true
    | false ->
        L.log L.Normal (lazy "Analyse result: Postcondition not unifiable.");
        Hashtbl.replace global_results (test.name, test.id) false; false) 

let make_post_subst (test : t) : SSubst.t =  
  let subst_lst = 
    List.map 
      (fun x -> 
        if (is_aloc_name x) 
          then (x, Expr.ALoc x) 
          else (x, Expr.LVar x)) 
      (SS.elements test.spec_vars) in
  let params_subst_lst = SStore.bindings (AbsSState.M.get_store (test.pre_state)) in
  let subst = SSubst.init (subst_lst @ params_subst_lst) in 
  subst 


let analyse_proc_results (subst : SSubst.t) (test : t) (flag : Flag.t) (rets : AbsSInterpreter.M.result_t list) : bool = 
  let success : bool = 
    (rets <> []) && 
    List.fold_left (fun ac result -> 
      match (result : AbsSInterpreter.M.result_t) with 
        | RFail (proc, i, state, errs) -> 
            L.log L.Verboser (lazy (Printf.sprintf 
              "VERIFICATION FAILURE: Procedure %s, Command %d\nSpec %s %d\nState:\n %s\nErrors: \n\t%s\n" 
                proc i test.name test.id (AbsSState.M.str state) (String.concat "\n\t" (List.map SError.M.str errs)))); false
        | RSucc (fl, v, state) -> 
            if (Some fl <> test.flag) then (
              let msg = lazy (
                Printf.sprintf "VERIFICATION FAILURE: Spec %s %d terminated with flag %s instead of %s\n"
                  test.name test.id (Flag.str fl) (Flag.str flag)) in 
              L.log L.Normal msg; 
              false 
            ) else if (analyse_result subst test state) then (
              let msg = lazy (
                Printf.sprintf "VERIFICATION SUCCESS: Spec %s %d terminated successfully\n" test.name test.id) in 
              L.log L.Normal msg; 
              ac 
            ) else (
              let msg = lazy (
                Printf.sprintf "VERIFICATION FAILURE: Spec %s %d - post condition not unifiable\n" test.name test.id)  in 
              L.log L.Normal msg; 
              false
            )
      ) true rets in 
    if (rets = []) then (L.log L.Normal (lazy (Printf.sprintf "ERROR: Function %s evaluates to 0 results." test.name)); exit 1);
    success


let analyse_lemma_results (subst : SSubst.t) (test : t) (rets : AbsSState.M.t list) : bool = 
  let success : bool = 
    (rets <> []) && 
    List.fold_left (fun ac final_state -> 
      if (analyse_result subst test final_state) then (
        let msg = lazy (
          Printf.sprintf "VERIFICATION SUCCESS: Spec %s %d terminated successfully\n" test.name test.id) in 
        L.log L.Normal msg; 
        ac 
      ) else (
        let msg = lazy (
          Printf.sprintf "VERIFICATION FAILURE: Spec %s %d - post condition not unifiable\n" test.name test.id)  in 
        L.log L.Normal msg; 
        false
      )) true rets in 
  if (rets = []) then (L.log L.Normal (lazy (Printf.sprintf "ERROR: Function %s evaluates to 0 results." test.name)); exit 1);
  success


let verify (prog : UP.prog) (test : t) : bool = 
  let post_subst = make_post_subst test in 
  let state'     = AbsSState.M.add_pred_defs prog.preds test.pre_state in 
  
  match test.flag with 
    | Some flag -> 
      (* TEST for procedure *)
      let rets = AbsSInterpreter.M.evaluate_proc (fun x -> x) prog test.name test.params state' in 
      L.log L.Verbose (lazy (Printf.sprintf "Verification: Concluded evaluation: %d obtained results.%s\n" 
        (List.length rets) (AbsSInterpreter.M.string_of_result rets))); 
      analyse_proc_results post_subst test flag rets 
    
    | None -> 
      let lemma = Prog.get_lemma prog.prog test.name in 
      (match lemma.proof with 
        | None       -> raise (Failure (Printf.sprintf "Lemma %s WITHOUT proof" test.name))
        | Some proof ->
          let rets = AbsSInterpreter.M.evaluate_lcmds prog proof state' in 
          analyse_lemma_results post_subst test rets) 



let verify_procs (prog : Prog.t) : unit = 

  SCommon.javert := true;

  let preds      = prog.preds in 

  let start_time = Sys.time () in 

  (** STEP 1: Get the specs to verify *)
  (* Printf.printf "Obtaining specs to verify.\n"; *)
  let specs_to_verify : Spec.t list = Prog.get_proc_specs prog in 

  (** STEP 2: Convert specs to symbolic tests *)
  let cur_time = Sys.time () in 
  (* Printf.printf "Converting symbolic tests from specs: %f\n" (cur_time -. start_time); *)
  let tests : t list = 
    List.concat (List.map 
      (fun spec -> 
        let tests, new_spec = testify_spec preds spec in
        let proc = try Hashtbl.find prog.procs spec.name with _ -> raise (Failure "DEATH") in
        Hashtbl.replace prog.procs proc.name { proc with spec = Some new_spec }; 
        tests 
      )
      specs_to_verify) in 
  
  (** STEP 3: Convert lemmas to symbolic tests *)
  let cur_time = Sys.time () in 
  (* Printf.printf "Converting symbolic tests from lemmas: %f\n" (cur_time -. start_time); *)
  let tests' : t list = 
    List.concat (List.map 
      (fun lemma -> 
        let tests, new_lemma = testify_lemma preds lemma in
        Hashtbl.replace prog.lemmas lemma.name new_lemma; 
        tests 
      )
      (Prog.get_lemmas prog)) in

   L.log L.Verbose (lazy ("-------------------------------------------------------------------------\n" ^ 
                        (Printf.sprintf "UNFOLDED and SIMPLIFIED SPECS and LEMMAS\n%s\n%s" 
                          (String.concat "\n" (List.map Spec.str (Prog.get_specs prog)))
                          (String.concat "\n" (List.map Lemma.str (Prog.get_lemmas prog)))) ^ 
                        "-------------------------------------------------------------------------"));

  (** STEP 4: Create unification plans for specs and predicates *)
  let cur_time = Sys.time () in 
  (* Printf.printf "Creating unification plans: %f\n" (cur_time -. start_time); *)
  (match UP.init_prog prog with
  | Error _ -> raise (Failure "Creation of unification plans failed.")
  | Ok prog' -> 
    (** STEP 5: Run the symbolic tests *)
    let cur_time = Sys.time () in 
    (* Printf.printf "Running symbolic tests: %f\n" (cur_time -. start_time); *)
    let success : bool = 
      List.fold_left 
        (fun ac test -> if (verify prog' test) then ac else false) 
        true (tests' @ tests) in 

    let end_time = Sys.time () in 

    let msg : string = if success then "All specs succeeded:" else "There were failures:" in 
    let msg : string = Printf.sprintf "%s %f%!" msg (end_time -. start_time) in 
      Printf.printf "%s\n" msg; L.log L.Normal (lazy msg)
  )