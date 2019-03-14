open CCommon
open SCommon
open Literal 

module L = Logging

(** General JSIL Interpreter *)
module M 
  (Val      : Val.M) 
  (Subst    : Subst.M with type vt = Val.t and type t = Val.st)
  (Store    : Store.M with type vt = Val.t) 
  (Error    : Error.M with type vt = Val.t and type st = Subst.t)
  (State    : State.M with type vt = Val.t and type st = Subst.t and type store_t = Store.t and type err_t = Error.t) = struct 
 
(* *************** *
 * Auxiliary Types *
 * *************** *)

module CallStack = CallStack.M(Val)(Store)
module External  = External.M(Val)(Subst)(Store)(State)

(** Type of configurations: state, optional predicate set, call stack, previous index, current index *)
type cconf_t = 
  | ConfErr    of string * int * State.t * Error.t list 
  | ConfCont   of State.t * CallStack.t * int * int * int 
  | ConfFinish of Flag.t  * State.vt    * State.t 
  (** Equal to Conf cont + the id of the required spec *)
  | ConfSusp   of string  * State.t * CallStack.t * int * int * int 

type conf_t = 
  | BConfErr    of Error.t list 
  | BConfCont   of State.t

type result_t = 
  | RFail    of string * int * State.t * Error.t list 
  | RSucc    of Flag.t * State.vt * State.t  


let max_branching = 50

exception State_error of (Error.t list) * State.t

(** Internal error, carrying a string description *)
exception Internal_error of string  

(** Syntax error, carrying a string description *)
exception Syntax_error of string


let string_of_single_result (res : result_t) : string =  
  match res with 
    | RFail (proc, i, state, errs) -> 
        Printf.sprintf "FAILURE TERMINATION: Procedure %s, Command %d\nErrors: %s\nFINAL STATE:\n%s" 
          proc i (String.concat ", " (List.map Error.str errs)) (State.str state)

    | RSucc (fl, v, state) ->
        Printf.sprintf "SUCCESSFUL TERMINATION: (%s, %s)\nFINAL STATE:\n%s" 
          (Flag.str fl) (Val.str v) (State.str state)


(* ******************* *
 * Auxiliary Functions *
 * ******************* *)

let get_cmd (prog : UP.prog) (cs : CallStack.t) (i : int) : string * (Annot.t * Cmd.t) = 
	let pid    = CallStack.get_cur_proc_id cs in 
	let proc   = Prog.get_proc prog.prog pid in 
  let proc   = (match proc with | Some proc -> proc | None -> raise (Failure ("Procedure " ^ pid ^ " does not exist."))) in
    pid, proc.body.(i)  


let get_predecessor (prog : UP.prog) (cs : CallStack.t) (prev : int) (i : int) : int = 
	let pid = CallStack.get_cur_proc_id cs in 
	try Hashtbl.find prog.prog.predecessors (pid, prev, i)
		with _ ->  raise (Failure (Printf.sprintf "Undefined predecessor: %s %d %d" pid prev i)) 

let update_store (state : State.t) (x : string) (v : Val.t) : State.t = 
  let store  = State.get_store state in 
  let _      = Store.put store x v in 
  let state' = State.set_store state store in 
    state' 

let eval_subst_list 
    (state     : State.t)
    (subst_lst : (string * (string * Expr.t) list) option) : (string * (string * Val.t) list) option = 
  match subst_lst with 
    | None -> None 
    | Some (lab, subst_lst) -> 
        let subst_lst' = 
          List.map (fun (x, e) -> x, State.eval_expr state e) subst_lst in 
      Some (lab, subst_lst')

let rec protected_get_cell 
    (prog    : UP.prog) 
    (state   : State.t)  
    (e1      : Expr.t) 
    (e2      : Expr.t) 
    (err_msg : string) : (State.t * Val.t * Val.t * (Val.t option)) list =

  let loc, prop =
    try State.eval_expr state e1, State.eval_expr state e2
    with State.Internal_State_Error (errs, s) -> raise (State_error (errs, s))
    in

  match State.get_cell state loc prop with 
    | GCSucc rets -> rets 
    | GCFail errs -> raise (State_error (errs, state)) 


let make_eval_expr state   =
   fun e -> (try State.eval_expr state e
             with State.Internal_State_Error(errs, s) -> raise (State_error(errs, s)))

let print_configuration (cmd : (Annot.t * Cmd.t)) (state : State.t)  (cs : CallStack.t) (i : int) (b_counter : int) : unit = 
  let annot, cmd = cmd in
  let msg = (lazy (Printf.sprintf
    "------------------------------------------------------\n--%s: %i--\nTIME: %f\nCMD: %s\nBRANCHING: %d\n\n%s\n------------------------------------------------------\n"
    (CallStack.get_cur_proc_id cs) i (Sys.time()) (Cmd.str "" 0 cmd) b_counter (State.str state) )) in 
  L.log L.Normal msg


let print_lconfiguration (lcmd : LCmd.t) (state : State.t) : unit = 
  let msg = (lazy (Printf.sprintf
    "------------------------------------------------------\nTIME: %f\nLCMD: %s\n\n%s\n------------------------------------------------------\n"
    (Sys.time()) (LCmd.str lcmd) (State.str state) )) in 
  L.log L.Normal msg


(* ************** *
 * Main Functions *
 * ************** *)

(**
    Evaluation of logic commands

    @param prog JSIL program
    @param lcmd Logic command to be evaluated
    @param state Current state
    @param preds Current predicate set
    @return List of states/predicate sets resulting from the evaluation
  *)
  let rec evaluate_lcmd 
      (prog   : UP.prog)
      (lcmd   : LCmd.t) 
      (state  : State.t) : State.t list =
    
    let eval_expr = make_eval_expr state in

    print_lconfiguration lcmd state; 

    match lcmd with
    | AssumeType (x, t) -> 
        (match Val.from_expr (LVar x) with 
          | Some v_x -> 
            (match State.assume_t state v_x t with 
            | Some state' -> [ state' ]  
            | _ -> raise (Failure (Printf.sprintf "ERROR: AssumeType: Cannot assume type %s for variable %s." (Type.str t) x)))
          | _ -> raise (Failure (Printf.sprintf "ERROR: AssumeType: Variable %s cannot be turned into a value." x)))
    
    | Assume f -> 
        let store_subst = Store.to_ssubst (State.get_store state) in 
        let f'          = Formula.substitution store_subst true f in  
        (* Printf.printf "Assuming %s\n" (Formula.str f'); *)
        let fos         = 
          if !SCommon.bi 
            then (
              let fos = Formula.get_disjuncts f' in 
              match fos with 
                | []     -> [] 
                | [ f' ] -> [ f', state ]
                | f' :: other_fos -> 
                  let new_fos_states = List.map (fun f'' -> f'', (State.copy state)) other_fos in 
                  (f', state) :: new_fos_states 
            ) else [ f', state ] in  
        (* Printf.printf "Considering the following disjuncts: %s\n" *)
          (String.concat "; " (List.map (fun (f, _) -> Formula.str f) fos)); 
        List.concat (List.map (fun (f'', state)  -> 
          match State.assume_a state [ f'' ] with 
          | Some state' -> [ state' ]
          | _ -> (* Printf.printf "WARNING: ASSUMING FALSE\n"; *) []
        ) fos) 
      (*
        (match State.assume_a state [ f' ] with 
          | Some state' -> [ state' ]
          | _ -> (* Printf.printf "WARNING: ASSUMING FALSE\n"; *) []) *)
    
    | SpecVar xs -> [ State.add_spec_vars state (Var.Set.of_list xs) ]
    
    | FreshLVar (x, s) -> 
       (* I need to evaluate the expression - it needs to be a real string *)
       let new_lvar  = fresh_lvar () ^ s in
       let state'    = State.add_spec_vars state (Var.Set.of_list [ new_lvar ]) in 
       let v         = eval_expr (LVar new_lvar) in 
       let state''   = update_store state' x v in 
       [ state'' ]

    | Assert f -> 
        let store_subst = Store.to_ssubst (State.get_store state) in 
        let f'          = Formula.substitution store_subst true f in  
        (match State.assert_a state [ f' ] with 
        | true -> [ state ] 
        | false -> 
          let err : Error.t = ESpec ([], Not f', [ [ MPF f' ]]) in 
          let failing_model = State.sat_check_f state [ Not f' ] in 
          let fm_str        = Option.map_default (fun subst -> Subst.str subst) "CANNOT CREATE MODEL" failing_model in 
          let msg           = Printf.sprintf "Assert failed with argument %s.\nFailing Model:\n\t%s\n" (Formula.str f') fm_str in 
          if (not !SCommon.bi) then (Printf.printf "%s" msg); 
          L.log L.Normal (lazy msg); 
          raise (State_error ([ err ], state)))
    
    | Macro (name, args) -> 
        let macro = Macro.get prog.prog.macros name in 
        (match macro with 
        | None -> 
          L.log L.Verboser (lazy (Printf.sprintf "Current MACRO TABLE:\n%s\n" (Macro.str_of_tbl prog.prog.macros))); 
          raise (Failure (Printf.sprintf "NO MACRO found when executing: %s" (LCmd.str lcmd)))
        | Some macro -> 
          let lcmds = Macro.expand_macro macro args in 
            evaluate_lcmds prog lcmds state)

    (* We have to understand what is the intended semantics of the logic if *)
    | If (e, lcmds_t, lcmds_e) -> 
        let ve = eval_expr (Expr.UnOp (Not, e)) in 
        if (State.sat_check state ve)
          then evaluate_lcmds prog lcmds_e state
          else evaluate_lcmds prog lcmds_t state

    | Branch fof -> 
        let state' = State.copy state in 
        let state  = Option.map_default (fun x -> [ x ]) [] (State.assume_a state [ fof ]) in 
        let state' = Option.map_default (fun x -> [ x ]) [] (State.assume_a state' [ (Not fof) ]) in
        state @ state' 

    | SL sl_cmd -> State.evaluate_slcmd prog sl_cmd state 

  and evaluate_lcmds
    (prog    : UP.prog)
    (lcmds   : LCmd.t list) 
    (state   : State.t) : State.t list =
  
    match lcmds with 
    | [] -> [ state ] 
    | lcmd :: rest_lcmds -> 
      let rets = evaluate_lcmd prog lcmd state in 
      List.concat (List.map (fun state -> evaluate_lcmds prog rest_lcmds state) rets)



(**
  Evaluation of basic commands

  @param prog JSIL program
  @param bcmd Basic command to be evaluated
  @param state Current state
  @param preds Current predicate set
  @return List of states/predicate sets resulting from the evaluation
*)
let evaluate_bcmd 
    (prog   : UP.prog)
    (bcmd   : BCmd.t) 
    (state  : State.t) : State.t list =
	
  let store     = State.get_store state in
	let eval_expr = make_eval_expr state in 
  let protected_get_cell = protected_get_cell prog in 

	match bcmd with
	| Skip -> [ state ] 

	| Assignment (x, e) ->
		let v      = eval_expr e in 
    let state' = update_store state x v in 
		  [ state' ]

	| New (x, loc, metadata) ->
    let l_val       = Option.map eval_expr loc in    
		let m_val       = Option.map_default eval_expr (Val.from_literal Null) metadata in		
		let loc, state' = State.alloc state l_val m_val in 
		let state''     = update_store state' x loc in
		  [ state'' ] 

	| Lookup (x, e1, e2) ->
    List.map 
			(fun (state', loc, prop, pval) -> 
			  match pval with 
				  | Some pval -> update_store state' x pval  
				  | None -> 
              let err : Error.t = EResource [ MCell (loc, prop) ] in 
              raise (State_error ([ err ], state)))
			(protected_get_cell state e1 e2 "Lookup") 

	| Mutation (e1, e2, e3) ->
		let v = eval_expr e3 in
		List.map 
			(fun (state', loc, prop, _) -> 
				State.set_cell state' loc prop (Some v)
			) (protected_get_cell state e1 e2 "Mutation")

	| Delete (e1, e2) ->
		List.map 
			(fun (state', loc, prop, _) -> 
				State.set_cell state' loc prop None 
			) (protected_get_cell state e1 e2 "Delete") 

	| DeleteObj e ->
		[ State.delete_object state e ]  

	| HasField (x, e1, e2) ->
    List.map 
			(fun (state', _, _, pval) -> 
				match pval with 
			  | Some pval -> update_store state' x (Val.from_literal (Bool true)) 
				| None      -> update_store state' x (Val.from_literal (Bool false))) 
			(protected_get_cell state e1 e2 "HasField") 

	| GetFields (x, e) ->
		let props_v = State.get_domain state (eval_expr e) in 
    (match props_v with 
    | GDSucc [ state', props_v ] -> [ update_store state' x props_v ]
    | GDFail errs -> raise (State_error (errs, state)))

	| MetaData (x, e) ->
    let loc = eval_expr e in 
    (match State.get_metadata state loc with 
      | GMSucc [ ] -> L.log L.Verboser (lazy (Printf.sprintf "SOY BANANAS!!!"));  raise (Failure "BANANAS!!!")
      | GMSucc [ state', _, vm ] -> [ update_store state' x vm ] 
      | GMFail errs -> raise (State_error (errs, state))
    )
	
	| _ -> raise (Internal_error "Basic command not supported!")

(**
  Evaluation of commands

  @param prog JSIL program
  @param state Current state
  @param preds Current predicate set
  @param cs Current call stack
  @param prev Previous index
  @param i Current index
  @return List of configurations resulting from the evaluation
*)
let evaluate_cmd 
	(prog      : UP.prog)
	(state     : State.t)
	(cs        : CallStack.t)
	(prev      : int)
	(i         : int)
  (b_counter : int) : cconf_t list = 

  (* State simplification *)
  (if (!javert) then let _ = State.simplify state in ()); 
  
  let store                = State.get_store state in 
  let eval_expr            = make_eval_expr state in 
  let proc_name, annot_cmd = get_cmd prog cs i in  
  let _, cmd    = annot_cmd in 

  let vtrue  = Val.from_literal (Bool true) in
  let vfalse = Val.from_literal (Bool false) in

  exec_cmds := !exec_cmds + 1;
  
  let first_time = UP.first_time_running prog proc_name i in 
  UP.update_coverage prog proc_name i; 
  print_configuration annot_cmd state cs i b_counter;

  let evaluate_procedure_call x pid v_args j subst = 
    let pid = 
      (match Val.to_literal pid with 
      | Some (String pid) -> pid 
      | Some other_thing  -> 
          let err = [ Error.EProc pid ] in 
          raise (State_error (err, state))
      | None -> raise (Internal_error "Procedure Call Error - unlifting procedure ID failed")) in 
    
    let proc   = Prog.get_proc prog.prog pid in 
    let spec   = Hashtbl.find_opt prog.specs pid in 
    let params = 
      match proc, spec with 
        | Some proc, _ -> Proc.get_params proc
        | None, Some spec -> Spec.get_params spec.spec             
        | _ -> raise (State_error ([Error.EProc (Val.from_literal (String pid))], state)) in
    let prmlen = List.length params in 

    let args   = Array.make prmlen (Val.from_literal Undefined) in 
    let _      = List.iteri (fun i v_arg -> if (i < prmlen) then (args.(i) <- v_arg)) v_args in 
    let args   = Array.to_list args in 
    
    (match spec with 
      | Some spec -> 
          let subst = eval_subst_list state subst in 
          L.log L.Verboser  (lazy (Printf.sprintf "ABOUT TO USE THE SPEC OF %s IN BIABDUCTION!!!\n" pid)); 
          let rets : (State.t * Val.t option * Flag.t) list = State.run_spec spec state args subst in 
           L.log L.Verboser (lazy (Printf.sprintf "Run_spec returned %d Results!!!\n" (List.length rets))); 
          let b_counter = if (List.length rets > 1) then b_counter + 1 else b_counter in 
          List.map (fun (ret_state, v_ret, fl) -> 
            match v_ret, fl, j with 
              | Some v_ret, Flag.Normal, _ -> 
                  let ret_state = update_store ret_state x v_ret in
                  ConfCont (ret_state, (CallStack.copy cs), i, i+1, b_counter)
              
              | Some v_ret, Flag.Error, Some j ->
                  let ret_state = update_store ret_state x v_ret in 
                  ConfCont (ret_state, (CallStack.copy cs), i, j, b_counter)

              | Some v_ret, Flag.Error, None -> 
                  let msg = Printf.sprintf "SYNTAX ERROR: No error label provided when calling procedure %s" pid in 
                  L.log L.Normal (lazy msg);
                  raise (Syntax_error msg)

              | None, _, _ -> 
                  let msg = Printf.sprintf "SYNTAX ERROR: The postcondition of %s does not define the return variable" pid in 
                  L.log L.Normal (lazy msg);
                  raise (Syntax_error msg)
          ) rets
    
     | _ -> 
        if (Hashtbl.mem prog.prog.bi_specs pid) then (
          [ ConfSusp (pid, state, cs, prev, i, b_counter) ]
        ) else (
          let new_store  = Store.init (List.combine params args) in
          let old_store  = State.get_store state in 
          let state'     = State.set_store state new_store in 
          let cs'        = (pid, v_args, Some old_store, x, i, i+1, j) :: cs in 
          [ ConfCont (state', cs', -1, 0, b_counter) ] 
        )
    ) in 
          
  match cmd with 
  | Basic bcmd ->
      let resulting_states : State.t list = evaluate_bcmd prog bcmd state in
      let b_counter = if (List.length resulting_states > 1) then b_counter + 1 else b_counter in 
      List.map (fun state -> ConfCont (state, cs, i, i+1, b_counter)) resulting_states

  | Logic lcmd -> 
      let resulting_states : State.t list = evaluate_lcmd prog lcmd state in 
      (match lcmd with 
          | SL (Invariant _) when (not first_time) -> [] 
          | _ ->  
            let b_counter = if (List.length resulting_states > 1) then b_counter + 1 else b_counter in 
            List.map (fun state -> ConfCont (state, cs, i, i+1, b_counter)) resulting_states)


  | Goto j -> [ ConfCont (state, cs, i, j, b_counter) ] 

  (* When executing the guarded goto, we copy only when needed and parallelise *)
  | GuardedGoto (e, j, k) ->
      let vt  = eval_expr e in      
      let lvt = Val.to_literal vt in 
      let vf = (match lvt with 
        | Some (Bool true)  -> vfalse
        | Some (Bool false) -> vtrue
        | _ -> eval_expr (UnOp (Not, e))) in
      L.log L.Verboser (lazy (Printf.sprintf "Evaluated expressions: %s, %s" (Val.str vt) (Val.str vf)));
      let can_put_t, can_put_f = (match lvt with 
        | Some (Bool true)  -> true ,false
        | Some (Bool false) -> false, true
        | _ -> State.sat_check state vt, State.sat_check state vf) in 
      let sp_t, sp_f = (match can_put_t, can_put_f with 
        | false, false -> [], []
        | true,  false -> List.map (fun x -> x, j) (State.assume state vt), []
        | false, true -> [], List.map (fun x -> x, k) (State.assume state vf)
        | true,  true -> 
          let state' = State.copy state in 
          List.map (fun x -> x, j) (State.assume state vt), List.map (fun x -> x, k) (State.assume state' vf)
      ) in 
      let sp = sp_t @ sp_f in 
      
      let b_counter = if (List.length sp > 1) then b_counter + 1 else b_counter in 
      let result = List.mapi (fun j (state, next) -> ConfCont (state, (if j = 0 then cs else CallStack.copy cs), i, next, b_counter)) sp in 
        (match (List.length result = 2) && (!act_threads < !max_threads) with
        | true -> 
            act_threads := !act_threads + 1;
            let pid = Unix.fork () in 
            (match pid with 
              | 0 -> [ List.hd result ]
              | n -> CCommon.children := n :: !CCommon.children; List.tl result
            )
        | false -> result)

  | PhiAssignment lxarr ->
      let j = get_predecessor prog cs prev i in 
      let state' = List.fold_left (fun state (x, x_arr) ->
        let e = List.nth x_arr j in
        let v = eval_expr e in 
          update_store state x v) state lxarr in
        [ ConfCont (state', cs, i, i+1, b_counter) ]

  | Call (x, e, args, j, subst) ->
      let pid = eval_expr e in 
      let v_args = List.map eval_expr args in 
      let result = evaluate_procedure_call x pid v_args j subst in 
        result

  | ECall (x, pid, args, j) ->
      let pid = (match pid with | PVar pid -> pid) in
      let v_args = List.map eval_expr args in 
        List.map 
          (fun (state, cs, i, j) -> ConfCont (state, cs, i, j, b_counter))
          (External.execute prog.prog state cs i x pid v_args j)

  | Apply (x, pid_args, j) -> 
      let v_pid_args = eval_expr pid_args in 
      let v_pid_args_list = Val.to_list v_pid_args in 
      (match v_pid_args_list with 
      | Some v_pid_args_list ->
          let pid = List.hd v_pid_args_list in 
          let v_args = List.tl v_pid_args_list in 
            evaluate_procedure_call x pid v_args j None 
      | None -> raise (Failure (Printf.sprintf "Apply not called with a list: %s" (Val.str v_pid_args))))

  | Arguments x -> 
      let args = CallStack.get_cur_args cs in 
      let args = Val.from_list args in 
      let state' = update_store state x args in 
        [ ConfCont (state', cs, i, i+1, b_counter) ]
		
  | ReturnNormal -> 
      let v_ret = Store.get store Flag.return_variable in
      let result = (match v_ret, cs with 
      | None, _  -> raise (Failure "nm_ret_var not in store (normal return)")
      | Some v_ret, (_, _, None, _, _, _, _) :: _ -> [ ConfFinish (Normal, v_ret, state) ]
      | Some v_ret, (_, _, Some old_store, x, prev', j, _) :: cs' -> 
          let state'  = State.set_store state old_store in 
          let state'' = update_store state' x v_ret in
          [ ConfCont (state'', cs', prev', j, b_counter) ] 
      | _ -> raise (Failure "Malformed callstack")) in 
        L.log L.Verboser (lazy "Returning.");
        result

  | ReturnError -> 
      let v_ret = Store.get store Flag.return_variable in
      (match v_ret, cs with 
      | None, _  -> raise (Failure "Return variable not in store (error return) ")
      | Some v_ret, (_, _, None, _, _, _, _) :: _ -> [ ConfFinish (Error, v_ret, state) ]
      | Some v_ret, (pid, _, Some old_store, x, prev', _, Some j) :: cs' ->
          let state'  = State.set_store state old_store in 
          let state'' = update_store state' x v_ret in
          [ ConfCont (state'', cs', prev', j, b_counter) ] 
      | _ -> raise (Failure "Malformed callstack"))
				
  | _ -> raise (Failure "Command not supported!")


let protected_evaluate_cmd 
  (prog      : UP.prog)
  (state     : State.t)
  (cs        : CallStack.t)
  (prev      : int)
  (i         : int) 
  (b_counter : int) : cconf_t list = 

  try 
    evaluate_cmd prog state cs prev i b_counter
  with 
    | State_error (errs, state) 
    | State.Internal_State_Error (errs, state) -> 
    (* Return: current procedure name, current command index, the state, and the associated errors *)
    let proc = CallStack.get_cur_proc_id cs in 
    [ ConfErr (proc, i, state, errs) ]



(**
  Iterative evaluation of commands

  @param prog JSIL program
  @param confs Current configurations
  @param results Current evaluation outcomes
  @return List of final configurations
*)
let rec evaluate_cmd_iter 
  (ret_fun      : (result_t -> 'a))
  (retry        : bool)
	(prog         : UP.prog)
  (hold_results : 'a list)
  (on_hold      : (cconf_t * string) list)
	(confs        : cconf_t list)
	(results      : result_t list) : 'a list =
  
  let f = evaluate_cmd_iter ret_fun retry prog hold_results on_hold in 

  match confs with 
  | [] ->
    let results = List.map ret_fun results in  
    let results = hold_results @ results in 
    if (not retry) then (
       results 
    ) else (
      L.log L.Verboser (lazy (Printf.sprintf "Relaunching suspended confs")); 
      let hold_confs = List.filter (fun (_, pid) -> Hashtbl.mem prog.specs pid) on_hold in 
      let hold_confs = List.map (fun (conf, _) -> conf) hold_confs in 
      evaluate_cmd_iter ret_fun false prog results [] hold_confs [ ]
    )
      
  | (ConfCont (state, cs, prev, i, b_counter)) :: rest_confs 
        when (b_counter < max_branching) -> 
      let next_confs = protected_evaluate_cmd prog state cs prev i b_counter in 
      f (next_confs @ rest_confs) results 
  
  | (ConfCont (state, cs, prev, i, b_counter)) :: rest_confs -> 
      let _, annot_cmd = get_cmd prog cs i in  
      Printf.printf "WARNING: MAX BRANCHING STOP: %d.\n" b_counter; 
      L.log L.Verboser (lazy (Printf.sprintf "Stopping Symbolic Execution due to MAX BRANCHING with %d. STOPPING CONF:\n" b_counter));
      print_configuration annot_cmd state cs i b_counter;
      f rest_confs results 

  | (ConfErr (proc, i, state, errs)) :: rest_confs -> 
      let errs = Error.sanitise errs in 
      let result = RFail (proc, i, state, errs) in 
      f rest_confs (result :: results)

  | (ConfFinish (fl, v, state)) :: rest_confs -> 
      let result = RSucc (fl, v, state) in 
      f rest_confs (result :: results)

  | (ConfSusp (fid, state, cs, prev, i, b_counter)) :: rest_confs 
        when retry -> 
    let conf = ConfCont (state, cs, prev, i, b_counter) in  
    L.log L.Verboser (lazy (Printf.sprintf "Suspending a computation that was trying to call %s" fid)); 
    evaluate_cmd_iter ret_fun retry prog  hold_results ((conf, fid) :: on_hold) rest_confs results

  | _ :: rest_confs -> f rest_confs results 


(**
  Evaluation of procedures

  @param prog JSIL program
  @param name Identifier of the procedure to be evaluated
  @param params Parameters of the procedure to be evaluated
  @state state Current state
  @preds preds Current predicate set
  @return List of final configurations
*)
let evaluate_proc 
    (ret_fun : (result_t -> 'a))
    (prog     : UP.prog) 
    (name     : string) 
    (params   : string list) 
    (state    : State.t) : 'a list = 

  L.log L.Normal (lazy (
    "*******************************************\n" ^
    "*** Executing procedure: " ^ name ^ "\n" ^
    "*******************************************\n"
  ));

  let store = State.get_store state in 
  let args  = 
    List.map 
      (fun x -> 
        match Store.get store x with 
          | Some v_x -> v_x 
          | None -> raise (Failure "Symbolic State does NOT contain formal parameter"))
      params in  

  let cs   : CallStack.t = [ (name, args, None, "out", -1, -1, (Some (-1))) ] in 
  let conf : cconf_t     = ConfCont (state, cs, (-1), 0, 0) in 
  evaluate_cmd_iter ret_fun true prog [] [] [ conf ] [ ]   


(**
  Evaluation of programs

  @param prog Target JSIL program
  @return Final configurations
*)
let evaluate_prog (prog : UP.prog) : result_t list =
	Random.self_init();
  let ret_fun = fun x -> x in 
  let initial_cs   = [ ("main", [], None, "out", -1, -1, (Some (-1))) ] in 
  let initial_conf = ConfCont ((State.init (Some prog.preds)), initial_cs, -1, 0, 0) in  
	evaluate_cmd_iter ret_fun true prog [] [] [ initial_conf ] [] 

(**
  Configuration printer

  @param result Target configuration
  @return String representation of the configuration
*)
let string_of_result (result : result_t list) : string = 
  
  let f i res = 
    Printf.sprintf "RESULT: %d.\n%s" i (string_of_single_result res) in 
  
  String.concat "" (List.mapi f result)

end 
