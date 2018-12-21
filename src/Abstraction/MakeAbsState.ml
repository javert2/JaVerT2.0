open CCommon
open SCommon
open Literal 
open AbsState

module L = Logging

module M 
  (Val      : Val.M) 
  (Subst    : Subst.M with type vt = Val.t and type t = Val.st)
  (Store    : Store.M with type vt = Val.t) 
  (Error    : Error.M with type vt = Val.t and type st = Subst.t)
  (State    : State.M with type vt = Val.t and type st = Subst.t and type store_t = Store.t and type err_t = Error.t) 
  (Preds    : Preds.M with type vt = Val.t and type st = Subst.t)
    : (AbsState.M with type vt = Val.t and type st = Subst.t and type store_t = Store.t and type state_t = State.t and type preds_t = Preds.t and type err_t = Error.t) = struct  

  type t       = State.t * Preds.t * UP.preds_tbl_t
  type vt      = Val.t 
  type st      = Subst.t 
  type store_t = Store.t 
  type abs_t   = Preds.abs_t
  type state_t = State.t 
  type preds_t = Preds.t 
  type err_t   = Error.t 

  exception Internal_State_Error of (err_t list) * t

  module Unifier = MakeUnifier.M(Val)(Subst)(Store)(Error)(State)(Preds)

  type gc_ret = 
    | GCSucc  of (t * Val.t * Val.t * (Val.t option)) list
    | GCFail  of Error.t list  

  type gd_ret = 
    | GDSucc  of (t * Val.t) list
    | GDFail  of Error.t list  

  type gm_ret = 
    | GMSucc  of (t * Val.t * Val.t) list 
    | GMFail  of Error.t list 

  type gp_ret = 
    | GPSucc  of (t * (Val.t list)) list 
    | GPFail  of Error.t list 

  type u_res = 
    | UWTF    
    | USucc   of t
    | UFail   of err_t list  


  let init (pred_defs : UP.preds_tbl_t option) : t = 
    let empty_pred_defs : UP.preds_tbl_t  = UP.init_pred_defs () in 
    let new_pred_defs : UP.preds_tbl_t = Option.default empty_pred_defs pred_defs in 
    State.init pred_defs, Preds.init [], new_pred_defs

  let get_pred_defs (state : t) : UP.preds_tbl_t option = 
    let _, _, pred_defs = state in  
    Some pred_defs

  let initialise (state : State.t) (preds : Preds.t) (pred_defs : UP.preds_tbl_t option) : t = 
    let pred_defs = Option.default (UP.init_pred_defs ()) pred_defs in 
    state, preds, pred_defs

  let eval_expr (astate : t) (e : Expr.t) = 
    let state, _, _ = astate in 
    try State.eval_expr state e
    with State.Internal_State_Error (errs, s) -> raise (Internal_State_Error (errs, astate))
  
  let get_store (astate : t) : Store.t = 
    let state, _, _ = astate in 
    State.get_store state
  
  let set_store (astate : t) (store : Store.t) : t = 
    let state, preds, pred_defs = astate in 
    let state' = State.set_store state store in 
    (state', preds, pred_defs)

  let alloc (astate : t) (loc : Val.t option) (m : Val.t) : (Val.t * t) = 
    let state, preds, pred_defs = astate in 
    let loc', state' = State.alloc state loc m in  
    (loc', (state', preds, pred_defs))

  let to_loc (astate : t) (v : Val.t) : (t * Val.t) option = 
    let state, preds, pred_defs = astate in 
    match State.to_loc state v with 
      | Some (state', loc) -> Some ((state', preds, pred_defs), loc)
      | None -> None 

  let rec get_cell ?(remove : bool option) (astate : t) (loc : Val.t) (prop : Val.t) : gc_ret  = 
    let f (_, astate) = get_cell ?remove:remove astate loc prop in 
    let remove   = Option.default false remove in  

    let merge_gc_results (rets : gc_ret list) : gc_ret = 
      let ret_succs, ret_fails = List.partition (fun ret -> match ret with | GCSucc _ -> true | _ -> false) rets in
      if (ret_fails <> []) 
        then (
          let errs = List.map (fun ret -> match ret with | GCFail errs -> errs | _ -> []) ret_fails in 
          GCFail (List.concat errs) 
        ) else (
          let rets = List.map (fun ret -> match ret with | GCSucc rets -> rets | _ -> []) ret_succs in 
          GCSucc (List.concat rets)
        ) in 

    let state, preds, pred_defs = astate in 
    match !SCommon.unfolding, remove, State.get_cell ~remove:remove state loc prop with 
      | _, _, GCSucc rets        -> GCSucc (List.map (fun (state', loc', prop', v) -> ((state', preds, pred_defs), loc', prop', v)) rets)
      | _, true, GCFail errs   
      | false, _, GCFail errs    -> GCFail errs 
      | true, false, GCFail errs ->     
          let next_states, worked = Unifier.unfold_with_vals astate [ loc ] in 
          if worked then (
            let rets = List.map f next_states in 
            merge_gc_results rets 
          ) else GCFail errs  


  let set_cell (astate : t) (loc : Val.t) (prop : Val.t) (v : Val.t option) : t = 
    let state, preds, pred_defs = astate in 
    let state' = State.set_cell state loc prop v in 
    state', preds, pred_defs 

  let rec get_domain ?(expected_props : vt option) ?(remove : bool option) (astate : t) (loc : Val.t) : gd_ret = 
    let f (_, astate) = get_domain ?expected_props:expected_props ?remove:remove astate loc in 
    let remove   = Option.default false remove in  

    let merge_gd_results (rets : gd_ret list) : gd_ret = 
      let ret_succs, ret_fails = List.partition (fun ret -> match ret with | GDSucc _ -> true | _ -> false) rets in
      if (ret_fails <> []) 
        then (
          let errs = List.map (fun ret -> match ret with | GDFail errs -> errs | _ -> []) ret_fails in 
          GDFail (List.concat errs) 
        ) else (
          let rets = List.map (fun ret -> match ret with | GDSucc rets -> rets | _ -> []) ret_succs in 
          GDSucc (List.concat rets)
        ) in 

    let state, preds, pred_defs = astate in 
    match !SCommon.unfolding, remove, State.get_domain ~remove:remove state loc with 
      | _, _, GDSucc rets  -> GDSucc (List.map (fun (state', v) -> (state', preds, pred_defs), v) rets)

      | _, true, GDFail errs  
      | false, _, GDFail errs  -> GDFail errs
      
      | true, false, GDFail errs -> 
          let next_states, worked = Unifier.unfold_with_vals astate [ loc ] in 
          if worked then (
            let rets = List.map f next_states in 
            merge_gd_results rets 
          ) else  GDFail errs  
        
  
  let set_domain (astate : t) (loc : Val.t) (dom : Val.t) : t = 
    let state, preds, pred_defs = astate in 
    (State.set_domain state loc dom), preds, pred_defs 
  
  let rec get_metadata ?(remove : bool option) (astate : t) (loc : Val.t) : gm_ret = 
    let f (_, astate)  = get_metadata ?remove:remove astate loc in 
     let remove   = Option.default false remove in  

    let merge_gm_results (rets : gm_ret list) : gm_ret = 
      let ret_succs, ret_fails = List.partition (fun ret -> match ret with | GMSucc _ -> true | _ -> false) rets in
      if (ret_fails <> []) 
        then (
          let errs = List.map (fun ret -> match ret with | GMFail errs -> errs | _ -> []) ret_fails in 
          GMFail (List.concat errs) 
        ) else (
          let rets = List.map (fun ret -> match ret with | GMSucc rets -> rets | _ -> []) ret_succs in 
          GMSucc (List.concat rets)
        ) in 

    let state, preds, pred_defs = astate in 
    match !SCommon.unfolding, remove, State.get_metadata ~remove:false state loc with 
    | _, _, GMSucc rets        -> GMSucc (List.map (fun (state', loc, v) -> (state', preds, pred_defs), loc, v) rets)
    | _, true, GMFail errs   
    | false, _, GMFail errs     -> GMFail errs 
    | true, false, GMFail errs  -> 
        let next_states, worked = Unifier.unfold_with_vals astate [ loc ] in 
        if worked then (
          let rets = List.map f next_states in 
          merge_gm_results rets 
        ) else GMFail errs  
  
  let set_metadata (astate : t) (loc : Val.t) (m : Val.t) : t = 
    let state, preds, pred_defs = astate in 
    (State.set_metadata state loc m), preds, pred_defs
  
  (* This requires !!MAJOR!! changes *)
  let delete_object (astate : t) (loc : Expr.t) : t = 
    let state, preds, pred_defs = astate in 
    (State.delete_object state loc), preds, pred_defs 

  let assume (astate : t) (v : Val.t) : t list = 
    let state, preds, pred_defs = astate in 
    List.concat (List.map (fun state -> 
      let astate' = state, preds, pred_defs in 
      (match !SCommon.unfolding, Val.to_expr v with
        | _, (Lit (Bool true)) -> [ astate' ] 
        | false, _ -> [ astate' ]
        | true, _ -> 
          let next_states, worked = Unifier.unfold_with_vals astate' [ v ] in
          if (not worked) 
            then [ astate' ]
            else List.map (fun (_, astate) -> astate) next_states)
    ) (State.assume state v))

  let assume_a (astate : t) (fs : Formula.t list) : t option = 
    let state, preds, pred_defs = astate in 
    match State.assume_a state fs with 
      | Some state -> Some (state, preds, pred_defs)
      | None -> None 

  let assume_t (astate : t) (v : Val.t) (t : Type.t) : t option = 
    let state, preds, pred_defs = astate in 
    match State.assume_t state v t with 
      | Some state -> Some (state, preds, pred_defs)
      | None -> None 
  
  let sat_check (astate : t) (v : Val.t) : bool = 
    let state, _, _ = astate in 
    State.sat_check state v 
  
  let sat_check_f (astate : t) (fs : Formula.t list) : Subst.t option = 
    let state, _, _ = astate in 
    State.sat_check_f state fs 
  
  let assert_a (astate : t) (fs : Formula.t list) : bool = 
    let state, _, _ = astate in 
    State.assert_a state fs 
     
  let equals (astate : t) (v1 : Val.t) (v2 : Val.t) : bool = 
    let state, _, _ = astate in 
    State.equals state v1 v2 

  let get_type (astate : t) (v : Val.t) : Type.t option = 
    let state, _, _ = astate in 
    State.get_type state v  

  let copy (astate : t) : t = 
    let state, preds, pred_defs = astate in  
    State.copy state, Preds.copy preds, pred_defs

  let rec simplify ?(kill : bool option) (astate : t) : Subst.t =
    let kill            = Option.default true kill in 
    let state, preds, _ = astate in 
    let subst           = State.simplify ~kill:kill state in
    Preds.substitution_in_place subst preds; 
    subst 
  
  let simplify_val (astate : t) (v : Val.t) : Val.t = 
    let state, _, _ = astate in 
    State.simplify_val state v 

  let str (astate : t) : string =
    let state, preds, _ = astate in  
    let state_str = State.str state in 
    let preds_str =  Printf.sprintf "\nPREDICATES: %s\n" (Preds.str preds) in 
    state_str ^ preds_str 

  let add_spec_vars (astate : t) (vs : Var.Set.t) : t = 
    let state, preds, pred_defs = astate in  
    let state' = State.add_spec_vars state vs in 
    (state', preds, pred_defs)

  let get_spec_vars (astate : t) : Var.Set.t = 
    let state, _, _ = astate in  
    State.get_spec_vars state 

  let get_lvars (astate : t) : Var.Set.t = 
    let state, _, _ = astate in  
    State.get_lvars state 

  let get_folded_pred 
      (astate    : t) 
      (pname     : string) 
      (vs_ins    : Val.t list) : gp_ret = 
    
    let state, preds, pred_defs = astate in 
    let pred         = UP.get_pred_def pred_defs pname in 
    let pred_def     = pred.pred in
    let pred_pure    = pred.pure in
    (match Preds.get_pred pred_pure preds pname vs_ins pred_def.ins (State.equals state) with 
      | Some (_, vs) -> 
           let vs_outs = Pred.out_args pred_def vs in
           GPSucc [ (state, preds, pred_defs), vs_outs ]
      | _ -> GPFail [ ESpec ( vs_ins, True, []) ] )

  let to_assertions ?(to_keep : SS.t option) (astate : t) : Asrt.t list = 
    let state, preds, _ = astate in
    let s_asrts = State.to_assertions ?to_keep:to_keep state in   
    let p_asrts = Preds.to_assertions preds in 
      List.sort Asrt.compare (p_asrts @ s_asrts)

 let substitution_in_place (subst : st) (astate : t) : unit = 
    let state, preds, _ = astate in 
    State.substitution_in_place subst state; 
    Preds.substitution_in_place subst preds 


  (** This needs to change -> we need to return a unfication ret type, so we can 
      compose with bi-abduction at the spec level *)
  let run_spec_aux 
      ?(existential_bindings : ((string * vt) list) option)
      (name                  : string)
      (params                : string list)
      (up                    : UP.t) 
      (astate                : t)
      (args                  : vt list) : (t * vt option * Flag.t) list = 

    L.log L.Verboser (lazy (Printf.sprintf "INSIDE RUN spec of %s with the following UP:\n%s\n"  name (UP.str up))); 

    let old_store            = get_store astate in 
    let old_astate           = copy astate in 
    let new_store            = Store.init (List.combine params args) in
    let astate'              = set_store astate new_store in 
    let existential_bindings = Option.default [] existential_bindings in 
    let subst                = Subst.init (existential_bindings @ (Store.bindings new_store)) in 

    L.log L.Verboser (lazy (Printf.sprintf "About to use the spec of %s with the following UP:\n%s\n"  name (UP.str up))); 

    match Unifier.unify astate' subst up with 
      | UPUSucc rets -> 
        (** Successful Unification *)
        List.concat 
          (List.map 
            (fun (frame_state, subst, posts) -> 
              let fl, posts = 
                (match posts with 
                  | Some (fl, posts) -> fl, posts
                  | _ -> 
                    let msg = Printf.sprintf "SYNTAX ERROR: Spec of %s does not have a postcondition" name in 
                    L.log L.Normal (lazy msg);
                    raise (Failure msg)) in 

              let sp = Unifier.produce_posts frame_state subst posts in  
              List.map 
                (fun final_state -> 
                  let final_store  = get_store final_state in 
                  let v_ret        = Store.get final_store Flag.return_variable in
                  let final_state' = set_store final_state (Store.copy old_store) in 
                  final_state', v_ret, fl
                ) sp
            ) rets)
            
      | UPUFail errs -> 
          let msg = (Printf.sprintf "WARNING: Failed to unify against the precondition of procedure %s\nSTATE:\n%s" name (str old_astate)) in 
          L.log L.Normal (lazy msg); 
          raise (Failure msg)

  let fresh_subst (xs : SS.t) : Subst.t = 
    let xs = SS.elements xs in 
    let bindings = List.map (fun x -> x, Option.get (Val.from_expr (Expr.LVar (SCommon.fresh_lvar ())))) xs in 
    Subst.init bindings 


  (**
    Evaluation of logic commands

    @param prog JSIL program
    @param lcmd Logic command to be evaluated
    @param state Current state
    @param preds Current predicate set
    @return List of states/predicate sets resulting from the evaluation
  *)
  let rec evaluate_slcmd 
      (prog   : UP.prog)
      (lcmd   : SLCmd.t) 
      (astate : t) : t list =

    let state, preds, pred_defs = astate in 
    let store         = State.get_store state in 
    let eval_expr e   = try State.eval_expr state e
                        with State.Internal_State_Error (errs, s) -> raise (Internal_State_Error (errs, astate)) in 

    let make_id_subst (a : Asrt.t) : Subst.t = 
      let lvars       = Asrt.lvars a in 
      let alocs       = Asrt.alocs a in 
      let lvars_subst = List.map (fun x -> (x, Option.get (Val.from_expr (Expr.LVar x)))) (SS.elements lvars) in 
      let alocs_subst = List.map (fun x -> (x, Option.get (Val.from_expr (Expr.ALoc x)))) (SS.elements alocs) in 
      let subst_lst   = lvars_subst @ alocs_subst in 
      Subst.init subst_lst in

    match lcmd with
    | Fold (pname, les, folding_info) -> 
        let pred       = UP.get_pred_def prog.preds pname in 
        let vs         = List.map eval_expr les in
        let params     = List.map (fun (x, _) -> x) pred.pred.params in   
        let i_bindings = 
          Option.map_default 
            (fun (def, bindings) -> List.map (fun (x, e) -> (x, eval_expr e)) bindings) 
            [] folding_info in   
        let param_bindings = 
          if (List.length params = List.length vs) 
            then List.combine params vs 
            else List.combine (Pred.in_params pred.pred)  vs in 
        let subst      = Subst.init (i_bindings @ param_bindings) in 
        (match Unifier.unify astate subst pred.up with 
          | UPUSucc [ astate', subst', _ ] ->
              let _, preds', _ = astate' in 
              let arg_vs = 
                if (List.length params = List.length vs) 
                  then vs 
                  else (
                    let out_params = Pred.out_params pred.pred in 
                    let vs_outs = 
                      List.map 
                        (fun x ->
                          let v_x = Subst.get subst' x in 
                          match v_x with 
                            | Some v_x -> v_x 
                            | None -> raise (Failure "DEATH. evaluate_slcmd. fold")  
                        ) out_params in 
                    Pred.combine_ins_outs pred.pred vs vs_outs
                  ) in  
              Preds.extend preds' (pname, arg_vs); 
              [ astate' ] 
          | _ ->  
            let msg = Printf.sprintf "IMPOSSIBLE FOLD for %s(%s) with folding_info: %s" 
              pname (String.concat ", " (List.map Val.str vs)) (SLCmd.str_of_folding_info folding_info) in 
            raise (Failure msg))    
    
    | Unfold (pname, les, unfold_info, b) -> 
        let pred     = UP.get_pred_def prog.preds pname in 
        let les_ins  = if ((List.length les) < (List.length pred.pred.params)) then les else Pred.in_args pred.pred les in 
        let vs_ins   = List.map eval_expr les_ins in
        (match Unifier.get_pred astate pname vs_ins with 
          | GPSucc [ _, vs' ] ->
              L.log L.Verboser (lazy (Printf.sprintf "Returned values: %s" (String.concat ", " (List.map Val.str vs'))));
              let vs = Pred.combine_ins_outs pred.pred vs_ins vs' in 
              L.log L.Verboser (lazy (Printf.sprintf "LCMD Unfold about to happen with rec %b info: %s" b (SLCmd.str_of_folding_info unfold_info)));
              if b 
                then [ Unifier.rec_unfold astate pname vs ]
                else (
                  L.log L.Verboser (lazy (Printf.sprintf "Values: %s" (String.concat ", " (List.map Val.str vs))));
                  List.map 
                    (fun (_, state) -> state) 
                    (Unifier.unfold astate pname vs unfold_info))
          | _ -> raise (Failure "IMPOSSIBLE UNFOLD"))
    
    | GUnfold pname ->
       [ Unifier.unfold_all astate pname ]

    | SepAssert (a, binders) -> 
        let store = State.get_store state in 
        let pvars_store = Store.domain store in 
        let pvars_a = Asrt.pvars a in 
        let pvars_diff = SS.diff pvars_a pvars_store in 
        L.log L.Verboser (lazy (Printf.sprintf "%s" (String.concat ", " (SS.elements pvars_diff))));
        (match (pvars_diff = SS.empty) with 
        | false -> 
            let pvars_errs = List.map (fun pvar -> Error.EVar pvar) (SS.elements pvars_diff) in 
            raise (Internal_State_Error (pvars_errs, astate))
        | true -> 
            let store_subst  = Store.to_ssubst store in 
            let a            = Asrt.substitution store_subst true a in  
            (* let known_vars   = SS.diff (SS.filter is_spec_var_name (Asrt.lvars a)) (SS.of_list binders) in *)
            (* Get pvars, banana *)
            let state_vars   = State.get_lvars state in 
            let known_vars   = SS.diff (SS.inter state_vars (Asrt.lvars a)) (SS.of_list binders) in
            let known_vars   = SS.union known_vars (Asrt.alocs a) in 
            let up           = UP.init known_vars SS.empty prog.prog.preds [ (a, (None, None)) ] in 
            let vars_to_forget = SS.inter state_vars (SS.of_list binders) in 
            if (vars_to_forget <> SS.empty) 
                then (
                  let oblivion_subst = fresh_subst vars_to_forget in 
                  L.log L.Verboser (lazy (Printf.sprintf "Forget %s with subst: %s" 
                    (String.concat ", " (SS.elements vars_to_forget))
                    (Subst.str oblivion_subst))); 
                  substitution_in_place oblivion_subst astate;
                  L.log L.Verboser (lazy (Printf.sprintf "State after substitution:\n%s\n" (str astate))); 
                ) else ();   
            (match up with 
            | Error errs -> raise (Internal_State_Error ([ Error.EUP (Error.UPAssert (a, errs)) ], astate))
            | Ok up -> 
                let bindings   = 
                  List.map 
                    (fun x -> 
                      let le_x = if (SCommon.is_aloc_name x) then Expr.ALoc x else Expr.LVar x in 
                      (x, Option.get (Val.from_expr le_x))) 
                  (SS.elements known_vars) in 
                let old_astate = copy astate in 
                let subst      = Subst.init bindings in
                let u_ret      = Unifier.unify astate subst up  in
                match u_ret with 
                | UPUSucc [ _, subst', _ ] ->      
                  (** Successful Unification *)
                  let new_bindings = List.map (fun x -> x, Subst.get subst' x) binders in 
                  let success      = List.for_all (fun (x, x_v) -> x_v <> None) new_bindings in 
                  if (not success) then raise (Failure (Printf.sprintf "Assert failed - binders missing")) else (
                    let new_bindings   = List.map (fun (x, x_v) -> Asrt.Pure (Eq (Expr.LVar x, Val.to_expr (Option.get x_v)))) new_bindings in 
                    let a_new_bindings = Asrt.star new_bindings in   
                    let subst_bindings = make_id_subst a_new_bindings in 
                    (match Unifier.produce old_astate subst_bindings a_new_bindings with 
                      | Some new_astate -> 
                        let new_state, new_preds, pred_defs = new_astate in 
                        let new_state'           = State.add_spec_vars new_state (SS.of_list binders) in 
                        State.simplify ~kill:false new_state';  
                          [ new_state', new_preds,  pred_defs ]
                      | _ -> 
                        let msg = Printf.sprintf "Assert failed with argument %s. unable to produce variable bindings." (Asrt.str a) in 
                        raise (Failure msg)))
                | UPUFail errs -> 
                  let fail_pfs : Formula.t list = List.map Error.get_failing_constraint errs in 
                  let fail_pfs = List.filter (fun (f : Formula.t) -> f <> True) fail_pfs in 
                  
                  let failing_model = State.sat_check_f state fail_pfs in 
                  let fm_str        = Option.map_default (fun subst -> Subst.str subst) "CANNOT CREATE MODEL" failing_model in 
                  let errs_str      = String.concat "\n" (List.map Error.str errs) in 
                  let msg           = Printf.sprintf "Assert failed with argument %s. Unification failed.\nErrors:\n\t%s. \nFailing Model:\n\t%s\n" 
                    (Asrt.str a) errs_str fm_str in 
                  Printf.printf "%s" msg; 
                  raise (Internal_State_Error (errs, old_astate))))

    | ApplyLem (lname, args, binders) -> 
        let lemma = UP.get_lemma prog lname in 
        (match lemma with 
        | Error _ -> raise (Internal_State_Error ([ ELemma lname ], astate))
        | Ok lemma -> 
          let v_args : vt list = List.map eval_expr args in 
          (* Printf.printf "apply lemma. binders: %s. existentials: %s\n\n"
             (String.concat ", " binders) (String.concat ", " lemma.lemma.existentials);  *)
          let existential_bindings = 
            List.map2 (fun x y -> (x, Option.get (Val.from_expr (Expr.LVar y)))) lemma.lemma.existentials binders in 
          let rets  = run_spec_aux ~existential_bindings:existential_bindings lname lemma.lemma.params lemma.up astate v_args in 
          List.map (fun (astate, _, _) ->  add_spec_vars astate (Var.Set.of_list binders)) rets) 

    | Invariant (a, existentials) -> 
        let store_subst   = Store.to_ssubst (State.get_store state) in 
        let invariant     = a in 
        let a             = Asrt.substitution store_subst true a in  
        let cur_spec_vars = get_spec_vars astate in 
        let state_vars    = State.get_lvars state in 
        let known_vars    = SS.diff (SS.inter state_vars (Asrt.lvars a)) (SS.of_list existentials) in
        let known_vars    = SS.union known_vars (Asrt.alocs a) in 
        let up            = UP.init known_vars SS.empty prog.prog.preds [ a, (None, None) ] in 
        (match up with 
        | Error errs -> raise (Internal_State_Error ([ Error.EUP (Error.UPInvariant (a, errs)) ], astate))
        | Ok up -> 
            let bindings   = 
              List.map 
                (fun x -> 
                  let le_x = if (SCommon.is_aloc_name x) then Expr.ALoc x else Expr.LVar x in 
                  (x, Option.get (Val.from_expr le_x))) 
              (SS.elements known_vars) in 
            let subst      = Subst.init bindings in
            let u_ret      = Unifier.unify astate subst up  in
            match u_ret with 
            | UPUSucc [ _, _, _ ] ->   
              (** Successful Unification *)
              let id_subst = make_id_subst a in 
              L.log L.Verboser (lazy (Printf.sprintf "Producing invariant %s with subst %s"
                (Asrt.str invariant) (Subst.str id_subst))); 
              let new_astate = init (Some pred_defs) in 
              let new_astate = add_spec_vars new_astate cur_spec_vars in 
              (match Unifier.produce new_astate id_subst invariant with 
                | Some new_astate -> 
                    Subst.iter id_subst (fun x le_x -> if (SCommon.is_pvar_name x) then Store.put (get_store new_astate) x le_x); 
                    simplify ~kill:false new_astate;  
                    [ new_astate ] 
                | _ -> 
                  let msg = Printf.sprintf "Invariant Unification failed for %s" (Asrt.str a) in 
                  raise (Failure msg))
            | _ -> 
              let msg = Printf.sprintf "Invariant Unification failed for %s" (Asrt.str a) in 
              raise (Failure msg))

    | _ -> raise (Failure "COMMAND NOT YET SUPPORTED")
  


  let run_spec 
      (spec : UP.spec)
      (astate : t)
      (args   : vt list)
      (subst : (string * (string * vt) list) option) : (t * vt option * Flag.t) list = 
    match subst with 
      | None -> run_spec_aux spec.spec.name spec.spec.params spec.up astate args 
      | Some (_, subst_lst) -> run_spec_aux ~existential_bindings:subst_lst spec.spec.name spec.spec.params spec.up astate args 


  let unify (astate : t) (subst : st) (up : UP.t) : bool = 
    match Unifier.unify astate subst up with 
      | Unifier.UPUSucc _ -> true 
      | _ -> false 

  
  let unfolding_vals (astate : t) (fs : Formula.t list) : vt list = 
    let state, _, _ = astate in 
    State.unfolding_vals state fs  

  
  let add_pred_defs (pred_defs : UP.preds_tbl_t) (astate : t) : t = 
    let state, preds, _ = astate in 
    state, preds, pred_defs 

  let fresh_val (astate : t) : vt =
    let state, _, _ = astate in 
    State.fresh_val state  

  
  let fresh_loc ?(loc : vt option) (astate : t) : vt =
    let state, _, _ = astate in 
    State.fresh_loc ?loc:loc state 

  let deabstract (astate : t) : state_t * bool =
    let state, preds, _ = astate in 
    state, (Preds.is_empty preds)  

  let get_locs (astate : t) : vt list =
    let state, _, _ = astate in 
      State.get_locs state 

  let get_locs_and_props (astate : t) : (vt * vt) list =
    let state, _, _ = astate in 
      State.get_locs_and_props state 

  let clean_up (astate : t) : unit =
    let state, _, _ = astate in 
      State.clean_up state 

  let produce (astate : t) (subst : st) (a : Asrt.t) : t option = 
    Unifier.produce astate subst a  

  let unify_assertion (astate : t) (subst : st) (p : Asrt.t) : u_res = 
    match Unifier.unify_assertion astate subst p with 
    | UWTF          -> UWTF    
    | USucc astate' -> USucc astate' 
    | UFail errs    -> UFail errs  

  let produce_posts (astate  : t) (subst  : st) (asrts : Asrt.t list) : t list = 
    Unifier.produce_posts astate subst asrts 
  
  let get_all_preds ?(keep : bool option) (sel : abs_t -> bool) (astate : t) : abs_t list = 
    let _, preds, _ = astate in 
    Preds.find_all ?keep:keep sel preds 

  let set_pred (astate : t) (pred : abs_t) : unit = 
    let _, preds, _ = astate in
    Preds.extend preds pred

  let update_subst (astate : t) (subst : st) : unit = 
    let state, _, _ = astate in 
    State.update_subst state subst 

 end 




