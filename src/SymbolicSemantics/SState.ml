open CCommon
open SCommon
open Literal

module L = Logging

module SSubst = SVal.SSubst 
module SError = SError.M

(**
   Symbolic execution indicator
*)
let cosette = ref false

module M = struct 

  type vt           = SVal.M.t 
  type st           = SVal.SSubst.t 
  type store_t      = SStore.t
  type err_t        = SError.t 
  type t            = SHeap.t * SStore.t * PFS.t * TypEnv.t * SS.t 


  exception Internal_State_Error of (err_t list) * t

  type gc_ret = 
    | GCSucc  of (t * vt * vt * (vt option)) list
    | GCFail  of err_t list  

  type gd_ret = 
    | GDSucc  of (t * vt) list
    | GDFail  of err_t list  

  type gm_ret = 
    | GMSucc  of (t * vt * vt) list 
    | GMFail  of err_t list 

  type u_res = 
    | UWTF    
    | USucc   of t
    | UFail   of err_t list  

  (* Auxiliary Functions *)
  let get_loc_name (loc : Expr.t) state : string option = 
    L.log L.TMI (lazy (Printf.sprintf "get_loc_name: %s" (Expr.str loc)));
    let _, _, pfs, _, _ = state in 
    match loc with 
    | Lit (Loc loc)  
    | ALoc loc -> Some loc 
    | LVar x   -> 
      (match Reduction.resolve_location x (PFS.to_list pfs) with 
       | Some (loc_name, _) -> Some loc_name
       | _ ->  None) 
    | _ -> let msg = Printf.sprintf "Unsupported location: %s" (Expr.str loc) in 
        L.log L.Verboser (lazy msg);
        raise (Internal_State_Error ([ SError.EType (loc, None, Type.ObjectType) ], state))


  let loc_from_loc_name (loc_name : string) : Expr.t = 
    if (SCommon.is_aloc_name loc_name) 
    then ALoc loc_name 
    else (Lit (Loc loc_name))


  let lift_lnone_to_metanone (fv : Expr.t) : Expr.t option = 
    match fv with 
    | Nono -> None 
    | fv    -> Some fv 

  let str (state : t) : string = 
    let heap, store, pfs, gamma, svars = state in 
    let heap_str = if (!CCommon.no_heap) then "NO HEAP PRINTED" else SHeap.str heap in 
    Printf.sprintf "SPEC VARS: %s\n\nHEAP:\n%s\n\nSTORE:%s\n\nPURE FORMULAE:%s\n\nTYPING ENVIRONMENT:\n%s"
      (String.concat ", " (SS.elements svars)) heap_str (SStore.str store) (PFS.str pfs) (TypEnv.str gamma)

  let s_init (heap : SHeap.t) (store : SStore.t) (pfs : PFS.t) (gamma : TypEnv.t) (svars : SS.t) : t =
    heap, store, pfs, gamma, svars 

  let init (pred_defs : UP.preds_tbl_t option) = 
    SHeap.init (), SStore.init [], PFS.init (), TypEnv.init (), SS.empty

  let get_pred_defs (state : t) : UP.preds_tbl_t option = None 

  let lift l = Expr.Lit l  

  let unlift (l : Expr.t) = 
    match l with 
    | Lit l -> Some l
    | _      -> None 

  let eval_expr state e =
    let rec symb_evaluate_expr ?(no_reduce=false) (state:t) (expr : Expr.t) : Expr.t =
      let f = symb_evaluate_expr ~no_reduce:true state in
      let _, store, pfs, gamma, _ = state in
      let result : Expr.t = (match expr with
          (* Variables:
             a) If a variable is already in the store, return the variable
             b) Otherwise, it dies! *)
          | PVar x -> (match SStore.get store x with
              | Some x -> x
              | None   -> raise (Internal_State_Error ([SError.EVar x], state)))

          (* Binary operators *)
          | BinOp (e1, op, e2) -> BinOp (f e1, op, f e2)

          (* Unary operators *)
          | UnOp (op, e) -> UnOp (op, f e)

          (* Lists, sets, n-ary operators *)
          | EList es       -> EList (List.map f es)
          | ESet  es       -> ESet  (List.map f es)
          | NOp   (op, es) -> NOp   (op, List.map f es)

          | _ -> expr) in
      (* Perform reduction *)
      if no_reduce then result else
        Reduction.reduce_lexpr ~gamma:gamma ~pfs:pfs result
    in symb_evaluate_expr state e


  let store_update state x v = 
    let _, store, _, _, _ = state in 
    SStore.put store x v; 
    state 

  let get_store state = 
    let _, store, _, _, _ = state in 
    store 

  let make_store params args = SStore.init (List.combine params args)

  let set_store state store = 
    let heap, _, pfs, gamma, svars = state in 
    heap, store, pfs, gamma, svars

  let get_var_val store x = SStore.get store x 


  let copy (state : t) : t = 
    let heap, store, pfs, gamma, svars = state in 
    (SHeap.copy heap, SStore.copy store, PFS.copy pfs, TypEnv.copy gamma, svars)


  let alloc state loc mv = 
    let heap, store, pfs, gamma, _ = state in 
    let (loc_name : string), (loc : Expr.t) =
      match (loc : Expr.t option) with 
      | None -> 
        let loc_name = fresh_loc () in 
        loc_name, Lit (Loc loc_name)
      | Some (Lit (Loc loc)) -> loc, Lit (Loc loc)
      | Some (ALoc loc)       -> loc, ALoc loc
      | Some (LVar v) ->  
        let loc_name = fresh_loc () in 
        PFS.extend pfs (Eq (LVar v, ALoc loc_name));
        loc_name, Lit (Loc loc_name)
      | Some le -> raise (Failure (Printf.sprintf "Alloc with a non-loc loc argument: %s" (Expr.str le))) in 
    (* let hdomain = SS.elements (SHeap.domain heap) in 
       let clocs = List.filter SCommon.is_lloc_name hdomain in 
       List.iter (fun loc_name -> PFS.extend pfs (Formula.Not (Eq (loc, Lit (Loc loc_name))))) clocs; *)
    SHeap.init_object heap loc_name mv; 
    loc, state

  let to_loc (state : t) (loc : vt) : (t * vt) option =
    let _, _, pfs, gamma, _ = state in 
    let loc = Reduction.reduce_lexpr ~gamma:gamma ~pfs:pfs loc in 
    match loc with 
    | Lit (Loc loc_name)
    | ALoc loc_name -> Some (state, loc)
    | LVar x -> 
      (match Reduction.resolve_location x (PFS.to_list pfs) with 
       | Some (loc_name, _) -> 
         if (is_aloc_name loc_name) 
         then Some (state, ALoc loc_name) 
         else Some (state, Lit (Loc loc_name))
       | None -> 
         let new_aloc = fresh_aloc () in 
         let p : Formula.t = Eq (LVar x, ALoc new_aloc) in 
         if (FOSolver.check_satisfiability (p :: (PFS.to_list pfs)) gamma) then (
           PFS.extend pfs p; 
           Some (state, Expr.ALoc new_aloc) 
         ) else None)
    | _ -> None 


  let get_locs state = 
    let heap, _, _, _, _ = state in
    let locs = SS.elements (SHeap.domain heap) in 
    List.map (fun loc : Expr.t -> if (is_aloc_name loc) then ALoc loc else Lit (Loc loc)) locs 


  let set_cell state loc prop v =
    let heap, _, pfs, _, _ = state in
    let loc_name = get_loc_name loc state in
    (match loc_name, v with 
     | None, _ -> raise (Failure "DEATH. set_cell. LOCATION UNKNOWN") 
     | Some loc_name, None   -> SHeap.set_fv_pair heap loc_name prop Nono
     | Some loc_name, Some v -> SHeap.set_fv_pair heap loc_name prop v); 
    state 


  let get_cell ?(remove : bool option) (state : t) (loc : vt) (prop : vt) : gc_ret = 

    let heap, store, pfs, gamma, _ = state in
    let loc_name = get_loc_name loc state in
    let remove = Option.default false remove in

    L.log L.TMI (lazy (Printf.sprintf "GetCell: resolved location: %s -> %s" (SVal.M.str loc) (Option.map_default (fun x -> x) "None" loc_name)));

    let make_gc_error (loc_name : string) (prop : vt) (props : vt list) (dom : vt option) : SError.t = 
      let loc = loc_from_loc_name loc_name in 
      let failing_constraint   = 
        Formula.conjunct (List.map (fun prop' -> Formula.Not (Eq (prop, prop'))) props) in
      let fixes_existing_props = 
        List.map (fun prop' -> [ SError.MPF (Formula.Eq (prop, prop') ) ] ) props in 
      let fix_new_property : SError.fix_t list = [ MCell (loc, prop); MPF (failing_constraint) ] in 

      (match dom with 
       | Some dom -> 
         let failing_constraint'  : Formula.t      = SetMem (prop, dom) in 
         let failing_constraint'' : Formula.t      = And (failing_constraint, failing_constraint') in 
         let fix_new_property' : SError.fix_t list = MPF (failing_constraint') :: fix_new_property in 
         ESpec ([ loc ], failing_constraint'', fix_new_property' :: fixes_existing_props)
       | None -> ESpec ([ loc ], failing_constraint, (fix_new_property :: fixes_existing_props))) in 


    let f loc_name = 
      Option.map_default (fun ((fv_list, dom), mtdt) -> 
          (match SFVL.get prop fv_list with
           | Some ffv ->  
             (if remove then SHeap.set heap loc_name (SFVL.remove prop fv_list) dom mtdt);
             GCSucc [ state, loc, prop, (lift_lnone_to_metanone ffv) ]  
           | None -> 
             (match dom, (SFVL.get_first (fun name -> FOSolver.is_equal name prop pfs gamma) fv_list) with 
              | None, None -> GCFail [ (make_gc_error loc_name prop (SFVL.field_names fv_list) None) ]  

              | _, Some (ffn, ffv) -> 
                (if remove then SHeap.set heap loc_name (SFVL.remove ffn fv_list) dom mtdt);
                GCSucc [ state, loc, ffn, (lift_lnone_to_metanone ffv) ]

              | Some dom, _ -> 
                let a_set_inclusion : Formula.t = Not (SetMem (prop, dom)) in 
                if (FOSolver.check_entailment SS.empty (PFS.to_list pfs) [ a_set_inclusion ] gamma) 
                then (
                  let new_domain : Expr.t = NOp (SetUnion, [ dom; ESet [ prop ]]) in 
                  let new_domain = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) new_domain in
                  if (not remove) then (
                    let fv_list' = SFVL.add prop Nono fv_list in 
                    SHeap.set heap loc_name fv_list' (Some new_domain) mtdt
                  ) else (
                    SHeap.set heap loc_name fv_list (Some new_domain) mtdt
                  ); 
                  GCSucc  [ state, loc, prop, None ] 
                ) else (
                  let f_names : Expr.t list = SFVL.field_names fv_list in 
                  let full_knowledge : Formula.t = Eq (dom, ESet f_names) in
                  if (FOSolver.check_entailment SS.empty (PFS.to_list pfs) [ full_knowledge ] gamma) then (
                    L.log L.Verboser (lazy "GET CELL will branch\n"); 
                    let rets : ((t * vt * vt * (vt option)) option) list = 
                      List.map (fun (f_name, f_value) -> 
                          let new_f : Formula.t = (match Simplifications.reduce_assertion ~gamma:gamma ~pfs:pfs (Pure (Eq (f_name, prop))) with | Pure f -> f) in 
                          let sat = FOSolver.check_satisfiability (new_f :: (PFS.to_list pfs)) gamma in 
                          (match sat with 
                           | false -> None
                           | true -> 
                             (* Cases in which the prop exists *)
                             let heap, store, pfs, gamma, svars = copy state in 
                             PFS.extend pfs new_f; 
                             let f_value_ret = if (f_value = Expr.Nono) then None else Some f_value in 
                             Some ((heap, store, pfs, gamma, svars), loc, f_name, f_value_ret)  
                          )
                        ) (SFVL.to_list fv_list) in 

                    let rets = List.map Option.get (List.filter (fun x -> x <> None) rets) in 

                    (* I need the case in which the prop does not exist *)
                    let heap, store, pfs, gamma, svars = state in 
                    let new_f : Formula.t = (match Simplifications.reduce_assertion ~gamma:gamma ~pfs:pfs (Pure (Not (SetMem (prop, dom)))) with | Pure f -> f) in 
                    let sat = FOSolver.check_satisfiability (new_f :: (PFS.to_list pfs)) gamma in 
                    let dom_ret = (match sat with 
                        | false -> []
                        | true -> 
                          PFS.extend pfs new_f;
                          [ (heap, store, pfs, gamma, svars), loc, prop, None ]
                      ) in 
                    GCSucc (rets @ dom_ret)  
                  ) else GCFail [ (make_gc_error loc_name prop (SFVL.field_names fv_list) (Some dom)) ] 
                )))) (GCFail [ ESpec ([], False, [ [ MLCell (loc, prop) ] ]) ]) (SHeap.get heap loc_name) in 

    let result = Option.map_default f (GCFail [ ESpec ([], False, [ [ MLCell (loc, prop) ] ]) ]) loc_name in 
    result



  let get_domain ?(expected_props : vt option) ?(remove : bool option) (state : t) (loc : vt) : gd_ret = 

    let heap, _, pfs, gamma, _ = state in 
    let loc_name = get_loc_name loc state in 
    let remove = Option.default false remove in 
    let expected_props = Option.default (Expr.ESet []) expected_props in 

    L.log L.Verboser (lazy (SHeap.str heap));

    let make_gd_error (loc_name : string) (props : vt list) (dom : vt option) : SError.t = 
      let loc = loc_from_loc_name loc_name in 
      match dom with 
      | None -> 
        let new_domain = Expr.NOp (SetUnion, [ ESet props; expected_props ])  in
        let new_domain = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) new_domain in 
        let fix_existing_props : SError.fix_t list = [ MDomain (loc, new_domain) ]  in 
        ESpec ([], False, [ fix_existing_props ])
      | Some dom -> 
        let dom_diff : Expr.t = BinOp (dom, SetDiff, ESet props) in 
        let dom_diff = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) dom_diff in 
        (match dom_diff with 
         | ESet props' -> 
           let fixes_existing_props = 
             List.map (fun prop' -> SError.MCell (loc, prop') ) props' in 
           ESpec ([], False, [ fixes_existing_props ])
         | _ -> ESpec ([], False, [])) in 

    let f loc_name = 
      match SHeap.get heap loc_name with 
      | None -> GDFail [ ESpec ([ loc ], False, [ ]) ]
      | Some ((fv_list, None), _) -> 
        GDFail [ (make_gd_error loc_name (SFVL.field_names fv_list) None) ]
      | Some ((fv_list, Some dom), mtdt) -> 
        let none_fv_list, pos_fv_list = SFVL.partition (fun _ fv -> (fv = Nono)) fv_list in    

        if remove then (
          (** Called from the entailment *)
          SHeap.set heap loc_name pos_fv_list None mtdt;
          let none_props = SFVL.field_names none_fv_list in 
          let domain     = Expr.BinOp (dom, SetDiff, ESet none_props) in
          let dom        = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) domain in 
          GDSucc [ state, dom ]
        ) else (
          (** Called from the semantics -> we need full knowledge *)
          let props = SFVL.field_names fv_list in 
          let a_set_equality : Formula.t = Eq (dom, ESet props) in
          let solver_ret =  FOSolver.check_entailment SS.empty (PFS.to_list pfs) [ a_set_equality ] gamma in 
          if solver_ret then (
            GDSucc [ state,  EList (SFVL.field_names pos_fv_list) ]
          ) else (
            GDFail [ (make_gd_error loc_name props (Some dom)) ]
          )
        ) in 

    let result = Option.map_default f (GDFail [ ESpec ([ loc ], False, [ ]) ]) loc_name in
    result


  let set_domain (state : t) (loc : vt) (dom : vt) : t = 
    let heap, _, pfs, _, _ = state in 
    let loc_name = get_loc_name loc state in 
    let loc_name = 
      match loc_name with 
      | Some loc_name -> loc_name 
      | None -> raise (Failure "DEATH. domain_update. NON EXISTING LOCATION") in 

    (match (SHeap.get heap loc_name) with 
     | None -> 
       SHeap.set heap loc_name SFVL.empty (Some dom) None
     | Some ((fv_list, _), mtdt) -> 
       (* TODO: This probably needs to be a bit more sophisticated *)
       SHeap.set heap loc_name fv_list (Some dom) mtdt);
    state

  let get_metadata ?(remove : bool option) (state : t) (loc : vt) : gm_ret = 
    let heap, _, pfs, _, _ = state in 
    let loc_name = get_loc_name loc state in 
    let remove = Option.default false remove in 

    let make_gm_error (loc_name : string) : SError.t =   
      let loc = loc_from_loc_name loc_name in   
      let fix : SError.fix_t list = [ MMetadata loc ] in 
      ESpec ([ loc ], True, [ fix ]) in 

    let f loc_name = 
      let loc = if (is_aloc_name loc_name) then Expr.ALoc loc_name else Expr.Lit (Loc loc_name) in 
      match SHeap.get heap loc_name with 
      | None -> GMFail [ (make_gm_error loc_name) ]
      | Some ((fv_list, dom), mtdt) -> 
        (if remove then  SHeap.set heap loc_name fv_list dom None);
        Option.map_default (fun mtdt -> GMSucc [ state, loc, mtdt ]) (GMFail [ (make_gm_error loc_name) ]) mtdt in 

    Option.map_default f (GMFail [ ESpec ([ loc ], True, [ [ MLMetadata loc ] ]) ]) loc_name  


  let set_metadata (state : t) (loc : vt) (mtdt : vt) : t = 
    L.log L.TMI (lazy "Trying to set metadata.");
    let heap, _, pfs, gamma, _ = state in 
    let loc_name = get_loc_name loc state in 
    let loc_name = 
      match loc_name with 
      | Some loc_name -> loc_name 
      | None -> raise (Failure (Printf.sprintf "DEATH. Metadata_update #1. NON EXISTING LOCATION: %s" (SVal.M.str loc))) in 

    (match (SHeap.get heap loc_name) with 
     | None -> 
       SHeap.set heap loc_name SFVL.empty None (Some mtdt)
     | Some ((fv_list, dom), None) -> 
       SHeap.set heap loc_name fv_list dom (Some mtdt)
     | Some ((fv_list, dom), Some omet) -> 
       if (omet <> Option.get (SVal.M.from_expr (Lit Null))) 
       then PFS.extend pfs (Eq (mtdt, omet))
       else SHeap.set heap loc_name fv_list dom (Some mtdt));
    L.log L.TMI (lazy "Done setting metadata.");
    state 


  let delete_object (state : t) (e_loc : Expr.t) : t = 
    let heap, _, pfs, gamma, _ = state in  
    let loc_name = get_loc_name (eval_expr state e_loc) state in 

    match loc_name with 
    | Some loc_name -> 
      if (SHeap.has_loc heap loc_name) then (
        SHeap.remove heap loc_name; state 
      ) else raise (Failure "delete_obj. Unknown Location")  
    | None -> raise (Failure "delete_obj. Unknown Location") 


  let assume (state : t) (v : Expr.t) : t list = 
    (* let t = time() in *)
    L.log L.Verbose (lazy (Printf.sprintf "Assuming expression: %s" (Expr.str v)));
    let _, _, pfs, _, _ = state in 
    let result = 
      if (v = Lit (Bool true))  then [ state ] else 
      if (v = Lit (Bool false)) then [ ] else (
        (* let t = time() in *)
        let v_asrt = match Formula.lift_logic_expr v with
          | Some (v_asrt, _) -> v_asrt
          | _  -> False in 
        if (v_asrt = False) then [ ] else (
          PFS.extend pfs v_asrt; 
          L.log L.Verbose (lazy (Printf.sprintf "Assumed state: %s" (str state)));
          [ state ]
        )
      ) in 
    (* update_statistics "Assume" (time() -. t); *)
    result

  let assume_a (state : t) (ps : Formula.t list) : t option = 
    let _, _, pfs, gamma, _  = state in 
    let result = if (FOSolver.check_satisfiability (ps @ (PFS.to_list pfs)) gamma) then (
        List.iter (PFS.extend pfs) ps; 
        Some state 
      ) else None in 
    result

  let assert_a (state : t) (ps : Formula.t list) : bool = 
    let _, _, pfs, gamma, _ = state in 
    FOSolver.check_entailment SS.empty (PFS.to_list pfs) ps gamma

  let sat_check (state : t) (v : Expr.t) : bool = 
    (* let t = time() in *)
    let _, _, pfs, gamma, _ = state in 
    if (v = Lit (Bool true))  then true  else
    if (v = Lit (Bool false)) then false else (
      let v_asrt = 
        match Formula.lift_logic_expr v with
        | Some (v_asrt, _) -> v_asrt
        | _  -> False in 
      let result = FOSolver.check_satisfiability (v_asrt :: (PFS.to_list pfs)) gamma in 
      (* update_statistics "SAT Check" (time() -. t); *)
      result)

  let sat_check_f (state : t) (fs : Formula.t list) : st option =  
    let _, store, pfs, gamma, _ = state in 
    (FOSolver.check_satisfiability_with_model (fs @ (PFS.to_list pfs)) gamma)

  let equals (state : t) (le1 : vt) (le2 : vt) : bool =
    let _, _, pfs, gamma, _ = state in 
    let result = FOSolver.is_equal le1 le2 pfs gamma in 
    result

  let get_type (state : t) (le : vt) : Type.t option = 
    let _, _, pfs, gamma, _ = state in 
    let le = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) le in 
    let t, _, _ = Typing.type_lexpr gamma le in 
    t 

  let assume_t (state : t) (v : vt) (t : Type.t) : t option = 
    let _, _, pfs, gamma, _ = state in 
    match Typing.reverse_type_lexpr true gamma v t with 
    | None -> None 
    | Some gamma' -> TypEnv.extend gamma gamma'; Some state


  let simplify ?(kill : bool option) (state : t) : st = 
    (* let start_time = time() in *)
    let kill = Option.default true kill in
    let heap, store, pfs, gamma, svars = state in 
    L.log L.Verboser (lazy (Printf.sprintf "-----------------------------------\nSTATE BEFORE SIMPLIFICATIONS:\n%s\n-----------------------------------" (str state))); 
    let subst, _ = Simplifications.simplify_pfs_and_gamma ~kill:kill gamma pfs (Some (Some svars)) in 
    SHeap.substitution_in_place subst heap; 
    SStore.substitution_in_place subst store;
    if (not kill) then Typing.naively_infer_type_information pfs gamma;  
    L.log L.Verboser (lazy (Printf.sprintf "-----------------------------------\nSTATE AFTER SIMPLIFICATIONS:\n%s\n\nwith substitution:\n\t%s\n-----------------------------------" 
                              (str state) (SVal.SSubst.str subst))); 
    (* update_statistics "Simplify" (time() -. start_time); *)
    subst

  let simplify_val (state : t) (v : vt) : vt = 
    let _, _, pfs, gamma, _ = state in 
    Reduction.reduce_lexpr ~gamma:gamma ~pfs:pfs v 

  let to_assertions ?(to_keep : SS.t option) (state : t) : Asrt.t list = 
    let heap, store, pfs, gamma, _ = state in 
    let store' = Option.map_default (fun store_dom -> SStore.projection store (SS.elements store_dom)) store to_keep in 
    let asrts_pfs   = List.sort Asrt.compare (List.map (fun f -> Asrt.Pure f) (PFS.to_list pfs)) in
    let asrts_store =  List.sort Asrt.compare (List.map (fun f -> Asrt.Pure f) (SStore.assertions store')) in
    if (TypEnv.empty gamma) then asrts_store @ SHeap.assertions heap @ asrts_pfs
    else asrts_store @ SHeap.assertions heap @ asrts_pfs @ [ Types (TypEnv.to_list gamma) ] 


  let add_spec_vars (state : t) (xs : Var.Set.t) : t = 
    let heap, store, pfs, gamma, svars = state in 
    heap, store, pfs, gamma, (SS.union xs svars)

  let get_spec_vars (state : t) : SS.t = 
    let _, _, _, _, svars = state in 
    svars 

  let unfolding_vals (state : t) (fs : Formula.t list) : vt list = 
    let lvars = SS.of_list (List.concat (List.map (fun f -> SS.elements (Formula.lvars f)) fs)) in 
    let alocs = SS.of_list (List.concat (List.map (fun f -> SS.elements (Formula.alocs f)) fs)) in 
    let clocs = SS.of_list (List.concat (List.map (fun f -> SS.elements (Formula.clocs f)) fs)) in 
    let lvars = List.map (fun x -> Expr.LVar x) (SS.elements lvars) in 
    let alocs = List.map (fun x -> Expr.ALoc x) (SS.elements alocs) in 
    let clocs = List.map (fun x -> Expr.Lit (Loc x)) (SS.elements clocs) in 
    clocs @ alocs @ lvars 

  let is_well_formed (state : t) : unit = 
    let heap, _, _, _, _ = state in 
    SHeap.is_well_formed heap


  let run_spec (spec : UP.spec) (state : t) (args : vt list) (subst : (string * (string * vt) list) option) : (t * vt option * Flag.t) list = 
    raise (Failure "ERROR: run_spec called for non-abstract execution")

  let unify (state : t) (subst : st) (up : UP.t) : bool = 
    raise (Failure "ERROR: unify called for non-abstract execution") 

  let evaluate_slcmd (prog : UP.prog) (slcmd : SLCmd.t) (state : t) : t list = 
    raise (Failure "ERROR: evaluate_slcmd called for non-abstract execution")      

  let substitution_in_place (subst : st) (state : t) : unit = 
    let heap, store, pfs, gamma, svars = state in 
    let subst' = SSubst.copy subst in 
    (* SSubst.filter_in_place subst (fun x v_x -> if (SS.mem x svars) then None else Some v_x);   *)
    SHeap.substitution_in_place subst heap; 
    SStore.substitution_in_place subst store;
    PFS.substitution_in_place subst pfs; 
    Typing.substitution_in_place subst gamma

  let fresh_val (state : t) : vt = LVar (SCommon.fresh_lvar ()) 

  let fresh_loc ?(loc : vt option) (state : t) : vt =
    let _, _, pfs, _, _ = state in 
    match loc with 
    | Some loc -> 
      let loc_name = get_loc_name loc state in 
      (match loc_name with 
       | Some loc_name -> if (is_aloc_name loc_name) then Expr.ALoc loc_name else Expr.Lit (Loc loc_name)
       | None -> ALoc (SCommon.fresh_aloc ()))
    | None -> ALoc (SCommon.fresh_aloc ()) 

  let get_locs (state : t) : vt list = 
    let heap, _, _, _, _ = state in 
    let domain = SS.elements (SHeap.domain heap) in 
    List.map (fun loc -> if (is_aloc_name loc) then Expr.ALoc loc else Expr.Lit (Loc loc)) domain

  let get_lvars (state : t) : Var.Set.t = 
    let heap, store, pfs, gamma, svars = state in 
    List.fold_left SS.union SS.empty [ SHeap.lvars heap; SStore.lvars store; PFS.lvars pfs; TypEnv.lvars gamma; svars ]

  let get_locs_and_props (state : t) : (vt * vt) list =
    let heap, _, _, _, _ = state in 
    let domain = SS.elements (SHeap.domain heap) in 
    List.concat (List.map (fun loc -> 
        let eloc = if (is_aloc_name loc) then Expr.ALoc loc else Expr.Lit (Loc loc) in
        let ((fvl, _), _) = SHeap.get_with_default heap loc in 
        let fields = SFVL.field_names fvl in 
        List.map (fun name -> (eloc, name)) fields
      ) domain)

  let clean_up (state : t) : unit = 
    let heap, _, _, _, _ = state in 
    SHeap.clean_up heap

  let unify_assertion (state : t) (subst : st) (p : Asrt.t) : u_res = 
    raise (Failure "Unify assertion from non-abstract symbolic state.")   

  let produce_posts (state  : t) (subst  : st) (asrts : Asrt.t list) : t list = 
    raise (Failure "produce_posts from non-abstract symbolic state.")  

  let produce (state  : t) (subst  : st) (asrt : Asrt.t) : t option = 
    raise (Failure "produce_post from non-abstract symbolic state.")

  let update_subst (state : t) (subst : st) : unit = 
    let _, _, pfs, gamma, _ = state in 
    let new_bindings = 
      SSubst.fold
        subst  
        (fun x e ac -> 
          match e with 
            | LVar y ->
                (match TypEnv.get gamma y with 
                  | Some ObjectType -> 
                      (match Reduction.resolve_location y (PFS.to_list pfs) with 
                      | Some (loc_name, _) -> 
                          if (SCommon.is_aloc_name loc_name) 
                            then (x, Expr.ALoc loc_name) :: ac 
                            else  ac 
                      | _ ->  ac) 
                  | _ -> ac)
            | _ -> ac 
        ) [] in 
  List.iter (fun (x, e) -> SSubst.put subst x e) new_bindings 

end



