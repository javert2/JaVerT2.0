open CCommon
open SCommon
open Literal

module L      = Logging
module SSubst = SVal.SSubst 

module M 
  (Val     : Val.M) 
  (Subst   : Subst.M with type vt = Val.t and type t = Val.st) 
  (Store   : Store.M with type vt = Val.t) 
  (Error   : Error.M with type vt = Val.t and type st = Val.st)
  (State   : State.M with type vt = Val.t and type st = Subst.t and type store_t = Store.t and type err_t = Error.t) 
  (Preds   : Preds.M with type vt = Val.t and type st = Subst.t)
    : (Unifier.M with type vt = Val.t and type st = Subst.t and type err_t = Error.t and type state_t = State.t and type preds_t = Preds.t) = struct 

  type vt      = Val.t 
  type st      = Subst.t 
  type err_t   = Error.t 
  type state_t = State.t 
  type preds_t = Preds.t
  type abs_t   = string * (vt list) 
  type t       = state_t * preds_t * UP.preds_tbl_t

  type post_res      = (Flag.t * (Asrt.t list)) option
  type search_state  = (t * st * UP.t) list * Error.t list 
  type unfold_info_t = string * ((string * Expr.t) list) 

  type gp_ret = 
    | GPSucc  of (t * (vt list)) list 
    | GPFail  of err_t list 

  type u_res = 
    | UWTF    
    | USucc   of t
    | UFail   of err_t list  

  type up_u_res = 
    | UPUSucc of (t * st * post_res) list 
    | UPUFail of err_t list 
  
  let update_store (astate : t) (x : string) (v : Val.t) : t =
    let state, preds, pred_defs = astate in 
    let store        = State.get_store state in 
    let _            = Store.put store x v in 
    let state'       = State.set_store state store in 
      state', preds, pred_defs

  let simplify_astate (astate : t) : st = 
    let state, preds, pred_defs = astate in 
    let subst        = State.simplify ~kill:false state in
    Preds.substitution_in_place subst preds;
    subst  

  let string_of_astate (astate : t) : string = 
    let state, preds, _ = astate in 
    Printf.sprintf "%s\nPREDS:\n%s\n" (State.str state) (Preds.str preds)

  let copy_astate (astate : t) : t = 
    let state, preds, pred_defs = astate in 
    State.copy state, Preds.copy preds, pred_defs

  let subst_in_expr_opt (astate : t) (subst : st) (e : Expr.t) : vt option = 
    let state, _, _ = astate in 
    let v = Option.map_default Val.from_expr None (Subst.subst_in_expr_opt subst e) in 
    Option.map (State.simplify_val state) v 
 
  let subst_in_expr (subst : Subst.t) (le : Expr.t) : Val.t option = 
    Val.from_expr (Subst.subst_in_expr subst false le) 
  
  let compose_substs (subst_lst : (string * vt) list) (subst1 : st) (subst2 : st) : st = 
    let subst = Subst.init [] in
    
    let aux (v : vt) : vt = 
      let e1 = Subst.subst_in_expr subst1 true (Val.to_expr v) in
      let e2 = Subst.subst_in_expr subst2 true e1 in
      (match Val.from_expr e2 with 
        | None    -> v
        | Some v2 -> v2) in

    List.iter (fun (x, v) -> Subst.put subst x (aux v)) subst_lst; 
    subst 
  
  (** l \in clues /\ metadata(l) = l' => l' \in clues' 
      returns clues' 
    *)
  let expand_unfolding_clues_old (state : State.t) (vs : Val.t list) : Val.t list = 
    
    let aux (v : Val.t) : Val.t option = 
      let e_v = Val.to_expr v in 
      (match e_v with 
        | ALoc _ | Lit (Loc _) -> 
            let v_md = State.get_metadata state v in 
            (match v_md with 
              | GMSucc [ (_, _, v_md) ] -> 
                  let e_md = Val.to_expr v_md in 
                  (match e_md with 
                    | ALoc _ | Lit (Loc _) -> Some v_md 
                    | _ -> None)
              | _ -> None)
        | _ -> None) in 
    get_list_somes (List.map aux vs) 
  
  let expand_unfolding_clues_new (metadata_inv : (Val.t, Val.t) Hashtbl.t) (vs : Val.t list) : Val.t list = 
    
    let aux (v : Val.t) : Val.t list = 
      if (Hashtbl.mem metadata_inv v) then [ Hashtbl.find metadata_inv v ] else [] in 
    List.concat (List.map aux vs) 


  let get_pred_with_vs (astate : t) (vs : Val.t list) : abs_t option = 

    let state, preds, pred_defs = astate in 
    
    let vs = (expand_unfolding_clues_old state vs) @ vs in 

    let print_local_info (i : int) (name : string) (args : Val.t list) : unit = 
       L.log L.Verboser (lazy (Printf.sprintf "Strategy %d: Examining %s(%s)" i name (String.concat ", " (List.map Val.str args)))) in 
    
    let get_pred_def (name : string) : Pred.t = 
       try let pred = Hashtbl.find pred_defs name in pred.pred with _ -> raise (Failure "ERROR: get_pred_with_vs: Predicate doesn't exist.") in

    let apply_strategies (strategies : ((string * Val.t list) -> bool) list) : int option = 
      List.fold_left 
        (fun ac strategy -> if (ac <> None) then ac else Preds.index_of preds strategy)
        None strategies in 

    (* Strategy 1: The values that we are looking for are in the in-parameters *)
    let strategy_1 ((name, args) : string * Val.t list) : bool = 
      print_local_info 1 name args; 
      let pred_def = get_pred_def name in
      let in_args  = Pred.in_args pred_def args in
      let vs_inter = list_inter vs args in 
      let es_inter = List.fold_left (fun ac e -> Expr.Set.add e ac) Expr.Set.empty (List.map Val.to_expr vs_inter) in 
      L.log L.Verboser (lazy 
        (Printf.sprintf "get_pred_with_vs. Strategy 1. Intersection: %s" 
          (String.concat ", " (List.map Expr.str (Expr.Set.elements es_inter)))));
      es_inter <> Expr.Set.empty in 

    (* Strategy 2: Predicate has all literals as in-parameters *)
    let strategy_2 ((name, args) : string * Val.t list) : bool = 
      print_local_info 2 name args;
      let pred_def = get_pred_def name in 
      let in_args  = Pred.in_args pred_def args in
      let all_literals = List.map (fun (x : Expr.t) -> (match x with Lit _ -> true | _ -> false)) (List.map Val.to_expr in_args) in 
      List.for_all (fun x -> x = true) all_literals in 

    (* Strategy 3: Predicate has non-literal parameters in pure formulae *)
    let strategy_3 ((name, args) : string * Val.t list) : bool = 
      print_local_info 3 name args;
      let lvars_state = State.get_spec_vars state in
      let lvars_args  = List.fold_left SS.union SS.empty (List.map (fun x -> Expr.lvars (Val.to_expr x)) args)  in 
      let inter       = SS.inter lvars_args lvars_state in 
      inter <> SS.empty in 

    let index = apply_strategies [ strategy_1; strategy_2; strategy_3 ] in 
    match index with 
      | None       -> None 
      | Some index -> 
          let pred_a = Preds.get_index preds index in 
          Preds.remove_index preds index; 
          Some pred_a      


  let produce_assertion 
    (astate  : t) 
    (subst   : Subst.t)
    (a       : Asrt.t) : t option =  
    
    let state, preds, pred_defs = astate in 
    L.log L.Verboser (lazy ( 
      Printf.sprintf "------------------------\nProduce simple assertion: %s\nSubst:%s\nSTATE:\n%s\nPREDS:\n%s\n" 
        (Asrt.str a) (Subst.str subst) (State.str state) (Preds.str preds)
    )); 

    match a with 
      | PointsTo(le1, le2, le3) -> 
          let loc  = subst_in_expr subst le1 in 
          let prop = subst_in_expr subst le2 in 
          let v    = subst_in_expr subst le3 in 
          (match loc, prop, v with 
            | Some loc, Some prop, Some v ->
                Option.map_default 
                  (fun (state', loc) ->
                    let state'' = State.set_cell state' loc prop (Some v) in 
                    Some (state'', preds, pred_defs) 
                  ) None (State.to_loc state loc) 
            | _ -> None)

      | MetaData (le1, le2) -> 
          let loc  = subst_in_expr subst le1 in 
          let mtdt = subst_in_expr subst le2 in 
          (match loc, mtdt with 
            | Some loc, Some mtdt ->
                let result = Option.map_default 
                  (fun (state', loc) ->
                    let state'' = State.set_metadata state' loc mtdt in 
                    Some (state'', preds, pred_defs) 
                  ) None (State.to_loc state loc) in 
                result
            | _ -> None)
      
      | EmptyFields (le1, le2) -> 
          let loc    = subst_in_expr subst le1 in 
          let domain = subst_in_expr subst le2 in
          (match loc, domain with 
            | Some loc, Some domain -> 
                Option.map_default 
                  (fun (state', loc) ->
                    let state'' = State.set_domain state' loc domain in 
                    Some (state'', preds, pred_defs)
                  ) None (State.to_loc state loc) 
            | _ -> None)
        
      | Types les ->
          let state' = 
            List.fold_left 
              (fun state (le, t) ->
                (match state with 
                  | None -> None 
                  | Some state -> 
                      let v = subst_in_expr subst le in
                      (match v with 
                      | None -> None 
                      | Some v -> State.assume_t state v t)))
              (Some state) les in 
          Option.map (fun state -> state, preds, pred_defs) state' 

      | Pred (pname, les) -> 
          let vs = List.map (subst_in_expr subst) les in 
          let failure = List.exists (fun x -> x = None) vs in
          if (failure) then None else (
            let vs = List.map Option.get vs in 
            Preds.extend preds (pname, vs);  
            Some (state, preds, pred_defs) 
          ) 

      | Pure (Eq ((PVar x), le))
      | Pure (Eq (le, (PVar x))) -> 
          if (Subst.mem subst x) 
            then (
              let v_x  = Subst.get subst x in 
              let v_le = subst_in_expr subst le in 
              match v_x, v_le with 
                | Some v_x, Some v_le -> 
                    Option.map_default 
                      (fun state -> Some (state, preds, pred_defs))
                      None 
                      (State.assume_a state [ Eq (Val.to_expr v_x, Val.to_expr v_le) ])
                | _ -> None   
            ) else ( 
               Option.map_default 
                 (fun v -> 
                   L.log L.Verboser (lazy (Printf.sprintf "UNHAPPY. update_store inside produce assertions with prog variable: %s!!!\n" x));
                   Some (update_store astate x v)) 
                 None (subst_in_expr subst le)
            )

      | Pure f -> 
        let sbst_lst = Subst.to_ssubst subst in 
        let sbst     = SSubst.init sbst_lst in
        let f'       = Formula.substitution sbst false f in 
        L.log L.Verbose (lazy (Printf.sprintf "About to assume %s in state %s" (Formula.str f') (State.str state)));
        (match State.assume_a state [ f' ] with 
          | None -> None 
          | Some state' -> 
              SSubst.iter sbst 
                (fun x le -> 
                  if (not (Subst.mem subst x)) then (
                    match Val.from_expr le with 
                    | Some v ->  Subst.put subst x v 
                    | None -> L.fail "Produce simple assertion: did not obtain a value." 
                  )
                ); 
              Some (state', preds, pred_defs))

      | _ -> L.fail "Produce simple assertion: unsupported assertion"

  
  let produce_asrt_list 
      (astate  : t)
      (subst   : Subst.t)
      (sas     : Asrt.t list) : t option = 
    
    let state, preds, _ = astate in 
    let _            = Subst.iter subst (fun v value -> Subst.put subst v (State.simplify_val state value)) in   
    let rec loop (loop_state : (Asrt.t list) * t) : t option  = 
      match loop_state with 
        | ([ ], astate) ->
            Some astate
        | ( a :: rest_as, astate) -> 
          let ret = produce_assertion astate subst a in 
          (match ret with 
            | Some astate' -> loop (rest_as, astate')
            | None        -> None) in 
    
    let ret = loop (sas, astate) in 
    ret 


  let produce 
      (astate : t) 
      (subst  : Subst.t)
      (a      : Asrt.t) : t option =   

    L.log L.Verbose (lazy (Printf.sprintf "-----------------\n-----------------\nProduce assertion: %s" (Asrt.str a)));   
    let sas = UP.collect_simple_asrts a in 
    produce_asrt_list astate subst sas 
    

  let produce_posts 
      (state  : t) 
      (subst  : Subst.t)
      (asrts  : Asrt.t list) : t list = 
    L.log L.Verboser (lazy (Printf.sprintf "Produce posts: There are %d postconditions to produce. And here they are:\n%s" 
      (List.length asrts) (String.concat "\n" (List.map Asrt.str asrts))));
    let rets = 
      List.map 
        (fun a -> 
          let subst = Subst.copy subst in 
          produce (copy_astate state) subst a, subst) asrts in 
    let rets = List.filter (fun (x, _) -> x <> None) rets in 
    let rets = 
      List.map 
        (fun (x, subst) -> 
          let state = Option.get x in 
          Subst.iter subst (fun x v -> if (is_pvar_name x) then (update_store state x v; ()));
          state) rets in 
    rets 

  
  let use_unfold_info
    (unfold_info : (string * ((string * Expr.t) list)) option)
    (pred        : Pred.t)
    (state       : State.t)
    (subst       : Subst.t) : Asrt.t list = 
    match unfold_info with
    | None -> List.map (fun (_, x) -> x) pred.definitions    
    | Some (def_id, bindings) ->
      let defs     = 
        List.filter 
          (fun (os, a) -> 
            match os with 
              | None -> false 
              | Some (def_id', _) -> def_id' = def_id)
          pred.definitions in 
      let defs'    = List.map (fun (os, a) -> a) defs in 
      let bindings = List.map (fun (x, e) -> x, State.eval_expr state e) bindings in 
      Subst.extend subst bindings; 
      L.log L.Verboser (lazy (Printf.sprintf "Using unfold info, obtained subst:\n%s\n" 
            (Subst.str subst)));
      defs' 



  let unfold 
      (astate      : t) 
      (pname       : string)
      (args        : Val.t list)
      (unfold_info : (string * ((string * Expr.t) list)) option) : (Subst.t * t) list =
    
    let state, preds, pred_defs = astate in 
    let pred         = UP.get_pred_def pred_defs pname in 
    let params       = List.map (fun (x, _) -> x) pred.pred.params in 
    L.log L.Verboser (lazy 
      (Printf.sprintf "Combine going to explode. Params: %s. Args: %s"
        (String.concat ", "  params)
        (String.concat ", " (List.map Val.str args)))); 
    let subst_i = Subst.init (right_combine params args) in 
    
    L.log L.Verboser (lazy (Printf.sprintf "unfold with unfold_info with:\n%s\n" 
            (SLCmd.str_of_folding_info unfold_info)));

    let rets = 
      match use_unfold_info unfold_info pred.pred state subst_i with 
      | []                     -> raise (Failure "Cannot Unfold Predicate with No Definitions")
      | def :: rest_defs  ->
          (* QUESTION? : Add spec vars to state 
          let exprs : Expr.t list = Option.map_default (fun (_, unfold_info) -> let _, exprs = List.split unfold_info in exprs) [] unfold_info in
          let vars  : Var.t option list = List.map (fun x -> match x with | Expr.LVar x when is_spec_var_name x -> Some x | _ -> None) exprs in 
          let vars  : Var.t list = List.map Option.get (List.filter (fun x -> x <> None) vars) in 
          let (state, preds, pred_table) = astate in 
          let state' = State.add_spec_vars state (SS.of_list vars) in 
          let astate = (state', preds, pred_table) in *)

          L.log L.Verboser (lazy (Printf.sprintf "Going to produce %d definitions with subst\n%s" 
            (List.length (def :: rest_defs)) (Subst.str subst_i)));
          let results = 
            List.map 
              (fun def -> produce (copy_astate astate) (Subst.copy subst_i) def)
              rest_defs in 
          let first_result = produce astate subst_i def in 
          let results = List.filter (fun x -> x <> None) (first_result :: results) in 
          let results = List.map Option.get results in 
          let results = List.map (fun x -> (simplify_astate x), x) results in 
            results in
    
    let rets_str () = 
      String.concat "\n " 
        (List.mapi 
          (fun i (subst, astate) -> Printf.sprintf "Result %d\nSTATE:\n%s\nSUBST:%s\n" i (string_of_astate astate) (Subst.str subst))
          rets) in 
    
    L.log L.Verboser (lazy (Printf.sprintf "Results of unfolding %s(%s):\n%s" pname (String.concat ", "  params) (rets_str ()))); 
    rets


  let rec rec_unfold
      (astate    : t) 
      (pname     : string)
      (args      : Val.t list) : t =
    
    let saved_state = copy_astate astate in 

    match unfold astate pname args None with 
      | [ _, astate ] -> 
        let _, preds, _ = astate in 
        let pred_asrts  = Preds.find_pabs_by_name preds pname in 
        (match pred_asrts with 
        | [ pred_asrt ] -> 
          (match Preds.remove_by_name preds pname with 
            | Some (pname, vs) -> 
                rec_unfold astate pname vs 
            | None -> raise (Failure "DEATH. rec_unfold"))
        | _ -> astate)
      | _ -> saved_state
   

  let unfold_all 
      (astate    : t) 
      (pname     : string) : t =    
    L.log L.Verboser (lazy "Starting UNFOLD ALL\n");
    let rec loop astate = 
      let _, preds, _ = astate in  
      (match Preds.remove_by_name preds pname with 
        | None ->
            L.log L.Verboser (lazy (Printf.sprintf "Finishing Unfond_all with state:%s\n" (string_of_astate astate))); 
            astate
        | Some (pname, vs) ->
           let astate = rec_unfold astate pname vs in 
           L.log L.Verboser (lazy "IN UNFOLD ALL - ONE SUCCESSFUL CALL TO REC UNFOLD\n"); 
           loop astate) in 
    loop astate


  let unfold_with_vals  
      (astate     : t)
      (vs         : Val.t list) : (Subst.t * t) list * bool = 
    
    L.log L.Verboser (lazy (Printf.sprintf "Starting unfold_with_vals: %s\n%s.\n" 
      (String.concat ", " (List.map Val.str vs)) (string_of_astate astate))); 
  
    if (!CCommon.manual_proof) then [ Subst.init [], astate ], false else (
        match get_pred_with_vs astate vs with 
          | Some (pname, v_args) ->
              L.log L.Verboser (lazy (Printf.sprintf "FOUND STH TO UNFOLD!!!!\n")); 
              let rets = unfold (copy_astate astate) pname v_args None in
              L.log L.Verboser (lazy (Printf.sprintf "Unfold complete: %s(%s)" pname (String.concat ", " (List.map Val.str v_args)))); 
              List.iteri
                (fun i (subst, astate) -> 
                  L.log L.Verboser (lazy (Printf.sprintf "Result of UNFOLD %d:\n%s\nSubst:\n%s\n" 
                    i (string_of_astate astate) (Subst.str subst)))) 
                rets;
              rets, true 
          
          | None -> (
              L.log L.Verboser (lazy (Printf.sprintf "NOTHING TO UNFOLD!!!!\n")); 
              [ Subst.init [], astate ], false
            )
    )

  

   let unfold_concrete_preds (astate : t) : (st option * t) option = 
      let state, preds, pred_defs = astate in 

      let is_unfoldable_lit lit = 
        match lit with 
          | Loc _ | LList _ -> false 
          | _ -> true in 

     let should_unfold (pname, vs) =
        let pred       = UP.get_pred_def pred_defs pname in  
        let vs_ins     = Pred.in_args pred.pred vs in 
        let lit_ins    = get_list_somes (List.map Val.to_literal vs_ins) in 
        let flash_lits = List.map is_unfoldable_lit lit_ins in 
        List.exists (fun x -> x) flash_lits in 
      
      let pred_to_unfold = Preds.find false preds should_unfold in
      match pred_to_unfold with 
        | Some (name, vs) -> 
          let astate' = copy_astate astate in 
          let next_states = unfold astate name vs None in 
          (match next_states with  
            | [ ] -> None 
            | [ subst, astate'' ] -> 
                L.log L.Verboser (lazy (Printf.sprintf 
                  "unfold_concrete_preds WORKED. Unfolded: %s(%s)"
                  name (String.concat ", " (List.map Val.str vs)))); 
                Some ((Some subst), astate'')
            | _  -> Some (None, astate'))
        | None -> Some (None, astate) 


  (**
    Unification of two logical expressions

    @param subst  Substitution 
    @param le     Value
    @param le_pat Logical expression

    @return If the unification is possible: set of newly found variables, list of discharges
            and updates the substitution destructively  
  *)
  let rec unify_expr_core (state : State.t) (subst : Subst.t) (v : Val.t) (le_pat : Expr.t) : (SS.t * ((Val.t * Expr.t) list)) option = 
    L.log L.TMI (lazy (Printf.sprintf "unify_expr_core: val: %s. le_pat: %s. subst: %s" (Val.str v) (Expr.str le_pat) (Subst.str subst))); 

    let f = unify_expr_core state subst in 
    
    let eval_expr = State.eval_expr state in 

    let f2 v1 le_pat1 v2 le_pat2 =
      Option.map_default 
        (fun (new_vars1, discharges1) ->  
          Option.map_default 
            (fun (new_vars2, discharges2) -> Some (new_vars2, discharges1 @ discharges2))
            None (f v2 le_pat2)
        ) None (f v1 le_pat1) in 

    match le_pat with
      | Lit _ 
      | Nono  -> 
          let le = Val.to_expr v in 
          if (le = le_pat) 
            then Some (SS.empty, [])
            else Some (SS.empty, [ (v, le_pat) ])

      | PVar x 
      | LVar x -> 
          (match Subst.get subst x with 
            | Some v' -> Some (SS.empty, [ (v, Val.to_expr v') ])
            | None    ->
                let v' = State.simplify_val state v in   
                Subst.put subst x v'; Some (SS.singleton x, [ ]))

      | ALoc x -> 
          (match Subst.get subst x with 
            | Some v' -> Some (SS.empty, [ (v, Val.to_expr v') ])
             | None    ->
                let v' = State.simplify_val state v in   
                let tv = State.get_type state v' in 
                (match tv with 
                  | Some ObjectType 
                  | None   -> Subst.put subst x v'; Some (SS.singleton x, [ ])
                  | Some _ -> None))
      
      | BinOp (le_pat1, Plus, Lit (Num i)) 
      | BinOp (Lit (Num i), Plus, le_pat1) -> 
          let le  : Expr.t = Val.to_expr v in 
          let le1 : Expr.t = BinOp (le, Minus, Lit (Num i)) in 
          let v1  : Val.t  = eval_expr le1 in 
          f v1 le_pat1 

      | BinOp (le_pat1, LstCons, le_pat2)  -> 
          let le  : Expr.t = Val.to_expr v in 
          let le1 : Expr.t = UnOp (Car, le) in 
          let le2 : Expr.t = UnOp (Cdr, le) in
          let v1  : Val.t  = eval_expr le1 in 
          let v2  : Val.t  = eval_expr le2 in    
          f2 v1 le_pat1 v2 le_pat2 

      | BinOp (EList (le_pat_hd :: le_pat_tl), LstCat, le_pat2) ->
          let le  : Expr.t = Val.to_expr v in 
          let le1 : Expr.t = UnOp (Car, le) in
          let le2 : Expr.t = UnOp (Cdr, le) in
          let v1  : Val.t  = eval_expr le1 in 
          let v2  : Val.t  = eval_expr le2 in 
          f2 v1 le_pat_hd v2 (BinOp (EList le_pat_tl, LstCat, le_pat2)) 
      
      (* | BinOp (le_pat1, LstCat, EList le_pat2) when (List.length le_pat2) > 0 ->
          (match List.rev le_pat2 with 
            | le_pat2_last :: le_pat2_prefix -> 
              let le  : Expr.t = Val.to_expr v in 
              let le1 : Expr.t = UnOp (Car, UnOp (LstRev, le)) in
              let le2 : Expr.t = UnOp (Cdr, UnOp (LstRev, le)) in
              let v1  : Val.t  = eval_expr le1 in 
              let v2  : Val.t  = eval_expr le2 in 
              f2 v1 le_pat2_last v2 (BinOp (EList le_pat2_prefix, LstCat, UnOp (LstRev, le_pat1)))
            | _ -> raise (Failure "DEATH. unify_expr_core")) *)

      | BinOp (EList [], LstCat, le_pat2) -> f v le_pat2 

      | BinOp (le_pat1, LstCat, EList []) -> f v le_pat1 

      | UnOp (LstRev, le_pat) -> 
          let le  : Expr.t = Val.to_expr v in 
          let le' : Expr.t = UnOp (LstRev, le) in 
          let v1  : Val.t  = eval_expr le' in 
          f v1 le_pat 

      | EList (le_pat_hd :: le_pat_tl) -> 
          let le  : Expr.t = Val.to_expr v in 
          let le1 : Expr.t = UnOp (Car, le) in
          let le2 : Expr.t = UnOp (Cdr, le) in
          let v1  : Val.t  = eval_expr le1 in 
          let v2  : Val.t  = eval_expr le2 in 
          f2 v1 le_pat_hd v2 (EList le_pat_tl)  

      | _ -> Some (SS.empty, [ v, le_pat ]) 


   (* I don't know how much recovery information we can give when the unification of lexprs fails *)
    let unify_lexpr  (state : State.t) (subst : Subst.t) (v : Val.t) (le : Expr.t) : bool = 
      let le      = Reduction.reduce_lexpr le in 
      L.log L.Verboser (lazy (
        (Printf.sprintf "Unify lexpr with v: %s, le: %s" (Val.str v) (Expr.str le))));
      
      try (
        let ret     = unify_expr_core state subst v le in 
        let ret_str = 
          match ret with 
            | None -> "None"
            | Some (vars, les) -> Printf.sprintf "Some { %s }, [ %s ]" 
                (String.concat ", " (SS.elements vars)) 
                (String.concat ", " (List.map (fun (a, b) -> "(" ^ (Val.str a) ^ ", " ^ (Expr.str b) ^ ")") les)) in 
        L.log L.Verboser (lazy ("Unify lexpr: Entering stage 1 with " ^ ret_str));
      
        match ret with 
          | None -> false 
          | Some (new_vars, discharges) -> 
              let eqs : Formula.t list = 
                List.map 
                  (fun (v1, e2) -> 
                    L.log L.Verboser (lazy (Printf.sprintf "Unify lexpr: Passed to stage 2: %s %s" (Val.str v1) (Expr.str e2)));
                    let v1' = State.simplify_val state v1 in 
                    Formula.Eq (Val.to_expr v1', e2)) discharges in 
              State.assert_a state eqs
      ) with | Reduction.ReductionException _ -> false


  let unify_lexprs (state : State.t) (subst : Subst.t) (lst : (Val.t * Expr.t) list) : bool = 
    List.fold_left 
      (fun b (v, le) -> if b then unify_lexpr state subst v le else false)
      true lst 



  let complete_subst (subst : Subst.t) (lab : (string * SS.t) option) : bool = 
    match lab with 
      | None -> true
      | Some (_, existentials) -> 
          List.fold_left 
            (fun ac x -> 
              if (not (Subst.mem subst x))
                then (
                  let new_lvar = Expr.LVar x in 
                  let v_x  = Val.from_expr new_lvar in 
                  match v_x with 
                    | None     -> false
                    | Some v_x -> Subst.put subst x v_x; true  
                ) else ac 
            ) true (SS.elements existentials)


  let rec get_pred  
      ?(in_unification : bool option)
      (astate          : t) 
      (pname           : string) 
      (vs_ins          : vt list) : gp_ret = 
    
    let merge_gp_results (rets : gp_ret list) : gp_ret = 
      let ret_succs, ret_fails = List.partition (fun ret -> match ret with | GPSucc _ -> true | _ -> false) rets in
      if (ret_fails <> []) 
        then (
          let errs = List.map (fun ret -> match ret with | GPFail errs -> errs | _ -> []) ret_fails in 
          GPFail (List.concat errs) 
        ) else (
          let rets = List.map (fun ret -> match ret with | GPSucc rets -> rets | _ -> []) ret_succs in 
          GPSucc (List.concat rets)
        ) in 

    L.log L.TMI (lazy (Printf.sprintf "get_pred %s. args: %s" pname (String.concat ", " (List.map Val.str vs_ins)))); 
     
    let state, preds, pred_defs  = astate in 
    let pred                     = UP.get_pred_def pred_defs pname in
    let pred_def                 = pred.pred in
    let pred_pure                = pred.pure in
    match Preds.get_pred pred_pure preds pname vs_ins pred_def.ins (State.equals state) with 
      | Some (_, vs) -> 
          L.log L.Verboser (lazy (Printf.sprintf "Returning the following vs: %s" (String.concat ", " (List.map Val.str vs)))); 
          GPSucc [ astate, Pred.out_args pred_def vs ]  
      | _ -> 
        (** Recursive Case - Folding required *)
        L.log L.Verbose (lazy "Recursive case - attempting to fold."); 
        let up            = pred.up in 
        let param_ins     = Pred.in_params pred.pred in 
        let subst         = Subst.init (List.combine param_ins vs_ins) in
        (match unify ?in_unification:in_unification astate subst up with 
          | UPUSucc rets ->
            let rets = 
              List.map   
                (fun (astate', subst', _) -> 
                  L.log L.Verbose (lazy "Recursive fold success."); 
                  let out_params = Pred.out_params pred_def in 
                  let vs_outs    = List.map (Subst.get subst') out_params in 
                  L.log L.Verboser (lazy (Printf.sprintf "Out parameters : %s" (String.concat ", " (List.map (Option.map_default Val.str "None") vs_outs))));
                  let failure    = List.exists (fun x -> x = None) vs_outs in 
                  if failure then GPFail [ ESpec ( vs_ins, True, []) ] else (
                    let vs_outs  = List.map Option.get vs_outs in 
                    GPSucc [ astate', vs_outs ]
                  ) 
                ) rets in 
            merge_gp_results rets
          | UPUFail errs -> GPFail errs) 


  and unify_assertion 
      (astate    : t) 
      (subst     : Subst.t) 
      (p         : Asrt.t) : u_res = 
   
    let subst_in_expr_opt = subst_in_expr_opt astate subst in 
    let subst_in_expr     = subst_in_expr subst in

    let make_resource_fail () = UFail [ Error.ESpec ([], True, []) ] in 

    L.log L.Verbose 
       (lazy (Printf.sprintf "Unify assertion: %s\nSubst:\n\t%s\nSTATE:\n%s"
         (Asrt.str p) (Subst.str subst) (string_of_astate astate))); 
    
    let state, preds, pred_defs = astate in 

    (match (p : Asrt.t) with 
    | PointsTo (le1, le2, le3) -> 
        let loc  = subst_in_expr_opt le1 in 
        let prop = subst_in_expr_opt le2 in 
        (match loc, prop with 
        | Some loc, Some prop ->
            let m_err = UFail [ Error.ESpec ([ loc ], True, []) ]  in 
            (match State.get_cell ~remove:true state loc prop with 
              | GCSucc [ state', _, _, op ] -> 
                (match op with 
                  | None -> 
                    L.log L.Verboser (lazy "Unify GetCell returns none"); 
                    (match Val.from_expr Expr.Nono with 
                      | Some v_nono -> 
                          if unify_lexpr state' subst v_nono le3 
                            then USucc (state', preds, pred_defs) 
                            else UFail [ Error.ESpec ([ loc ], True, [ ]) ] 
                      | None -> 
                          if Expr.Nono = le3 
                            then USucc (state', preds, pred_defs) 
                            else UFail [ Error.ESpec ([ loc ], True, [ ]) ])
                  | Some p_val -> 
                      L.log L.Verboser (lazy (Printf.sprintf "Unify get cell returns some thing")); 
                      if unify_lexpr state' subst p_val le3 
                        then USucc (state', preds, pred_defs) 
                        else (
                          match subst_in_expr le3 with
                            | Some v3 -> UFail [ Error.ESpec ([ loc ], True, [ [ MCellV (loc, prop, v3) ] ]) ]
                            | None ->  UFail [ Error.ESpec ([ loc ], True, [ ]) ]
                        )) 

              | GCSucc _ -> raise (Failure "DEATH. BRANCHING GETCELL INSIDE UNIFICATION.")

              | GCFail errs ->  
                  L.log L.Verboser (lazy (Printf.sprintf "GETCell returned errors:\n%s\nCUR STATE:\n%s"
                    (String.concat ", " (List.map Error.str errs)) (string_of_astate astate)));
                  (match State.get_metadata ~remove:false state loc, subst_in_expr le3 with 
                    | GMSucc [ _, loc, _ ], Some v3 -> UFail [ Error.ESpec ([ loc ], True, [ [ MCellV(loc, prop, v3) ] ]) ]
                    | _, Some v3 -> UFail [ Error.ESpec ([ loc ], True, [ [ MLCellV(loc, prop, v3) ] ]) ]
                    | _ -> UFail [ Error.ESpec ([ loc ], True, [ ]) ]))    
        | _ -> make_resource_fail ())

    | MetaData (le1, le2) -> 
        let loc  = subst_in_expr_opt le1 in  
        (match loc with 
          | Some loc -> 
              (match State.get_metadata ~remove:false state loc with 
                | GMSucc [ state', _, mtdt ] ->
                    if unify_lexpr state' subst mtdt le2 
                      then USucc (state', preds, pred_defs) 
                      else (
                        match subst_in_expr le2 with
                          | Some v2 -> UFail [ Error.ESpec ([ loc ], True, [ [ MMetadataV (loc, v2) ] ]) ]
                          | None -> UFail [ Error.ESpec ([ loc ], True, [ ]) ]
                      )

                | GMSucc _ -> raise (Failure "DEATH. BRANCHING GETMETADATA INSIDE UNIFICATION.")

                | GMFail errs -> 
                    (match subst_in_expr_opt le2 with 
                      | Some v2 -> UFail [ Error.ESpec ([ loc ], True, [ [ MMetadataV (loc, v2) ] ]) ]
                      | None -> UFail errs))
          | None -> make_resource_fail ())
    
    | EmptyFields (le1, le2) -> 
        let loc    = subst_in_expr_opt le1 in 
        let domain = subst_in_expr_opt le2 in
        (match loc, domain with 
          | Some loc, Some domain -> 
              L.log L.Verboser (lazy (Printf.sprintf "Got domain: %s -> %s" (Val.str loc) (Val.str domain)));
              (match State.get_domain ~expected_props:domain ~remove:true state loc with  
                | GDSucc [ state', domain' ] -> 
                  
                  L.log L.Verboser (lazy (Printf.sprintf "Got domain': %s -> %s" (Val.str loc) (Val.str domain')));
                  let ldom  = Val.to_expr domain  in 
                  let ldom' = Val.to_expr domain' in

                  let dd : Expr.t  = Val.to_expr (State.eval_expr state' (Expr.BinOp (ldom, SetDiff, ldom'))) in 
                  let dfd : Expr.t = Val.to_expr (State.eval_expr state' (Expr.BinOp (ldom', SetDiff, ldom))) in 
  
                  L.log L.Verboser (lazy (Printf.sprintf "DD: %s\nDFD: %s" (Expr.str dd) (Expr.str dfd)));

                  (match dd, dfd with 
                    | ESet dd, ESet [] ->
                        List.iter 
                          (fun v_prop -> 
                            match Val.from_expr v_prop with 
                              | Some v_prop -> State.set_cell state' loc v_prop None; ()
                              | _ -> raise (Failure "DEATH. unify_assertion. EmptyFields")) 
                          dd; 
                        USucc (state', preds, pred_defs)     
                    | _, ESet props -> 
                      let prop_vs = List.map Val.from_expr props in 
                      let success = List.for_all (fun x -> x <> None) prop_vs in 
                      if (success) 
                        then (
                          let prop_vs = List.map Option.get prop_vs in 
                          UFail [ Error.ESpec (loc :: prop_vs, True, []) ]
                        ) else raise (Failure "DEATH. unify_assertion. EmptyFields"))
                
                | GDSucc _ -> raise (Failure "DEATH. BRANCHING GETDOMAIN INSIDE UNIFICATION.")

                | GDFail errs -> UFail errs) 
          | _ -> raise (Failure "DEATH. unify_assertion. EmptyFields"))


    | Pure (Eq (le1, le2)) when (UP.outs_expr le1 <> SS.empty) -> 
        let res_fail = make_resource_fail () in 
        let v2 = subst_in_expr_opt le2 in
        Option.map_default 
          (fun v2 -> 
            if unify_lexpr state subst v2 le1 
              then USucc astate 
              (** CHANGE IS REQUIRED BABYYYY!!!!!! *)
              else (
                match subst_in_expr le1 with
                  | Some v1 -> UFail [ Error.ESpec ([ v2 ], True, [ [ MPF (Eq (Val.to_expr v2, Val.to_expr v1))] ]) ]
                  | None -> UFail [ Error.ESpec ([ v2 ], True, [ ]) ]
              )) res_fail v2 
       
    | Types les -> 
        let corrections = 
          List.fold_left 
            (fun (ac : Formula.t list) (le, t) -> 
              let v_le = subst_in_expr_opt le in 
              let v_le : vt = 
                match v_le with 
                  | Some v_le -> v_le 
                  | None -> raise (Failure "DEATH. unify assertion Types") in 
              match State.get_type state v_le with 
                | Some t' -> if (t <> t') then False :: ac else ac 
                | None -> Eq (UnOp (TypeOf, Val.to_expr v_le), Lit (Type t)) :: ac) 
            [] les in
      
        if (corrections = []) then USucc astate else (
            let les, _ = List.split les in 
            let les = List.map subst_in_expr_opt les in 
              UFail [ Error.ESpec ((List.map Option.get (List.filter (fun x -> x <> None) les)), True,  [ [ Error.MPF (Formula.conjunct corrections) ] ])  ])

    | Pred (pname, les) ->
        let pred      = UP.get_pred_def pred_defs pname in 
        let pred_def  = pred.pred in
        let les_ins   = Pred.in_args pred_def les in
        let vs_ins    = List.map subst_in_expr_opt les_ins in
        let failure   = List.exists (fun x -> x = None) vs_ins in
        
        L.log L.Verbose (lazy "Unifying predicate assertion"); 
        if failure then make_resource_fail () else (
          let vs_ins          = List.map Option.get vs_ins in  
          (match get_pred ~in_unification:true astate pname vs_ins  with 
            | GPSucc [] -> 
              L.log L.Verboser (lazy "SUCCEEDED WITH NOTHING! MEDOOOOOO!!!!!"); UWTF

            | GPSucc [ astate', vs_outs ] -> 
              let les_outs  = Pred.out_args pred_def les in 
              L.log L.Verboser (lazy (Printf.sprintf "learned the outs of a predicate. going to unify (%s) against (%s)!!!\n" 
                  (String.concat ", " (List.map Val.str vs_outs))
                  (String.concat ", " (List.map Expr.str les_outs)))) ; 
              let state', _, _ = astate' in 
              if unify_lexprs state' subst (List.combine vs_outs les_outs) 
                then USucc astate'
                else make_resource_fail ()
            
            | GPSucc _ -> raise (Failure "DEATH. BRANCHING GETPRED INSIDE UNIFICATION.")

            | GPFail errs -> 
                make_resource_fail ()))

    | Pure f -> 
        let sbst_lst = Subst.to_ssubst subst in 
        let sbst     = SSubst.init sbst_lst in
        let f'       = Formula.substitution sbst false f in 
        if (State.assert_a state [ f' ]) 
          then USucc astate 
          else (
            let vs = State.unfolding_vals state [ f' ] in 
            UFail [ Error.ESpec (vs, Not f, [ [ Error.MPF f' ] ]) ]
          )

    (* LTrue, LFalse, LEmp, LStar*)
    | _ -> raise (Failure "Illegal Assertion in Unification Plan"))
  

  and unify_up 
      (s_states    : search_state) : up_u_res = 
    
    let s_states, errs_so_far = s_states in  
    L.log L.Verboser (lazy (Printf.sprintf "Unify UP: There are %d states left to consider." (List.length s_states)));
    let f = unify_up in 
    (match s_states with 
    | [] -> UPUFail errs_so_far
    | (state, subst, up) :: rest -> 
        let cur_asrt : Asrt.t option = UP.head up in 
        let ret = Option.map_default (unify_assertion state subst) (USucc state) cur_asrt in 
          (match ret with 
            | UWTF -> UPUSucc []  

            | USucc state' -> 
                (match UP.next up with
                  | None -> UPUSucc [ state', subst, (UP.posts up) ] 
                  | Some [ (up, lab) ] -> 
                      if (complete_subst subst lab) 
                        then f (((state', subst, up) :: rest), errs_so_far)
                        else f (rest, errs_so_far) 
                  | Some ((up, lab) :: ups')  ->
                      let next_states = 
                        List.map 
                          (fun (up, lab) -> 
                            let new_subst = Subst.copy subst in 
                            let new_state = copy_astate state' in 
                            if (complete_subst new_subst lab)
                              then Some (new_state, new_subst, up)
                              else None)
                          ups' in 
                      let next_states = get_list_somes next_states in 
                      let next_states = 
                        if (complete_subst subst lab)
                          then (state', subst, up) :: next_states 
                          else next_states in 
                      f ((next_states @ rest), errs_so_far)
                  | Some [] -> L.fail "ERROR: unify_up: empty unification plan"
                )

            | UFail errs -> 
                let cur_asrt_str = Option.map_default Asrt.str "no assertion - phantom node" cur_asrt in 
                L.log L.Verbose (lazy (Printf.sprintf "WARNING: Unify Assertion Failed: %s with errors: %s" 
                  cur_asrt_str (String.concat "\n" (List.map Error.str errs))));
                f (rest, (errs @ errs_so_far))
          )
    )
 
  and unify
      ?(in_unification : bool option)
      (astate          : t)
      (subst           : Subst.t)
      (up              : UP.t) : up_u_res =
    
    let astate_i       = copy_astate astate in 
    let subst_i        = Subst.copy subst in 
    let in_unification = Option.default false in_unification in 

    let merge_upu_res (rets : up_u_res list) : up_u_res = 
      let ret_succs, ret_fails = List.partition (fun ret -> match ret with | UPUSucc _ -> true | _ -> false) rets in
      if (ret_fails <> []) 
        then (
          let errs = List.map (fun ret -> match ret with | UPUFail errs -> errs | _ -> []) ret_fails in 
          UPUFail (List.concat errs) 
        ) else (
          let rets = List.map (fun ret -> match ret with | UPUSucc rets -> rets | _ -> []) ret_succs in 
          UPUSucc (List.concat rets)
        ) in

    let ret = unify_up ([ astate, subst, up ], []) in 
    match ret with  
      | UPUSucc _ -> ret 
      | UPUFail errs when (!SCommon.unfolding && (Error.can_fix errs) && (not in_unification)) -> 
          let vals = Error.get_recovery_vals errs in 
          L.log L.Verbose (lazy (Printf.sprintf "Unify. Unable to unify. Checking if there are predicates to unfold. Looking for: %s" (String.concat ", " (List.map Val.str vals)))); 
          let sp, worked = unfold_with_vals astate_i vals in 
          if (not worked) then (
            L.log L.Normal (lazy "Unify. No predicates found to unfold.");
            UPUFail errs
          ) else (
            L.log L.Verbose (lazy "Unfolding successful."); 
            let rets = 
              List.map 
                (fun (subst, astate) ->
                  match unfold_concrete_preds astate with 
                    | None -> UPUSucc [] 
                    | Some (_, astate) -> 
                        (* let subst'' = compose_substs (Subst.to_list subst_i) subst (Subst.init []) in *)
                        let subst'' = Subst.copy subst_i in 
                        unify_up ([ astate, subst'', up ], []))
                sp in 
            merge_upu_res rets 
          )
      | UPUFail errs -> ret 
end 
