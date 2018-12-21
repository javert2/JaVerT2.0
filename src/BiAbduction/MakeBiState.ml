open CCommon
open SCommon
open Literal 

module L = Logging

module M 
  (Val      : Val.M) 
  (Subst    : Subst.M with type vt = Val.t and type t = Val.st)
  (Store    : Store.M with type vt = Val.t) 
  (Error    : Error.M with type vt = Val.t and type st = Subst.t)
  (State    : State.M with type vt = Val.t and type st = Subst.t and type store_t = Store.t and type err_t = Error.t) = struct 

  module Preds     = MakePreds.M(Val)(Subst) 
  module AbsState  = MakeAbsState.M(Val)(Subst)(Store)(Error)(State)(Preds)
  module JSCleanUp = MakeJSCleanUp.M(Val)(Subst)(Store)(Error)(AbsState)

  type vt      = Val.t 
  type st      = Subst.t 
  type store_t = Store.t 
  type err_t   = Error.t 
  type state_t = State.t 
  type t       = SS.t * state_t * state_t 

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

  type fix_t = 
    | MCell      of vt * vt * vt 
    | MMetadata  of vt * vt 
    | MDomain    of vt * vt
    | MPF        of Formula.t
    | MType      of vt * Type.t 
    | MSVar      of string list 
    | MAsrt      of Asrt.t * Subst.t 


  let val_to_lvar (v : vt) : string option  = 
    match Val.to_expr v with 
      | LVar v_name -> Some v_name 
      | _ -> None 

  let complete_single_fix (procs : SS.t) (state : state_t) (fix : Error.fix_t) : fix_t list = 
    
    let fresh_object_fixes loc = 
      let loc'     = State.fresh_loc state in 
      let loc_m    = State.fresh_loc state in 
        loc', [ 
          MPF (Eq (Val.to_expr loc', Val.to_expr loc)); 
          MMetadata (loc', loc_m); 
          MMetadata (loc_m, Val.from_literal Null)
        ] in 

    match fix with 
      | MCell (loc, prop)    -> 
          let v = State.fresh_val state in
          let fix_svar = Option.map_default (fun v_name -> [ MSVar [ v_name ] ]) [] (val_to_lvar v) in 
          (MCell (loc, prop, v)) :: fix_svar 
      | MCellV (loc, prop, v) -> [ MCell (loc, prop, v) ]
      | MMetadata loc        -> 
          let loc_m = State.fresh_loc state in 
         [ MMetadata (loc, loc_m); MMetadata (loc_m, Val.from_literal Null) ]
      | MMetadataV (loc, v)  -> [ MMetadata (loc, v) ]
      | MDomain (loc, d_val) -> [ MDomain (loc, d_val) ]
      | MPF f                -> [ MPF f ]
      | MType (v, t)         -> [ MType (v, t) ]
      | MLCell (loc, prop)   -> 
          let loc', obj_fixes = fresh_object_fixes loc in 
          let v         = State.fresh_val state in 
          let fix_svar  = Option.map_default (fun v_name -> [ MSVar [ v_name ] ]) [] (val_to_lvar v) in 
          L.log L.Verboser (lazy (Printf.sprintf "Bi-abducing a new object at loc %s"
            (Val.str loc'))); 
          fix_svar @ [ MCell (loc', prop, v) ] @ obj_fixes
      | MLCellV (loc, prop, v) -> 
          let loc', obj_fixes = fresh_object_fixes loc in 
          [ MCell (loc', prop, v) ] @ obj_fixes
      | MLMetadata loc       -> 
          let loc', obj_fixes = fresh_object_fixes loc in 
          obj_fixes 
      | MLMetadataV (loc, v) -> 
          let loc' = State.fresh_loc state in 
          [ 
            MPF (Eq (Val.to_expr loc', Val.to_expr loc)); 
            MMetadata (loc', v)
          ]
          


(* ; Lit (String "@call"); Lit (String "@construct"); Lit (String "@scope") *)

  let complete_single_fix_js (procs : SS.t) (state : state_t) (fix : Error.fix_t) : fix_t list = 
 
    let new_metadata_fixes (loc_m : vt) : fix_t list = 
      let dom_fix = 
        match Val.from_expr (ESet [ Lit (String "@class"); Lit (String "@extensible"); Lit (String "@proto")]) with 
          | Some v_dom -> MDomain (loc_m, v_dom)
          | _ -> raise (Failure "DEATH. complete_single_fix_js") in 
      dom_fix ::   
        [ 
          MMetadata (loc_m, Val.from_literal Null); 
          MCell (loc_m, Val.from_literal (String "@class"), Val.from_literal (String "Object"));
          MCell (loc_m, Val.from_literal (String "@extensible"), Val.from_literal (Bool true)); 
          MCell (loc_m, Val.from_literal (String "@proto"), Val.from_literal (Loc JS2JSIL_Constants.locObjPrototype));
        ] in 

    let new_object_fixes ?(metadata : vt option) (loc : vt) : vt * (fix_t list) = 
      let loc_m     = 
        match metadata with 
          | None       -> State.fresh_loc state 
          | Some loc_m -> loc_m in 
      let loc'      = State.fresh_loc state in 
      let mtd_fixes = new_metadata_fixes loc_m in 
      let obj_fixes = 
        [ 
          MPF (Eq (Val.to_expr loc', Val.to_expr loc)); 
          MMetadata (loc', loc_m)
        ] in
          loc', (obj_fixes @ mtd_fixes) in 


    let new_prop_fixes_default (loc : vt) (prop : vt) : fix_t list = 
      let prop_val = State.fresh_val state in 
      let fix_svar = Option.map_default (fun v_name -> [ MSVar [ v_name ] ]) []  (val_to_lvar prop_val) in 
      let prop_val_desc = 
        match Val.from_expr (EList [ Lit (String "d"); Val.to_expr prop_val; Lit (Bool true); Lit (Bool true); Lit (Bool true)]) with 
          | Some prop_val_desc -> prop_val_desc 
          | _ -> raise (Failure "DEATH. complete_single_fix_js") in 
      let prop_val_not_empty : Formula.t = Not (Eq (Val.to_expr prop_val, Lit Empty)) in 
      let prop_val_not_desc  : Formula.t = Not (Eq (UnOp (TypeOf, (Val.to_expr prop_val)), Lit (Type ListType))) in 
        [MCell (loc, prop, prop_val_desc); MPF prop_val_not_empty; MPF prop_val_not_desc ] @ fix_svar in 


    let new_prop_function (loc : vt) (prop : vt) (fun_def : Asrt.t) : fix_t list = 
      let fun_loc = State.fresh_loc state in 
      let prop_val_desc = 
        match Val.from_expr (EList [ Lit (String "d"); Val.to_expr fun_loc; Lit (Bool true); Lit (Bool true); Lit (Bool true)]) with 
          | Some prop_val_desc -> prop_val_desc 
          | _ -> raise (Failure "DEATH. complete_single_fix_js") in 
      let subst_i = Subst.init [ ("x", fun_loc) ] in 
      [ MCell (loc, prop, prop_val_desc); MAsrt(fun_def, subst_i) ] in 


    let new_prop_fixes_reserved_method (loc : vt) (prop : string) : fix_t list = 
      let ancestor_loc     = Hashtbl.find JSIL_PostParser.reserved_methods prop in 
      let ancestor_loc_val = Val.from_literal (Loc ancestor_loc) in 
      let proto_str_val    = Val.from_literal (String "@proto") in 
      let prop_val         = Val.from_literal (String prop) in 
      let nono_val         = Option.get (Val.from_expr Nono) in 
      match State.get_cell state loc proto_str_val with
        | GCSucc [ state', _, _, Some loc_proto ] -> 
            (match State.get_cell state loc_proto proto_str_val with    
              | GCSucc _ -> (** CANNOT FIX *) []
              | GCFail _ -> 
                (** Set the proto of the proto to Ancestor *)
                [ MCell(loc_proto, proto_str_val, ancestor_loc_val); MCell(loc_proto, prop_val, nono_val); MCell(loc, prop_val, nono_val) ]
            )
        | GCSucc _ -> 
          (** CANNOT FIX *)
          []
        | GCFail _ -> 
          (** Set the proto to Ancestor *)
          [ MCell(loc, proto_str_val, ancestor_loc_val);  MCell(loc, prop_val, nono_val) ] in
   
    let new_prop_fixes_reserved_property (loc : vt) (prop : string) : fix_t list = 
      let proto_loc, obj_pred, proto_pred = Hashtbl.find JSIL_PostParser.reserved_properties prop in 
      let proto_loc_val = Val.from_literal (Loc proto_loc) in 
      let proto_str_val = Val.from_literal (String "@proto") in
      match State.get_cell state loc proto_str_val with
        | GCSucc _ -> (** CANNOT FIX *) []
        | GCFail _ -> 
          (** Set the proto to Ancestor *)
            let pred_defs = State.get_pred_defs state in 
            L.log L.Verboser (lazy (Printf.sprintf "I will have to bi-abduce resource for the reserved property %s!!!\n" prop)); 
            (match pred_defs with 
              | None -> (** CANNOT FIX *) []
              | Some pred_defs ->
                  (* let pred_defs_str = UP.string_of_pred_defs pred_defs in *)
                  (* Printf.printf "there are pred_defs!!!\n"; *)
                  let pred_obj   = UP.get_pred_def pred_defs obj_pred in 
                  let pred_proto = UP.get_pred_def pred_defs proto_pred in 
                    (match List.map (fun (_, def) -> def) pred_obj.pred.definitions,  
                          List.map (fun (_, def) -> def) pred_proto.pred.definitions with 
                      | [ def_pred_obj ], [ def_pred_proto ] -> 
                        let subst_obj   = Subst.init [ ("x", loc) ] in 
                        let subst_proto = Subst.init [ ] in 
                        if (List.mem proto_loc_val (State.get_locs state)) 
                          then [ MAsrt(def_pred_obj, subst_obj);  ]
                          else [ MAsrt(def_pred_obj, subst_obj); MAsrt(def_pred_proto, subst_proto)]
                      | _ -> (** CANNOT FIX *) [])
              ) in  

    let new_prop_fixes (loc : vt) (prop : vt) : fix_t list = 
      match (Val.to_literal prop) with 
        | Some (String prop_name) 
              when Hashtbl.mem JSIL_PostParser.reserved_methods prop_name -> 
            new_prop_fixes_reserved_method loc prop_name

         | Some (String prop_name) 
              when Hashtbl.mem JSIL_PostParser.reserved_properties prop_name -> 
            new_prop_fixes_reserved_property loc prop_name        

        | Some (String prop_name)
              when SS.mem prop_name procs -> 
              let pred_defs = State.get_pred_defs state in 
              L.log L.Verboser (lazy (Printf.sprintf "Bi-abduce a function object for %s!!!\n" prop_name)); 
              (match pred_defs with 
                | None -> 
                    (* Printf.printf "nao ha pred_defs!!!\n"; *)
                    raise (Failure "no bi-abduce for functions")
                | Some pred_defs ->
                    (* let pred_defs_str = UP.string_of_pred_defs pred_defs in *)
                    (* Printf.printf "there are pred_defs!!!\n"; *)
                    let pred = UP.get_pred_def pred_defs (prop_name ^ "_FO_BI") in 
                    match List.map (fun (_, def) -> def) pred.pred.definitions with 
                      | [ def ] -> new_prop_function loc prop def 
                      | _ -> raise (Failure "no bi-abduce for functions")
              ) 

        | _ -> new_prop_fixes_default loc prop in 

    match fix with 
      | MCell (loc, prop)      -> new_prop_fixes loc prop 
      | MCellV (loc, prop, v)  -> [ MCell (loc, prop, v) ]
      | MMetadata loc          -> 
          let loc_m = State.fresh_loc state in 
          (MMetadata (loc, loc_m)) :: (new_metadata_fixes loc_m)
      | MMetadataV (loc, v)    -> [ MMetadata (loc, v) ]
      | MDomain (loc, d_val)   -> [ MDomain (loc, d_val) ]
      | MPF f                  -> [ MPF f ]
      | MType (v, t)           -> [ MType (v, t) ]
      | MLCell (loc, prop)     -> 
          let loc', obj_fixes  = new_object_fixes loc in  
          let prop_fixes = new_prop_fixes loc' prop in  
          prop_fixes @ obj_fixes 
      | MLCellV (loc, prop, v) -> 
          let loc', obj_fixes  = new_object_fixes loc in  
          (MCell (loc', prop, v)) :: obj_fixes    
      | MLMetadata loc       -> 
          let _, obj_fixes = new_object_fixes loc in 
          obj_fixes
      | MLMetadataV (loc, v)       -> 
          let loc', obj_fixes = new_object_fixes ~metadata:v loc in 
          obj_fixes


  let apply_fix (procs : SS.t) (state : state_t) (fixes : fix_t list) : state_t option = 
    List.fold_left 
      (fun (state : state_t option) (fix : fix_t) : state_t option ->
        match state, fix with 
          | None, _ -> None 
          | Some state, MCell (loc, prop, pval) -> Some (State.set_cell state loc prop (Some pval))
          | Some state, MMetadata (loc, pval)   -> Some (State.set_metadata state loc pval)
          | Some state, MDomain (loc, dom)      -> Some (State.set_domain state loc dom)
          | Some state, MPF formula             -> State.assume_a state [ formula ]
          | Some state, MType (v, t)            -> State.assume_t state v t
          | Some state, MSVar vs                -> Some (State.add_spec_vars state (SS.of_list vs))
          | Some state, MAsrt (a, subst)        -> 
            (match State.produce state subst a with 
            | Some state -> State.update_subst state subst; Some state
            | None -> None))
      (Some state) fixes 

  let get_fix ?(simple_fix: bool option) (procs : SS.t) (state : state_t) (errs : Error.t list) : fix_t list list = 
    
    let simple_fix = 
      match simple_fix with 
        | Some b -> b 
        | None -> false in 

    let complete_fixes (fixes : Error.fix_t list) : fix_t list =
      if ((not simple_fix) && (!SCommon.js))
        then List.concat (List.map (complete_single_fix_js procs state) fixes) 
        else List.concat (List.map (complete_single_fix procs state) fixes) in 
  
    let aux (err : Error.t) : fix_t list list = 
      match err with 
        | ESpec (_, _, fixes) -> List.map complete_fixes fixes
        | _ -> raise (Failure "DEATH. get_fix. ERROR is not fixable!!") in 

    List.concat (List.map aux errs)

  let init (pred_defs : UP.preds_tbl_t option) : t =  
    SS.empty, State.init pred_defs, State.init pred_defs

  let get_pred_defs (bi_state : t) : UP.preds_tbl_t option = 
    let _, state, _ = bi_state in
    State.get_pred_defs state   

  let initialise (procs : SS.t) (state : State.t) (pred_defs : UP.preds_tbl_t option) : t = 
    procs, state, (State.init pred_defs)

  let eval_expr (bi_state : t) (e : Expr.t) = 
    let _, state, _ = bi_state in 
    try State.eval_expr state e
    with State.Internal_State_Error (errs, s) -> raise (Internal_State_Error (errs, bi_state)) 
  
  let get_store (bi_state : t) : store_t = 
    let _, state, _ = bi_state in 
    State.get_store state
  
  let set_store (bi_state : t) (store : store_t) : t = 
    let procs, state, af_state = bi_state in 
    let state'          = State.set_store state store in 
    (procs, state', af_state)

  let alloc (bi_state : t) (loc : vt option) (m : vt) : (vt * t) = 
    let procs, state, af_state = bi_state in 
    let loc', state'    = State.alloc state loc m in  
    (loc', (procs, state', af_state))

  let to_loc (bi_state : t) (v : vt) : (t * vt) option = 
    let procs, state, af_state = bi_state in 
    match State.to_loc state v with 
      | Some (state', loc) -> Some ((procs, state', af_state), loc)
      | None -> 
        (* BIABDUCTION TODO: CREATE A NEW OBJECT *)
        None 

  let merge_gc_results (rets : gc_ret list) : gc_ret = 
    let ret_succs, ret_fails = List.partition (fun ret -> match ret with | GCSucc _ -> true | _ -> false) rets in
    if (ret_fails <> []) 
      then (
        let errs = List.map (fun ret -> match ret with | GCFail errs -> errs | _ -> []) ret_fails in 
        GCFail (List.concat errs) 
      ) else (
        let rets = List.map (fun ret -> match ret with | GCSucc rets -> rets | _ -> []) ret_succs in 
        GCSucc (List.concat rets)
      ) 

  let rec get_cell ?(remove : bool option) (bi_state : t) (loc : vt) (prop : vt) : gc_ret  = 
    let procs, state, state_af = bi_state in 
    match State.get_cell ?remove:remove state loc prop with 
      | GCSucc rets   -> GCSucc (List.map (fun (state', loc', prop', v) -> ((procs, state', state_af), loc', prop', v)) rets)
      | GCFail errs when Error.can_fix errs -> 
          let rets =  
            List.map 
              (fun fix -> 
                let state'    = apply_fix procs state fix in 
                let state_af' = apply_fix procs state_af fix in 
                match state', state_af' with 
                  | Some state', Some state_af' -> Some (get_cell ?remove:remove (procs, state', state_af') loc prop)
                  | _ -> None)
              (get_fix procs state errs) in
          let rets = CCommon.get_list_somes rets in  
          merge_gc_results rets  
      | GCFail errs -> GCFail errs 

  let set_cell (bi_state : t) (loc : vt) (prop : vt) (v : vt option) : t = 
    let procs, state, state_af = bi_state in 
    let state' = State.set_cell state loc prop v in 
    procs, state', state_af 

  let merge_gd_results (rets : gd_ret list) : gd_ret = 
    let ret_succs, ret_fails = List.partition (fun ret -> match ret with | GDSucc _ -> true | _ -> false) rets in
    if (ret_fails <> []) 
      then (
        let errs = List.map (fun ret -> match ret with | GDFail errs -> errs | _ -> []) ret_fails in 
        GDFail (List.concat errs) 
      ) else (
        let rets = List.map (fun ret -> match ret with | GDSucc rets -> rets | _ -> []) ret_succs in 
        GDSucc (List.concat rets)
      )  

  let rec get_domain ?(expected_props : vt option) ?(remove : bool option) (bi_state : t) (loc : vt) : gd_ret = 
    let procs, state, state_af = bi_state in 
    match State.get_domain ?remove:remove state loc with 
      | GDSucc rets  -> GDSucc (List.map (fun (state', v) -> (procs, state', state_af), v) rets)
      | GDFail errs when Error.can_fix errs -> 
          let rets = 
            List.map 
              (fun fix -> 
                let state'    = apply_fix procs state fix in 
                let state_af' = apply_fix procs state_af fix in 
                match state', state_af' with 
                  | Some state', Some state_af' -> Some (get_domain ?remove:remove (procs, state', state_af') loc)
                  | _, _ -> None) 
              (get_fix procs state errs) in
          let rets = CCommon.get_list_somes rets in   
          merge_gd_results rets
      | GDFail errs -> GDFail errs
          
  
  let set_domain (bi_state : t) (loc : vt) (dom : vt) : t = 
    let procs, state, state_af = bi_state in 
    procs, (State.set_domain state loc dom), state_af
  
  
  let merge_gm_results (rets : gm_ret list) : gm_ret = 
    let ret_succs, ret_fails = List.partition (fun ret -> match ret with | GMSucc _ -> true | _ -> false) rets in
    if (ret_fails <> []) 
      then (
        let errs = List.map (fun ret -> match ret with | GMFail errs -> errs | _ -> []) ret_fails in 
        GMFail (List.concat errs) 
      ) else (
        let rets = List.map (fun ret -> match ret with | GMSucc rets -> rets | _ -> []) ret_succs in 
        GMSucc (List.concat rets)
      )  

  let rec get_metadata ?(remove : bool option) (bi_state : t) (loc : vt) : gm_ret = 
    let procs, state, state_af = bi_state in 
    
    match State.get_metadata ~remove:false state loc with 
      | GMSucc rets   -> GMSucc (List.map (fun (state', loc, v) -> (procs, state', state_af), loc, v) rets)
      | GMFail errs when Error.can_fix errs -> 
          let rets = 
            List.map 
              (fun fix -> 
                let state'    = apply_fix procs state fix in 
                let state_af' = apply_fix procs state_af fix in 
                match state', state_af' with 
                  | Some state', Some state_af' -> Some (get_metadata ?remove:remove (procs, state', state_af') loc)
                  | _, _ -> None) 
              (get_fix procs state errs) in
          let rets = CCommon.get_list_somes rets in 
          merge_gm_results rets   
      | GMFail errs -> GMFail errs
  
  let set_metadata (bi_state : t) (loc : vt) (m : vt) : t = 
    let procs, state, state_af = bi_state in 
    procs, (State.set_metadata state loc m), state_af
  
  let delete_object (bi_state : t) (loc : Expr.t) : t = 
    let procs, state, state_af = bi_state in 
    procs, (State.delete_object state loc), state_af

  let assume (bi_state : t) (v : vt) : t list = 
    let procs, state, state_af = bi_state in 
    let v_not = Val.from_expr (Expr.UnOp (Not, Val.to_expr v)) in 
    let bi_abduce = Option.map_default (fun v -> State.sat_check state v) true v_not in 
    List.map 
      (fun state' -> 
        if bi_abduce then (
          match State.assume state_af v with 
            | [ state_af' ] -> procs, state', state_af' 
            | _ -> raise (Failure "DEATH. ASSUME BI-ABDUCTION")
        ) else procs, state', state_af 
      ) (State.assume state v)

  let assume_a (bi_state : t) (fs : Formula.t list) : t option = 
    let procs, state, state_af = bi_state in 
    match State.assume_a state fs with 
      | Some state -> Some (procs, state, state_af)
      | None -> None 

  let assume_t (bi_state : t) (v : vt) (t : Type.t) : t option = 
    let procs, state, state_af = bi_state in 
    match State.assume_t state v t with 
      | Some state -> Some (procs, state, state_af)
      | None -> None 
  
  let sat_check (bi_state : t) (v : vt) : bool = 
    let _, state, _ = bi_state in 
    State.sat_check state v 
  
  let sat_check_f (bi_state : t) (fs : Formula.t list) : Subst.t option = 
    let _, state, _= bi_state in 
    State.sat_check_f state fs 
  
  let assert_a (bi_state : t) (fs : Formula.t list) : bool = 
    let _, state, _ = bi_state in 
    State.assert_a state fs 
     
  let equals (bi_state : t) (v1 : vt) (v2 : vt) : bool = 
    let _, state, _ = bi_state in 
    State.equals state v1 v2 

  let get_type (bi_state : t) (v : vt) : Type.t option = 
    let _, state, _ = bi_state in 
    State.get_type state v  

  let copy (bi_state : t) : t = 
    let procs, state, state_af = bi_state in  
    procs, State.copy state, State.copy state_af

  let rec simplify ?(kill : bool option) (bi_state : t) : Subst.t =
    let kill            = Option.default true kill in 
    let procs, state, state_af = bi_state in 
    let subst           = State.simplify ~kill:kill state in
    (* let subst'          = Subst.copy subst in *)
    let svars           = State.get_spec_vars state in 
    Subst.filter_in_place subst (fun x x_v -> if (SS.mem x svars) then None else Some x_v); 
    State.substitution_in_place subst state_af; 
    subst
  
  let simplify_val (bi_state : t) (v : vt) : vt = 
    let _, state, _ = bi_state in 
    State.simplify_val state v 

  let str (bi_state : t) : string =
    let procs, state, state_af = bi_state in  
    let state_str       = State.str state in
    let state_af_str    = State.str state_af in   
    Printf.sprintf "PROCS:\n%s\nMAIN STATE:\n%s\nANTI FRAME:\n%s\n" 
      (String.concat ", " (SS.elements procs))
      state_str state_af_str  

  let add_spec_vars (bi_state : t) (vs : Var.Set.t) : t = 
    let procs, state, state_af = bi_state in  
    let state' = State.add_spec_vars state vs in 
    (procs, state', state_af)

  let get_spec_vars (bi_state : t) : Var.Set.t = 
    let _, state, _ = bi_state in  
    State.get_spec_vars state 

  let get_lvars (bi_state : t) : Var.Set.t = 
    let _, state, _ = bi_state in  
    State.get_lvars state 

  let to_assertions ?(to_keep : SS.t option) (bi_state : t) : Asrt.t list = 
    let _, state, _ = bi_state in
    State.to_assertions ?to_keep:to_keep state 

  let rec evaluate_slcmd 
      (prog     : UP.prog)
      (lcmd     : SLCmd.t) 
      (bi_state : t) : t list =
    let procs, state, state_af = bi_state in 
    List.map 
      (fun state' -> procs, state', state_af) 
      (State.evaluate_slcmd prog lcmd state)

  let unfolding_vals (bi_state : t) (fs : Formula.t list) : vt list = 
    let procs, state, _ = bi_state in 
    State.unfolding_vals state fs  

  let substitution_in_place (subst : st) (bi_state : t) : unit = 
    raise (Failure "substitution_in_place inside BI STATE")

  let fresh_val (bi_state : t) : vt =
    raise (Failure "fresh_val inside BI STATE")

  let fresh_loc ?(loc : vt option) (bi_state : t) : vt =
    raise (Failure "fresh_loc inside BI STATE")

  let get_locs (bi_state : t) : vt list = 
    let _, state, _ = bi_state in 
      State.get_locs state

  let get_locs_and_props (bi_state : t) : (vt * vt) list = 
    let _, state, _ = bi_state in 
      State.get_locs_and_props state

  let clean_up (bi_state : t) : unit = 
    let _, state, _ = bi_state in 
      State.clean_up state


  let make_id_subst (a : Asrt.t) : Subst.t =
    let lvars = Asrt.lvars a in 
    let alocs = Asrt.alocs a in 
    let lvar_bindings = List.map (fun x -> (x, Expr.LVar x)) (SS.elements lvars) in 
    let aloc_bindings = List.map (fun x -> (x, Expr.ALoc x)) (SS.elements alocs) in 
    let bindings  = lvar_bindings @ aloc_bindings in 
    let bindings' = 
      List.map 
        (fun (x, e) ->
          match Val.from_expr e with 
            | Some v -> (x, v)
            | _ -> raise (Failure "DEATH. make_id_subst"))
        bindings in 
    Subst.init bindings' 


  let get_components (bi_state : t) : (State.t * State.t) = 
    let _, state, state_af = bi_state in 
    (state, state_af)


  let make_spec (prog : UP.prog) (name : string) (params : string list) (bi_state_i : t)  (bi_state_f : t) (fl : Flag.t) : Spec.t = 

    (* let start_time = time() in *)

    let _ = simplify bi_state_f in 
    let _, state_i, _        = bi_state_i in 
    let _, state_f, state_af = bi_state_f in 
    let pvars = SS.of_list (Flag.return_variable :: params) in 

    L.log L.Verbose (lazy (
      Printf.sprintf "Going to create a spec for %s(%s)\nAF:\n%s\nFinal STATE:\n%s"
        name (String.concat ", " params) (State.str state_af) (State.str state_f)
    )); 

    let post = 
      if ((name <> "main") && !SCommon.js) then (
        let astate_f = AbsState.initialise state_f (Preds.init []) (Some prog.preds) in 
        let astate_f = JSCleanUp.exec prog astate_f name false in  
        Asrt.star (List.sort Asrt.compare (AbsState.to_assertions ~to_keep:pvars astate_f))
      ) else Asrt.star (List.sort Asrt.compare (State.to_assertions ~to_keep:pvars state_f)) in 
  
    let pre  =
      if ((name <> "main") && !SCommon.js) then (
        let astate_i = AbsState.initialise state_i (Preds.init []) (Some prog.preds) in 
        let af_asrt  = Asrt.star (State.to_assertions state_af) in 
        let af_subst = make_id_subst af_asrt in  
        match AbsState.produce astate_i af_subst af_asrt with 
          | Some astate_i' -> 
              let _ = AbsState.simplify astate_i' in 
              let astate_i'' = JSCleanUp.exec prog astate_i' name true in  
              Asrt.star (AbsState.to_assertions ~to_keep:pvars astate_i'')
          | _ -> raise (Failure "DEATH. make_spec")
      ) else Asrt.star (List.sort Asrt.compare ((State.to_assertions ~to_keep:pvars state_i) @ (State.to_assertions state_af))) in 

    (* update_statistics "make_spec_Bi" (time() -. start_time); *)

    { 
      name   = name; 
      params = params;
      sspecs = [ { 
        pre       = pre; 
        posts     = [ post ]; 
        flag      = fl; 
        to_verify = false; 
        label     = None 
      }]; 
      normalised = true; 
      to_verify  = false
    }


  let subst_in_val (subst : st) (v : vt) : vt = 
    match Val.from_expr (Subst.subst_in_expr subst true (Val.to_expr v)) with 
      | Some v -> v 
      | None -> v  


  let compose_substs (subst1 : st) (subst2 : st) : st = 
    let bindings = 
      Subst.fold 
        subst1 
        (fun x v bindings -> (x, subst_in_val subst2 v) :: bindings)
        [] in 
    Subst.init bindings 


  type post_res = (Flag.t * (Asrt.t list)) option

  let unify
      (procs    : SS.t)
      (state    : State.t)
      (state_af : State.t)
      (subst    : Subst.t)
      (up       : UP.t) : (state_t * state_t * st * post_res) list =
    
    let state_i = State.copy state in 
    let subst_i = Subst.copy subst in 
    let search_state = [ state, state_af, subst, up ], [] in 
    
    let rec search search_state = 
      match search_state with 
        | [], rets -> rets 
        | (state, state_af, subst, up) :: rest, rets -> 
          let cur_asrt : Asrt.t option = UP.head up in 
          let ret : State.u_res = Option.map_default (State.unify_assertion state subst) (USucc state) cur_asrt in 
          (match ret with 
            | UWTF -> search (rest, rets)  

            | USucc state' -> 
                (match UP.next up with
                  | None ->
                      L.log L.Verboser (lazy "ONE SPEC IS DONE!!!\n");
                      search (rest, (state', state_af, subst, (UP.posts up)) :: rets)
                  | Some [ (up, lab) ] ->  search (((state', state_af, subst, up) :: rest), rets)
                  | Some ((up, lab) :: ups')  ->
                      let next_states = (state', state_af, subst, up) :: (List.map (fun (up, lab) -> State.copy state', State.copy state_af, Subst.copy subst, up) ups') in 
                      search ((next_states @ rest), rets)
                  | Some [] -> search (rest, rets))

            | UFail errs -> 
                let cur_asrt_str = Option.map_default Asrt.str "no assertion - phantom node" cur_asrt in 
                L.log L.Verbose (lazy (Printf.sprintf "WARNING: Unify Assertion Failed: %s with errors: %s. CUR SUBST:\n%s\n" 
                  cur_asrt_str (String.concat "\n" (List.map Error.str errs)) (Subst.str subst)));
                
                if (Error.can_fix errs) then (
                   L.log L.Verboser (lazy (Printf.sprintf "CAN FIX!!!"));
                  let ffixes       = get_fix ~simple_fix:true procs state errs in 
                  let fixed_states = 
                    List.map 
                      (fun new_fixes -> 
                        let state'    = State.copy state in 
                        let state_af' = State.copy state_af in 
                        let state'    = apply_fix procs state' new_fixes in 
                        let state_af' = apply_fix procs state_af' new_fixes in 
                        Option.map 
                          (fun state' -> 
                            let state_af' = Option.get state_af' in 
                            L.log L.Verboser (lazy (Printf.sprintf "BEFORE THE SIMPLIFICATION!!!")); 
                            let new_subst = State.simplify state' in
                            L.log L.Verboser (lazy (Printf.sprintf "SIMPLIFICATION SUBST:\n%s" (Subst.str new_subst)));  
                            let subst' = compose_substs subst new_subst in 
                            L.log L.Verboser (lazy (Printf.sprintf "AF BEFORE SIMPLIFICATION:\n%s\n" (State.str state_af'))); 
                            let svars  = State.get_spec_vars state' in 
                            Subst.filter_in_place new_subst (fun x x_v -> if (SS.mem x svars) then None else Some x_v); 
                            State.substitution_in_place new_subst state_af'; 
                            L.log L.Verboser (lazy (Printf.sprintf "AF AFTER SIMPLIFICATION:\n%s\n" (State.str state_af'))); 
                            state', state_af', subst' 
                          ) state')
                      ffixes in
                  let fixed_states = get_list_somes fixed_states in 
                  let next_search_states = 
                    List.map (fun (state, state_af, subst) -> (state, state_af, subst, up)) fixed_states in 
                  
                  if ((List.length next_search_states) = 0) then (
                     L.log L.Verboser (lazy (Printf.sprintf "TRIED TO FIX BUT CANNOT FIX!!!"))
                  );

                  search (next_search_states @ rest, rets)  
                ) else (
                   L.log L.Verboser (lazy (Printf.sprintf "CANNOT FIX!!!"));
                  search (rest, rets)
                )
        ) in 
    search search_state 
                

  let run_spec 
      (spec        : UP.spec) 
      (bi_state    : t)
      (args        : vt list)
      (subst       : (string * (string * vt) list) option) : (t * vt option * Flag.t) list = 

    (* let start_time = time() in  *)
    L.log L.Verboser (lazy (Printf.sprintf "INSIDE RUN spec of %s with the following UP:\n%s\n"  spec.spec.name (UP.str spec.up))); 
    let subst_i = simplify bi_state in 
    let args    = List.map (subst_in_val subst_i) args in 
    L.log L.Verboser (lazy (Printf.sprintf "ARGS: %s. SUBST:\n%s"
      (String.concat ", " (List.map Val.str args)) (Subst.str subst_i))); 

    let procs, state, state_af = bi_state in 

    let old_store = State.get_store state in 
    let old_state = State.copy state in 

    let new_store  = Store.init (List.combine spec.spec.params args) in
    let state'     = State.set_store state new_store in 
    let subst      = Subst.init (Store.bindings new_store) in 

    L.log L.Verboser (lazy (Printf.sprintf "About to use the spec of %s with the following UP inside BI-ABDUCTION:\n%s\n"  spec.spec.name (UP.str spec.up))); 
    let ret_states = unify procs state' state_af subst spec.up in 
    L.log L.Verboser (lazy (Printf.sprintf "Concluding unification With %d results" (List.length ret_states))); 

    let result = List.concat (List.map 
      (fun (frame_state, state_af, subst, posts) -> 
        let fl, posts = 
          (match posts with 
            | Some (fl, posts) -> fl, posts
            | _ -> 
                let msg = Printf.sprintf "SYNTAX ERROR: Spec of %s does not have a postcondition" spec.spec.name in 
                L.log L.Normal (lazy msg);
                raise (Failure msg)) in 
         

         L.log L.Verboser (lazy (Printf.sprintf "SUBST:\n%s\nFRAME STATE:\n%s\nANTI FRAME\n:%s\n"
              (Subst.str subst) (State.str frame_state) (State.str state_af))); 
        

        let sp : State.t list = State.produce_posts frame_state subst posts in  
        List.map 
          (fun (final_state : State.t) ->
            let state_af'    : State.t    = State.copy state_af in 
            let final_store  : Store.t    = State.get_store final_state in 
            let v_ret        : vt option  = Store.get final_store Flag.return_variable in
            let final_state' : State.t    = State.set_store final_state (Store.copy old_store) in 
            let bi_state     : t          = procs, final_state', state_af' in 
            
            L.log L.Verboser (lazy (Printf.sprintf "At the end of unification with AF:\n%s\nAND STATE\n:%s\n"
              (State.str state_af') (State.str final_state'))); 

            bi_state, v_ret, fl) 
          sp
      ) ret_states) in 
    (* update_statistics "run_spec" (time() -. start_time); *)
    result
            
  let produce_posts (state  : t) (subst  : st) (asrts : Asrt.t list) : t list = 
    raise (Failure "produce_posts from bi_state.")  
  
  let produce (state  : t) (subst  : st) (asrts : Asrt.t) : t option = 
    raise (Failure "produce_posts from bi_state.") 


  let unify_assertion (state : t) (subst : st) (p : Asrt.t) : u_res = 
    raise (Failure "Unify assertion from bi_state.")   

  let update_subst (state : t) (subst : st) : unit = () 

 end 

