open CCommon

module L = Logging 

module M 
  (Val     : Val.M) 
  (Subst   : Subst.M with type vt = Val.t and type t = Val.st) 
  (Store   : Store.M with type vt = Val.t) 
  (Error   : Error.M with type vt = Val.t and type st = Val.st)
  (State   : AbsState.M with type vt = Val.t and type st = Subst.t and type store_t = Store.t) = struct 

  type vt = Val.t 

  let protected_fold (prog : UP.prog) (state : State.t) (pred : string) (args : Expr.t list) (info : SLCmd.folding_info option) : State.t =
    let old_state = State.copy state in 
    (try
      (match State.evaluate_slcmd prog (Fold (pred, args, info)) state with 
      | [ state ] -> state
      | _ -> state)
    with
    | _ -> 
      L.log L.Verboser (lazy "Warning: protected fold unsuccesful, reverting.");
      old_state)

  
  let str_of_js_full_object (args : Expr.t list) : string option = 
    (* Printf.printf " str_of_js_full_object.\n"; *)
    match args with 
      | [ loc; loc_proto; cl; ext; EList cells ] ->
          let loc_str   = Expr.str loc in 
          let proto_str = Expr.str loc_proto in 
          let cl_str    = Expr.str cl in 
          let ext_str   = Expr.str ext in
          let cells_str = 
            List.map 
              (fun (prop_val_pair : Expr.t) -> 
                match prop_val_pair with 
                | EList [ prop; prop_v ] -> Some (Printf.sprintf "%s: %s" (Expr.str prop) (Expr.str prop_v))
                | _ -> None 
              ) cells in 
          
          let success = List.for_all (fun x -> x <> None) cells_str in
          if success then (
            let cells_str = CCommon.get_list_somes cells_str in 
            let cells_str = String.concat ", " cells_str in
            let ret_str = (Printf.sprintf "%s |-> { %s | class: %s, ext: %s, proto: %s }"
                loc_str cells_str cl_str ext_str proto_str) in 
            (* Printf.printf "LALALA: %s\n" ret_str; *)
            Some ret_str
              
          ) else raise (Failure "NONE in str_of_js_full_object 1") 
      | _ -> raise (Failure "NONE in str_of_js_full_object 2")  
      

  let js_preds_printer (pred : string * (Expr.t list)) : string option = 
    (* Printf.printf "js_preds_printer!!!\n"; *)
    match pred with 
      | pname, args when (pname = "JSFullObject") -> 
          (* Printf.printf "I found a JSFullObject to print!\n"; *)
          str_of_js_full_object args 
      | _ -> None 

  let exec (prog : UP.prog) (astate : State.t) (name : string) (is_pre : bool) : State.t = 
    
    L.log L.Verboser (lazy (Printf.sprintf "js_state_clean_up!!")); 

    let (pname : string), (args : Expr.t list) = 
      if is_pre 
        then JSIL_PostParser.pre_scope_prefix ^ name, [ PVar JS2JSIL_Constants.var_scope ] 
        else JSIL_PostParser.post_scope_prefix ^ name,[ PVar JS2JSIL_Constants.var_scope; PVar JS2JSIL_Constants.var_er ] in  
    

    let js_prop_clean_up (astate : State.t) (loc : vt) (prop : vt) : State.t =    
      match State.get_cell astate loc prop with 
        | State.GCSucc [ astate, _, _, Some pval ] -> 
            (match Val.to_expr pval with 
              | EList [ Lit (String "d"); _; Lit (Bool true); Lit (Bool true); Lit (Bool true) ] 
              | Lit (LList [ String "d"; _; Bool true; Bool true; Bool true ]) -> 
                  (match State.evaluate_slcmd prog (Fold ("DataProp", [ Val.to_expr loc; Val.to_expr prop ], None)) astate with 
                    | [ astate ] -> astate
                    | _ -> astate)
              | EList [ Lit (String "d"); _; Lit (Bool false); _; Lit (Bool false) ] 
              | Lit (LList [ (String "d"); _; Bool false; _; Bool false ]) -> 
                  (match State.evaluate_slcmd prog (Fold ("DataPropConst", [ Val.to_expr loc; Val.to_expr prop ], None)) astate with 
                    | [ astate ] -> astate
                    | _ -> astate)
              | EList [ Lit (String "d"); _; _; _; _ ] 
              | Lit (LList [ (String "d"); _; _; _; _ ]) -> 
                  (match State.evaluate_slcmd prog (Fold ("DataPropGen", [ Val.to_expr loc; Val.to_expr prop ], None)) astate with 
                    | [ astate ] -> astate
                    | _ -> astate)
              | _ -> astate)
        | _ -> astate in  

    let js_loc_clean_up (astate : State.t) (loc : vt) : State.t = 
      match State.get_metadata astate loc with 
      | State.GMSucc [ astate, _, m_loc ] -> 
          (match Val.to_expr m_loc with 
            | ALoc _ 
            | Lit (Loc _) ->
               (match State.get_cell astate m_loc (Val.from_literal (String "@er")) with 
               | State.GCSucc [ astate, _, _, Some _ ] -> 
                  let astate = State.delete_object astate (Val.to_expr loc) in 
                  let astate = State.delete_object astate (Val.to_expr m_loc) in
                    astate
               | _ -> 
                  (match State.get_cell astate m_loc (Val.from_literal (String "@class")) with 
                    | State.GCSucc [ astate, _, _, Some pval ] -> 
                        (match Val.to_literal pval with 
                          | Some (String "Object") -> 
                              (match State.evaluate_slcmd prog (Fold ("JSObjGeneral", [ (Val.to_expr loc) ], None)) astate with 
                                | [ astate ] -> astate
                                | _ -> astate)    
                          
                          | Some (String "Array") ->
                              L.log L.Verboser (lazy "Array class.");
                              (match State.get_cell astate loc (Val.from_literal (String "length")) with 
                                | State.GCSucc [ astate, _, _, Some pval ] ->
                                    L.log L.Verboser (lazy "Got length.");
                                    (match Val.to_literal pval with 
                                    | Some (LList [ String "d"; Num n; Bool true; Bool false; Bool false]) when (Arith_Utils.is_int n) -> 
                                      L.log L.Verboser (lazy "Length is an integer.");
                                      (match State.evaluate_slcmd prog (Fold ("JSArray", [ (Val.to_expr loc) ], None)) astate with 
                                        | [ astate ] -> astate
                                        | _ -> L.log L.Verboser (lazy "Array fold failed."); astate)
                                    | _ -> L.log L.Verboser (lazy "Length is not an integer."); astate) 
                                | _ -> astate)
                          
                          | Some (String "String") ->
                              L.log L.Verboser (lazy "String class.");
                              (match State.evaluate_slcmd prog (Fold ("StringObject", [ (Val.to_expr loc) ], None)) astate with 
                                  | [ astate ] -> astate
                                  | _ -> L.log L.Verboser (lazy "String fold failed."); astate)

                          | Some (String "Number") ->
                              L.log L.Verboser (lazy "Number class.");
                              (match State.evaluate_slcmd prog (Fold ("NumberObject", [ (Val.to_expr loc) ], None)) astate with 
                                  | [ astate ] -> astate
                                  | _ -> L.log L.Verboser (lazy "Number fold failed."); astate)
                              
                          | Some (String "Boolean") ->
                              L.log L.Verboser (lazy "Boolean class.");
                              (match State.evaluate_slcmd prog (Fold ("BooleanObject", [ (Val.to_expr loc) ], None)) astate with 
                                  | [ astate ] -> astate
                                  | _ -> L.log L.Verboser (lazy "Boolean fold failed."); astate)

                          | Some (String "Error") ->
                              L.log L.Verboser (lazy "Error class.");
                              (match State.get_cell astate m_loc (Val.from_literal (String "@proto")) with 
                                | State.GCSucc [ astate, _, _, Some pval ] ->
                                  (match Val.to_literal pval with 
                                  | Some (Loc ploc) -> 
                                    let withMessage =
                                      (match State.get_cell astate loc (Val.from_literal (String "message")) with 
                                      | State.GCSucc [ astate, _, _, Some pval ] -> true 
                                      | _ -> false) in 
                                    let predicate = 
                                      (if ploc = JS2JSIL_Constants.locTErrPrototype then Some "TypeErrorComplete"      else 
                                       if ploc = JS2JSIL_Constants.locSErrPrototype then Some "SyntaxErrorComplete"    else 
                                       if ploc = JS2JSIL_Constants.locRErrPrototype then Some "ReferenceErrorComplete" else 
                                       if ploc = JS2JSIL_Constants.locErrPrototype 
                                          then (if withMessage then Some "ErrorWithMessage" else Some "ErrorComplete") 
                                          else None) in 
                                        (match predicate with 
                                        | Some pred -> 
                                            (match State.evaluate_slcmd prog (Fold (pred, [ (Val.to_expr loc) ], None)) astate with 
                                            | [ astate ] -> astate
                                            | _ -> L.log L.Verboser (lazy "Error fold failed."); astate)
                                        | None -> astate)
                                  | _ -> astate)
                                | _ -> astate)

                          | _ -> astate)
                    | _ -> astate))
            | _ -> astate)
      | _ -> astate in 
    
    
    let fold_js_object (astate : State.t) (loc : vt) (preds : (string * (vt list)) list) : (string * (vt list)) list =  
      let (main_obj_pred : (string * (vt list)) list), prop_preds = 
        List.partition 
          (fun (pname, _) -> pname = "JSObjGeneral")
          preds in 
      match main_obj_pred with 
      | [ (_, [ loc; loc_proto; cl; ext]) ] -> 
        let cells = 
          List.map 
            (fun (_, [_; prop; prop_val]) ->
              Expr.EList [ Val.to_expr prop; Val.to_expr prop_val]  
            ) prop_preds in 
        let cells = Val.from_expr (EList cells) in 
        Option.map_default 
          (fun cells -> [ "JSFullObject", [loc; loc_proto; cl; ext ] @ [ cells ] ])
          preds cells 
      | _ -> preds in   


    let fold_js_objects (astate : State.t) : unit =
      let sel (pname, _) = ((pname = "DataProp") || (pname = "JSObjGeneral")) in 
      let objPreds = State.get_all_preds ~keep:false sel astate in  
      let objs     = Hashtbl.create CCommon.medium_tbl_size in 
      List.iter 
        (fun (pname, loc :: vs) -> 
          let loc_preds = try Hashtbl.find objs loc with Not_found -> [] in  
          Hashtbl.replace objs loc ((pname, loc :: vs) :: loc_preds) 
        ) objPreds;
      let new_obj_preds = 
        Hashtbl.fold 
          (fun loc preds obj_preds -> 
              let new_obj_preds = fold_js_object astate loc preds in 
              new_obj_preds @ obj_preds
          ) objs [] in 
      List.iter (fun obj_pred -> State.set_pred astate obj_pred) new_obj_preds in 


    let js_locs_clean_up (astate : State.t) : State.t = 
      let locs = State.get_locs astate in 
      let locs_and_props = State.get_locs_and_props astate in 
      let astate = List.fold_left js_loc_clean_up astate locs in 
      List.fold_left (fun astate (loc, prop) -> 
        js_prop_clean_up astate loc prop 
      ) astate locs_and_props in 

    let result = (match State.evaluate_slcmd prog (Fold (JSIL_PostParser.heap_asrt_name, [], None)) astate with 
      | [ astate ] ->
        L.log L.Verboser (lazy "FOLD SCOPE.");
        let astate = protected_fold prog astate pname args None in  
        State.clean_up astate; 
        let astate = js_locs_clean_up astate in  
        fold_js_objects astate; 
        State.clean_up astate; 
        astate
      | _ -> astate) in 
    result

end