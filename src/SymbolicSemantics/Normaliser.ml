open SCommon
open CCommon
open SState

module L      = Logging
module SSubst = SVal.SSubst
module SPreds = SPreds.M
module SState = SState.M


let new_aloc_name var = aloc_prefix ^ var
let new_lvar_name var = lvar_prefix ^ var

module CStore = MakeStore.M(CVal.M)

(**
  le -> non - normalised logical expression
  subst -> table mapping variable and logical variable
  gamma -> table mapping logical variables + variables to types

  the store is assumed to contain all the program variables in le
*)
let rec normalise_lexpr 
    ?(store : SStore.t option) ?(subst : SSubst.t option) (gamma : TypEnv.t) (le : Expr.t) =

  let store = Option.default (SStore.init []) store in 
  let subst = Option.default (SSubst.init []) subst in 

  let f = normalise_lexpr ~store:store ~subst:subst gamma in
  
  let result : Expr.t = match (le : Expr.t) with
  | Lit _
  | Nono -> le
  | LVar lvar -> Option.default (Expr.LVar lvar) (SSubst.get subst lvar)
  | ALoc aloc -> ALoc aloc (* raise (Failure "Unsupported expression during normalization: ALoc") Why not ALoc aloc? *)
  | PVar pvar ->
    let value = SStore.get store pvar in
    (match value with
    | Some value -> value
    | None -> 
      let new_lvar = fresh_lvar () in 
        SStore.put store pvar (LVar new_lvar); 
        SSubst.put subst pvar (LVar new_lvar);
        LVar new_lvar
    )

  | BinOp (le1, bop, le2) ->
    let nle1 = f le1 in
    let nle2 = f le2 in
    (match bop with 
    | LstNth  ->
      (match (nle1 : Expr.t), (nle2 : Expr.t) with
        | Lit (LList list), Lit (Num n) when (Arith_Utils.is_int n) ->
          let lit_n = (try List.nth list (int_of_float n) with _ ->
            raise (Failure "List index out of bounds")) in
          Lit lit_n
        | Lit (LList list), Lit (Num n) -> raise (Failure "Non-integer list index")
        | EList list, Lit (Num n) when (Arith_Utils.is_int n) ->
          let le_n = (try List.nth list (int_of_float n) with _ ->
            raise (Failure "List index out of bounds")) in
          f le_n
        | EList list, Lit (Num n) -> raise (Failure "Non-integer list index")
        | _, _ -> BinOp (nle1, LstNth, nle2))

    | StrNth ->
      (match nle1, nle2 with
        | Lit (String s), Lit (Num n) when (Arith_Utils.is_int n) ->
          let s = (try (String.make 1 (String.get s (int_of_float n))) with _ ->
            raise (Failure "String index out of bounds")) in
          Lit (String s)
        | Lit (String s), Lit (Num n) -> raise (Failure "Non-integer string index")
        | _, _ -> BinOp (nle1, LstNth, nle2))

    | _ -> (match (nle1 : Expr.t), (nle2 : Expr.t) with
      | Lit lit1, Lit lit2 ->
        let lit = CExprEval.evaluate_binop (CStore.init []) bop (Lit lit1) (Lit lit2) in
          Lit lit
      | _, _ -> BinOp (nle1, bop, nle2)))

  | UnOp (uop, le1) ->
    let nle1 = f le1 in
    (match nle1 with
      | Lit lit1 ->
        let lit = CExprEval.evaluate_unop uop lit1 in
        Lit lit

      | _ -> 
        (match uop with
        | TypeOf ->
          let nle1 = f le1 in
          (match nle1 with
            | Lit llit -> Lit (Type (Literal.type_of llit))
            | Nono -> raise (Failure "Illegal Logic Expression: TypeOf of None")
            | LVar lvar ->
              (try Lit (Type (TypEnv.get_unsafe gamma lvar)) with _ -> UnOp (TypeOf, LVar lvar))
                (* raise (Failure (Printf.sprintf "Logical variables always have a type, in particular: %s." lvar))) *)
            | ALoc _ -> Lit (Type ObjectType)
            | PVar _ -> raise (Failure "This should never happen: program variable in normalised expression")
            | BinOp (_, _, _)
            | UnOp (_, _) -> UnOp (TypeOf, nle1)
            | EList _ -> Lit (Type ListType))
          
        | _ -> UnOp (uop, nle1)))



  | EList le_list ->
    let n_le_list = List.map (fun le -> f le) le_list in
    let all_literals, lit_list =
      List.fold_left
        (fun (ac, list) le ->
          match (le : Expr.t) with
          | Lit lit -> (ac, (list @ [ lit ]))
          | _ -> (false, list))
        (true, [])
        n_le_list in
    if (all_literals)
    then Lit (LList lit_list)
    else EList n_le_list
    
  | ESet le_list ->
    let n_le_list = List.map (fun le -> f le) le_list in
    ESet n_le_list
  
  | NOp (op, le_list) -> 
    let n_le_list = List.map (fun le -> f le) le_list in
      NOp (op, n_le_list) in 

    Typing.infer_types_expr gamma result;
    result


let extend_typing_env_using_assertion_info
  (gamma : TypEnv.t) (a_list : Formula.t list) : unit =
  List.iter (fun a ->
    match (a : Formula.t) with
    | Eq (LVar x, le) | Eq (le, LVar x)
    | Eq (PVar x, le) | Eq (le, PVar x) ->
      let x_type = TypEnv.get gamma x in
      (match x_type with
      | None ->
        let le_type, _, _ = Typing.type_lexpr gamma le in
        TypEnv.weak_update gamma x le_type
      | Some _ -> ())
    | _ -> ()
  ) a_list





(*  -----------------------------------------------------
  Normalise Logic Expressions
  -----------------------------------------------------
  _____________________________________________________
*)
let normalise_logic_expression 
    (store : SStore.t) (gamma : TypEnv.t) (subst : SSubst.t)
    (le    : Expr.t) : Expr.t = 
  let le'           = normalise_lexpr ~store:store ~subst:subst gamma le in 
  le' 


(*  -----------------------------------------------------
  Normalise Pure Assertion (only one!)
  -----------------------------------------------------
  Invoke normalise_logic_expression on all the logic
  expressions of a
  _____________________________________________________
*)
let rec normalise_pure_assertion
    (store : SStore.t)
    (gamma : TypEnv.t)
    (subst : SSubst.t)
    (assertion : Formula.t) : Formula.t =
  let fa = normalise_pure_assertion store gamma subst in
  let fe = normalise_logic_expression store gamma subst in
  let result : Formula.t = (match (assertion : Formula.t) with
  | Eq (le1, le2) -> Eq((fe le1), (fe le2))
  | Less (le1, le2) -> Less((fe le1), (fe le2))
  | LessEq (le1, le2) -> LessEq ((fe le1), (fe le2))
  | Not (Eq (le1, le2)) -> Not (Eq((fe le1), (fe le2)))
  | Not (LessEq (le1, le2)) -> Not (LessEq((fe le1), (fe le2)))
  | Not (Less (le1, le2)) -> Not (Less((fe le1), (fe le2)))
  | Not (SetSub (le1, le2)) -> Not (SetSub ((fe le1), (fe le2)))
  | Not (SetMem (le1, le2)) -> Not (SetMem ((fe le1), (fe le2)))
  | And (a1, a2) -> And ((fa a1), (fa a2))
  | Or (a1, a2) -> Or ((fa a1), (fa a2))
  | False -> False
  | True -> True
  | SetSub (le1, le2) -> SetSub ((fe le1), (fe le2))
  | SetMem (le1, le2) -> SetMem ((fe le1), (fe le2))
  | ForAll (bt, a) -> ForAll (bt, fa a)
  | _ ->
      let msg = Printf.sprintf "normalise_pure_assertion can only process pure assertions: %s" (Formula.str assertion) in
      raise (Failure msg)) in
    Typing.infer_types_formula gamma result;
    result


(** -----------------------------------------------------
  * Normalise Pure Assertions
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_pure_assertions
    (store  : SStore.t)
    (gamma  : TypEnv.t)
    (subst  : SSubst.t)
    (args   : SS.t option)
    (fs     : Formula.t list) : PFS.t =

  let pvar_equalities           = Hashtbl.create 31 in
  let non_store_pure_assertions = Stack.create () in

  (**
   * Step 1 - Get equalities involving program variables
   * -----------------------------------------------------------------------------------
   * Returns the list of equalities in a involving program variables of the form x = E
   * or E = x, for a logical expression E and a variable x
   * -----------------------------------------------------------------------------------
   *)
  let rec init_pvar_equalities (fs : Formula.t list) : unit =
    List.iter (fun (f : Formula.t) : unit -> 
      match f with 
      | Eq (PVar x, e) | Eq(e, PVar x) -> 
          if ((not (Hashtbl.mem pvar_equalities x)) && (not (SStore.mem store x)))
            then Hashtbl.add pvar_equalities x e
            else Stack.push (Formula.Eq (PVar x, e)) non_store_pure_assertions
      | _ -> Stack.push f non_store_pure_assertions
    ) fs in


  (**
   * Step 2 - Build a table mapping pvars to integers
   * ------------------------------------------------
   *)
  let get_vars_tbl (vars : SS.t) : (string, int) Hashtbl.t =
    let len = SS.cardinal vars in
    let vars_tbl = Hashtbl.create len in
    List.iteri (fun i var -> Hashtbl.add vars_tbl var i) (SS.elements vars);
      vars_tbl in


  (**
   * Step 3 - PVars Dependency Graph
   * ------------------------------------------------------------------------
   * Compute a dependency graph between PVar equalities (which are treated as
   * definitions)
   * ------------------------------------------------------------------------
   *)
  let pvars_graph
      (p_vars : SS.t)
      (p_vars_tbl : (string, int) Hashtbl.t) : (int list) array =
    let len = SS.cardinal p_vars in
    let graph = Array.make len [] in

    List.iteri (fun u cur_var ->
      let cur_le = Hashtbl.find pvar_equalities cur_var in
      let cur_var_deps = Expr.pvars cur_le in
      SS.iter (fun v ->
        (try
          let v_num = Hashtbl.find p_vars_tbl v in
          graph.(u) <- v_num :: graph.(u)
          with _ -> ())) cur_var_deps) (SS.elements p_vars);

    graph in


  (**
   * Step 4 - Normalise PVar equalities
   * ------------------------------------------------------------------------
   * Normalise equalities involving pvars
   * Detect cyclic dependencies between pvar definitions
   * Break dependencies by introducing new logical variables
   * E.g.
   *      (x = y + 1) * (y = #z) ==> (x = #z + 1) * (y = #z)
   *      (x = y + 1) * (y = (3 * x) - 2) ==>
          (x = #w + 1) * (y = #y) * (#y = (3 * (#y + 1)) - 2)
          where #y = new_lvar_name (y)
   * ------------------------------------------------------------------------
   *)
  let normalise_pvar_equalities
      (graph : int list array)
      (p_vars : SS.t)
      (p_vars_tbl : (string, int) Hashtbl.t) =

    let p_vars      = Array.of_list (SS.elements p_vars) in
    let len         = Array.length p_vars in
    let visited_tbl = Array.make len false in

    let is_searchable u =
      List.fold_left
        (fun ac v -> ac && (not visited_tbl.(v)))
        true
        graph.(u) in

    (** a pvar-equality that cannot be lifted to the abstract store
        has to remain in the pure formulae *)
    let remove_assignment var =
      (try
        let e = Hashtbl.find pvar_equalities var in
        Stack.push (Formula.Eq (LVar (new_lvar_name var), e)) non_store_pure_assertions;
        Hashtbl.remove pvar_equalities var
      with _ ->
        let msg = Printf.sprintf "DEATH. normalise_pure_assertions -> normalise_pvar_equalities -> remove_assignment. Var: %s." var in
        raise (Failure msg)) in


    (** lifting an assignment to the abstract store *)
    let rewrite_assignment var =
      (try
        let le  = Hashtbl.find pvar_equalities var in
        let le' = normalise_lexpr ~store:store ~subst:subst gamma le in
        SStore.put store var le';
        ()
      with _ ->
        let msg = Printf.sprintf "DEATH. normalise_pure_assertions ->  normalise_pvar_equalities -> rewrite_assignment. Var: %s\n" var in
        raise (Failure msg)) in


    (** DFS on pvar dependency graph *)
    let rec search (u : int) =
      let u_var = p_vars.(u) in
      visited_tbl.(u) <- true;
      match (is_searchable u) with
      | false -> remove_assignment u_var
      | true ->
          List.iter
            (fun v ->
              (* Given that u is searchable this if is very strange *)
              if (visited_tbl.(v))
                then ()
                else search v)
            graph.(u);
          rewrite_assignment u_var in
    for i = 0 to (len - 1) do
      if (not (visited_tbl.(i)))
      then search i
      else ()
    done in

  (**
   * Step 5 - The store is always full
   * ------------------------------------------------------------------------
   * PVars that were not associated with a logical expression in the store
   * are mapped to a newly created logical variable
   * ------------------------------------------------------------------------
   *)
  let fill_store args =
    let def_pvars  = SS.of_list (List.concat (List.map (fun f -> SS.elements (Formula.pvars f)) fs)) in
    let p_vars = Option.default def_pvars args in 
    SS.iter
      (fun var -> if (not (SStore.mem store var)) then (SStore.put store var (LVar (new_lvar_name var)); ()))
      p_vars in

  (**
   * Step 6 - Normalise Pure Assertions
   * ------------------------------------------------------------------------
   * The pure assertions that were not lifted to the store need to be
   * normalised
   * ------------------------------------------------------------------------
   *)
  let normalise_pure_assertions () =
    let stack_size = Stack.length non_store_pure_assertions in
    let pi         = DynArray.make (stack_size * 2) in
    let cur_index  = ref 0 in

    while (not (Stack.is_empty non_store_pure_assertions)) do
      let p_assertion  = Stack.pop non_store_pure_assertions in
      let p_assertion' = normalise_pure_assertion store gamma subst p_assertion in
      DynArray.add pi p_assertion';
      cur_index := (!cur_index) + 1
    done;
    
    L.log L.Verboser (lazy "About to simplify."); 
    let _ = Simplifications.simplify_pfs_and_gamma gamma pi (Some None) in
      L.log L.Verboser (lazy "Done simplifying.");
      pi in


  (* Doing IT *)
  (* 1 *) init_pvar_equalities fs;
  let p_vars = Hashtbl.fold (fun var le ac -> SS.add var ac) pvar_equalities SS.empty in
  
  L.log L.Verboser (lazy (Printf.sprintf "PVars in normalise_pvar_equalities: %s\n" (String.concat ", " (SS.elements p_vars))));

  (* 2 *) let p_vars_tbl = get_vars_tbl p_vars in
  (* 3 *) let pvars_graph = pvars_graph p_vars p_vars_tbl in
  (* 4 *) normalise_pvar_equalities pvars_graph p_vars p_vars_tbl;
  L.log L.Verboser (lazy "Going to fill the store now."); 
  (* 5 *) fill_store args;
  L.log L.Verboser (lazy "Filled store."); 
  (* 6 *) let result = normalise_pure_assertions () in 
            L.log L.Verboser (lazy "Finished normalising pure assertions.");
            result




(** -----------------------------------------------------
  * Separate an assertion into 
  *   cells, efs, metadata, pure, typing, predicates
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let rec separate_assertion 
  (store : SStore.t)
  (subst : SSubst.t)
  (a     : Asrt.t) : ((Expr.t * Expr.t * Expr.t) list) * ((Expr.t * Expr.t) list) * ((Expr.t * Expr.t) list) * (Formula.t list) * ((Expr.t * Type.t) list) * ((string * Expr.t list) list) = 
  
  let f  = separate_assertion store subst in 

  let var_to_aloc le = 
    (* TODO: Understand where the next line should go *)
    let le = Reduction.reduce_lexpr le in 
    match (le : Expr.t) with 
    | Lit (Loc _) -> () 
    | ALoc x -> ()
    | PVar x -> 
      if (not (SStore.mem store x))
      then (SStore.put store x (ALoc (new_aloc_name x)); ());
    | LVar x -> 
      if (not (SSubst.mem subst x))
        then SSubst.put subst x (ALoc (new_aloc_name x))
    | _ -> raise (Failure (Printf.sprintf "Illegal LExpr denoting location: %s" (Expr.str le))) in 
  
  match a with
    | Star (al, ar) ->
       let cells_l, efs_l, mtdt_l, pure_l, types_l, preds_l = f al in 
       let cells_r, efs_r, mtdt_r, pure_r, types_r, preds_r = f ar in 
     (cells_l @ cells_r, efs_l @ efs_r, mtdt_l @ mtdt_r, pure_l @ pure_r, types_l @ types_r, preds_l @ preds_r)

    | PointsTo (le1, le2, le3) -> 
      var_to_aloc le1; 
      [ (le1, le2, le3) ], [], [], [], [], []  

    | EmptyFields (le1, le2) -> 
      var_to_aloc le1; 
      [], [ (le1, le2) ], [], [], [], []  

    | MetaData (le1, le2) -> 
      var_to_aloc le1; 
      [], [], [ (le1, le2) ], [], [], [] 

    | Emp -> [], [], [], [], [], []

    | Types lst -> [], [], [], [], lst, []

    | Pred (name, params) -> [], [], [], [], [], [ (name, params) ]

    | Pure f -> [], [], [], [ f ], [], []

(** -----------------------------------------------------
  * Normalise Cell Assertions
  * (Initialise Symbolic Heap)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let rec normalise_cells
  (heap : SHeap.t) 
  (store : SStore.t)
  (p_formulae : PFS.t) 
  (gamma : TypEnv.t)
  (subst : SSubst.t) 
  (cells : (Expr.t * Expr.t * Expr.t) list) : unit =
  
  let fe = normalise_logic_expression store gamma subst in

  let normalise_cell_assertion (loc, prop, p_val) = 
    let loc   = fe loc in 
    let prop  = fe prop in
    let p_val = fe p_val in 

    let loc_name =
      match loc with
        | Lit (Loc loc_name) | ALoc loc_name -> loc_name
      | _ -> raise (Failure "Illegal Cell Assertion!!!") in
    
    let (field_val_pairs, dom), metadata = SHeap.get_with_default heap loc_name in
    SHeap.set heap loc_name (SFVL.add prop p_val field_val_pairs) dom metadata in 

  List.iter normalise_cell_assertion cells 


(** -----------------------------------------------------
  * Normalise EmptyFields Assertions
  * (Initialise Symbolic Heap Domains)
  * -----------------------------------------------------
  * ERROR: TO FIX: EF can be duplicated
  * -----------------------------------------------------
**)
let normalise_efs
  (heap       : SHeap.t) 
  (store      : SStore.t)
  (p_formulae : PFS.t) 
  (gamma      : TypEnv.t)
  (subst      : SSubst.t) 
  (ef_asrts   : (Expr.t * Expr.t) list) : unit =
  
  let fe    = normalise_logic_expression store gamma subst in

  let add_domain (loc, domain)  =
    let loc, domain = fe loc, fe domain in 
    L.log L.Verboser (lazy (Printf.sprintf "Normalise EFs: Location: %s" (Expr.str loc)));
    
    let loc_name =
      match loc with
      | Lit (Loc loc_name) | ALoc loc_name -> loc_name
      | _ ->  L.fail "ERROR: Normalise EFs: Illegal EmptyFields." in 

    let (fv_list, old_domain), metadata = SHeap.get_with_default heap loc_name in 
    
    match old_domain with
      | None   -> SHeap.set heap loc_name fv_list (Some domain) metadata
      | Some _ -> L.fail "ERROR: Normalise EFs: Duplicate EF assertion." in

  List.iter add_domain ef_asrts



(** -----------------------------------------------------
  * Normalise Metadata
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_metadata
  (heap       : SHeap.t) 
  (store      : SStore.t)
  (p_formulae : PFS.t) 
  (gamma      : TypEnv.t)
  (subst      : SSubst.t) 
  (mtdt_asrts : (Expr.t * Expr.t) list) : unit =
  
  let fe = normalise_logic_expression store gamma subst in

  let add_metadata (loc, metadata)  =
    let loc_name =
      match (loc : Expr.t) with
        | Lit (Loc loc_name) | ALoc loc_name -> loc_name
        | _ -> raise (Failure (Printf.sprintf "Illegal Metadata: %s" (Expr.str loc))) in

    let (fv_list, domain), old_metadata = SHeap.get_with_default heap loc_name in 

     match old_metadata with
      | None            
      | Some (Lit Null) -> SHeap.set heap loc_name fv_list domain (Some metadata)
      | Some om          -> 
          (* This is a bit of a hack, we need to revisit *)
          (match metadata, om with 
          | ALoc nm, ALoc om ->
              let new_subst = SSubst.init [ nm, ALoc om ] in 
              SHeap.substitution_in_place new_subst heap;
              SStore.substitution_in_place new_subst store;
              PFS.substitution_in_place new_subst p_formulae;
              SSubst.iter subst (fun v le ->  SSubst.put subst v (SSubst.subst_in_expr subst true le))
          | _ -> raise (Failure (Printf.sprintf "Duplicate Metadata assertion: %s : from %s to %s" loc_name (Expr.str om) (Expr.str metadata)))) in

  List.iter add_metadata (List.map (fun (loc, md) -> fe loc, fe md) mtdt_asrts)



(** -----------------------------------------------------
  * Normalise Type Assertions
  * (Initialise Typing Environment)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_types
  (store      : SStore.t)
  (gamma      : TypEnv.t)
  (subst      : SSubst.t) 
  (type_list : (Expr.t * Type.t) list) : bool =

  let fe    = normalise_logic_expression store gamma subst in

  let type_check_lexpr (le : Expr.t) (t : Type.t) : bool = 
    let le_type, success, _ = Typing.type_lexpr gamma le in
      if (not success) then 
        raise (Failure (Printf.sprintf "DEATH. normalise_type_assertions: expression %s not typable" (Expr.str le)))
      else
        Option.map_default
          (fun tt -> t = tt)
          (let new_gamma = Typing.reverse_type_lexpr false gamma le t in
            Option.map_default (fun new_gamma -> TypEnv.extend gamma new_gamma; true) false new_gamma) le_type in


   List.fold_left
     (fun ac (le, t) -> 
       if (not ac) then false else (
         match (fe le) with
         | Lit lit -> (Literal.type_of lit) = t 

     | LVar x   -> TypEnv.update gamma x (Some t); true 

     | PVar x   ->  raise (Failure "DEATH. normalise_type_assertions") 

     | le       -> type_check_lexpr le t)
    ) true type_list



(** -----------------------------------------------------
  * Normalise Predicate Assertions
  * (Initialise Predicate Set)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_preds
  (store      : SStore.t) 
  (gamma      : TypEnv.t)
  (subst      : SVal.SSubst.t) 
  (pred_asrts : (string * Expr.t list) list) : SPreds.t =
  
  let fe    = normalise_logic_expression store gamma subst in
  let preds = SPreds.init [] in
    
    List.iter (fun (pn, les) -> SPreds.extend preds (pn, (List.map fe les))) pred_asrts; 

  preds



(** -----------------------------------------------------
  * Normalise Assertion
  * Given an assertion creates a symbolic state and a
  * substitution
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_assertion
    ?(pred_defs : UP.preds_tbl_t option)
    (gamma : TypEnv.t option)
    (subst : SSubst.t option)
    (pvars : SS.t option)
    (a     : Asrt.t) : (AbsSState.M.t * SSubst.t) option =

  L.log L.Verboser (lazy (Printf.sprintf "Normalising assertion:\n\t%s" (Asrt.str a)));

  let falsePFs pfs = (DynArray.length pfs = 1) && (DynArray.get pfs 0 = Formula.False) in

  (** Step 1 -- Preprocess list expressions - resolve l-nth(E, i) when possible  *)
  let svars = SS.filter SCommon.is_spec_var_name (Asrt.lvars a) in 
  let a     = Reduction.pre_process_list_exprs a in

  (** Step 2a -- Create empty symbolic heap, symbolic store, typing environment, and substitution *)
  let heap  = SHeap.init () in
  let store = SStore.init [] in
  let gamma = Option.map_default TypEnv.copy (TypEnv.init ()) gamma in
  let subst = Option.map_default SSubst.copy (SSubst.init []) subst in


  (** Step 2b -- Separate assertion *)
  let cells, efs, mtdts, pfs, types, preds = separate_assertion store subst a in

  L.log L.Verboser (lazy (Printf.sprintf "Separate assertion subst: %s" (SSubst.str subst)));
  L.log L.Verboser (lazy (Printf.sprintf "Here are the pfs: %s" (PFS.str (PFS.of_list pfs))));

  (** Step 3 -- Normalise type assertions and pure assertions
    * 3.1 - type assertions -> initialises gamma
    * 3.2 - pure assertions -> initialises store and pfs
  *)
  let success = normalise_types store gamma subst types in
  (match success with
  | false -> L.log L.Verboser (lazy ("WARNING: normalise_assertion: type assertions could not be normalised")); None
  | true -> 
    let pfs = normalise_pure_assertions store gamma subst pvars pfs in
    (match falsePFs pfs with
    | true -> L.log L.Verboser (lazy "WARNING: normalise_assertion: pure formulae false"); None
    | false -> 
      L.log L.Verboser (lazy (Printf.sprintf "Here is the store: %s" (SStore.str store)));
      (** Step 4 -- Add to the store the program variables that are not there yet, BUT for which we know the types *)
      extend_typing_env_using_assertion_info gamma (PFS.to_list pfs);

      (** Step 5 -- Normalise cell assertions, pred assertions, and ef assertions
        * 5.1 - cells, efs, metadata -> initialises heap
        * 5.2 - pred assertions      -> initialises pred set
      *)
      normalise_cells heap store pfs gamma subst cells;
      normalise_efs heap store pfs gamma subst efs; 

      normalise_metadata heap store pfs gamma subst mtdts; 
      let preds = normalise_preds store gamma subst preds in
      
      SSubst.iter subst (fun var value -> PFS.extend pfs (Eq (LVar var, value)));

      let ret_ss = SState.s_init heap store pfs gamma svars in 
      L.log L.Verboser (lazy (Printf.sprintf "Subst:\n\t%s\n%s" (SSubst.str subst) (SState.str ret_ss)));

      (** Step 6 -- Check if the symbolic state makes sense *)
      let hp_constraints = SHeap.wf_assertions heap in
      if (FOSolver.check_satisfiability (hp_constraints @ (PFS.to_list pfs)) gamma)
        then ( 
          let ret_ss = SState.s_init heap store pfs gamma svars in
          let heap, store, pfs, gamma, svars = ret_ss in 
          let pred_vars = SPreds.lvars preds in 
          let subst', _ = Simplifications.simplify_pfs_and_gamma gamma pfs ~kill:true (Some (Some (SS.union pred_vars svars))) in 
          L.log L.Verboser (lazy (Printf.sprintf "normalise_assertion returning:\nSTATE:\n%s\nPREDICATES:\n%s\nand subst:\n%s" 
            (SState.str ret_ss) (SPreds.str preds) (SSubst.str subst')));
          
          let subst'' = SSubst.filter subst' (fun x _ -> not (SS.mem x svars)) in 
          SHeap.substitution_in_place subst'' heap; 
          SStore.substitution_in_place subst'' store; 
          
          let inv_metadata = SHeap.get_inv_metadata heap in 
          let astate       = AbsSState.M.initialise ret_ss preds pred_defs in 
          let _            = AbsSState.M.simplify astate in
          Some (astate, subst)
        ) else (L.log L.Verboser (lazy "WARNING: normalise_assertion: returning None"); None)))


