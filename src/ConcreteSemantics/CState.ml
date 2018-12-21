open CCommon
open SCommon

open Literal

(*********************)
(*                   *)
(*  C States  *)
(*                   *)
(*********************)

type vt      = CVal.M.t 
type st      = CVal.CSubst.t 
type store_t = CStore.M.t
type err_t   = CError.M.t 
type t       = CHeap.t * CStore.M.t * (vt list)

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

let init (pred_defs : UP.preds_tbl_t option) = (CHeap.init ()), (CStore.M.init []), [] 

let get_pred_defs (state : t) : UP.preds_tbl_t option = None 

let lift l = l 

let unlift l = Some l 

let eval_expr state e =
  let _, store, _ = state in
  CExprEval.evaluate_expr store e 

let get_store state = 
   let _, store, _ = state in 
   store 

let set_store state store = 
    let heap, _, locs = state in 
    (heap, store, locs)

let alloc (state : t) (loc : vt option) (mv : vt) = 
   let heap, store, locs = state in 
   let new_loc =
     match loc with 
     | None -> fresh_loc ()
     | Some (Loc loc) -> loc 
     | _ -> raise (Failure "C Allocation: non-loc loc argument") in
   CHeap.set heap new_loc (CObject.init (), mv); 
   let new_loc_lit = Loc new_loc in 
   new_loc_lit, (heap, store, (new_loc_lit :: locs))

let to_loc (state : t) (loc : vt) : (t * vt) option = 
  match loc with 
  | Literal.Loc _ -> Some (state, loc)
  | _ -> None

let get_locs state = 
  let _, _, locs = state in 
  locs

let set_cell state loc prop v = 
  let heap, _, _ = state in
  let loc, prop = 
    match loc, prop with 
      | Loc loc, String prop -> loc, prop 
      | _ -> raise (Failure "C Heap Update: illegal heap update") in 
   
  let obj = CHeap.get heap loc in
  (match obj with 
    | None -> raise (Failure "C Heap Update: object not found")
    | Some (obj, _) ->
        (match v with 
          | None   -> CObject.remove obj prop 
          | Some v -> CObject.set    obj prop v); 
        state)


let get_cell ?(remove : bool option) (state : t) (loc : vt) (prop : vt) : gc_ret = 
  let heap, store, _ = state in 
  let loc, prop = 
    match loc, prop with 
      | Loc loc, String prop -> loc, prop 
      | _ -> raise (Failure "Illegal get_cell") in 

  let remove = Option.default false remove in 
  if remove then (
    raise (Failure "Concrete get_cell. Remove Option must be implemented!")
  ) else (  
    match CHeap.get heap loc with 
      | None          -> GCFail [] 
      | Some (obj, _) -> GCSucc [ (state, Loc loc, String prop, (CObject.get obj prop)) ] 
  )   
   

let get_domain ?(expected_props : vt option) ?(remove : bool option) (state : t) (loc : vt) : gd_ret = 
   let heap, store, _ = state in 
   let loc = 
      match loc with 
      | Loc loc -> loc 
      | _ -> raise (Failure "Illegal get_domain") in 

   let remove = Option.default false remove in 
   if remove then (
     raise (Failure "Concrete get_domain. Remove Option must be implemented!")
   ) else (
     match CHeap.get heap loc with 
       | None           -> GDFail []  
       | Some (obj, _)  -> 
         let props = CObject.properties obj in 
         GDSucc [ state, LList (List.map (fun prop -> String prop) props) ]
    )


let get_metadata ?(remove : bool option) (state : t) (loc : vt) : gm_ret = 
  let heap, store, _ = state in 
  let loc = 
    match loc with 
      | Loc loc -> loc 
      | _ -> raise (Failure "Illegal get_domain") in 

  let remove = Option.default false remove in 
    if remove then (
      raise (Failure "Concrete get_metadata. Remove Option must be implemented!")
    ) else (
      match CHeap.get heap loc with 
        | None            -> GMFail []  
        | Some (obj, vm)  -> GMSucc [ state, Loc loc, vm ]  
    )


let set_domain (state : t) (loc : vt) (dom : vt) : t = 
  raise (Failure "domain_update illegal in concrete semantics")


let set_metadata (state : t) (loc : vt) (mtdt : vt) : t =
  let heap, store, _ = state in 
  let loc = 
    match loc with 
    | Loc loc -> loc 
    | _ -> raise (Failure "Illegal metadata_update") in 
  let obj = 
    match CHeap.get heap loc with 
    | None          -> raise (Failure "Illegal metadata_update") 
    | Some (obj, _) -> obj in 
  CHeap.set heap loc (obj, mtdt); 
  state 

let delete_object (state : t) (e_loc : Expr.t) : t = 
  let heap, store, locs = state in 
  let loc  = eval_expr state e_loc in 
  let loc = 
    match loc with 
      | Loc loc -> loc 
      | _ -> raise (Failure "Illegal get_domain") in 
   (match CHeap.get heap loc with 
     | None            -> raise (Failure "delete_obj. location does NOT exist in the heap") 
     | Some _          -> CHeap.remove heap loc); 
   let locs' = List.filter (fun l -> not(l = Loc loc)) locs in 
     (heap, store, locs') 


let assume (state : t) (l : Literal.t) : t list =  
  match l with 
    | Bool true  -> [ state ]
    | Bool false -> [ ]
    | _          -> raise (Failure "assume. illegal argument to assume")

let assume_a (state : t) (ps : Formula.t list) : t option = 
  let les : Expr.t option list = List.map Formula.to_expr ps in 
  let es  : Expr.t option list  = List.map (fun le -> Option.map Expr.to_expr le) les in  
  let bs  : CVal.M.t option list  = List.map (fun e -> Option.map (eval_expr state) e) es in 
  if List.exists (fun expr_b -> expr_b <> Some (Bool true)) bs 
    then Some state 
    else None  

let assume_t (state : t) (v : vt) (t : Type.t) : t option = 
  if ((Literal.type_of v) = t) 
    then Some state 
    else None 

let assert_a (state : t) (ps : Formula.t list) : bool = 
  Option.map_default (fun _ -> true) false (assume_a state ps)  

let sat_check (state : t) (l : Literal.t) : bool = 
  match l with 
    | Bool b  -> b
    | _       -> raise (Failure "SAT Check: non-boolean argument")


(* Implentation MISSING!!! *)
let sat_check_f (state : t) (f : Formula.t list) : st option = 
  None 

let str state = 
  let heap, store, locs = state in 
  let store_str = CStore.M.str store in
  let heap_str = if (!CCommon.no_heap) then "HEAP NOT PRINTED" else CHeap.str heap in 
  Printf.sprintf "%sSTORE: %s\nHEAP:\n%s\n" SCommon.dashes store_str heap_str

let copy state = 
  let (cheap, cstore, vts) = state in 
    (CHeap.copy cheap, CStore.M.copy cstore, vts)

let equals state v1 v2 = (v1 = v2)

let get_type state v = Some (Literal.type_of v)

let simplify ?(kill : bool option) (state : t) : st = CVal.CSubst.init []

let simplify_val state v = v 

let add_spec_vars state xs = raise (Failure "ERROR: add_spec_var called for concrete executions")

let get_spec_vars state = raise (Failure "ERROR: get_spec_vars called for concrete executions")

let get_lvars state = raise (Failure "ERROR: get_lvars called for concrete executions")

let to_assertions ?(to_keep : SS.t option) (state : t) : Asrt.t list =  raise (Failure "ERROR: to_assertions called for concrete executions")

let run_spec (spec : UP.spec) (state : t) (args : vt list) (subst : (string * (string * vt) list) option) : (t * vt option * Flag.t) list = 
  raise (Failure "ERROR: run_spec called for non-abstract execution")

let unify (state : t) (subst : st) (up : UP.t) : bool = 
  raise (Failure "ERROR: unify called for non-abstract execution") 

let unfolding_vals (state : t) (fs : Formula.t list) : vt list = 
  raise (Failure "ERROR: unfolding_vals called for non-abstract execution") 

let evaluate_slcmd (prog : UP.prog) (slcmd : SLCmd.t) (state : t) : t list = 
  raise (Failure "ERROR: evaluate_slcmd called for non-abstract execution")      

let substitution_in_place (subst : st) (state : t) : unit = () 

let fresh_val (state : t) = raise (Failure "fresh_val not implemented in concrete state")

let fresh_loc ?(loc : vt option) (state : t) = raise (Failure "fresh_loc not implemented in concrete state")

let get_locs (state : t) = 
  raise (Failure "Unsupported: get locs in a concrete state")

let get_locs_and_props (state : t) = 
  raise (Failure "Unsupported: get locs and props in a concrete state")

let clean_up (state : t) = 
  raise (Failure "Cleanup of concrete state.")

let unify_assertion (state : t) (subst : st) (p : Asrt.t) : u_res = 
  raise (Failure "Unify assertion from concrete state.")   

 let produce_posts (state  : t) (subst  : st) (asrts : Asrt.t list) : t list = 
    raise (Failure "produce_posts from concrete state.")   

  let produce (state  : t) (subst  : st) (asrt : Asrt.t) : t option = 
    raise (Failure "produce_post from non-abstract symbolic state.")

let update_subst (state : t) (subst : st) : unit = () 


