(** JSIL Typing Environment *)

open CCommon
open SCommon
open SVal

module L = Logging

type t = (string, Type.t) Hashtbl.t

let str (x : t) : string =
  Hashtbl.fold
    (fun var var_type ac ->
      let var_type_pair_str = Printf.sprintf "(%s: %s)" var (Type.str var_type) in
      let new_line = if (ac = "") then "\t" else "\n\t" in
        ac ^ new_line ^ var_type_pair_str)
    x
    ""

(*************************************)
(** Typing Environment Functions    **)
(*************************************)

(* Initialisation *)
let init () : t = Hashtbl.create medium_tbl_size
  
(* Copy *)
let copy (x : t) : t = Hashtbl.copy x

(* Type of a variable *)
let get (x : t) (var : string) : Type.t option =
  Hashtbl.find_opt x var

(* Membership *)
let mem (x : t) (v : string) : bool = 
  Hashtbl.mem x v

(* Empty *)
let empty (x : t) : bool =
  (Hashtbl.length x == 0)

(* Type of a variable *)
let get_unsafe (x : t) (var : string) : Type.t =
  (match Hashtbl.mem x var with
  | true -> Hashtbl.find x var
  | false -> raise (Failure ("TypEnv.get_unsafe: variable " ^ var ^ " not found.")))

(* Get all unifiable elements *)
let unifiables (x : t) : SS.t = 
  Hashtbl.fold (fun var _ ac -> SS.add var ac) x SS.empty

(* Get all variables *)
let vars (x : t) : SS.t =
  Hashtbl.fold (fun var _ ac -> SS.add var ac) x SS.empty

(* Get all logical variables *)
let lvars (x : t) : SS.t =
  Hashtbl.fold (fun var _ ac -> if is_lvar_name var then SS.add var ac else ac) x SS.empty

(* Get all variables of specific type *)
let get_vars_of_type (x : t) (tt : Type.t) : string list =
  Hashtbl.fold (fun var t ac_vars -> (if (t = tt) then var :: ac_vars else ac_vars)) x []

(* Get all var-type pairs as a list *)
let get_var_type_pairs (x : t) : (string * Type.t) list = Hashtbl.fold (fun var t ac_vars -> ((var, t) :: ac_vars)) x []

(* Iteration *)
let iter (x : t) (f : string -> Type.t -> unit) : unit = 
  Hashtbl.iter f x

let fold (x : t) (f : string -> Type.t -> 'a -> 'a) (init : 'a) : 'a = 
  Hashtbl.fold f x init

(* Update with removal *)
let update (x : t) (v : string) (te : Type.t option) : unit =
  (match te with
  | None    -> Hashtbl.remove x v
  | Some te -> Hashtbl.replace x v te)

(* Update without removal *)
let weak_update (x : t) (v : string) (te : Type.t option) : unit =
  (match te with
  | None -> ()
  | Some te -> Hashtbl.replace x v te)

(* Extend gamma with more_gamma *)
let extend (x : t) (y : t) : unit =
  iter y
    (fun v t ->
      match (Hashtbl.find_opt x v) with
      | None    -> Hashtbl.replace x v t
      | Some t' -> if (t <> t') then raise (Failure "Typing environment cannot be extended.")
    )

(* Filter using function on variables *)
let filter (x : t) (f : string -> bool) : t =
  let new_gamma = init () in
  iter x (fun v v_type -> (if (f v) then update new_gamma v (Some v_type)));
  new_gamma

(* Filter using function on variables *)
let filter_in_place (x : t) (f : string -> bool) : unit =
  iter x (fun v v_type -> (if (not (f v)) then update x v None))

(* Filter for specific variables *)
let filter_vars (gamma : t) (vars : SS.t) : t = filter gamma (fun v -> SS.mem v vars)

(* Filter for specific variables *)
let filter_vars_in_place (gamma : t) (vars : SS.t) : unit = filter_in_place gamma (fun v -> SS.mem v vars)

(* Perform substitution, return new typing environment *)
let rec substitution (x : t) (subst : SSubst.t) (partial : bool) : t =
  let new_gamma = init () in
  iter x
    (fun var v_type ->
      let new_var = SSubst.get subst var in
      (match new_var with
      | Some (LVar new_var) -> update new_gamma new_var (Some v_type)
      | Some _ -> if partial then update new_gamma var (Some v_type)
      | None   -> if partial then update new_gamma var (Some v_type)
                    else 
            if (is_lvar_name var) then (
              let new_lvar = fresh_lvar () in
              SSubst.put subst var (LVar new_lvar);
              update new_gamma new_lvar (Some v_type)
            )));
  new_gamma


(* Convert to assertion *)
let to_list (x : t) : (Expr.t * Type.t) list = 
  let le_type_pairs = 
    Hashtbl.fold
      (fun x t (pairs : (Expr.t * Type.t) list) -> 
        (if (is_lvar_name x) 
          then (LVar x, t) :: pairs
          else (PVar x, t) :: pairs)) x [] in 
  le_type_pairs 

let is_well_formed (x : t) : bool = true