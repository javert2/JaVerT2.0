open SVal

(** Implementation of JSIL Stores *)
module M (Val : Val.M) : (Store.M with type vt = Val.t) = struct

  module L = Logging 

  (** Type of JSIL values *)
  type vt = Val.t

  (** Actual type of JSIL Stores *)
  type t = {
    conc: (Var.t, vt) Hashtbl.t; 
    symb: (Var.t, vt) Hashtbl.t 
  }

  (** 
    Store initialisation

    @param vars_and_vals Variables and values to be put in the store
    @return Newly constructed and initialised store
  *)
  let init (vars_and_vals : (Var.t * vt) list) : t = 
    let new_store = { conc = Hashtbl.create CCommon.big_tbl_size; symb = Hashtbl.create CCommon.big_tbl_size } in 
      List.iter (fun (x, v) -> if (Val.is_concrete v) then (Hashtbl.replace new_store.conc x v) else (Hashtbl.replace new_store.symb x v)) vars_and_vals; 
      new_store 

  (** 
    Store copy

    @param store Target store
    @return Copy of the given store
  *)
  let copy (store : t) : t = 
    { conc = Hashtbl.copy store.conc; symb = Hashtbl.copy store.symb }

  (** 
    Store lookup

    @param store Target store
    @param x Target variable
    @return Optional value of the variable in the store
  *)
  let get (store : t) (x : Var.t) : vt option = 
    let result = Hashtbl.find_opt store.conc x in 
    if (result = None) then Hashtbl.find_opt store.symb x
      else result

  (** 
    Store get with throw

    @param store Target store
    @param x Target variable
    @raise Failure Variable not found in the store
    @return Value of the variable in the store
  *)
  let get_unsafe (store : t) (v : Var.t) : vt =
    match (get store v) with 
    | Some result -> result
    | None -> raise (Failure (Printf.sprintf "Store.get_unsafe: variable %s not found in store" v))

  (** 
    Store update (in-place)

    @param store Target store
    @param x Target variable
    @param v Value to be put
  *)
  let put (store : t) (x : Var.t) (v : vt) : unit = 
    let add, rem = if Val.is_concrete v then store.conc, store.symb else store.symb, store.conc in 
      Hashtbl.replace add x v; Hashtbl.remove rem x 

  (** 
    Store removal (in-place)

    @param store Target store
    @param x Target variable
  *)
  let remove (store : t) (x : Var.t) : unit = 
    Hashtbl.remove store.conc x; Hashtbl.remove store.symb x

  (** 
    Store membership check 

    @param store Target store
    @param x Target variable
    @return true if the variable is in the store, false otherwise
  *)
  let mem (store : t) (x : Var.t) : bool =
    Hashtbl.mem store.conc x || Hashtbl.mem store.symb x

  (** 
    Store iterator

    @param store Target store
    @param f Iterator function 
  *)
  let iter (store : t) (f : Var.t -> vt -> unit) : unit =
    Hashtbl.iter f store.conc; Hashtbl.iter f store.symb

  (** 
    Store fold

    @param store Target store
    @param f Fold function 
    @param ac Accumulator
  *)
  let fold (store : t) (f : Var.t -> vt -> 'a  -> 'a) (ac : 'a) : 'a =
    Hashtbl.fold f store.symb (Hashtbl.fold f store.conc ac)

  (** 
    Store bindings 

    @param store Target store
    @return Bindings of the store formatted as (variable, value)
  *)
  let bindings (store : t) : (Var.t * vt) list = 
      fold store (fun x le ac -> (x, le) :: ac) []

  (** 
    Store domain

    @param store Target store
    @return Set of variables that are in the domain of the store
  *)
  let domain (store : t) : Var.Set.t =
    Var.Set.of_list (fold store (fun x _ ac -> x :: ac) [])

  (** 
    Store filtering (in-place)

    @param store Target store
    @param f The filtering function
  *)
  let filter (store : t) (f : Var.t -> vt -> vt option) : unit = 
    Hashtbl.filter_map_inplace f store.conc; Hashtbl.filter_map_inplace f store.symb

  (** 
    Store partition

    @param store Target store
    @param f The partitioning function
    @return Set of variables satisfying the function, set of variables not satisfying the function
  *)
  let partition (store : t) (f : vt -> bool) : Var.Set.t * Var.Set.t =
    fold store (fun store le (pred_xs, npred_xs) ->
      if (f le) then (Var.Set.add store pred_xs, npred_xs) else (pred_xs, Var.Set.add store npred_xs))
    (Var.Set.empty, Var.Set.empty)

  (** 
    Store projection

    @param store Target store
    @param xs List of variables to be projected
    @return New store that only contains the projected variables
  *)
  let projection (store : t) (xs : Var.t list) : t =
    let y = init [] in
      List.iter (fun v ->
        if (mem store v) then put y v (get_unsafe store v)
      ) xs;
      y

  (** 
    Store printer 

    @param store JSIL store
    @return String representation of the store
  *)
  let str (store : t) : string =
    let bindings = bindings store in 
    let bindings = List.sort (fun (v, _) (w, _) -> Pervasives.compare v w) bindings in 
    let sep = "\n    " in
    let var_vals_str = List.map (fun (x, x_val) -> "(" ^ x ^ ": " ^ (Val.full_str x_val) ^ ")") bindings in 
    "\n  [" ^ sep ^ (String.concat sep var_vals_str) ^ "\n  ]" 

  (** 
    Store to substitution

    @param store to turn into an ssubst 
    @return ssubst mapping the store variables to lexprs 
  *) 
  let to_ssubst (store : t) : SSubst.t = 
    let subst = SSubst.init [ ] in 
    iter store (fun x v -> SSubst.put subst x (Val.to_expr v)); 
    subst 

  (** 
    Variables that can be affected by substitution

    @param target store 
    @return Set of variables that can be affected by substitution
  *) 
  let symbolics (store : t) : Var.Set.t = 
    L.log L.Verboser (lazy (Printf.sprintf "SCON: %d" (Hashtbl.length store.conc)));
    L.log L.Verboser (lazy (Printf.sprintf "SSYM: %d" (Hashtbl.length store.symb)));
    Hashtbl.fold (fun v _ ac -> Var.Set.add v ac) store.symb Var.Set.empty

  let lvars (store : t) : Var.Set.t = 
    Hashtbl.fold (fun _ v ac -> Var.Set.union ac (Expr.lvars (Val.to_expr v))) store.symb Var.Set.empty

end