open CCommon
open SCommon

module L = Logging

module M (Val : Val.M) : (Subst.M with type vt = Val.t) = struct 

  (** Type of JSIL values *)
  type vt = Val.t 

  (** Type of JSIL substitutions, implemented as hashtables *)
  type t  = ((Var.t, vt) Hashtbl.t)

  (** 
    Substitution constructor 

    @param vars_les Bindings of the form (variable, value)
    @return Substitution with the given bindings
  *)
  let init (vars_les : (Var.t * vt) list) : t =
    let subst = Hashtbl.create big_tbl_size in
    List.iter (fun (v, v_val) -> Hashtbl.replace subst v v_val) vars_les; 
    subst 

  let clear (subst : t) : unit =
    Hashtbl.clear subst

  (** 
    Substitution domain 

    @param subst Target substitution
    @param filter_out Optional filtering function
    @return Domain of the (filtered) substitution
  *)
  let domain (subst : t) (filter_out : (Var.t -> bool) option) : SS.t = 
    let filter = 
      match filter_out with 
      | Some filter -> filter 
      | None -> (fun x -> false) in 
    Hashtbl.fold 
      (fun k v ac -> if (filter k) then ac else SS.add k ac)
    subst SS.empty
  
  (** 
    Substitution range 

    @param subst Target substitution
    @return Range of the substitution
  *)
  let range (subst : t) : vt list = 
    Hashtbl.fold (fun v v_val ac -> v_val :: ac) subst [] 

  (** 
    Substitution lookup 

    @param subst Target substitution
    @param x Target variable
    @return Resulting (optional) value
  *)
  let get (subst : t) (x : Var.t) : vt option = 
    Hashtbl.find_opt subst x 

  (** 
    Substitution incremental update 

    @param subst Target substitution
    @param x Target variable
    @param v Target value
  *)
  let add (subst : t) (x : Var.t) (v : vt) : unit = 
    Hashtbl.add subst x v 
  
  (** 
    Substitution update 

    @param subst Target substitution
    @param x Target variable
    @param v Target value
  *)
  let put (subst : t) (x : Var.t) (v : vt) : unit = 
    Hashtbl.replace subst x v 

  (** 
    Substitution membership 

    @param subst Target substitution
    @param x Target variable
    @return Returns true if the variable is in the domain of the substitution, and false otherwise
  *)
  let mem (subst : t) (x : Var.t) : bool = 
    Hashtbl.mem subst x 

  (** 
    Substitution copy

    @param subst Target store
    @return Copy of the given substitution
  *)
  let copy (subst : t) : t = Hashtbl.copy subst

  (** 
    Substitution extension

    @param store Target substitution
    @param extend 
  *)
  let extend (subst : t) (vars_les : (Var.t * vt) list) : unit =
    List.iter (fun (v, v_val) -> Hashtbl.replace subst v v_val) vars_les

  (** 
    Substitution iterator

    @param subst Target substitution
    @param f Iterator function 
  *)
  let iter (subst : t) (f : Var.t -> vt -> unit) : unit = 
    Hashtbl.iter f subst

  (** 
    Substitution fold

    @param subst Target substitution
    @param f Fold function 
    @param ac Accumulator
  *)
  let fold (subst : t) f ac = 
    Hashtbl.fold f subst ac

  (** 
    Substitution merge into left

    @param subst Target substitution
    @param subst_ext Substitution extension
  *)
  let merge_left (subst : t) (subst_ext : t) : unit =
    Hashtbl.iter (fun v v_val -> Hashtbl.replace subst v v_val) subst_ext

  (** 
    Substitution filter 

    @param subst Target substitution
    @param filter Filtering function
    @return The new, filtered substitution
  *)
  let filter (subst : t) (filter : Var.t -> vt -> bool) : t  =
    let new_subst = copy subst in
    Hashtbl.filter_map_inplace (fun v v_val ->
      match (filter v v_val) with
      | true -> Some v_val
      | false -> None) new_subst;
    new_subst
  
  (** 
    Substitution filter by variables

    @param subst Target substitution
    @param vars Variables to save
    @return The new, filtered substitution
  *)
  let projection (subst : t) (vars : SS.t) : t =
    filter subst (fun x _ -> SS.mem x vars)            

  (** 
    Substitution printer 
  
    @param subst Target substitution
    @return String representation of the substitution
  *)
  let str (subst : t) : string =
    if (Hashtbl.length subst = 0) then "[]" else 

    let kvpairs = Hashtbl.fold (fun v v_val ac -> (v, v_val) :: ac) subst [] in 
    let kvpairs = List.sort (fun (v1, _) (v2, _) -> Pervasives.compare v1 v2) kvpairs in 
    let strs = List.map (fun (v, v_val) -> "(" ^ v ^ ": " ^ (Val.str v_val) ^ ")") kvpairs in 
      "[" ^ (String.concat ", " strs) ^ "]"

  (** 
    Substitution in-place filter 
  
    @param subst Target substitution
    @param filter Filtering function
    @return Filtered substitution
  *)
  let filter_in_place (subst : t) (filter : (Var.t -> vt -> vt option)) : unit = 
     Hashtbl.filter_map_inplace filter subst

  (** 
    Conversion to a list

    @params subst Target substitution
    @return List of bindings of the form (variable, value)
  *)
  let to_list (subst : t) : (Var.t * vt) list = 
     Hashtbl.fold 
      (fun v v_val ac ->  (v, v_val) :: ac)
      subst                                      
      []    

  (** 
    Substitution inside an expression 

    @param subst Target substitution
    @param le Target expression
    @return Expression resulting from the substitution, with fresh locations created.
  *)
  let subst_in_expr (subst : t) (partial : bool) (le : Expr.t) : Expr.t = 
    
    let find_in_subst (x : Var.t) (le_x_old : Expr.t) (make_new_x : unit -> Expr.t) : Expr.t = 
      (match get subst x with 
      | Some v -> Val.to_expr v
      | None -> 
        if partial then le_x_old else (
          let new_le_x = make_new_x () in
          match Val.from_expr new_le_x with 
            | Some sv -> put subst x sv; new_le_x
            | None -> raise (Failure "DEATH. subst_in_expr"))) in  

    let f_before (le : Expr.t) = 
      match (le : Expr.t) with 
        | LVar x    -> find_in_subst x le (fun () -> Expr.LVar (fresh_lvar ())), false 
        | ALoc x    -> find_in_subst x le (fun () -> Expr.ALoc (fresh_aloc ())), false
        | PVar x    -> find_in_subst x le (fun () ->
            let lvar = fresh_lvar () in
            L.log L.Verboser (lazy (Printf.sprintf "General: Subst in lexpr: PVar %s not in subst, generating fresh: %s" x lvar)); 
            Expr.LVar lvar), false 
        | _            -> le, true in 
      Expr.map f_before None le   

  (** 
    Optional substitution inside an expression 

    @param subst Target substitution
    @param le Target expression
    @return Expression resulting from the substitution. No fresh locations are created.
  *)
  let subst_in_expr_opt (subst : t) (le : Expr.t) : Expr.t option = 

    let f_before (le : Expr.t) =
      match (le : Expr.t) with 
        | LVar x | ALoc x | PVar x -> Option.map Val.to_expr (get subst x), false 
        | _         -> Some le, true in
    Expr.map_opt f_before None le

  (** 
    Conversion to a symbolic substitution

    @params subst Target substitution
    @return List of bindings of the form (variable, logical expression)
  *)
  let to_ssubst (subst : t) : (Var.t * Expr.t) list = 
    List.map (fun (x, v_x) -> x, Val.to_expr v_x) (to_list subst)


  let compatible (subst : t) (new_subst : t) : bool = 
    Hashtbl.fold (fun x v ac ->
      if (not ac) then false else (
        if (Hashtbl.mem new_subst x) then (
          v = (Hashtbl.find new_subst x)
        ) else true 
      ) 
    ) subst true

  let is_empty (subst : t) : bool = 
    Hashtbl.length subst = 0

end 