(** JSIL symbolic field-value list *)

open CCommon
open SCommon
open SVal

module L = Logging

type field_name  = Expr.t
type field_value = Expr.t

(* Definition *)
type t = field_value Expr.Map.t

let gsbsts = Expr.substitutables

(* Printing *)
let str (sfvl : t) : string = 
  let fv_strs = 
    Expr.Map.fold
      (fun field value ac ->
	    let field_str = Expr.str field in
		let value_str = Expr.str value in
		("(" ^ field_str ^ " :" ^ value_str ^ ")") :: ac) 
	  sfvl [] in 
  String.concat ", " fv_strs

		
(*************************************)
(** Field Value List Functions      **)
(*************************************)

(* Map functions to be reused *)

let add         = (fun fn fv -> Expr.Map.add fn fv)
let empty       = Expr.Map.empty
let field_names = (fun sfvl -> let result, _ = List.split (Expr.Map.bindings sfvl) in result)
let fold        = (fun f sfvl ac -> Expr.Map.fold f sfvl ac)
let get         = (fun fn sfvl -> Option.map (fun fv -> fv) (Expr.Map.find_opt fn sfvl))
let is_empty    = (fun sfvl -> sfvl = empty)
let iter        = (fun f sfvl -> Expr.Map.iter f sfvl)
let partition   = (fun f sfvl -> Expr.Map.partition f sfvl)
let remove      = Expr.Map.remove
(* WHAT IS THIS? *)
let union       = Expr.Map.union (fun k fvl fvr -> 
  L.log L.Verbose (lazy (Printf.sprintf "WARNING: SFVL.union: merging with field in both lists (%s: %s and %s), choosing left." (Expr.str k) (Expr.str fvl) (Expr.str fvr))); Some fvl)


let to_list fv_list = 
  fold (fun f v ac -> (f, v) :: ac) fv_list [] 

(** Gets a first key-value pair that satisfies a predicate *)
let get_first (f : field_name -> bool) (sfvl : t) : (field_name * field_value) option = 
	let found = ref false in
	Expr.Map.fold (fun fn fv ac -> 
		if !found then ac
		else 
			if (f fn) 
				then (found := true; Some (fn, fv))
				else ac) sfvl None

(** Returns the logical variables occuring in --sfvl-- *)
let lvars (sfvl : t) : SS.t =
	let gllv = Expr.lvars in
	Expr.Map.fold (fun e_field e_val ac -> SS.union ac (SS.union (gllv e_field) (gllv e_val))) sfvl SS.empty 

(** Returns the abstract locations occuring in --sfvl-- *)
let alocs (sfvl : t) : SS.t =
	Expr.Map.fold (fun e_field e_val ac -> SS.union ac (SS.union (Expr.alocs e_field) (Expr.alocs e_val))) sfvl SS.empty 

let assertions (loc : Expr.t) (sfvl : t) : Asrt.t list = 
	List.rev (Expr.Map.fold (fun field value (ac : Asrt.t list) -> (PointsTo (loc, field, value) :: ac)) sfvl [])

(* Substitution *)
let substitution 
		(subst   : SSubst.t) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = SSubst.subst_in_expr subst partial in 
	Expr.Map.fold (fun le_field le_val ac -> 
		let sf = f_subst le_field in
		let sv = f_subst le_val in 
			Expr.Map.add sf sv ac) fv_list Expr.Map.empty

(* Selective substitution *)
let selective_substitution 
		(subst   : SSubst.t) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = SSubst.subst_in_expr subst partial in 
	Expr.Map.fold (fun le_field le_val ac -> 			
		let sv = f_subst le_val in 
			Expr.Map.add le_field sv ac) fv_list Expr.Map.empty

(* Correctness of field-value lists *)
let is_well_formed (sfvl : t) : bool = true

let wf_assertions (sfvl : t) : (Formula.t list) = 
  let props  = field_names sfvl in 
  let props' = cross_product props props (fun x y -> (x, y)) in 
  let props' = List.filter (fun (x, y) -> x <> y) props' in 
  List.map (fun (x, y) : Formula.t -> Not (Eq (x, y))) props' 
