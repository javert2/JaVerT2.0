open SVal

(***************************************************************)
(** Logic Commmands                                           **)
(***************************************************************)

(** {b JSIL logic commands}. *)
type t =
	| If         of Expr.t * (t list) * (t list) (** If-then-else     *)
  | Branch     of Formula.t                    (** branching on a FO formual *)
	| Macro      of string * (Expr.t list)       (** Macro            *)
	| Assert     of Formula.t                    (** Assert           *)
  | Assume     of Formula.t                    (** Assume           *)
  | AssumeType of string * Type.t              (** Assume Type      *)
  | SpecVar    of string list                  (** Spec Var         *)
  | SL         of SLCmd.t                                                           

let rec map 
	(f_l  : (t -> t) option)
	(f_e  : (Expr.t -> Expr.t) option)
  (f_p  : (Formula.t -> Formula.t) option)
  (f_sl : (SLCmd.t -> SLCmd.t) option)
	(lcmd : t) : t =

  (* Functions to map over formulas, expressions, and sl-commands *)
  let f      = map f_l f_e f_p f_sl in
  let map_e  = Option.default (fun x -> x) f_e in
  let map_p  = Option.default (fun x -> x) f_p in
  let map_sl = Option.default (fun x -> x) f_sl in

	(* Apply the given function to the logical command *)
	let mapped_lcmd = Option.map_default (fun f -> f lcmd) lcmd f_l in  

	(* Map over the elements of the command *)
	match mapped_lcmd with
		| If (e, l1, l2)     -> If ((map_e e), (List.map f l1), (List.map f l2))
		| Macro (s, l)       -> Macro (s, (List.map map_e l))
    | Assume a           -> Assume (map_p a)
		| Assert a           -> Assert (map_p a)
    | AssumeType _       -> mapped_lcmd 
    | SpecVar _          -> mapped_lcmd 
    | SL sl_cmd          -> SL (map_sl sl_cmd)


let substitution (subst : SSubst.t) (partial : bool) (lcmd : t) : t =  
  map None (Some (SSubst.subst_in_expr subst partial)) 
    (Some (Formula.substitution subst partial)) (Some (SLCmd.substitution subst partial)) lcmd


let rec str (lcmd : t) : string =
  	match lcmd with  	
    | If (le, then_lcmds, else_lcmds) ->
    		let le_str = Expr.str le in
    		let then_lcmds_str = String.concat "; " (List.map str then_lcmds) in
    		let else_lcmds_str = String.concat "; " (List.map str else_lcmds) in
    		let ret = if ((List.length else_lcmds) = 0)
      			then "if (" ^ le_str ^ ") then { " ^ then_lcmds_str ^ " }"
      			else "if (" ^ le_str ^ ") then { " ^ then_lcmds_str ^ " } else { " ^  else_lcmds_str ^ " }" in
    		ret
  	
    | Branch fo -> "branch (" ^ (Formula.str fo) ^ ")"

    | Macro (name, lparams) ->
    		let lparams_str = String.concat ", " (List.map Expr.str lparams) in
    		name ^ "(" ^ lparams_str ^ ")"
  	
    | Assert a           -> "assert (" ^ (Formula.str a) ^ ")"
  	
    | Assume a           -> "assume (" ^ (Formula.str a) ^ ")"
    
    | AssumeType (x, t)  -> "assume_type (" ^ x ^ ", " ^ (Type.str t) ^ ")" 
    
    | SpecVar xs         -> "spec_var (" ^ (String.concat ", " xs) ^ ")"

    | SL sl_cmd          -> SLCmd.str sl_cmd 