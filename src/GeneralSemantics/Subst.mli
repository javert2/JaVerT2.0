(**
    Interface for JSIL Substitutions.
    JSIL substitutions are mappings from JSIL Variables to JSIL Values.
    JSIL substitutions are mutable.
*)
module type M = 
  sig 

    (** Type of JSIL values *)
    type vt 

    (** Type of JSIL substitutions *)
    type t 
    
    (** Substitution constructor, with a list of bindings of the form (variable, value) *)
    val init : (Var.t * vt) list -> t 

    (** Is the substitution empty? *)
    val is_empty : t -> bool 

    (** Reset substitution *)
    val clear : t -> unit

    (** Domain of the substitution *)
    val domain : t -> (Var.t -> bool) option -> Var.Set.t 

    (** Range of the substitution *)
    val range : t -> vt list 

    (** Substitution lookup *)
    val get : t -> Var.t -> vt option

    (** Substitution incremental update *)
    val add : t -> Var.t -> vt -> unit 

    (** Substitution update *)
    val put : t -> Var.t -> vt -> unit 

    (** Substitution membership *)
    val mem : t -> Var.t -> bool 

    (** Substitution copy *)
    val copy : t -> t 

    (** Substitution extension with a list of bindings *)
    val extend : t -> (Var.t * vt) list -> unit 

    (** Substution merge into left *)
    val merge_left : t -> t -> unit 

    (** Compatible substitutions *)
    val compatible : t -> t -> bool 

    (** Substitution filter *)
    val filter : t -> (Var.t -> vt -> bool) -> t

    (** Substitution variable filter *)
    val projection : t -> Var.Set.t -> t

    (** Substitution iterator *)
    val iter : t -> (Var.t -> vt -> unit) -> unit

    (** Substitution fold *)
    val fold : t -> (Var.t -> vt -> 'a -> 'a) -> 'a -> 'a
    
    (** Printer *)
    val str : t -> string 

    val filter_in_place : t -> (Var.t -> vt -> vt option) -> unit 

    (** Convert substitution to list *)
    val to_list : t -> (Var.t * vt) list
    
    (** Substitution inside a logical expression *)
    val subst_in_expr : t -> bool -> Expr.t -> Expr.t 

    (** Optional substitution inside a logical expression *)
    val subst_in_expr_opt : t -> Expr.t -> Expr.t option 

    (** Convert to a symbolic substitution *)
    val to_ssubst : t -> (Var.t * Expr.t) list
end 