open SVal

(** 
  Interface for JSIL Stores. 
  JSIL stores are mappings from JSIL variables to JSIL values.
  JSIL stores are mutable.
*)
module type M = 
  sig

    (** Type of JSIL values *)
    type vt

    (** Type of JSIL stores *)
    type t

    (** Return the set of bindings in a given store *)
    val bindings : t -> (Var.t * vt) list

    (** Store copy *)
    val copy : t -> t

    (** Store domain *)
    val domain : t -> Var.Set.t

    (** Store filtering *)
    val filter : t -> (Var.t -> vt -> vt option) -> unit

    (** Store fold *)
    val fold : t -> (Var.t -> vt -> 'a -> 'a) -> 'a -> 'a

    (** Return value of a given variable, if possible *)
    val get : t -> Var.t -> vt option

    (** Return value of a given variable or throw *)    
    val get_unsafe : t -> Var.t -> vt

    (** Store constructor, with a list of bindings of the form (variable, value) *)
    val init : (Var.t * vt) list -> t

    (** Store iterator *)
    val iter : t -> (Var.t -> vt -> unit) -> unit

    (** Store membership *)
    val mem : t -> Var.t -> bool

    (** Partition store domain *)
    val partition : t -> (vt -> bool) -> Var.Set.t * Var.Set.t
    
    (** Store projection (returns new store) *)
    val projection : t -> Var.t list -> t

    (** Update value of variable in store *)
    val put : t -> Var.t -> vt -> unit

    (** Remove value of variable in store *)
    val remove : t -> Var.t -> unit

    (** Store printer *)
    val str : t -> string
    
    (** Converts the store into an ssubst *)
    val to_ssubst : t -> SSubst.t 

    (** Symbolic indices *)
    val symbolics : t -> Var.Set.t

    (** Logical variables *)
    val lvars : t -> Var.Set.t

  end