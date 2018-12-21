(** Interface for JSIL Values *)
module type M = 
  sig

    (** Type of JSIL values *)
    type t

    (** Type of substitutions for JSIL values *)
    type st 

    (** Printer *)
    val str : t -> string 

    val full_str : t -> string 

    (** Convert a value to a literal, if possible *)
    val to_literal : t -> Literal.t option

    (** Convert a literal to a value, always possible *)
    val from_literal : Literal.t -> t

    (** Convert a value to a logical expression, always possible *)
    val to_expr : t -> Expr.t 

    (** Converts a logical expression to a value, if possible *)
    val from_expr : Expr.t -> t option

    (** Convert a list of values to a single value, always possible *)
    val from_list : t list -> t

    (** Convert a value to a list of values, if possible *)
    val to_list : t -> t list option

    (** Return the list of all literals, variables, and abstract locations of a given value *)
    val base_elements : t -> t list 

    (** Is the value concrete? *)
    val is_concrete : t -> bool
  end 