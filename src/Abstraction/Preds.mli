
module type M = 
  sig 

    (* value type *)
    type vt

    (* substitution type for the value type *)
    type st  

    (* preds *)
    type t 
    
    type abs_t = string * (vt list)
    
    val length : t -> int 

    val init : abs_t list -> t 

    val to_list : t -> abs_t list

    val copy : t -> t 

    val is_empty : t -> bool 

    val extend : t -> abs_t -> unit 

    val remove : t -> abs_t -> bool 

    val remove_by_name : t -> string -> abs_t option

    val find_pabs_by_name : t -> string -> abs_t list 
    
    val find_index : t -> abs_t -> int option 

    val iteri : (int -> abs_t -> unit) -> t -> unit 
    
    val get_index : t -> int -> abs_t 

    val remove_index : t -> int ->  unit 

    val set_index : t -> int -> abs_t -> unit

    val str : t -> string

    val string_of_pabs : abs_t -> string 
    
    val get_pred : bool -> t -> string -> vt list -> int list -> (vt -> vt -> bool) -> abs_t option 

    val find : bool -> t -> (abs_t -> bool) -> abs_t option

    val find_all : ?keep:bool -> (abs_t -> bool) -> t -> abs_t list  

    val substitution : st -> t -> t 

    val substitution_in_place : st -> t -> unit 

    (** Turns a predicate set into a list of assertions *)
    val to_assertions : t -> Asrt.t list 
    
    val index_of : t -> (abs_t -> bool) -> int option 

    val lvars : t -> CCommon.SS.t 

  end 