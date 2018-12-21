
module type M = 
  sig 
  
  type vt 

  type st 

  type fix_t = 
  | MCell        of vt * vt 
  | MCellV       of vt * vt * vt
  | MMetadata    of vt 
  | MMetadataV   of vt * vt 
  | MDomain      of vt * vt 
  | MPF          of Formula.t
  | MType        of vt * Type.t 
  | MLCell       of vt * vt
  | MLCellV      of vt * vt * vt        
  | MLMetadata   of vt
  | MLMetadataV  of vt * vt  

  type up_error = 
    | UPSpec      of string * Asrt.t list list
    | UPPred      of string * Asrt.t list list
    | UPLemma     of string * Asrt.t list list
    | UPAssert    of Asrt.t * Asrt.t list list
    | UPInvariant of Asrt.t * Asrt.t list list

  (** Type of JSIL errors *)
  type t = 
    | ESpec     of vt list * Formula.t * (fix_t list list)  (** Missing resource: values involved, failing constraint *)
    | EType     of vt * Type.t option * Type.t              (** Incorrect type *)
    | EResource of fix_t list                               (** Absent resource *)
    | EProc     of vt                                       (** Incorrect/undefined procedure identifier *)
    | ELemma    of string                                   (** Undefined Lemma *)
    | EVar      of Var.t                                    (** Undefined Variable *)
    | EGeneral  of string                                   (** General error with a string description *)
    | EUP       of up_error                                    (** Unification plan error *)

  exception ThrowError of t

  val str : t -> string
  
  val can_fix : t list -> bool 

  val get_recovery_vals : t list -> vt list

  val get_failing_constraint : t -> Formula.t 

  val string_of_fix : fix_t -> string 
 
  val sanitise : t list -> t list

end 