type t

val str : string -> t -> CVal.M.t -> string

val init : unit -> t

val get    : t -> string -> CVal.M.t option
val set    : t -> string -> CVal.M.t -> unit
val remove : t -> string -> unit

val properties : t -> string list