(** {b Return flags for JSIL specifications}. *)
type t =
	| Normal (** Normal return *)
	| Error  (** Error return *)

(** JSIL spec return flag *)
let str (flag : t) : string =
  match flag with
  | Normal -> "normal"
  | Error -> "error"

let compare = Pervasives.compare

module MyFlag =
  struct
    type nonrec t = t
    let compare = Pervasives.compare
  end

module Set = Set.Make(MyFlag)

let return_variable = "ret"