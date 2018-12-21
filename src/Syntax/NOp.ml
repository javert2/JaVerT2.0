(* JSIL n-ary Operators *)

type t =
	(* Set management *)
	| SetUnion 
  | SetInter 
	[@@deriving show, compare]

let equal = [%compare.equal : t]

let str (x : t) = 
	match x with
	| SetUnion -> "-u-"
	| SetInter -> "-i-"