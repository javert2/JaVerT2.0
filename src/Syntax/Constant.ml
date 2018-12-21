(** 
	JSIL Constants 
*)

type t =
	| Min_float (** The smallest positive value *)
	| Max_float (** The largest positive finite value *)
	| Random    (** A random number between 0 and 1 *)
	| E         (** {i e}, the base of natural logarithms *)
	| Ln10      (** Natural logarithm of 10 *)
	| Ln2       (** Natural logarithm of 2 *)
	| Log2e     (** Base-2 logarithm of {i e} *)
	| Log10e    (** Base-10 logarithm of {i e} *)
	| Pi        (** The number pi *)
	| Sqrt1_2   (** The square root of 1/2 *)
	| Sqrt2     (** The square root of 2 *)
	| UTCTime   (** Current UTC time *)
	| LocalTime (** Current local time *)
	[@@deriving show, compare]

let equal = [%compare.equal : t]

(** Print *)
let str (x : t) =
  match x with
  | Min_float -> "$$min_value"
  | Max_float -> "$$max_value"
  | Random    -> "$$random"
  | E         -> "$$e"
  | Ln10      -> "$$ln10"
  | Ln2       -> "$$ln2"
  | Log2e     -> "$$log2e"
  | Log10e    -> "$$log10e"
  | Pi        -> "$$pi"
  | Sqrt1_2   -> "$$sqrt1_2"
  | Sqrt2     -> "$$sqrt2"
  | UTCTime   -> "$$utctime"
  | LocalTime -> "$$localtime"
