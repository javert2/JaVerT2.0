open Batteries

(** 
	JSIL Literals 
*)

type t =
	| Undefined               (** The literal [undefined] *)
	| Null                    (** The literal [null] *)
	| Empty                   (** The literal [empty] *)
	| Constant  of Constant.t (** JSIL constants ({!type:jsil_constant}) *)
	| Bool      of bool       (** JSIL booleans: [true] and [false] *)
	| Num       of float      (** JSIL floats - double-precision 64-bit IEEE 754 *)
	| String    of string     (** JSIL strings *)
	| Loc       of string     (** JSIL object locations *)
	| Type      of Type.t     (** JSIL types ({!type:Type.t}) *)
	| LList     of t list     (** Lists of JSIL literals *)

(** Print *)
let rec str (x : t) =
  	match x with
  	| Undefined  -> "undefined"
  	| Null       -> "null"
  	| Empty      -> "empty"
  	| Constant c -> Constant.str c
  	| Bool b     -> if b then "true" else "false" 
  	| Num n      -> CCommon.string_of_float n
  	| String x   -> let wrap = if !CCommon.escape_string then "\\" else "" in
		                  Printf.sprintf "%s\"%s%s\"" wrap x wrap
  	| Loc loc    -> loc
  	| Type t     -> Type.str t
  	| LList ll   -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map str ll))

(** Typing *)
let type_of (x : t) : Type.t =
	match x with
	| Undefined    -> UndefinedType
	| Null         -> NullType
	| Empty        -> EmptyType
	| Constant _   -> NumberType
	| Bool _       -> BooleanType
	| Num n        -> NumberType
	| String _     -> StringType
	| Loc _        -> ObjectType
	| Type _       -> TypeType
	| LList _      -> ListType


let evaluate_constant (c : Constant.t) : t =
	match c with
  | Min_float -> Num (5e-324)
	| Max_float -> Num (max_float)
	| Random -> Num (Random.float (1.0 -. epsilon_float))
	| E -> Num (exp 1.0)
	| Ln10 -> Num (log 10.0)
	| Ln2 -> Num (log 2.)
	| Log2e -> Num (log (exp 1.0) /. log (2.0))
	| Log10e -> Num (log10 (exp 1.0))
	| Pi -> Num (4.0 *. atan 1.0)
	| Sqrt1_2 -> Num (sqrt 0.5)
	| Sqrt2 -> Num (sqrt 2.0)
	| UTCTime ->
			let t = Unix.gettimeofday() in
			let (usec, _) = Float.modf t in
			let gct = Unix.gmtime t in
			let (gctime, _) = Unix.mktime gct in
			let gctime = gctime +. usec in
			let (_, tg) = Float.modf (gctime *. 1e+3) in
				Num (float_of_int (int_of_float tg))
	| LocalTime ->
		  let t = Unix.gettimeofday() in
			let (usec, _) = Float.modf t in
			let lct = Unix.localtime t in
			let (lctime, _) = Unix.mktime lct in
			let lctime = lctime +. usec in
			let (_, tl) = Float.modf (lctime *. 1e+3) in
				Num (float_of_int (int_of_float tl))

let rec fold 
	(f_ac    : t -> 'b -> 'b -> 'a list -> 'a) 
	(f_state : (t -> 'b -> 'b) option)
	(state   : 'b) 
	(lit     : t) : 'a =

	let new_state = (Option.default (fun le x -> x) f_state) lit state in
	let fold_lit  = fold f_ac f_state new_state in
	let f_ac      = f_ac lit new_state state in

  	match lit with
  	| Undefined  | Null   | Empty    | Constant _ 
  	| Bool _ | Num _  | String _ 
  	| Loc _  | Type _ -> f_ac [] 
  	| LList lits -> f_ac (List.map fold_lit lits)

let from_list lits = LList lits

let to_list lit = (match lit with
  | LList les -> Some les 
  | _ -> None
)

let rec base_elements (lit : t) : t list = 
  let f_ac lit _ _ ac =
    match lit with
    | LList les -> List.concat (List.map base_elements les @ ac)
    | _ -> lit :: (List.concat ac) in
  fold f_ac None None lit
