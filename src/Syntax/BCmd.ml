open CCommon

(***************************************************************)
(***************************************************************)
(** JSIL Basic Commmands                                      **)
(***************************************************************)
(***************************************************************)

type t =
	| Skip                                                     (** Empty command *)
	| Assignment of string * Expr.t                            (** Assignment *)
	| New        of string * (Expr.t option) * (Expr.t option) (** Object creation *)
	| Lookup     of string * Expr.t * Expr.t                   (** Field lookup *)
	| Mutation   of Expr.t * Expr.t * Expr.t                   (** Field mutation *)
	| Delete     of Expr.t * Expr.t                            (** Field deletion *)
	| DeleteObj  of Expr.t                                     (** Object deletion *)
	| HasField   of string * Expr.t * Expr.t                   (** Field check *)
	| GetFields  of string * Expr.t                            (** All fields of an object *)
	| MetaData   of string * Expr.t                            (** Object metadata *)

let rec str (i : int option) (bcmd : t) : string =
  	let se = Expr.str in
  	let str_i = (match i with 
      		| None -> "" 
      		| Some i -> if !CCommon.line_numbers_on then (string_of_int i) ^ ". " else "") in
  	match bcmd with
  	(* skip *)
  	| Skip -> Printf.sprintf "%sskip" str_i
  	(* var := e *)
  	| Assignment (var, e) -> Printf.sprintf "%s%s := %s" str_i var (se e)
  	(* x := new() *)
  	| New (var, loc, metadata) -> 
      (match loc, metadata with 
      | None, None -> Printf.sprintf "%s%s := new()" str_i var
      | None, Some metadata -> Printf.sprintf "%s%s := new(%s)" str_i var (se metadata)
      | Some loc, Some metadata -> Printf.sprintf "%s%s := new(%s, %s)" str_i var (se loc) (se metadata)
      | _, _ -> raise (Failure "BCmd: Impossible: New with loc and no metadata."))
  	(* x := [e1, e2]	*)
  	| Lookup (var, e1, e2) -> Printf.sprintf "%s%s := [%s, %s]" str_i var (se e1) (se e2)
  	(* [e1, e2] := e3 *)
  	| Mutation (e1, e2, e3) -> 
      Printf.sprintf "%s[%s, %s] := %s" str_i (se e1) (se e2) (se e3)
  	(* delete(e1, e2) *)
  	| Delete (e1, e2) ->  Printf.sprintf "%sdelete (%s,%s)" str_i (se e1) (se e2)
  	(* x := deleteObj(e1) *)
  	| DeleteObj (e1) ->  Printf.sprintf "%sdeleteObject (%s)" str_i (se e1)
  	(* x := hasField(e1, e2) *)
  	| HasField (var, e1, e2) -> Printf.sprintf "%s%s := hasField(%s,%s)" str_i var (se e1) (se e2)
  	(* x := getFields (e1, e2) *)
  	| GetFields (var, e) -> Printf.sprintf "%s%s := getFields (%s)" str_i var (se e)
		(* x := metadata(e) *)
		| MetaData (var, e) -> Printf.sprintf "%s%s := metadata (%s)" str_i var (se e)

let vars (bcmd : t) : SS.t = 
  let ve = Expr.vars in 
  (match bcmd with
  | Skip -> SS.empty
  | Assignment (x, e) -> SS.add x (ve e)
  | New (x, oe1, oe2) -> SS.add x (SS.union (Option.map_default ve SS.empty oe1) (Option.map_default ve SS.empty oe2))
  | Lookup   (x, e1, e2) -> SS.add x (SS.union (ve e1) (ve e2))
  | Mutation (e1, e2, e3) -> SS.union (ve e1) (SS.union (ve e2) (ve e3))
  | Delete   (e1, e2) -> SS.union (ve e1) (ve e2)
  | DeleteObj e -> ve e 
  | HasField (x, e1, e2) -> SS.add x (SS.union (ve e1) (ve e2))
  | GetFields (x, e) 
  | MetaData  (x, e) -> SS.add x (ve e))