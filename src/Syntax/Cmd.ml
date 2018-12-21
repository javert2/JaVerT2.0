open CCommon

(**************************************************************)
(**************************************************************)
(** JSIL Commmands                                           **)
(**************************************************************)
(**************************************************************)

type t =
	| Basic          of BCmd.t                                     (** JSIL basic commands *)
  | Logic          of LCmd.t                                     (** JSIL Logic commands *)
	| Goto           of int                                        (** Unconditional goto *)
	| GuardedGoto    of Expr.t * int * int                         (** Conditional goto *)
	| Call           of string * Expr.t * Expr.t list * int option * (string * (string * Expr.t) list) option (** Procedure call *)
  | ECall          of string * Expr.t * Expr.t list * int option (** External Procedure call *)
	| Apply          of string * Expr.t * int option               (** Application-style procedure call *)
	| Arguments      of string                                     (** Arguments of the current function *)
	| PhiAssignment  of (string * Expr.t list) list                (** PHI assignment *)
  | ReturnNormal                                                 (** Normal return *)
  | ReturnError                                                  (** Error return *)

(** JSIL All Statements *)
let str (str_tabs : string) (i : int) (cmd : t) : string =	
	let se = Expr.str in
	let str_i = if !CCommon.line_numbers_on then (string_of_int i) ^ ". " else "" in
	match cmd with
	(* Basic command *)
	| Basic bcmd -> str_tabs ^ (BCmd.str (Some i) bcmd)
	(* goto j *)
	| Goto j -> str_tabs ^ Printf.sprintf "%sgoto %s" str_i (string_of_int j)
	(* goto [e] j k *)
	| GuardedGoto (e, j, k) ->
  		str_tabs ^ Printf.sprintf "%sgoto [%s] %s %s" str_i (se e) (string_of_int j) (string_of_int k)
	(* x := f(y1, ..., yn) with j *)
	| Call (var, name, args, error, subst) ->
  		str_tabs ^  Printf.sprintf "%s%s := %s(%s)%s" str_i var (se name) (String.concat ", " (List.map se args))
    			(
            (match error with
     			    | None -> ""
     			    | Some index -> (" with " ^ (string_of_int index))) ^
            (match subst with 
              | None -> ""
              | Some (lab, subst_lst) 
                  when List.length subst_lst > 0 -> 
                    Printf.sprintf " use_subst [%s - %s]" lab (String.concat ", " (List.map (fun (x, le) -> x ^ ": " ^ Expr.str le) subst_lst))
              | Some (lab, subst_lst) 
                  when List.length subst_lst = 0 -> 
                    Printf.sprintf " use_subst [%s]" lab
            )
          ) 

  | ECall (var, name, args, error) ->
      str_tabs ^ Printf.sprintf "%s%s := extern %s(%s) %s" str_i var (se name) (String.concat ", " (List.map se args))
          (match error with
          | None -> ""
          | Some index -> ("with " ^ (string_of_int index)))

	(* x := apply(y1, ..., yn) with j *)
	| Apply (var, args, error) ->
  		Printf.sprintf "%s%s := apply(%s)%s" str_tabs var (se args)
    		  (match error with
     			| None -> ""
     			| Some index -> (" with " ^ (string_of_int index)))
  (* x := args *)
  | Arguments var -> str_tabs ^ Printf.sprintf "%s%s := args" str_i var
	(* var := PHI(var_1, var_2, ..., var_n) *)
	| PhiAssignment lva ->
      let vars, var_args = List.split lva in
      let str_vars = String.concat ", " vars in 
      let str_var_args = String.concat "; " (List.map (fun arg -> String.concat ", " (List.map se arg)) var_args) in 
  		  Printf.sprintf "%s%s := PHI(%s)" str_tabs str_vars str_var_args
  | ReturnNormal -> str_tabs ^ Printf.sprintf "%sreturn" str_i
  | ReturnError  -> str_tabs ^ Printf.sprintf "%sthrow"  str_i
  | Logic lcmd   -> str_tabs ^ str_i ^ (LCmd.str lcmd)

let vars (cmd : t) : SS.t = 
  let ve = Expr.vars in 
  let vb = BCmd.vars in 
  (match cmd with 
  | Basic bcmd -> vb bcmd
  | Goto _ -> SS.empty
  | GuardedGoto (e, _, _) -> ve e
  | Call  (x, e, le, _, _) 
  | ECall (x, e, le, _) -> SS.add x (SS.union (ve e) (List.fold_left SS.union SS.empty (List.map ve le)))
  | Apply (x, e, _) -> SS.add x (ve e)
  | Arguments x -> SS.singleton x
  | PhiAssignment lele -> List.fold_left SS.union SS.empty (List.map (fun (_, le) -> List.fold_left SS.union SS.empty (List.map ve le)) lele)
  | ReturnNormal -> SS.empty
  | ReturnError -> SS.empty
  )