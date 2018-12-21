open JS2JSIL_Constants

(** Tables *)
module SS           = Set.Make(String)
let small_tbl_size  = 31
let medium_tbl_size = 101


let main_fid                      = "main"
let pi_pred_name                  = "Pi"
let object_class                  = "Object"
let syntax_error_pred_name        = "SyntaxError"
let type_error_pred_name          = "TypeError"
let initial_heap_pre_pred_name    = "initialHeapPre"
let initial_heap_post_pred_name   = "initialHeapPost"
let function_object_pred_name     = "function_object"
let standard_object_pred_name     = "standardObject"
let this_logic_var_name           = "#this"

let funobj_pred_name              = "JSFunctionObject"

let js_obj_internal_fields        = [ "@proto"; "@class"; "@extensible" ]


(** Fresh Names *)

let fid_to_lvar fid = "#fid_" ^ fid

let fid_to_lvar_fresh =
	let fids_tbl = Hashtbl.create 31 in
	fun fid ->
		let fid_count =
			try
				Hashtbl.find fids_tbl fid
			with Not_found -> 0 in
		Hashtbl.replace fids_tbl fid (fid_count + 1);
		"#fid_" ^ (string_of_int fid_count) ^ "_" ^ fid

let counter = ref 0
let pvar_counter = ref 0

let fresh_lvar () =
	let v = "_lvar_" ^ (string_of_int !counter) in
   	counter := !counter + 1;
   	v

let fresh_pvar () =
	let v = "pvar_" ^ (string_of_int !pvar_counter) in
   	pvar_counter := !pvar_counter + 1;
   	v

let vislist_2_les (vis_list : string list) (i : int) : Expr.t list =
	Array.to_list (
		Array.init i
			(fun j -> if (j = 0) then Expr.Lit (Loc JS2JSIL_Constants.locGlobName) else Expr.LVar (fresh_lvar ())))


(** Lists *)

let find_in_list (lst : string list) (x : string) =
	let rec loop lst i =
		match lst with
		| []        -> raise (Failure "DEATH: string not found in list")
		| y :: rest -> if (x = y) then i else loop rest (i+1) in
	loop lst 0

let list_overlap (lst_1 : string list) (lst_2 : string list) =
	print_endline (Printf.sprintf "List overlap:\n\t%s\n\t%s"
		(String.concat ", " lst_1) (String.concat ", " lst_2)
	);
	let rec loop lst_1 lst_2 i =
		match lst_1, lst_2 with
		| [], _
		| _, [] -> i
		| x1 :: rest_1, x2 :: rest_2 ->
			if (x1 = x2) then loop rest_1 rest_2 (i+1) else i in
	loop lst_1 lst_2 0


(** Scope Clarification *)

let psi (cc_tbl : cc_tbl_type) (vis_tbl : vis_tbl_type) (fid : string) (x : string) =
	let var_to_fid_tbl = get_scope_table cc_tbl fid in
	try (
		let fid' = Hashtbl.find var_to_fid_tbl x in
		let vis_list = get_vis_list vis_tbl fid in
		let i        = try find_in_list vis_list fid'
			with Not_found -> raise (Failure "DEATH. psi: find_in_list") in
		Some i )
	with Not_found -> None


let o_psi (vis_tbl : vis_tbl_type) (fid1 : string) (fid2 : string) =
	let vis_list_1 = try get_vis_list vis_tbl fid1
		with Not_found -> raise (Failure "DEATH. o_psi: get_vis_list") in
	let vis_list_2 = try get_vis_list vis_tbl fid2
		with Not_found -> raise (Failure "DEATH. o_psi: get_vis_list") in
	let i_overlap = list_overlap vis_list_1 vis_list_2 in
	i_overlap
