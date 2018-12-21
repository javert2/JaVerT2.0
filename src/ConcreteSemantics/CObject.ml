type t = (string, CVal.M.t) Hashtbl.t

let str (loc : string) (obj : t) (metadata : CVal.M.t) : string = 
  let prop_vals_str_lst = Hashtbl.fold (fun prop p_val lst -> (prop ^ ": " ^ (CVal.M.str p_val)) :: lst) obj [] in 
  loc ^ "|-> [ " ^ (String.concat ", " prop_vals_str_lst) ^ " ], " ^ (CVal.M.str metadata)

let init () : t =
  Hashtbl.create CCommon.medium_tbl_size

let get (obj : t) (prop : string) =
  Hashtbl.find_opt obj prop 

let set (obj : t) (prop : string) (value : CVal.M.t) =
  Hashtbl.replace obj prop value

let remove (obj : t) (prop : string) =
  Hashtbl.remove obj prop

let properties (obj : t) : string list =
  Var.Set.elements (Hashtbl.fold (fun prop _ props -> Var.Set.add prop props) obj Var.Set.empty)