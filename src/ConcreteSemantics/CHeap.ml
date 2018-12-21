open CCommon
open CVal

type t = (string, (CObject.t * CVal.M.t)) Hashtbl.t

let str (heap : t) : string = 
  let objs_str_lst = Hashtbl.fold (fun loc (obj, metadata) lst -> (CObject.str loc obj metadata) :: lst) heap [] in 
  String.concat "\n" objs_str_lst

let init () : t = 
  Hashtbl.create medium_tbl_size

let get (heap : t) (loc : string) = 
  Hashtbl.find_opt heap loc

let set (heap : t) (loc : string) (obj_with_mv : CObject.t * CVal.M.t) = 
  Hashtbl.replace heap loc obj_with_mv

let remove (heap : t) (loc : string) = 
  Hashtbl.remove heap loc

let copy (heap : t) =
  Hashtbl.copy heap