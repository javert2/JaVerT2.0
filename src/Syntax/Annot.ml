open CCommon

(** {b JSIL annot}. *)
type t = {
	line_offset     : int option;     (** Better not to know what this is for *)
}

(**/**)
let init ?(line_offset=None) () = { line_offset; }

let get_line_offset annot = annot.line_offset

let line_info_to_str (line_info : (string * int * int) list) : string = 
  let strs = List.map (fun (pname, i, j) -> Printf.sprintf "(%s, %i, %i)" pname i j) line_info in 
  String.concat "\n" strs 

(* FIXME: The following function does not make sense at all, and is unused *)
(* let str (space : string) (annot : t) : unit = ()  *)
