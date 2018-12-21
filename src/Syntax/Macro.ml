open CCommon
open SVal

(***************************************************************)
(** Macros                                                    **)
(***************************************************************)
type t = {
  name       : string;             (** Name of the macro *)
  params     : string list;        (** Actual parameters *)
  definition : LCmd.t list         (** Macro definition *)
}

type t_tbl = (string, t) Hashtbl.t

let init_tbl () : t_tbl = Hashtbl.create small_tbl_size 


let get (macros : t_tbl) (name : string) : t option = 
  Hashtbl.find_opt macros name 


let rec expand_macro (macro : t) (args : Expr.t list) : LCmd.t list =
  let params      = macro.params in
  let params_card = List.length params in 
  let args_card   = List.length args in 
  if (params_card <> args_card) then
    raise (Failure 
      (Printf.sprintf "Macro %s called with incorrect number of parameters: %d instead of %d." macro.name args_card params_card)); 
  let subst       = SSubst.init (List.combine params args) in 
  let lcmds       = macro.definition in 
  List.map (LCmd.substitution subst true) lcmds 


let str (macro : t) : string = 
  let lcmds_str = String.concat "\t\n" (List.map LCmd.str macro.definition) in 
  "macro " ^ macro.name ^ "(" ^ (String.concat ", " macro.params) ^ ")" ^ "\n" ^ lcmds_str 


let str_of_tbl (macros : t_tbl) : string = 
  let strs = 
    Hashtbl.fold 
      (fun _ macro strs -> (str macro) :: strs)
      macros [] in 
  String.concat "\n" strs 
