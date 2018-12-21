open CCommon 
open SCommon

(** {b JSIL procedures}. *)
type t = {
	name        : string;                  (** Name *)
	body        : (Annot.t * Cmd.t) array; (** List of commands *)
	params      : string list;             (** Parameters *)
	spec        : Spec.t option;           (** Specification *)
}

let get_params (proc : t) : string list = proc.params (* shorthand *)

(* Retrieves the given i'th command of the given procedure *)
let get_cmd (proc : t) (i : int) : Annot.t * Cmd.t =
	proc.body.(i)
     
let str (proc : t) : string =

let string_of_cmds 
    (tabs : int) (cmds : (Annot.t * Cmd.t) array) : string  =
  let str_tabs = repeat_string "\t" tabs in
  let cmds_strs =
    List.mapi 
      (fun i (annot, cmd) -> Cmd.str str_tabs i cmd)
      (Array.to_list cmds) in
  String.concat "\n" cmds_strs in

  (* Optional specification block *)
  let spec_str   = Option.map_default (fun spec -> Spec.str spec) "" proc.spec in 
  let params_str = String.concat ", " proc.params in 
  let body_str   = string_of_cmds 2 proc.body in 

  Printf.sprintf "%sproc %s (%s) {\n%s\n};\n"
    spec_str proc.name params_str body_str  


let line_info (proc : t) : (string * int * int) list = 
  let pname = proc.name in 
  List.mapi
    (fun i (annot, _) ->
      let a : Annot.t = annot in 
      match Annot.get_line_offset annot with
        | None -> (pname, i, -1)  
        | Some n -> (pname, i, n))
    (Array.to_list proc.body) 


let get_prog_vars (proc : t) : string list =
  let var_table = Hashtbl.create 1021 in
  let cmds = proc.body in
  let number_of_cmds = Array.length cmds in

  (** Step 1 - Process each command in the procedure individually,
   *  carrying along the variables found so far
   * -----------------------------------------------------------------------------------
   *)
  let rec loop
      (u : int)
      (vars : string list) : string list =
    if (u >= number_of_cmds)
    then vars
    else

      (** Step 2 - Process the command at the current index
       * -----------------------------------------------------------------------------------
       *)
      let spec, cmd = cmds.(u) in
      (match cmd with

       (** Step 3 - Pattern match on the command type to extract the variable
        * -----------------------------------------------------------------------------------
        *)
       | Basic (Assignment (var, _))
       | Basic (Lookup (var, _, _))
       | Basic (New (var, _, _))
       | Basic (HasField (var, _, _))
       | Basic (GetFields (var, _))
       | Basic (MetaData (var, _))
       | Call  (var, _, _, _, _) 
       | ECall (var, _, _, _) 
       | Apply (var, _, _) 
       | Arguments var when (not (Hashtbl.mem var_table var)) ->
          Hashtbl.add var_table var true;
          loop (u+1) (var :: vars)

       (* TODO: Phi *)

       | _ -> loop u vars) in

  (** Step 0 - Iterate over each index associated with a command
   * -----------------------------------------------------------------------------------
  *)
  loop 0 []
