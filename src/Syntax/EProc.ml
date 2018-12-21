open CCommon 
open SCommon

(* JSIL procedures extended with string labels *)
type t = {
  name        : string;
  body        : ((Annot.t * string option * LabCmd.t) array);
  params      : string list;
  spec        : Spec.t option;
}

let string_of_lab_cmds (cmds : (Annot.t * string option * LabCmd.t) list) : string  =

  let max_lab_length = ref 0 in 
  List.iter (fun (_, lab, _) -> Option.may (fun lab -> if (String.length lab > !max_lab_length) then max_lab_length := String.length lab) lab) cmds;

  let max_space = repeat_string " " (4 + !max_lab_length + 2) in 

  let cmds_strs : string list =
    List.map
      (fun (annot, lab, cmd) ->
        let lab = 
          Option.map_default 
            (fun lab -> "    " ^ lab ^ ": " ^ (repeat_string " " (!max_lab_length - String.length lab)))
            max_space lab in 
        let cmd_str = LabCmd.str cmd in
        lab ^ cmd_str)
      cmds in
  String.concat ";\n" cmds_strs   

(*
  spec xpto (arg1, arg2, ...)
	  [[ ... ]]
		[[ ... ]]
		normal|error;
		...
	proc xpto (arg1, arg2, ...) {
		cmds
	} with {
		ret: x_ret, i_ret;
		err: x_err, i_err
	}
*)
let str (proc : t) : string =
  (* Optional specification block *)
  let spec_str   = Option.map_default (fun spec -> Spec.str spec) "" proc.spec in 
  let params_str = String.concat ", " proc.params in 
  let body_str   = string_of_lab_cmds (Array.to_list proc.body) in 

  Printf.sprintf "%sproc %s (%s) {\n%s\n};\n"
    spec_str proc.name params_str body_str 


let line_info (proc : t) : (string * int * int) list = 
  let pname = proc.name in 
  List.mapi
    (fun i (annot, _, _) ->
      let a : Annot.t = annot in 
      match Annot.get_line_offset annot with
        | None -> (pname, i, -1)  
        | Some n -> (pname, i, n))
    (Array.to_list proc.body) 

let to_proc (lproc : t) : Proc.t = 

  let no_of_cmds = Array.length lproc.body in

  (** Step 1 - Map labels to numbers, adding the label to the mapping hashtable
   * -----------------------------------------------------------------------------------
   *)
  let map_labels_to_numbers =
    let mapping = Hashtbl.create no_of_cmds in
    for i = 0 to (no_of_cmds - 1) do
      (match (lproc.body).(i) with
        | (_, Some str, _) -> Hashtbl.add mapping str i
        | _ -> ());
    done;
    mapping in

  let find_with_error hash lab = 
  (match Hashtbl.find_opt hash lab with 
  | Some result -> result 
  | None -> raise (Failure ("Could not find label: " ^ lab))) in 

 (** Step 2 - Replace labels with numbers in the procedure commands
   * -----------------------------------------------------------------------------------
   *)
  let convert_to_jsil mapping =
    let cmds_nolab = Array.map (fun x -> (match x with | (spec, _, cmd) -> (spec, cmd))) lproc.body in
    let cmds = Array.map (fun x ->
      match x with
      | spec, x -> 
        let x : Cmd.t = match (x : LabCmd.t) with
            | LBasic cmd -> Basic cmd
            | LGoto lab -> Goto (find_with_error mapping lab)
            | LGuardedGoto (e, lt, lf) -> GuardedGoto (e, find_with_error mapping lt, find_with_error mapping lf)
            | LCall (x, e, le, ol, subst) -> Call (x, e, le, (match ol with | None -> None | Some lab -> Some (find_with_error mapping lab)), subst)
            | LECall (x, e, le, ol) -> ECall (x, e, le, match ol with | None -> None | Some lab -> Some (find_with_error mapping lab))
            | LApply (x, le, ol) -> Apply (x, le, match ol with | None -> None | Some lab -> Some (find_with_error mapping lab))
            | LArguments var -> Arguments var
            | LPhiAssignment xargs -> PhiAssignment xargs 
            | LReturnNormal -> ReturnNormal
            | LReturnError  -> ReturnError 
            | LLogic lcmd   -> Logic lcmd  in
        (spec, x)
      ) cmds_nolab in
      cmds in 

 (** Step 3 - Return a new procedure, with the components now devoid of labels
   * -----------------------------------------------------------------------------------
   *)
  let mapping = map_labels_to_numbers in
  let b = convert_to_jsil mapping in

  let proc : Proc.t =
    {
      name = lproc.name;
      body = b;
      params = lproc.params;
      spec = lproc.spec;
    } in
  proc


let check_spec_pvars
    (procedures : ((string, t) Hashtbl.t)) : unit =

  (** Step 1 - Get the specs for each procedure, and add the return and error variables to the list of allowed variables
    * -----------------------------------------------------------------------------------
  *)
  (* Allow these variables when dealing with JS files as they are used by the internal functions *)
  let js_constants =
    (match !CCommon.syntax_js with
     | true -> JS2JSIL_Constants.js2jsil_spec_vars
     | false -> []) in

  let specs : Spec.t list = Hashtbl.fold (fun proc_name (proc : t) acc ->
      match proc.spec with
        | None -> acc
        | Some s -> {s with params = (s.params @ [ Flag.return_variable ] @ js_constants)} :: acc
    ) procedures []
  in

  (** Step 2 - Function to check for any assertion in the spec
    * -----------------------------------------------------------------------------------
  *)
  let check_spec_assertion_pvars
      (spec_name : string)
      (pre : bool) (* true for pre, false for post *)
      (spec_params : string list)
      (previously_normalised : bool)
      (assertion : Asrt.t) : unit =

    let msg_construct_type =
      (match pre with
       | true -> "precondition"
       | false -> "postcondition")
    in

    List.map (fun pvar ->
        let valid_pvar = List.mem pvar spec_params in
        (match valid_pvar || previously_normalised with
         | true -> ()
         | false -> raise (Failure (Printf.sprintf "Undefined variable %s in the %s of %s." pvar msg_construct_type spec_name)))
      )
      (SS.elements (Asrt.pvars assertion)); ()
  in

  (** Step 3 - Run this function on the pre and all the post's of every spec
    * -----------------------------------------------------------------------------------
  *)
  List.map (fun (spec : Spec.t) ->
      let spec_params = spec.params in
      List.map (fun (single_spec : Spec.st) ->
          check_spec_assertion_pvars spec.name true spec_params spec.normalised single_spec.pre;
          List.map (fun post ->
              check_spec_assertion_pvars spec.name false spec_params spec.normalised post;
            )
            single_spec.posts;
        )
        spec.sspecs
    )
    specs;
  ()


let check_proc_spec_correspondence
    (procedures : ((string, t) Hashtbl.t)) : unit =

  Hashtbl.iter (fun _ (proc : t) ->
      match proc.spec with
      | None -> ()
      | Some spec ->

        (** Check the arguments correspond
          * -----------------------------------------------------------------------------------
        *)
        (match (List.length proc.params) = (List.length spec.params) with
          | true -> ()
          | false -> raise (Failure (Printf.sprintf "The spec and procedure definitions for %s have different number of arguments." proc.name)));
        (match proc.params = spec.params with
          | true -> ()
          | false -> raise (Failure (Printf.sprintf "The spec and procedure definitions for %s have different arguments." proc.name)));
    ) procedures
