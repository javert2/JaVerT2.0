open CCommon 
open SVal

(** {b JSIL logic predicate}. *)
type t = {
	name        : string;                                            (** Name of the predicate  *)
	num_params  : int;                                               (** Number of parameters   *)
	params      : (string * Type.t option) list;                     (** Actual parameters      *)
	ins         : int list;                                          (** Ins                    *)
	definitions : (((string * (string list)) option) * Asrt.t) list; (** Predicate definitions  *)
  pure        : bool;                                              (** Is the predicate pure  *)
	normalised  : bool;                                              (** If the predicate has been previously normalised *)
}


(** Creates/populates a Hashtbl from the predicate list pred_defs *)
let init (preds : t list) : (string, t) Hashtbl.t = 
  let pred_def_tbl = Hashtbl.create small_tbl_size in
  List.iter
    (fun pred_def -> Hashtbl.add pred_def_tbl pred_def.name pred_def)
    preds;
  pred_def_tbl


let ins_and_outs (pred : t) : (SI.t * SI.t) = 
  let ins_set  = SI.of_list pred.ins in  
  let _, outs    =
    List.fold_left 
     (fun (i, lst) (x, _) -> if (SI.mem i ins_set) then i+1, lst else i+1, i :: lst) 
     (0, []) pred.params in
  let outs_set = SI.of_list outs in 
  ins_set, outs_set 

let in_params (pred : t) : (string list) = 
  let ins_set = SI.of_list pred.ins in  
  let _, ins  = 
    List.fold_left 
      (fun (i, ins) (x, _) -> if (SI.mem i ins_set) then i+1, x :: ins else i+1, ins)
      (0, []) pred.params in 
  List.rev ins 

let in_args (pred : t) (args : 'a list) : ('a list) = 
  let ins_set = SI.of_list pred.ins in  
  let _, in_args = 
    List.fold_left 
      (fun (i, ins) x -> if (SI.mem i ins_set) then i+1, x :: ins else i+1, ins)
      (0, []) args in 
  List.rev in_args

let out_params (pred : t) : (string list) = 
  let ins_set = SI.of_list pred.ins in  
  let _, outs = 
    List.fold_left 
      (fun (i, outs) (x, _) -> if (SI.mem i ins_set) then i+1, outs else i+1, x :: outs)
      (0, []) pred.params in
  List.rev outs 


let out_args (pred : t) (args : 'a list) : ('a list) = 
  let ins_set = SI.of_list pred.ins in  
  let _, out_args = 
    List.fold_left 
      (fun (i, outs) x -> if (SI.mem i ins_set) then i+1, outs else i+1, x :: outs)
      (0, []) args in 
  List.rev out_args


(** JSIL logic predicates *) 
let rec str (pred : t) : string =
  let exist_ins = List.length pred.ins <> List.length pred.params in
  
  let slp = fun i (e, ot) -> 
    let is_in = if (exist_ins && List.mem i pred.ins) then "+" else "" in
        is_in ^ e ^ (Option.map_default (fun t -> " : " ^ Type.str t) "" ot) in
  
  let header = Printf.sprintf "pred %s (%s) :\n\t" pred.name (String.concat ", " (List.mapi slp pred.params)) in 
  
  let defs_strs = 
    List.map 
      (fun (id_existentials, assertion) -> 
          let id_str = 
            Option.map_default 
              (fun (id, existentials) ->
                match existentials with 
                  | [] ->  Printf.sprintf "[%s] " id 
                  | _  -> Printf.sprintf "[%s: %s] " id (String.concat ", " existentials)) 
            "" id_existentials in 
          id_str ^ Asrt.str assertion
      ) pred.definitions in 

  let defs_str = String.concat ",\n\t" defs_strs  in
      header ^ defs_str ^ ";\n" 


let check_pvars
    (predicates : (string, t) Hashtbl.t) : unit =

  let check_pred_pvars
    (pred_name : string)
    (predicate : t) : unit =

    (** Step 1 - Extract all the program variables used in the definition
      * -----------------------------------------------------------------------------------
    *)
    let all_pred_pvars : string list = List.concat (List.map (fun (_, ass) -> SS.elements (Asrt.pvars ass)) predicate.definitions) in

    (** Step 2 - Check all predicates
      * -----------------------------------------------------------------------------------
    *)
    let string_of_params = List.map (fun (pvar, _) -> pvar) predicate.params in
    List.map (fun (pvar : string) ->
        let valid_pvar = List.mem pvar string_of_params in
        (match valid_pvar || predicate.normalised with
        | true -> ()
        | false -> raise (Failure (Printf.sprintf "Undefined variable %s in the definition of predicate %s." pvar pred_name)))
      ) all_pred_pvars;
    ()

  in
  Hashtbl.iter check_pred_pvars predicates


(**  *)
let detect_trivia_and_nonsense (pred : t) : t =
  let new_defs = 
    List.map
      (fun (oc, x) -> oc, (Simplifications.reduce_assertion x)) 
      pred.definitions in
  let new_defs = List.filter (fun (oc, x) -> not (x = Asrt.Pure False)) new_defs in
  { pred with definitions = new_defs }


(** 
   JSIL Predicates can have non-pvar parameters - to say that a given parameter
   always has a certain value...
  *)
let explicit_param_types 
    (preds : (string, t) Hashtbl.t) 
    (pred : t) : t =
  
  let pt_asrt (a : Asrt.t) : Asrt.t = 
    let f_a_after a : Asrt.t = 
      match (a : Asrt.t) with 
        | Pred (name, les) -> 
          let pred     = try Hashtbl.find preds name with _ -> raise (Failure ("DEATH. parameter_types: predicate " ^ name ^ " does not exist.")) in 
            let ac_types = 
              List.fold_left (fun ac_types ((x, t_x), le) -> 
                match t_x with 
                | None     -> ac_types  
                | Some t_x -> (le, t_x) :: ac_types) [] (List.combine pred.params les) in 
            Star (Types(ac_types), a) 
        | _ -> a in   
    Asrt.map None (Some f_a_after) None None a in 

  let new_asrts =
    List.fold_right
      (fun (x, t_x) new_asrts ->
        match t_x with
          | None -> new_asrts
          | Some t_x -> Asrt.Types [ PVar x, t_x ] :: new_asrts)
      pred.params [] in
  let new_defs = List.map (fun (oid, a) -> (oid, Asrt.star (a :: new_asrts))) pred.definitions in
  let new_defs = List.map (fun (oid, a) -> oid, (pt_asrt a)) new_defs in 
    { 
      name         = pred.name;
      num_params   = pred.num_params;
      params       = pred.params;
      ins          = pred.ins;
      definitions  = new_defs;
      pure         = pred.pure;
      normalised   = pred.normalised 
    }



(* 
   Joining predicate definitions together
*)
let join (pred1 : t) (pred2 : t) : t =
  if pred1.name <> pred2.name || pred1.num_params <> pred2.num_params
    then (
      let msg = Printf.sprintf "Incompatible predicate definitions for: %s\n\tName:%s\tName:%s\n\tParams:%d\tParams:%d" pred1.name pred1.name pred2.name pred1.num_params pred2.num_params in
      L.fail msg
    ) else (
      let p1_params, _ = List.split pred1.params in
      let p2_params, _ = List.split pred2.params in
      let subst = SSubst.init (List.combine p2_params (List.map (fun var -> Expr.PVar var) p1_params)) in
      let defs  = 
        pred1.definitions @ (List.map (fun (oid, a) -> oid, (Asrt.substitution subst true a)) pred2.definitions) in
      { pred1 with definitions = defs }
    )

let combine_ins_outs (pred : t) (ins : 'a list) (outs : 'a list) : 'a list = 
  let in_indexes = SI.of_list pred.ins in 
  let max_index  = List.length pred.params in 

  let rec loop ins outs all cur_index = 
    if (cur_index = max_index) then all else (
      if (SI.mem cur_index in_indexes) then (
        match ins with 
        | [ ] -> raise (Failure "DEATH. combine_ins_outs")
        | hd :: tl -> loop tl outs (hd :: all) (cur_index + 1)  
      ) else (
        match outs with 
        | [] -> raise (Failure "DEATH. combine_ins_outs")
        | hd :: tl -> loop ins tl (hd :: all) (cur_index + 1)
      )
    ) in 

  List.rev (loop ins outs [] 0)

let empty_pred_tbl () = Hashtbl.create CCommon.small_tbl_size

let get_pred 
    (pred_defs : (string, t) Hashtbl.t) 
    (name : string) : t =
  try Hashtbl.find pred_defs name 
    with _ -> raise (Failure "DEATH. PRED NOT FOUND!")

 