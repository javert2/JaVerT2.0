module M 
  (Val   : Val.M) 
  (Subst : Subst.M with type vt = Val.t and type t = Val.st) : 
    (Error.M with type vt = Val.t and type st = Subst.t) = struct   

type vt = Val.t 

type st = Subst.t 

type fix_t = 
  | MCell        of vt * vt 
  | MCellV       of vt * vt * vt
  | MMetadata    of vt 
  | MMetadataV   of vt * vt 
  | MDomain      of vt * vt 
  | MPF          of Formula.t
  | MType        of vt * Type.t 
  | MLCell       of vt * vt
  | MLCellV      of vt * vt * vt        
  | MLMetadata   of vt
  | MLMetadataV  of vt * vt  
type up_error = 
  | UPSpec      of string * Asrt.t list list
  | UPPred      of string * Asrt.t list list
  | UPLemma     of string * Asrt.t list list
  | UPAssert    of Asrt.t * Asrt.t list list
  | UPInvariant of Asrt.t * Asrt.t list list

(** Type of JSIL errors *)
type t = 
  | ESpec     of Val.t list * Formula.t * (fix_t list list)  (** Missing resource: values involved, failing constraint *)
  | EType     of Val.t * Type.t option * Type.t              (** Incorrect type *)
  | EResource of fix_t list                                  (** Absent resource *)
  | EProc     of Val.t                                       (** Incorrect procedure identifier *)
  | ELemma    of string                                      (** Undefined Lemma *)
  | EVar      of Var.t                                       (** Undefined Variable *)
  | EGeneral  of string                                      (** General error with a string description *)
  | EUP       of up_error                                    (** Unification plan error *)

exception ThrowError of t

let string_of_fix (fix : fix_t) : string = 
  match fix with 
    | MCell (loc, prop)      -> Printf.sprintf "MCELL(%s, %s, -)" (Val.str loc) (Val.str prop)
    | MCellV (loc, prop, v)  -> Printf.sprintf "MCELLV(%s, %s, %s)" (Val.str loc) (Val.str prop) (Val.str v)
    | MMetadata loc          -> Printf.sprintf "MMetadata(%s)" (Val.str loc)
    | MMetadataV (loc, v)    -> Printf.sprintf "MMetadata(%s, %s)" (Val.str loc) (Val.str v)
    | MDomain (loc, dom)     -> Printf.sprintf "MDomain(%s, %s)" (Val.str loc) (Val.str dom)
    | MPF f                  -> Printf.sprintf "MPF(%s)" (Formula.str f)
    | MType (v, t)           -> Printf.sprintf "MType (%s, %s)" (Val.str v) (Type.str t)
    | MLCell (loc, prop)     -> Printf.sprintf "MLCELL(%s, %s, -)" (Val.str loc) (Val.str prop)
    | MLCellV (loc, prop, v) -> Printf.sprintf "MLCELLV(%s, %s, %s)" (Val.str loc) (Val.str prop) (Val.str v)
    | MLMetadata loc         -> Printf.sprintf "MLMetadata(%s)" (Val.str loc) 
    | MLMetadataV (loc, v)   -> Printf.sprintf "MLMetadataV(%s, %s)" (Val.str loc) (Val.str v)

let str_of_up_error (uperr : up_error) : string = 
  match uperr with
  | UPSpec      (spec_name,  disconnected) -> Printf.sprintf "spec, %s, [ %s ]"  spec_name  (String.concat ", " (List.map (fun al -> Printf.sprintf "[%s]" (String.concat ", " (List.map Asrt.str al))) disconnected))
  | UPPred      (pred_name,  disconnected) -> Printf.sprintf "pred, %s, [ %s ]"  pred_name  (String.concat ", " (List.map (fun al -> Printf.sprintf "[%s]" (String.concat ", " (List.map Asrt.str al))) disconnected))
  | UPLemma     (lemma_name, disconnected) -> Printf.sprintf "lemma, %s, [ %s ]" lemma_name (String.concat ", " (List.map (fun al -> Printf.sprintf "[%s]" (String.concat ", " (List.map Asrt.str al))) disconnected))
  | UPAssert    (assertion,  disconnected) -> Printf.sprintf "asrt, %s, [ %s ]" (Asrt.str assertion) (String.concat ", " (List.map (fun al -> Printf.sprintf "[%s]" (String.concat ", " (List.map Asrt.str al))) disconnected))
  | UPInvariant (invariant,  disconnected) -> Printf.sprintf "inv, %s, [ %s ]" (Asrt.str invariant) (String.concat ", " (List.map (fun al -> Printf.sprintf "[%s]" (String.concat ", " (List.map Asrt.str al))) disconnected))

let str (err : t) : string = 
  match err with 
    | ESpec (vs, fc, fixes)  -> 
        let fixes_strs =
          List.mapi (fun i fixes -> 
            let fix_str = String.concat ", " (List.map string_of_fix fixes) in 
            Printf.sprintf "[Fix %d: %s]" i fix_str  
          ) fixes in 
        let fixes_str = String.concat ", " fixes_strs in 
        Printf.sprintf "MResource(%s; %s; %s)" 
          (String.concat ", " (List.map Val.str vs)) (Formula.str fc) fixes_str
    | EType (v, t1, t2)   -> Printf.sprintf "EType(%s, %s, %s)" (Val.str v) (Option.map_default Type.str "None" t1) (Type.str t2)
    | EResource fixes     -> Printf.sprintf "EResource(%s)" (String.concat ", " (List.map string_of_fix fixes))
    | EProc pid           -> Printf.sprintf "EProc(%s)" (Val.str pid) 
    | ELemma lname        -> Printf.sprintf "ELemma(%s)" lname
    | EVar v              -> Printf.sprintf "EVar(%s)" (Var.str v)
    | EGeneral msg        -> Printf.sprintf "EGeneral(%s)" msg
    | EUP uperr           -> Printf.sprintf "EUP(%s)" (str_of_up_error uperr)

let can_fix (errs : t list) : bool = 
	List.for_all (fun e -> match e with | ESpec _ -> true | _ -> false) errs


let get_recovery_vals (errs : t list) : Val.t list = 
  let aux err = 
    match err with 
      | ESpec (vs, _, _) -> vs 
      | EType _
      | EResource _ 
      | EVar  _
      | EProc _ 
      | EGeneral _ -> 
        let msg = Printf.sprintf "DEATH. get_recovery_vals with %s" (str err) in 
          raise (Failure msg) in 
  List.sort_uniq Pervasives.compare (List.concat (List.map Val.base_elements (List.concat (List.map aux errs))))

let get_failing_constraint (err : t) : Formula.t = 
  match err with 
    | ESpec (vs, fc, _) -> fc 
    | _ -> True 

let sanitise_fix (fix : fix_t) = (match fix with 
  | MPF f -> 
    let f = Simplifications.reduce_formula f in 
    (match f with 
      (* Fishy, are these really the same? *)
      | True | False -> None
      | f -> Some (MPF f) 
    )
  | _ -> Some fix
) 

let sanitise (errs : t list) : t list = List.map 
  (fun err -> 
    (match err with 
    | ESpec (vs, f, fixes) -> 
      let fixes = List.map (fun fixes -> 
        let fixes = List.map sanitise_fix fixes in 
        List.map Option.get (List.filter (fun x -> x <> None) fixes)) fixes in 
      ESpec (vs, f, fixes)
    | EResource fixes -> 
      let fixes = List.map sanitise_fix fixes in 
      let fixes = List.map Option.get (List.filter (fun x -> x <> None) fixes) in 
        EResource fixes
    | _ -> err
    )
  ) errs 

end 