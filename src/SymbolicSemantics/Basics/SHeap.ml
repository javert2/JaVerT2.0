(** JSIL Symbolic Heap *)

open CCommon
open SCommon
open SVal

type s_object = (SFVL.t * (Expr.t option)) * Expr.t option

type t = {
    cfvl : (string, SFVL.t) Hashtbl.t;
    cdom : (string, Expr.t option) Hashtbl.t;
    cmet : (string, Expr.t option) Hashtbl.t;

    sfvl : (string, SFVL.t) Hashtbl.t;
    sdom : (string, Expr.t option) Hashtbl.t;
    smet : (string, Expr.t option) Hashtbl.t;

    cdmn : Var.Set.t ref;
    sdmn : Var.Set.t ref;
}

(* ************* *
 *  AUXILIARIES  *
 * ************* *)

let is_c = Expr.is_concrete

let merge (a : 't option) (b : 't option) (f : 't -> 't -> 't) : 't option = 
  (match a, b with 
  | a, None -> a
  | None, b -> b
  | Some a, Some b -> 
      Some (f a b))

let get_fvl (heap : t) (loc : string) : SFVL.t option = 
  let cfvl = Hashtbl.find_opt heap.cfvl loc in 
  let sfvl = Hashtbl.find_opt heap.sfvl loc in 
    merge cfvl sfvl SFVL.union

let get_dom (heap : t) (loc : string) : Expr.t option = 
  let cdom = Option.default None (Hashtbl.find_opt heap.cdom loc) in 
  let sdom = Option.default None (Hashtbl.find_opt heap.sdom loc) in 
    merge cdom sdom (fun _ _ -> raise (Failure "Domain in both the concrete and symbolic part of the heap."))

let get_met (heap : t) (loc : string) : Expr.t option = 
  let cmet = Option.default None (Hashtbl.find_opt heap.cmet loc) in 
  let smet = Option.default None (Hashtbl.find_opt heap.smet loc) in 
    merge cmet smet (fun _ _ -> raise (Failure "MetaData in both the concrete and symbolic part of the heap."))

let set_fvl (heap : t) (loc : string) (fvl : SFVL.t) : unit = 
  Hashtbl.remove heap.cfvl loc; Hashtbl.remove heap.sfvl loc;
  heap.cdmn := Var.Set.remove loc !(heap.cdmn); heap.sdmn := Var.Set.remove loc !(heap.sdmn);

  let cfvl, sfvl = SFVL.partition (fun prop value -> is_c value && is_c prop) fvl in 
    (match (cfvl = SFVL.empty), (sfvl = SFVL.empty) with
    | true,  true  -> Hashtbl.replace heap.cfvl loc SFVL.empty; Hashtbl.remove  heap.sfvl loc;      heap.cdmn := Var.Set.add loc !(heap.cdmn)
    | true,  false -> Hashtbl.remove  heap.cfvl loc;            Hashtbl.replace heap.sfvl loc sfvl; heap.cdmn := Var.Set.add loc !(heap.cdmn)
    | false, true  -> Hashtbl.replace heap.cfvl loc cfvl;       Hashtbl.remove  heap.sfvl loc;      heap.sdmn := Var.Set.add loc !(heap.sdmn)
    | false, false -> Hashtbl.replace heap.cfvl loc cfvl;       Hashtbl.replace heap.sfvl loc sfvl; heap.cdmn := Var.Set.add loc !(heap.cdmn); heap.sdmn := Var.Set.add loc !(heap.sdmn))

let set_dom (heap : t) (loc : string) (dom : Expr.t option) : unit = 
  Hashtbl.remove heap.cdom loc; Hashtbl.remove heap.sdom loc;
  let add, rem = (match dom with | Some x when (not (is_c x)) -> heap.sdom, heap.cdom | _ -> heap.cdom, heap.sdom) in 
    Hashtbl.replace add loc dom; Hashtbl.remove rem loc 

let set_met (heap : t) (loc : string) (met : Expr.t option) : unit = 
  Hashtbl.remove heap.cmet loc; Hashtbl.remove heap.smet loc;
  let add, rem = (match met with | Some x when (not (is_c x)) -> heap.smet, heap.cmet | _ -> heap.cmet, heap.smet) in 
    Hashtbl.replace add loc met; Hashtbl.remove rem loc

(*************************************)
(** Symbolic heap functions         **)
(*************************************)

(** Returns an empty symbolic heap *)
let init () : t =
  { 
    cfvl = Hashtbl.create big_tbl_size; sfvl = Hashtbl.create big_tbl_size;
    cdom = Hashtbl.create big_tbl_size; sdom = Hashtbl.create big_tbl_size;
    cmet = Hashtbl.create big_tbl_size; smet = Hashtbl.create big_tbl_size;
    cdmn = ref SS.empty; sdmn = ref SS.empty
  }

(** Symbolic heap read heap(loc) *)
let get (heap : t) (loc : string) : s_object option =
  let sfvl = get_fvl heap loc in 
    Option.map (fun sfvl -> ((sfvl, get_dom heap loc), get_met heap loc)) (get_fvl heap loc)

(** Symbolic heap read heap(loc) with the normal new obj default *)
let get_with_default (heap : t) (loc : string) : s_object =
  Option.default ((SFVL.empty, None), None) (get heap loc) 

(** Symbolic heap set heap(loc) is assigned to fv_list *)
let set (heap : t) (loc : string) (fv_list : SFVL.t) (dom : Expr.t option) (metadata : Expr.t option) : unit =
  set_fvl heap loc fv_list; set_dom heap loc dom; set_met heap loc metadata

(** Symbolic heap put heap (loc, (perm, field)) is assigned to value *) 
let set_fv_pair (heap : t) (loc : string) (field : Expr.t) (value : Expr.t) : unit =
  heap.cdmn := Var.Set.remove loc !(heap.cdmn); heap.sdmn := Var.Set.remove loc !(heap.sdmn);
  let add, sadd, rem = if (is_c field && is_c value) then heap.cfvl, heap.cdmn, heap.sfvl else heap.sfvl, heap.sdmn, heap.cfvl in 
    let fvadd = SFVL.add field value (Option.default SFVL.empty (Hashtbl.find_opt add loc)) in 
    let fvrem = SFVL.remove field (Option.default SFVL.empty (Hashtbl.find_opt rem loc)) in 
      sadd := Var.Set.add loc !sadd;
      Hashtbl.replace add loc fvadd;
      if (fvrem = SFVL.empty) then Hashtbl.remove rem loc else Hashtbl.replace rem loc fvrem 

let init_object (heap : t) (loc : string) (mtdt : Expr.t) : unit = 
  if (Hashtbl.mem heap.cfvl loc || Hashtbl.mem heap.sfvl loc) then raise (Failure "Illegal init_object") else (
    set heap loc SFVL.empty (Some (ESet [])) (Some mtdt)
  )

let has_loc (heap : t) (loc : string) : bool = 
  (Hashtbl.mem heap.cfvl loc || Hashtbl.mem heap.sfvl loc)

(** Removes the fv-list associated with --loc-- in --heap-- *)
let remove (heap : t) (loc : string) : unit =
  Hashtbl.remove heap.cfvl loc; Hashtbl.remove heap.sfvl loc;
  Hashtbl.remove heap.cdom loc; Hashtbl.remove heap.sdom loc;
  Hashtbl.remove heap.cmet loc; Hashtbl.remove heap.smet loc;
  heap.cdmn := Var.Set.remove loc !(heap.cdmn); heap.sdmn := Var.Set.remove loc !(heap.sdmn)

(** Retrieves the domain of --heap-- *)
let domain (heap : t) : SS.t =
    SS.union !(heap.cdmn) !(heap.sdmn)

let cdomain (heap : t) : SS.t = !(heap.cdmn)

(** Returns a copy of --heap-- *)
let copy (heap : t) : t = 
{ 
  cfvl = Hashtbl.copy heap.cfvl; sfvl = Hashtbl.copy heap.sfvl;
  cdom = Hashtbl.copy heap.cdom; sdom = Hashtbl.copy heap.sdom;
  cmet = Hashtbl.copy heap.cmet; smet = Hashtbl.copy heap.smet;
  cdmn = ref !(heap.cdmn); sdmn = ref !(heap.sdmn)
}

let merge_loc (heap : t) (new_loc : string) (old_loc : string) : unit =
  let domain = domain heap in 
  let cfvl, sfvl, dom, met = 
    (match SS.mem new_loc domain with 
    | true ->
        (* Merge field-value lists *)
        let ocvfl, osfvl = Option.default SFVL.empty (Hashtbl.find_opt heap.cfvl old_loc), Option.default SFVL.empty (Hashtbl.find_opt heap.sfvl old_loc) in 
        let ncvfl, nsfvl = Option.default SFVL.empty (Hashtbl.find_opt heap.cfvl new_loc), Option.default SFVL.empty (Hashtbl.find_opt heap.sfvl new_loc) in
        let cfvl = SFVL.union ncvfl ocvfl in 
        let sfvl = SFVL.union nsfvl osfvl in  

        (* Merge metadata *)
        let odom = get_dom heap old_loc in 
        let ndom = get_dom heap new_loc in 
        let dom  = (match odom, ndom with
                    | None, None -> None
                    | None, Some dom 
                    | Some dom, None -> Some dom 
                    | Some dom1, Some dom2 -> Some (NOp (SetUnion, [ dom1; dom2 ]))) in 
            
        let omet = get_met heap old_loc in 
        let nmet = get_met heap new_loc in 
        let met  = (match omet, nmet with
                    | None, None -> None
                    | None, Some met 
                    | Some met, None -> Some met 
                    | Some met1, Some met2 -> Some met1) in 

        cfvl, sfvl, dom, met

    | false -> 
        Option.default SFVL.empty (Hashtbl.find_opt heap.cfvl old_loc), 
        Option.default SFVL.empty (Hashtbl.find_opt heap.sfvl old_loc),
        get_dom heap old_loc, 
        get_met heap old_loc
    )
  in 
    set_fvl heap new_loc (SFVL.union cfvl sfvl);
    set_dom heap new_loc dom; set_met heap new_loc met;
    remove heap old_loc

(** Modifies --heap-- in place updating it to subst(heap) *)
let substitution_in_place (subst : SSubst.t) (heap : t) : unit =

  (* If the substitution is empty, there is nothing to be done *)
  if (not (SSubst.domain subst None = SS.empty)) then 
  (* The substitution is not empty *)
  (
    let le_subst = SSubst.subst_in_expr subst true in 

    (* 
      L.log L.Verboser (lazy (Printf.sprintf "CFVL: %d" (Hashtbl.length heap.cfvl)));
      L.log L.Verboser (lazy (Printf.sprintf "SFVL: %d" (Hashtbl.length heap.sfvl)));
      L.log L.Verboser (lazy (Printf.sprintf "CDOM: %d" (Hashtbl.length heap.cdom)));
      L.log L.Verboser (lazy (Printf.sprintf "SDOM: %d" (Hashtbl.length heap.sdom)));
      L.log L.Verboser (lazy (Printf.sprintf "CMET: %d" (Hashtbl.length heap.cmet)));
      L.log L.Verboser (lazy (Printf.sprintf "SMET: %d" (Hashtbl.length heap.smet))); 
    *)

    (* Field-value lists *)
    Hashtbl.iter (fun loc fvl -> 
      (* Substitute *)
      let fvl = SFVL.substitution subst true fvl in 
      (* Partition into concrete and symbolic *)
      let cfvl, sfvl = SFVL.partition (fun prop value -> is_c value && is_c prop) fvl in
      (* Set symbolic *)  
      Hashtbl.replace heap.sfvl loc sfvl;
      (* Merge concrete with new value taking precedence *)
      let prev_cfvl = Option.default SFVL.empty (Hashtbl.find_opt heap.cfvl loc) in 
      Hashtbl.replace heap.cfvl loc (SFVL.union cfvl prev_cfvl)
    ) heap.sfvl;

    (* Domain table *)
    Hashtbl.iter (fun loc dom -> 
      (* Substitute *)
      let dom = Option.map le_subst dom in
      (* Set domain *)
      set_dom heap loc dom
    ) heap.sdom;

    (* Metadata table *)
    Hashtbl.iter (fun loc met -> 
      (* Substitute *)
      let met = Option.map le_subst met in
      (* Set domain *)
      set_met heap loc met
    ) heap.smet;

    (* Now we need to deal with any substitutions in the locations themselves *)
    let aloc_subst = SSubst.filter subst (fun var _ -> is_aloc_name var) in
    SSubst.iter aloc_subst (fun aloc new_loc -> 
      let new_loc = match (new_loc : Expr.t) with | Lit (Loc loc) -> loc | ALoc loc -> loc | _ -> raise (Failure (Printf.sprintf "Heap substitution fail for loc: %s" (Expr.str new_loc))) in 
      merge_loc heap new_loc aloc;
    );
  )

(** Returns the serialization of --heap-- as a list *)
let to_list (heap : t) : (string * s_object) list =
  let domain = domain heap in 
    SS.fold (fun loc ac -> (loc, Option.get (get heap loc)) :: ac) domain []

(** converts a symbolic heap to a list of assertions *)
let assertions (heap : t) : Asrt.t list = 
  let make_loc_lexpr loc = 
    if (is_aloc_name loc) then Expr.ALoc loc else Expr.Lit (Loc loc) in 

  let rec assertions_of_object (loc, ((fv_list, domain), metadata)) =
    let le_loc = make_loc_lexpr loc in
    let fv_assertions = SFVL.assertions le_loc fv_list in 
    let domain = Option.map_default (fun domain -> [ Asrt.EmptyFields (le_loc, domain) ]) [] domain in
    let metadata = match metadata with | Some metadata -> [ Asrt.MetaData (le_loc, metadata) ] | None -> [ ] in
    fv_assertions @ domain @ metadata in
  
  List.sort Asrt.compare (List.concat (List.map assertions_of_object (to_list heap)))

let wf_assertions_of_obj (heap : t) (loc : string) : Formula.t list = 
  let cfvl = Option.default SFVL.empty (Hashtbl.find_opt heap.cfvl loc) in 
  let sfvl = Option.default SFVL.empty (Hashtbl.find_opt heap.sfvl loc) in 
  let cpps = SFVL.field_names cfvl in 
  let spps = SFVL.field_names sfvl in 
  let props = cross_product spps (cpps @ spps) (fun x y -> (x, y)) in 
  let props = List.filter (fun (x, y) -> x <> y) props in 
    List.map (fun (x, y) : Formula.t -> Not (Eq (x, y))) props

let wf_assertions (heap : t) : (Formula.t list) = 
  let domain = domain heap in 
    SS.fold (fun loc ac -> (wf_assertions_of_obj heap loc) @ ac) domain [] 

let is_well_formed (heap : t) : unit = 
  let cfvl = Hashtbl.fold (fun loc fvl ac -> 
    SFVL.fold (fun prop value ac -> ac && (is_c prop) && (is_c value)) fvl ac) heap.cfvl true in 
  if (not cfvl) then raise (Failure "Symbolicness in concrete part of the heap");
  let sfvl = Hashtbl.fold (fun loc fvl ac -> 
    SFVL.fold (fun prop value ac -> ac && ((not (is_c prop)) || (not (is_c value)))) fvl ac) heap.sfvl true in 
  if (not sfvl) then raise (Failure "Concreteness in the symbolic part of the heap");
  let dom_kept = domain heap in 
  let dom_calc_1 = SS.union (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.cfvl SS.empty) (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.sfvl SS.empty) in 
  let dom_calc_2 = SS.union (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.cdom SS.empty) (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.sdom SS.empty) in 
  let dom_calc_3 = SS.union (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.cmet SS.empty) (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.smet SS.empty) in 
  let dom_calc = SS.union dom_calc_1 (SS.union dom_calc_2 dom_calc_3) in 
  if (SS.elements dom_kept <> SS.elements dom_calc) then 
    let msg = Printf.sprintf "Domain mismatch:\n%s\n%s" (String.concat ", " (SS.elements dom_kept)) (String.concat ", " (SS.elements dom_calc)) in 
      L.fail msg 

let str (heap : t) = 
  let sorted_locs = SS.elements (domain heap) in 
  let sorted_locs_with_vals = List.map (fun loc -> (loc, Option.get (get heap loc))) sorted_locs in  
  let strings : string list = List.map (fun (loc, ((fv_pairs, domain), metadata)) ->
        let str_fv_pairs = SFVL.str fv_pairs in
        let domain_str = Option.map_default Expr.str "" domain in
        let meta_str = Option.map_default Expr.str "unknown" metadata in
        loc ^ " |-> [" ^  str_fv_pairs ^ " | " ^ domain_str ^ "] " ^ " with metadata " ^ meta_str) sorted_locs_with_vals in 
   "\t" ^ String.concat "\n\t" strings


let get_inv_metadata (heap : t) : (Expr.t, Expr.t) Hashtbl.t = 
  let inv_metadata = Hashtbl.create medium_tbl_size in  
  (* Hashtbl.iter 
    (fun loc (_, e_metadata) -> 
      match e_metadata with 
        | None -> () 
        | Some e_metadata -> 
            let loc_e = if (is_lloc_name loc) then Expr.Lit (Loc loc) else ALoc loc in 
            Hashtbl.add inv_metadata e_metadata loc_e) heap; *)
  inv_metadata  

let clean_up (heap : t) : unit = 
  SS.iter (fun loc -> 
    (match has_loc heap loc with 
    | false -> ()
    | true -> 
        let (fvl, dom), met = get_with_default heap loc in 
        (match (fvl = SFVL.empty), dom with 
        | true, None -> 
            remove heap loc;
            (match met with 
            | Some (ALoc loc)
            | Some (Lit (Loc loc)) -> remove heap loc
            | _ -> ())
        | _, _ -> ())
    )
  ) (domain heap)

let lvars (heap : t) : Var.Set.t = 
  let lvars_fvl = Hashtbl.fold (fun _ fvl ac -> Var.Set.union (SFVL.lvars fvl) ac) heap.sfvl Var.Set.empty in 
  let lvars_dom = Hashtbl.fold (fun _ oe ac -> let voe = Option.map_default Expr.lvars Var.Set.empty oe in Var.Set.union voe ac) heap.sdom Var.Set.empty in 
  let lvars_met = Hashtbl.fold (fun _ oe ac -> let voe = Option.map_default Expr.lvars Var.Set.empty oe in Var.Set.union voe ac) heap.smet Var.Set.empty in 
    List.fold_left SS.union Var.Set.empty [ lvars_fvl; lvars_met; lvars_dom ]
