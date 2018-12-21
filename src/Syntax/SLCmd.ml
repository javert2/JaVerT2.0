open SVal

(***************************************************************)
(** Separation Logic Commmands                                **)
(***************************************************************)

type folding_info = string * ((string * Expr.t) list)

(** {b JSIL Separation Logic commands}. *)
type t =
  | Fold       of string * Expr.t list * folding_info option         (** Fold             *)
  | Unfold     of string * Expr.t list * folding_info option * bool  (** Unfold           *)
  | GUnfold    of string                                             (** Global Unfold    *)
  | ApplyLem   of string * (Expr.t list) * (string list)             (** Apply lemma      *)
  | SepAssert  of Asrt.t * (string list)                             (** Assert           *)
  | Invariant  of Asrt.t * (string list)                             (** Invariant        *)
 
let map 
  (f_l : (t -> t) option)
  (f_a : (Asrt.t -> Asrt.t) option)
  (f_e : (Expr.t -> Expr.t) option)
  (lcmd : t) : t =

  (* Functions to map over assertions and expressions *)
  let map_e    = Option.default (fun x -> x) f_e in
  let map_a    = Option.default (fun x -> x) f_a in

  let mapped_lcmd = Option.map_default (fun f -> f lcmd) lcmd f_l in 

  (* Map over the elements of the command *)
  match mapped_lcmd with
    | Fold (name, les, None)               -> Fold (name, List.map map_e les, None)
    | Fold (name, les, (Some (s, l)))      -> Fold (name, List.map map_e les, (Some (s, (List.map (fun (x, e) -> (x, (map_e e))) l))))
    | Unfold (name, les, None, b)          -> Unfold (name, (List.map map_e les), None, b)
    | Unfold (name, les, (Some (s, l)), b) -> Unfold (name, List.map map_e les, (Some (s, (List.map (fun (x, e) -> (x, (map_e e))) l))), b)
    | GUnfold name                         -> GUnfold name 
    | ApplyLem (s, l, existentials)        -> ApplyLem (s, (List.map map_e l), existentials)
    | SepAssert (a, binders)               -> SepAssert (map_a a, binders)
    | Invariant (a, existentials)          -> Invariant (map_a a, existentials)
    
let substitution (subst : SSubst.t) (partial : bool) (lcmd : t) : t =  
  map None (Some (Asrt.substitution subst partial)) (Some (SSubst.subst_in_expr subst partial)) lcmd

let str_of_folding_info (unfold_info : folding_info option) : string  =
  match unfold_info with
  | None -> ""
  | Some (id, unfold_info_list) ->
      let unfold_info_list =
          List.map (fun (v, le) -> "(" ^ v ^ " := " ^ (Expr.str le) ^ ")") unfold_info_list in
      let unfold_info_list_str = String.concat " and " unfold_info_list in
      " [ " ^ id ^ " with " ^ unfold_info_list_str ^ " ]" 

let rec str (lcmd : t) : string =
    let string_of_args (les : Expr.t list) : string = 
       String.concat ", " (List.map Expr.str les) in 

    match lcmd with
    | Fold (name, les, fold_info) -> 
        "fold " ^ name ^ "(" ^ (string_of_args les) ^ ")" ^ (str_of_folding_info fold_info)
    
    | Unfold (name, les, unfold_info, b) ->
        let keyword = if b then "unfold* " else "unfold " in 
        keyword ^ name ^ "(" ^ (string_of_args les) ^ ")"  ^ (str_of_folding_info unfold_info)

    | GUnfold name -> "unfold_all " ^ name 
   
    | ApplyLem (lem_name, lparams, binders) ->
        let binders_str = 
          match binders with 
            | [] -> "" 
            | _  -> Printf.sprintf "[bind: %s]" (String.concat ", " binders) in 
        let lparams_str = String.concat ", " (List.map (fun e -> Expr.str e) lparams) in
        "sep_apply " ^  lem_name ^ "(" ^ lparams_str ^ ")" ^ binders_str
    
    | SepAssert (a, binders)  -> 
        let binders_str =
          match binders with 
            | [] -> "" 
            | _  -> "[bind: " ^ (String.concat ", " binders) ^ "]" in  
        "sep_assert (" ^ (Asrt.str a) ^ ")" ^ binders_str 

    | Invariant (a, existentials) -> 
        let existentials_str = 
          match existentials with 
            | [] -> "" 
            | _  -> "[existentials: " ^ (String.concat ", " existentials) ^ "]" in 
      "invariant (" ^ (Asrt.str a) ^ ")" ^ existentials_str