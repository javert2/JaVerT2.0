open SCommon
open CCommon

open SVal

module L = Logging

exception CompatFound of Asrt.t

module Error = MakeError.M(SVal.M)(SVal.SSubst)

type st = Asrt.t list 

type t = 
  | Leaf               of Asrt.t option * ((Flag.t * (Asrt.t list)) option) (* Final node and associated post-condition *)
  | Inner              of Asrt.t * (t list)
  | LabInner           of Asrt.t * ((t * (string * SS.t) option) list)
  | PhantomInner       of (t list)
  | LabPhantomInner    of ((t * (string * SS.t) option) list)   

type pred = {
  pred : Pred.t; 
  pure : bool;
  up   : t   
}

type spec = { 
  spec: Spec.t; 
  up  : t 
}

type lemma = { 
  lemma: Lemma.t; 
  up   : t 
}

type prog = { 
  preds    : (string, pred) Hashtbl.t; 
  specs    : (string, spec) Hashtbl.t; 
  lemmas   : (string, lemma) Hashtbl.t; 
  coverage : (string * int, int) Hashtbl.t; 
  prog     : Prog.t
}

type up_search_state = (st * SI.t * SS.t)

type preds_tbl_t = (string, pred) Hashtbl.t


let rec outs_expr (le : Expr.t) : SS.t = 
  let f = outs_expr in 
  match le with 
  | PVar x 
  | LVar x 
  | ALoc x                         -> SS.singleton x
  | UnOp (LstRev, le)              -> f le 
  | BinOp (le1, LstCons, le2)      -> SS.union (f le1) (f le2)
  | BinOp (EList les, LstCat, le2) -> SS.union (f (EList les)) (f le2)
  | BinOp (le1, LstCat, EList les) -> SS.union (f le1) (f (EList les))
  | BinOp (le1, LstCat, le2)       -> f le1 
  | EList les -> List.fold_left (fun ac le -> SS.union (f le) ac) SS.empty les 
  | _ -> SS.empty



let rec ins_outs_formula 
  (preds : (string, Pred.t) Hashtbl.t)
  (form  : Formula.t) : (SS.t * SS.t * Formula.t) list = 
  
  let f = ins_outs_formula preds in 
  let ins_e e = SS.union (SS.union (Expr.lvars e) (Expr.alocs e)) (Expr.pvars e) in 
  let ins_f f = SS.union (SS.union (Formula.lvars f) (Formula.alocs f)) (Formula.pvars f) in
  
  match form with 

    | Not e -> [ ins_f e, SS.empty, form ] 
     
    | And (f1, f2) -> 
        cross_product 
          (f f1) 
          (f f2) 
          (fun (ins1, outs1, f1) (ins2, outs2, f2) -> 
            SS.union ins1 ins2, SS.union outs1 outs2, Formula.And (f1, f2))
       
    | Eq (e1, e2) -> 
        let ins1  = ins_e e1 in 
        let outs1 = outs_expr e1 in 
        let ins2  = ins_e e2 in 
        let outs2 = outs_expr e2 in 

        let io_l2r = if SS.subset ins2 outs2 then [ ins1, outs2, Formula.Eq (e2, e1) ] else [] in 
        let io_r2l = if SS.subset ins1 outs1 then [ ins2, outs1, Formula.Eq (e1, e2) ] else [] in
        let ios = io_l2r @ io_r2l in 
        if ios <> [] then ios else [ SS.union ins1 ins2, SS.union outs1 outs2, Formula.Eq (e1, e2) ]

    | _ -> [ ins_f form, SS.empty, form ]



let rec ins_outs_assertion 
  (preds : (string, Pred.t) Hashtbl.t)
  (asrt  : Asrt.t) : (SS.t * SS.t * Asrt.t) list = 
  
  let f = ins_outs_assertion preds in 
  let ins_expr le = SS.union (SS.union (Expr.lvars le) (Expr.alocs le)) (Expr.pvars le) in 
  let ins_asrt a = SS.union (SS.union (Asrt.lvars a) (Asrt.alocs a)) (Asrt.pvars a) in
  
  let get_pred_ins name = 
    match Hashtbl.find_opt preds name with 
    | None      -> raise (Failure ("ins_outs_assertion. Unknown Predicate: " ^ name)) 
    | Some pred -> pred.ins in 

  match (asrt : Asrt.t) with 

    | Pure form -> List.map (fun (ins, outs, form) -> (ins, outs, Asrt.Pure form)) (ins_outs_formula preds form) 
      
    | PointsTo (e1, e2, e3) -> 
        [ (SS.union (ins_expr e1) (ins_expr e2)), outs_expr e3, asrt ]
     
    | MetaData (e1, e2) -> [ ins_expr e1, outs_expr e2, asrt ]

	  | EmptyFields (e1, e2) -> [ SS.union (ins_expr e1) (ins_expr e2), SS.empty, asrt ]
     
    | Pred (p_name, args) -> 
        let p_ins = get_pred_ins p_name in 
        let _, ins, outs = 
          List.fold_left 
            (fun (i, ins, outs) arg -> 
              if (List.mem i p_ins)
                then (i+1, SS.union ins (ins_expr arg), outs)
                else (i+1, ins, SS.union (outs_expr arg) outs))
            (0, SS.empty, SS.empty)
            args in 
        [ ins, outs, asrt ]

    | Types (les) -> 
        let ins = 
          List.fold_left
            (fun ins (le, _) -> SS.union ins (ins_expr le))
            SS.empty
            les in 
        [ ins, SS.empty, asrt ]
    
    | _ -> raise (Failure "DEATH. ins_outs_assertion. non-simple assertion")


let rec collect_simple_asrts (a : Asrt.t) : Asrt.t list = 
  let f = collect_simple_asrts in 
  match a with 
  | Pure True | Emp _  -> []
  | Pure _ | PointsTo _ | MetaData _ | Pred _  
  | Types _ | EmptyFields _ -> [ a ]
  | Star (a1, a2) -> (f a1) @ (f a2)


let string_of_ins_outs (ins_outs : (Asrt.t * ((SS.t * SS.t * Asrt.t) list)) list)  : string = 
  let str_of_si ss = "{ " ^ (String.concat ", " (SS.elements ss)) ^ " }" in 
  let ios = List.map (fun (a, ios) -> List.map (fun (ins, outs, a') -> a, ins, outs, a') ios) ins_outs in 
  "INS and OUTS:\n" ^ (String.concat "\n"
    (List.map 
      (fun (a, ins, outs, a') -> 
        Printf.sprintf "Asrt: %s. Ins: %s. Outs: %s. Asrt': %s" 
          (Asrt.str a) (str_of_si ins) (str_of_si outs) (Asrt.str a'))
      (List.concat ios))) ^ "\n"


let s_init
  (known_lvars  : SS.t)
  (preds        : (string, Pred.t) Hashtbl.t) 
  (a            : Asrt.t) : (st, st) result = 

  let prioritise (la : Asrt.t list) = 

    let lloc_aloc_pvar_lvar e1 e2 = 
      (match (e1 : Expr.t), (e2 : Expr.t) with 
        | Lit (Loc _), Lit (Loc _) -> 0
        | Lit (Loc _), _ -> -1
        | _, Lit (Loc _) -> 1
        | ALoc _, ALoc _ -> 0
        | ALoc _, _ -> -1
        | _, ALoc _ -> 0
        | PVar v1, PVar v2 -> 0 
        | PVar _, _ -> -1 
        | _, PVar _ -> 1
        | LVar v, LVar v' -> 
          (match is_spec_var_name v, is_spec_var_name v' with
          | true, true -> 0
          | true, false -> -1
          | false, true -> 1
          | false, false -> Pervasives.compare e1 e2
          )
        | _, _ -> Pervasives.compare e1 e2
      ) in 

    let lstr_pvar_lvar e1 e2 = 
      (match (e1 : Expr.t), (e2 : Expr.t) with 
        | Lit (String _), Lit (String _) -> 0
        | Lit (String _), _ -> -1
        | _, Lit (String _) -> 1
        | PVar v1, PVar v2 -> 0 
        | PVar _, _ -> -1 
        | _, PVar _ -> 1
        | LVar v, LVar v' -> 
          (match is_spec_var_name v, is_spec_var_name v' with
          | true, true -> 0
          | true, false -> -1
          | false, true -> 1
          | false, false -> Pervasives.compare e1 e2
          )
        | _, _ -> Pervasives.compare e1 e2
      ) in 

    List.sort (fun a1 a2 -> 
      (match (a1 : Asrt.t), (a2 : Asrt.t) with 
      | Types [ (e, t) ], Types [ (e', t') ] -> lloc_aloc_pvar_lvar e e'
      | Types _, _ -> -1
      | _, Types _ -> 1
      | PointsTo (el, ep, _), PointsTo (el', ep', _) -> 
        let comp_l = lloc_aloc_pvar_lvar el el' in 
        let comp_r = lstr_pvar_lvar ep ep' in 
          (match comp_l, comp_r with 
          | -1, _ -> -1
          | 0, _ -> comp_r
          | 1, _ -> 1)
      | PointsTo _, _ -> -1
      | _, PointsTo _ -> 1
      | MetaData (el, _), MetaData (el', _) -> lloc_aloc_pvar_lvar el el'
      | MetaData _, _ -> -1
      | _, MetaData _ -> 1
      | EmptyFields (el, _), EmptyFields (el', _) -> lloc_aloc_pvar_lvar el el'
      | EmptyFields _, _ -> -1 
      | _, EmptyFields _ -> 1
      | Pred _, _ -> 1
      | _, Pred _ -> -1
      | _, _ -> Pervasives.compare a1 a2)
    ) la in 

  let simple_asrts    = collect_simple_asrts a in 
  let simple_asrts    = List.map (fun a -> match (a : Asrt.t) with | Types _ -> Simplifications.reduce_assertion a | _ -> a) simple_asrts in 
  let simple_asrts    = List.concat (List.map (fun a -> match (a : Asrt.t) with | Types le -> List.map (fun e -> Asrt.Types [ e ]) le | _ -> [ a ]) simple_asrts) in 
  let simple_asrts    = if (List.mem (Asrt.Pure False) simple_asrts) then [ Asrt.Pure False ] else simple_asrts in 
  let simple_asrts    = List.filter (fun a -> a <> (Asrt.Pure True)) simple_asrts in 
  let stay, rest      = List.partition (function Asrt.Pred _ | Asrt.PointsTo _ | Asrt.EmptyFields _ -> true |  _ -> false) simple_asrts in 
  let rest            = Asrt.Set.elements (Asrt.Set.of_list rest) in 
  let simple_asrts    = prioritise (stay @ rest) in 
  let simple_asrts_io = List.map (fun a -> a, (ins_outs_assertion preds a)) simple_asrts in
  let simple_asrts_io = Array.of_list simple_asrts_io in

  (* check if the assertion at index i can be added to the unification 
     plan - its ins need to be contained in the current known lvars *)
  let visit_asrt (known_lvars : SS.t) (i : int) : (Asrt.t * SS.t) list = 
    let _, ios  = simple_asrts_io.(i) in 
    let act_ios = List.filter (fun (ins, _, _) -> SS.subset ins known_lvars) ios in 
      List.map (fun (_, outs, a) -> a, SS.union known_lvars outs) act_ios in 

  let rec visit_asrt_lst 
    (known_lvars : SS.t)
    (indexes : SI.t) 
    (visited_indexes : int list) : (SI.t * ((Asrt.t * SS.t) list)) option =  
    if (indexes = SI.empty) then None else 
    let i = SI.min_elt indexes in 
    let rest_indexes = SI.remove i indexes in 
      match visit_asrt known_lvars i with 
      | []  -> visit_asrt_lst known_lvars rest_indexes (i :: visited_indexes) 
      | ret -> Some (SI.union (SI.of_list visited_indexes) rest_indexes, ret) in 
  
  let rec search (up_search_states : up_search_state list) : (st, st) result = 
    match up_search_states with 
    | [] -> raise (Failure "UP: Should not happen: unification plan creation called with no starting state.")
    | (up, unchecked, _) :: _ when (unchecked = SI.empty) -> 
        L.log L.Verboser (lazy "Successfully created UP.");
        Ok (List.rev up) 
    | (up, unchecked, known_lvars) :: rest -> 
        let str = lazy (
          Printf.sprintf "KNOWN VARS: %s.\nCUR UP:\n\t%s\nTO VISIT: %s\n\t%s"
            (String.concat ", " (SS.elements known_lvars))
            (String.concat "\n\t" (List.map Asrt.str up))
            (String.concat ", " (List.map string_of_int (SI.elements unchecked)))
            (String.concat "\n\t" (List.map (fun i -> let a, _ = simple_asrts_io.(i) in Asrt.str a) (SI.elements unchecked)))) in
        L.log L.Verboser str;  
        (match visit_asrt_lst known_lvars unchecked [] with 
        | None -> 
            L.log L.Verboser (lazy "No assertions left to visit.");
            if (rest = []) then (
              L.log L.Verboser (lazy "Detecting spec-var existentials.");
              let unchckd = List.map (fun i -> let _, (ins, _, _) :: _ = simple_asrts_io.(i) in ins) (SI.elements unchecked) in 
              let unchckd = List.map (fun u -> SS.diff (SS.filter (fun x -> is_spec_var_name x) u) known_lvars) unchckd in 
              let unchckd = List.filter (fun u -> u <> SS.empty) unchckd in 
              L.log L.Verboser (lazy (Printf.sprintf "\t%s" (String.concat "\n\t" (List.map (fun u -> String.concat ", " (SS.elements u)) unchckd))));
              if (List.length unchckd > 0) then (
                let heuristic_var : string = SS.min_elt (List.hd unchckd) in 
                  L.log L.Verboser (lazy ("Heuristically adding existential: " ^ heuristic_var));
                  search [ (up, unchecked, SS.add heuristic_var known_lvars) ]
              ) else (
                (* This is where it really ends - couldn't continue naturally, couldn't heuristically extend *)
                L.log L.Verboser (lazy "Unification plan creation failure.");
                let unchecked, _ = List.split (List.map (fun i -> simple_asrts_io.(i)) (SI.elements unchecked)) in 
                Error unchecked
              )
            ) else search rest
        | Some (new_unchecked, ret) -> 
            (* L.log L.Verboser (lazy "Successfully added more assertions to the UP.");
            L.log L.Verboser (lazy (Printf.sprintf "States to examine: %d" (List.length ret)));
            L.log L.Verboser (lazy (Printf.sprintf "Unchecked remaining: %d" (SI.cardinal new_unchecked))); *)
            let new_search_states = 
              List.map 
                (fun (a, new_known_vars) -> 
                  (a :: up, new_unchecked, new_known_vars))
                ret in 
              search (new_search_states @ rest)) in 
  
  let initial_indexes = SI.of_list (Array.to_list (Array.init (List.length simple_asrts) (fun i -> i))) in 
  let initial_search_state = [], initial_indexes, known_lvars in 
  search [ initial_search_state ]

let rec lift_up (up : st) (posts : (Flag.t *  (Asrt.t list)) option) : t = 
  match up with 
  | [ ]      -> Leaf (None, posts)
  | [ p ]    -> Leaf (Some p, posts)
  | p :: up' -> Inner (p, [ lift_up up' posts ])

let add_up (g_up : t) (up_post : st * ((Flag.t * (Asrt.t list)) option)) : t = 
  match g_up, up_post with 
  | PhantomInner ups, (up, posts) -> PhantomInner (ups @ [ lift_up up posts ])
  | _, (up, posts) -> PhantomInner ([ g_up; (lift_up up posts) ])


let lift_ups (ups : (st *  ((string * SS.t) option * (Flag.t * (Asrt.t list)) option)) list) : t = 
  let b = List.exists (fun (_, (lab, _)) -> match lab with | Some _ -> true | _ -> false) ups in 
  let ups' = List.map (fun (up, (_, posts)) -> up, posts) ups in 
  if b 
    then (
      (* Printf.printf "BUILDING GUP FOR SPEC WITH EXISTENTIALS\n"; *)
      let gups = List.map (fun (up, (lab, posts)) -> lift_up up posts, lab) ups in 
      LabPhantomInner gups
    ) else List.fold_left add_up (PhantomInner []) ups'




let init 
 ?(use_params   : bool option)
  (known_vars   : SS.t)
  (params       : SS.t)
  (preds        : (string, Pred.t) Hashtbl.t) 
  (asrts_posts  : (Asrt.t * ((string * SS.t) option * ((Flag.t *  (Asrt.t list)) option))) list) : (t, st list) result = 

  let known_vars = (match use_params with | None -> known_vars | Some _ -> SS.union known_vars params) in 

  let ups = List.map (fun (asrt, (lab, posts)) -> (s_init known_vars preds asrt), (lab, posts)) asrts_posts in 
  let errors, _ = List.partition (fun (up, _) -> (match up with | Error _ -> true | Ok _ -> false)) ups in   
  let errors, _ = List.split errors in 
  let errors = List.map (fun x -> match x with | Error e -> e) errors in 
  
  if (errors <> []) then Error errors else (
    Ok (lift_ups (List.map (fun (up, posts) -> (match up with | Ok up -> up), posts) ups))
  )

let filter_ups (ups : (t * SS.t option) list) (lab : string option) : (t list) = 
  let projection = List.map (fun (up, labs) -> up) in 
  match lab with 
    | None     -> projection ups 
    | Some lab -> 
        let ups' = 
          List.filter 
            (fun (up, labs) ->
              match labs with 
                | None      -> false
                | Some labs -> SS.mem lab labs 
            ) ups in 
        projection ups

let next ?(lab: string option) (up : t) : ((t  * (string * SS.t) option) list) option = 
  match up with 
  | Leaf _ -> None 
  | Inner (_, ups) -> Some (List.map (fun x -> (x, None)) ups)
  | LabInner (_, lab_ups) when (List.length lab_ups) > 0 -> Some lab_ups 
  | PhantomInner (ups) when (List.length ups) > 0 -> Some (List.map (fun x -> (x, None)) ups)
  | LabPhantomInner (lab_ups) when (List.length lab_ups) > 0 -> Some lab_ups
  | _ -> None 


let head (up : t) : (Asrt.t option) = 
  match up with 
  | Leaf (Some p, _) 
  | Inner (p, _)
  | LabInner (p, _) -> Some p
  | _ -> None 



let posts (up : t) : (Flag.t * (Asrt.t list)) option = 
  match up with 
  | Leaf (_, posts) -> posts 
  | _ -> None 

let str (up : t) : string = 
  let tab = "\t" in 

  let str_of_lab (lab : (string * SS.t)) : string = 
    let lab, vars = lab in 
    Printf.sprintf " [%s: %s]" lab (String.concat ", " (SS.elements vars)) in 

  let rec aux (tabs : string) (up : t) : string = 
    (match up with 
    | Leaf (a, None) -> 
        let a_str = Option.map_default Asrt.str "NONE" a in 
        tabs ^ (Printf.sprintf "Leaf: %s with Posts = NONE" a_str)
    
    | Leaf (a, Some (flag, posts)) -> 
        let a_str = Option.map_default Asrt.str "NONE" a in 
        let posts_strs = List.map (fun post -> tab ^ tabs ^ (Asrt.str post)) posts in 
        let posts_strs = String.concat "\n" posts_strs in
        tabs ^ (Printf.sprintf "Leaf: %s with Flag %s and Posts:\n%s" a_str (Flag.str flag) posts_strs)
    
    | Inner (a, next_ups) -> 
        let main_str = tabs ^ (Printf.sprintf "Inner Node: %s with %d children\n" (Asrt.str a) (List.length next_ups)) in 
        if ((List.length next_ups) = 1) then (
          let next_str = aux tabs (List.nth next_ups 0) in 
          main_str ^ next_str 
        ) else (
          let next_tabs = tab ^ tabs in 
          let ups_strs = 
            List.mapi 
              (fun i up -> 
                 let str_i = next_tabs ^ (Printf.sprintf "Children %d\n" i) in 
                 let next_up_str = aux next_tabs up in
                 str_i ^ next_up_str 
              ) next_ups in 
          main_str ^ (String.concat "\n" ups_strs)
        )       

    | LabInner (a, next_ups) -> 
        let main_str = tabs ^ (Printf.sprintf "Inner Node: %s with %d children\n" (Asrt.str a) (List.length next_ups)) in 
        if ((List.length next_ups) = 1) then (
          let up, lab = List.nth next_ups 0 in 
          let lab_str = Option.map_default str_of_lab "" lab in 
          let next_str = aux tabs up in 
          main_str ^ lab_str ^ next_str 
        ) else (
          let next_tabs = tab ^ tabs in 
          let ups_strs = 
            List.mapi 
              (fun i (up, lab) -> 
                 let str_lab = Option.map_default str_of_lab "" lab in 
                 let str_i = next_tabs ^ (Printf.sprintf "Children %d%s\n" i str_lab) in 
                 let next_up_str = aux next_tabs up in
                 str_i ^ next_up_str 
              ) next_ups in 
          main_str ^ (String.concat "\n" ups_strs)
        )

    | PhantomInner (next_ups) -> 
        let main_str = tabs ^ (Printf.sprintf "Phantom Node %d children\n" (List.length next_ups)) in 
        let next_tabs = tab ^ tabs in 
        let ups_strs = 
          List.mapi 
            (fun i up -> 
              let str_i = next_tabs ^ (Printf.sprintf "Children %d\n" i) in 
              let next_up_str = aux next_tabs up in
              str_i ^ next_up_str 
            ) next_ups in 
        main_str ^ (String.concat "\n" ups_strs)


    | LabPhantomInner (next_ups) -> 
        let main_str  = tabs ^ (Printf.sprintf "LabPhantom Node %d children\n" (List.length next_ups)) in 
        let next_tabs = tab ^ tabs in 
        let ups_strs = 
          List.mapi 
            (fun i (up, lab) -> 
              let str_lab = Option.map_default str_of_lab "" lab in 
              let str_i = next_tabs ^ (Printf.sprintf "Children %d%s\n" i str_lab) in  
              let next_up_str = aux next_tabs up in
              str_i ^ next_up_str 
            ) next_ups in 
        main_str ^ (String.concat "\n" ups_strs)) in 

  aux "" up 
        
        
let init_specs  
    (preds : (string, Pred.t) Hashtbl.t)
    (specs : Spec.t list) : ((string, spec) Hashtbl.t, Error.t) result = 
  let u_specs = Hashtbl.create medium_tbl_size in try (
  List.iter (fun (spec : Spec.t) ->
    L.log L.Verbose (lazy (Printf.sprintf "Attempting to create UP for a spec of %s : %d specs" spec.name (List.length spec.sspecs)));
    let params = SS.of_list spec.params in 
    let sspecs : (Asrt.t * ((string * SS.t) option * ((Flag.t *  (Asrt.t list)) option))) list = 
      List.mapi 
        (fun i (sspec : Spec.st) -> 
          L.log L.Verboser (lazy 
            (Printf.sprintf "lab of sspec %d: %s" i
              (Option.map_default (fun (s, vars) -> Printf.sprintf "[%s: %s]" s (String.concat ", " vars)) "" sspec.label))
          ); 
          let label' = Option.map (fun (s, vars) -> (s, SS.of_list vars)) sspec.label in  
          sspec.pre, (label', Some (sspec.flag, sspec.posts)))
        spec.sspecs in

    let up = init ~use_params:true SS.empty params preds sspecs in 
    match up with 
      | Error err -> raise (Error.ThrowError (Error.EUP (Error.UPSpec (spec.name, err))))
          (* let msg = Printf.sprintf "Specification of %s cannot be turned into UP. %s" 
            spec.name (Spec.str spec) in 
          L.fail msg *)
      | Ok up -> 
          L.log L.Verbose (lazy (Printf.sprintf "Successfully created UP of specification of %s" spec.name));
          Hashtbl.replace u_specs spec.name { spec = spec; up = up }  
  ) specs; 
  Ok u_specs)
  with Error.ThrowError e -> Error e

let init_lemmas 
    (preds  : (string, Pred.t) Hashtbl.t)
    (lemmas : Lemma.t list) : ((string, lemma) Hashtbl.t, Error.t) result = 
  
  let u_lemmas = Hashtbl.create medium_tbl_size in try (
  List.iter (fun (lemma : Lemma.t) -> 

    let params = SS.of_list lemma.params in 
    let sspecs : (Asrt.t * ((string * SS.t) option * ((Flag.t *  (Asrt.t list)) option))) list =
      [ lemma.pre, (None, Some (Flag.Normal, lemma.posts)) ] in 
    let up = init ~use_params:true SS.empty params preds sspecs in     
    match up with 
    | Error err -> raise (Error.ThrowError (Error.EUP (Error.UPLemma (lemma.name, err))))
          (* let msg = Printf.sprintf "Lemma %s cannot be turned into UP" lemma.name in 
          L.fail msg *)
    | Ok up -> 
          L.log L.Verbose (lazy (Printf.sprintf "Successfully created UP of Lemma %s" lemma.name));
          Hashtbl.replace u_lemmas lemma.name { lemma = lemma; up = up }  
  ) lemmas;
  Ok u_lemmas 
  ) with Error.ThrowError e -> Error e


let init_preds   
  (preds : (string, Pred.t) Hashtbl.t) : ((string, pred) Hashtbl.t, Error.t) result = 
  let u_preds = Hashtbl.create medium_tbl_size in try (
  Hashtbl.iter (fun name (pred : Pred.t) ->
    L.log L.Verbose (lazy (Printf.sprintf "Attempting to create UP of predicate %s" name)); 
    let known_params = 
      SS.of_list 
        (List.map 
          (fun i -> let param, _ = List.nth pred.params i in param) 
          (pred.ins)) in 

    let defs = 
      List.map 
        (fun (lab, def) -> 
          let lab' = Option.map (fun (s, vars) -> s, SS.of_list vars) lab in 
          def, (lab', None)) 
        pred.definitions in 

    match init known_params SS.empty preds defs with 
    | Error err -> raise (Error.ThrowError (Error.EUP (Error.UPPred (pred.name, err))))
      (* let msg = Printf.sprintf "Predicate definition of %s cannot be turned into UP" pred.name in 
      L.fail msg *)
    | Ok up ->
      L.log L.Verbose (lazy (Printf.sprintf "Successfully created UP of predicate %s:\n%s" name (str up))); 
      Hashtbl.replace u_preds name { pred = pred ; pure = pred.pure; up = up }  
  ) preds; 
  Ok u_preds
  ) with Error.ThrowError e -> Error e 

let init_prog (prog : Prog.t) : (prog, Error.t) result = 
  let all_specs  : Spec.t list = Prog.get_specs prog in 

  let lemmas     : Lemma.t list = Prog.get_lemmas prog in
  let preds_tbl  : ((string, pred) Hashtbl.t, Error.t) result = init_preds prog.preds in 
  (match preds_tbl with 
  | Error e -> Error e
  | Ok preds_tbl -> 
    let lemmas_tbl : ((string, lemma) Hashtbl.t, Error.t) result = init_lemmas prog.preds lemmas in
    (match lemmas_tbl with 
    | Error e -> Error e 
    | Ok lemmas_tbl -> 
      let specs_tbl  : ((string, spec) Hashtbl.t, Error.t) result = init_specs prog.preds all_specs in 
      (match specs_tbl with 
      | Error e -> Error e
      | Ok specs_tbl -> 
          let coverage   : (string * int, int) Hashtbl.t = Hashtbl.create big_tbl_size in   
          Ok { prog = prog; specs = specs_tbl; preds = preds_tbl; lemmas = lemmas_tbl; coverage })))

let rec expr_compatible e e' subst : bool = 
  let result = (match (e : Expr.t), (e' : Expr.t) with
  | Lit  l1, Lit  l2 when (l1 = l2) -> true
  | PVar p1, PVar p2 when (p1 = p2) -> true 
  | LVar v1, LVar v2 -> (match SSubst.get subst v1 with | None -> SSubst.extend subst [v1, Expr.LVar v2]; true | Some v2' -> Expr.LVar v2 = v2')
  | ALoc a1, ALoc a2 -> (match SSubst.get subst a1 with | None -> SSubst.extend subst [a1, Expr.ALoc a2]; true | Some a2' -> Expr.ALoc a2 = a2')
  | UnOp (op1, e), UnOp (op2, e') when (op1 = op2) -> expr_compatible e e' subst 
  | BinOp (e1, op1, e2), BinOp (e1', op2, e2') when (op1 = op2) -> expr_compatible e1 e1' subst && expr_compatible e2 e2' subst 
  | NOp (op1, les), NOp (op2, les') when (op1 = op2) -> expr_list_compatible (List.combine les les') subst 
  | EList les, EList les' 
  | ESet  les, ESet  les' -> expr_list_compatible (List.combine les les') subst
  | Nono, Nono -> true
  | _, _ -> false
  ) in 
    (* L.log L.Verboser (lazy (Printf.sprintf "Compat expr: %s %s : %b with %s" (Expr.str e) (Expr.str e') result (SSubst.str subst))); *)
    result
and expr_list_compatible (esses : (Expr.t * Expr.t) list) (subst : SSubst.t) : bool =
  let temp_subst : SSubst.t = SSubst.init [] in 

  let rec loop esses = 
    (match esses with
    | [] -> if (SSubst.compatible subst temp_subst) then (SSubst.merge_left subst temp_subst; true) else false
    | (e, e') :: rest -> if (expr_compatible e e' temp_subst) then loop rest else false
    ) in 
  loop esses

let asrt_compatible p q subst = 
  (match (p : Asrt.t), (q : Asrt.t) with
  | PointsTo (el, ep, ev), PointsTo (el', ep', ev') -> expr_list_compatible (List.combine [el; ep; ev] [el'; ep'; ev']) subst
  | MetaData (el, em), MetaData (el', em') -> expr_list_compatible (List.combine [el; em] [el'; em']) subst 
  | Pred (name, es), Pred (name', es') when (name = name') -> expr_list_compatible (List.combine es es') subst
  | EmptyFields (el, ed), EmptyFields (el', ed') -> expr_list_compatible (List.combine [el; ed] [el'; ed']) subst
  | Pure (Eq (PVar x, le)), Pure (Eq (PVar y, le')) -> (x = y) && expr_list_compatible [ (le, le') ] subst
  | _ -> false)

let check_compatibility (ps : Asrt.t list) (qs : Asrt.t list) : SSubst.t option = 
  let subst = SSubst.init [] in 

  let rec loop (ps : Asrt.Set.t) (qs : Asrt.Set.t) : bool = 
    match (ps = Asrt.Set.empty) with 
    | true -> true
    | false -> 
        let p = Asrt.Set.min_elt ps in 
        let ps = Asrt.Set.remove p ps in
          (try (Asrt.Set.iter (fun q -> 
            let cassrts = asrt_compatible p q subst in 
            (* L.log L.Verboser (lazy (Printf.sprintf "Compat asrt: %s %s : %b with %s" (Asrt.str p) (Asrt.str q) cassrts (SSubst.str subst))); *)
            if cassrts 
              then raise (CompatFound q) qs) qs; false  
          ) with CompatFound q -> 
              let qs = Asrt.Set.remove q qs in 
                loop ps qs)
  in 
    if (loop (Asrt.Set.of_list ps) (Asrt.Set.of_list qs))
      then Some subst 
      else None 

(** Substitution inverse *)
let inverse (subst : SSubst.t) : SSubst.t = 
  let inv_subst = SSubst.init [] in 
    SSubst.iter subst (fun v le -> 
      (* Convert v to le *)
      let v_le : Expr.t = if ((is_spec_var_name v) || (is_lvar_name v)) 
        then LVar v
        else if (is_aloc_name v) 
          then ALoc v 
          else raise (Failure ("Bizarre variable in subst: " ^ v)) in 

      (* Convert le to v *)
      let le_v = (match (le : Expr.t) with 
        | LVar x | ALoc x -> Some x
        | _ -> None) in 

      (match le_v with 
        | None -> ()
        | Some v -> SSubst.add inv_subst v v_le
      )); 
  inv_subst

let create_partial_match_spec (spec : Spec.t) : Spec.st option = 
  
  let additional a = 
    let target_set = SS.add JS2JSIL_Constants.var_scope (SS.singleton JS2JSIL_Constants.var_this) in 
    (match (a : Asrt.t) with 
      | Pure (Eq (PVar x, _))
      | Pure (Eq (_, PVar x)) -> SS.mem x target_set
      | _ -> false
    ) in 

  let sspecs = spec.sspecs in 
  if (List.length sspecs = 1) then None else (
  
    let first_spec = List.hd sspecs in 
    let rest_specs = List.tl sspecs in 
    let first_flag = first_spec.flag in 
    let success    = List.for_all (fun (sspec : Spec.st) -> sspec.flag = first_flag) rest_specs in 
    if (not success) then None else (
      let pres                    = List.map (fun (sspec : Spec.st) -> sspec.pre) sspecs in  
      let s_pres                  = List.map collect_simple_asrts pres in 
      let spatial_pres, pure_pres = List.split (List.map (fun pre_asrts -> List.partition (fun a -> not (Asrt.is_pure_asrt a && (not (additional a)))) pre_asrts) s_pres) in 
      let pure_pres = List.map (fun x -> Asrt.Set.elements (Asrt.Set.of_list x)) pure_pres in 

      let lens           = List.map (fun pre_asrts -> List.length pre_asrts) spatial_pres in 
      let lens           = SI.of_list lens in 
      let success        = (SI.cardinal lens = 1) in
      (*L.log L.Verboser (lazy (Printf.sprintf "Create Partial Match : %s : passed to stage 2" spec.name)); *)
      if (not success) then None else (
        let first_pre_asrts = List.hd spatial_pres in 
        let rest_pre_asrts  = List.tl spatial_pres in 
        let first_pre_pure  = List.hd pure_pres in 
        let rest_pre_pures  = List.tl pure_pres in 
        let substs = List.map (fun cur_pre_asrts -> check_compatibility first_pre_asrts cur_pre_asrts) rest_pre_asrts in 
        let success = List.for_all (fun subst -> subst <> None) substs in 
        if (not success) then None else (

          let substs = List.map Option.get substs in 

          (* Analyse pure formulae for compatibility *)
          let isubsts = List.map inverse substs in 
          let rpps : Asrt.Set.t list = List.map2 (fun is rp -> Asrt.Set.of_list (List.map (Asrt.substitution is true) rp)) isubsts rest_pre_pures in 
          let inter = ref (Asrt.Set.of_list first_pre_pure) in 

            List.iter (fun rpp -> inter := Asrt.Set.inter !inter rpp) rpps;
            (* L.log L.Verboser (lazy (Printf.sprintf "Intersection: %s" (String.concat ", " (List.map Asrt.str (Asrt.Set.elements !inter))))); *)

          let common_pure = Asrt.Set.elements !inter in 
          let rpps = List.map (fun rpp -> Asrt.Set.elements (Asrt.Set.diff rpp !inter)) rpps in 

          let new_posts = List.concat (
            List.map 
              (fun ((isubst, (sspec : Spec.st)), pure_pre) -> 
                List.map (fun post -> Asrt.Star (Asrt.substitution isubst true post, (Asrt.star pure_pre))) sspec.posts)   
            (List.combine (List.combine isubsts rest_specs) rpps)) in
          let fpp = Asrt.Set.elements (Asrt.Set.diff (Asrt.Set.of_list first_pre_pure) !inter) in 
          let new_first_posts = List.map (fun post -> Asrt.Star (post, (Asrt.star fpp))) first_spec.posts in 
          let new_posts = new_first_posts @ new_posts in 
          let res : Spec.st = 
            {
              pre       = Asrt.star ((List.hd spatial_pres) @ common_pure); 
              posts     = new_posts; 
              flag      = first_flag;
              to_verify = false; 
              label     = None 
            } in 
          L.log L.Verboser (lazy (Printf.sprintf "Partial Match SPEC of %s:\n%s" spec.name (Spec.string_of_sspec "" res)));
          Some res 
        )
      )
    )
  )


let get_pred_def (pred_defs : preds_tbl_t) (name : string) : pred = 
  try 
    let up_pred = Hashtbl.find pred_defs name in 
      up_pred 
  with _ -> raise (Failure (Printf.sprintf "DEATH. PRED %s NOT DEFINED" name))  

 let init_pred_defs () : preds_tbl_t = 
   Hashtbl.create CCommon.medium_tbl_size

let get_procs (prog : prog) : Proc.t list = 
  Prog.get_procs (prog.prog) 

let get_bispecs (prog : prog) : BiSpec.t list = 
  Prog.get_bispecs (prog.prog) 

let get_lemma (prog : prog) (name : string) : (lemma, unit) result = 
  match (Hashtbl.find_opt prog.lemmas name) with
  | Some lemma -> Ok lemma
  | None -> Error ()

(** JSIL logic assertions *)
let rec string_of_asrt ?(preds_printer : (string * (Expr.t list) -> string option) option) (preds : preds_tbl_t) (a : Asrt.t) : string =
  let preds_printer =
    (match preds_printer with 
      | None -> 
        (* Printf.printf "NO PREDS_PRINTER WAS PROVIDED!\n"; *)
        (fun x -> None)
      | Some preds_printer -> 
        (* Printf.printf "WE HAVE A PREDS_PRINTER!\n"; *)
        preds_printer) in 
  let str = string_of_asrt ~preds_printer:preds_printer preds in 
  let sle = Expr.str in
  match a with
  | Star (a1, a2) -> Printf.sprintf "%s * %s" (str a1) (str a2)
  | Pred (name, args) -> 
    (match preds_printer (name, args) with 
      | Some ret -> ret 
      | None -> 
        try (
          let pred = get_pred_def preds name in 
          let out_params = Pred.out_params pred.pred in 
          let out_args = Pred.out_args pred.pred args in
          let in_args = Pred.in_args pred.pred args in  
          let out_params_args = List.combine out_params out_args in 
          let out_params_args_str = List.map (fun (x, e) -> Printf.sprintf "%s: %s" x (sle e)) out_params_args in 
          let in_args_str = List.map Expr.str in_args in 
          let args_str = Pred.combine_ins_outs pred.pred in_args_str out_params_args_str in 
          Printf.sprintf "%s(%s)" name (String.concat ", " args_str)
        ) with _ -> Asrt.str a)
  | a -> Asrt.str a 


let string_of_sspec ?(preds_printer : (string * (Expr.t list) -> string option) option)  (preds : preds_tbl_t) (prefix: string) (sspec : Spec.st) = 
    let sa = string_of_asrt ?preds_printer:preds_printer preds in 
    let sal asrts = String.concat "; " (List.map sa asrts) in 
    (prefix ^ "[[ " ^ (sa sspec.pre)   ^ " ]]\n" ^
     prefix ^ "[[ " ^ (sal sspec.posts) ^ " ]]\n" ^
     prefix ^ (Flag.str sspec.flag))


let string_of_spec ?(preds_printer : (string * (Expr.t list) -> string option) option) (preds : preds_tbl_t) (spec : Spec.t) : string =
  let normal_specs, error_specs = List.partition (fun (spec : Spec.st) -> spec.flag = Flag.Normal) spec.sspecs in 
  let nspecs_str = String.concat ";\n " (List.map (string_of_sspec ?preds_printer:preds_printer preds "\t") normal_specs) in 
  let especs_str = String.concat ";\n " (List.map (string_of_sspec ?preds_printer:preds_printer preds "\t") error_specs) in 
    Printf.sprintf "spec %s (%s)\n %s\n" spec.name (String.concat ", " spec.params) (nspecs_str ^ especs_str) 

let string_of_normal_spec ?(preds_printer : (string * (Expr.t list) -> string option) option) (preds : preds_tbl_t) (spec : Spec.t) : string =
  let normal_specs, _ = List.partition (fun (spec : Spec.st) -> spec.flag = Flag.Normal) spec.sspecs in 
  let nspecs_str = String.concat ";\n " (List.map (string_of_sspec ?preds_printer:preds_printer preds "\t") normal_specs) in 
    if (nspecs_str = "") then "" else (Printf.sprintf "spec %s (%s)\n %s\n" spec.name (String.concat ", " spec.params) (nspecs_str)) 


let add_spec (prog : prog) (spec : Spec.t) : unit = 
   
  let params = SS.of_list spec.params in 
  let proc   =
    match Prog.get_proc prog.prog spec.name with 
      | None -> raise (Failure "DEATH. ADDING SPEC TO UNKNOWN PROC!")
      | Some proc -> proc in  
  
  let posts_from_sspecs sspecs =  
    List.map 
      (fun (sspec : Spec.st) -> (sspec.pre, Some (sspec.flag, sspec.posts)))
      sspecs in 

  let new_uspec (spec : Spec.t) : spec = 
    let posts = List.map (fun (x, y) -> x, (None, y)) (posts_from_sspecs spec.sspecs) in 
    let up = init ~use_params:true SS.empty params prog.prog.preds posts in 
    match up with 
      | Error _  -> 
          let msg = Printf.sprintf "Spec addition: specification of %s cannot be turned into UP. %s" 
            spec.name (Spec.str spec) in 
          L.fail msg
      | Ok up -> 
          L.log L.Verbose (lazy (Printf.sprintf "Successfully created UP of specification of %s" spec.name));
          let new_spec : spec = { spec = spec; up = up } in  
          new_spec in 

  let extend_spec (uspec : spec) (sspecs : Spec.st list) : spec = 
    let spec    = Spec.extend uspec.spec sspecs in 
    let ups     = List.map (fun (asrt, posts) -> asrt, (s_init params prog.prog.preds asrt), posts) (posts_from_sspecs sspecs) in 
    let new_gup =
      List.fold_left 
        (fun g_up (pre, pre_up, posts) -> 
          match pre_up with 
            | Error _ -> 
                let msg = 
                  Printf.sprintf "WARNING!!! IT IS NOT POSSIBLE TO BUILD UP FOR INFERRED SPEC of %s!PRE:\n%s\n"
                    uspec.spec.name (Asrt.str pre) in 
                L.log L.Verboser (lazy msg); 
                (* Printf.printf "%s" msg; *)
                g_up
            | Ok pre_up -> add_up g_up (pre_up, posts))
        uspec.up 
        ups in 
    let uspec' : spec = { spec = spec; up = new_gup } in 
    uspec' in 


  let new_uspec = 
    match Hashtbl.find_opt prog.specs spec.name with 
      | None       -> new_uspec spec
      | Some uspec -> extend_spec uspec spec.sspecs in 

  Hashtbl.replace prog.specs spec.name new_uspec; 
  Hashtbl.replace prog.prog.procs spec.name { proc with spec = Some new_uspec.spec }


  let update_coverage (prog : prog) (proc_name : string) (index : int) : unit = 
    try 
      let count = Hashtbl.find prog.coverage (proc_name, index) in 
      Hashtbl.replace prog.coverage (proc_name, index) (count + 1)
    with Not_found -> 
      Hashtbl.replace prog.coverage (proc_name, index) 0

  let first_time_running (prog : prog) (proc_name : string) (index : int) : bool = 
    not (Hashtbl.mem prog.coverage (proc_name, index))


let string_of_pred_defs (pred_defs : preds_tbl_t) : string = 
  let pred_strs = 
    Hashtbl.fold 
      (fun pred_name pred ac -> 
        let pred_str = Pred.str pred.pred in 
        pred_str :: ac 
      ) pred_defs [] in 
  String.concat "\n" pred_strs 


