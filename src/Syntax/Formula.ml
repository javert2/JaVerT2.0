open SVal 
open CCommon
open SCommon

type t = 
  | True                                             (** Logical true *)
  | False                                            (** Logical false *)
  | Not         of t                                 (** Logical negation *)
  | And         of t * t                             (** Logical conjunction *)
  | Or          of t * t                             (** Logical disjunction *)
  | Eq          of Expr.t * Expr.t                   (** Expression equality *)
  | Less        of Expr.t * Expr.t                   (** Expression less-than for numbers *)
  | LessEq      of Expr.t * Expr.t                   (** Expression less-than-or-equal for numbers *)
  | StrLess     of Expr.t * Expr.t                   (** Expression less-than for strings *)
  | SetMem      of Expr.t * Expr.t                   (** Set membership *)
  | SetSub      of Expr.t * Expr.t                   (** Set subsetness *)
  | ForAll      of (string * Type.t option) list * t (** Forall *)

let compare = Pervasives.compare

module MyFormula =
  struct
    type nonrec t = t
    let compare = Pervasives.compare
  end

module Set = Set.Make(MyFormula)


(** Apply function f to the logic expressions in an assertion, recursively when f_a returns (new_asrt, true). *)
let rec map
    (f_a_before  : (t -> t * bool) option)
    (f_a_after   : (t -> t) option)
    (f_e         : (Expr.t -> Expr.t) option)
    (a           : t) : t =

  (* Map recursively to assertions and expressions *)
  let map_a      = map f_a_before f_a_after f_e in
  let map_e      = Option.default (fun x -> x) f_e in
  let f_a_before = Option.default (fun x -> x, true) f_a_before in 
  let f_a_after  = Option.default (fun x -> x) f_a_after in 
  let (a', recurse) = f_a_before a in 

  if not recurse then a' else ( 
    let a'' =
      match a' with
      | And (a1, a2)      -> And (map_a a1, map_a a2)
      | Or (a1, a2)       -> Or (map_a a1, map_a a2)
      | Not a             -> Not (map_a a)
      | True              -> True
      | False             -> False
      | Eq (e1, e2)       -> Eq (map_e e1, map_e e2)
      | Less (e1, e2)     -> Less (map_e e1, map_e e2)
      | LessEq (e1, e2)   -> LessEq (map_e e1, map_e e2)
      | StrLess (e1, e2)  -> StrLess (map_e e1, map_e e2)
      | SetMem (e1, e2)   -> SetMem (map_e e1, map_e e2)
      | SetSub (e1, e2)   -> SetSub (map_e e1, map_e e2) 
      | ForAll (bt, a)    -> ForAll (bt, map_a a) in 
    f_a_after a''
  )


let rec fold 
  (feo      : (Expr.t -> 'a) option) 
  (f_ac     : t -> 'b -> 'b -> 'a list -> 'a)
  (f_state  : (t -> 'b -> 'b) option) 
  (state    : 'b)
  (asrt     : t) : 'a =
  
  let new_state = (Option.default (fun a x -> x) f_state) asrt state in
  let fold_a    = fold feo f_ac f_state new_state in
  let f_ac      = f_ac asrt new_state state in
  let fes les   = Option.map_default (fun fe -> List.map fe les) [] feo in

  match asrt with
  | True | False -> f_ac []
  | Eq (le1, le2) | Less (le1, le2) | LessEq (le1, le2)
  | StrLess (le1, le2) | SetMem (le1, le2)
  | SetSub (le1, le2) -> f_ac (fes [ le1; le2 ])
  | And (a1, a2)             -> f_ac [ (fold_a a1); (fold_a a2) ]
  | Or (a1, a2)              -> f_ac [ (fold_a a1); (fold_a a2) ]
  | Not a                    -> f_ac [ (fold_a a) ]
  | ForAll (_, a)            -> f_ac [ (fold_a a) ]
  

(* Get all the logical variables in --a-- *)
let lvars (a : t) : SS.t =
  let fe_ac (le : Expr.t) _ _ (ac : string list list) : string list = 
    match le with
      | Expr.LVar x -> [ x ]
      | _      -> List.concat ac in 
  let fe = Expr.fold fe_ac None None in 
  let fp_ac (a : t) _ _ (ac : string list list) : string list = 
    match (a : t) with 
      | ForAll (bt, a1) -> 
        (* Quantified variables need to be excluded *)
        let binders, _  = List.split bt in
        let ac_vars     = SS.of_list (List.concat ac) in 
        let binder_vars = SS.of_list binders in 
        SS.elements (SS.diff ac_vars binder_vars)
      | _ -> List.concat ac in
  SS.of_list (fold (Some fe) fp_ac None None a)

(* Get all the program variables in --a-- *)
let pvars (a : t) : SS.t =
  let fe_ac le _ _ ac = match le with
    | Expr.PVar x -> [ x ]
    | _      -> List.concat ac in 
  let fe = Expr.fold fe_ac None None in 
  let f_ac a _ _ ac = List.concat ac in
  SS.of_list (fold (Some fe) f_ac None None a)

(* Get all the abstract locations in --a-- *)
let rec alocs (a : t) : SS.t =
  let fe_ac le _ _ ac =
    match le with
    | Expr.ALoc l -> l :: (List.concat ac)
    | _ -> List.concat ac in
  let fe = Expr.fold fe_ac None None in 
  let f_ac a _ _ ac = List.concat ac in
  SS.of_list (fold (Some fe) f_ac None None a)


(* Get all the concrete locations in [a] *)
let rec clocs (a : t) : SS.t =
  let fe_ac le _ _ ac =
    match le with
    | Expr.Lit (Loc l) -> l :: (List.concat ac)
    | _ -> List.concat ac in
  let fe = Expr.fold fe_ac None None in 
  let f_ac a _ _ ac = List.concat ac in
  SS.of_list (fold (Some fe) f_ac None None a)

(* Returns all the non-list listerals that occur in --a-- *)
let non_list_lits (a : t) : Literal.t list =  
  let f_ac a _ _ ac = List.concat ac in
  let fe = Expr.non_list_lits in 
  fold (Some fe) f_ac None None a

(* Get all the logical expressions of --a-- of the form (Lit (LList lst)) and (EList lst)  *)
let lists (a : t) : Expr.t list =
  let f_ac a _ _ ac = List.concat ac in 
  let fe = Expr.lists in 
  fold (Some fe) f_ac None None a

(* Get all the literal numbers and string occurring in --a-- *)
let strings_and_numbers (a : t) : (string list) * (float list) =
  let lits    = non_list_lits a in
  List.fold_left (fun (strings, numbers) (lit : Literal.t) -> 
    match lit with 
    | Num n    -> (strings, n :: numbers)
    | String s -> (s :: strings, numbers)
    | _        ->  (strings, numbers)
  ) ([], []) lits


(* Get all the logical expressions of --a-- that denote a list 
   and are not logical variables *)
let list_lexprs (a : t) : Expr.t list =

  let fe_ac le _ _ ac =
    match le with
    | Expr.Lit (LList _) | Expr.EList _   | Expr.BinOp (_, LstCons, _)
    | Expr.BinOp (_, LstCat, _) | Expr.UnOp (Car, _) | Expr.UnOp (Cdr, _)
    | Expr.UnOp (LstLen, _) -> le :: (List.concat ac)
    | _ -> List.concat ac in

  let fe = Expr.fold fe_ac None None in
  let f_ac a _ _ ac = List.concat ac in
  fold (Some fe) f_ac None None a 


let rec push_in_negations_off (a : t) : t =
  let f_off   = push_in_negations_off in
  let f_on    = push_in_negations_on in
  (match a with
  | And (a1, a2)   -> And ((f_off a1), (f_off a2))
  | Or (a1, a2)    -> Or ((f_off a1), (f_off a2))
  | Not a1         -> f_on a1 
  | ForAll (bt, a) -> ForAll (bt, f_off a)
  | _ -> a)
and push_in_negations_on (a : t) : t =
  let f_off   = push_in_negations_off in
  let f_on    = push_in_negations_on in
  (match a with
  | And (a1, a2) -> Or ((f_on a1), (f_on a2))
  | Or (a1, a2)  -> And ((f_on a1), (f_on a2))
  | True         -> False
  | False        -> True
  | Not a        -> (f_off a)
  | _            -> Not a)
and push_in_negations (a : t) : t =
  push_in_negations_off a 


(** JSIL logic assertions *)
let rec str (a : t) : string =
  let sle = Expr.str in
  match a with
  (* a1 /\ a2 *)
  | And (a1, a2) -> Printf.sprintf "(%s /\\ %s)" (str a1) (str a2)
  (* a1 \/ a2 *)
  | Or (a1, a2) -> Printf.sprintf "(%s \\/ %s)" (str a1) (str a2)
  (* ! a *)
  | Not a -> Printf.sprintf "(! %s)" (str a)
  (* true *)
  | True -> "True"
  (* false *)
  | False -> "False"
  (* e1 == e2 *)
  | Eq (e1, e2) -> Printf.sprintf "(%s == %s)" (sle e1) (sle e2)
  (* e1 << e2 *)
  | Less (e1, e2) -> Printf.sprintf "(%s <# %s)" (sle e1) (sle e2)
  (* e1 <<= e2 *)
  | LessEq (e1, e2) -> Printf.sprintf "(%s <=# %s)" (sle e1) (sle e2)
  (* e1 <<s e2 *)
  | StrLess (e1, e2) -> Printf.sprintf "(%s <s# %s)" (sle e1) (sle e2)
  (* forall vars . a *)
  | ForAll (lvars, a) -> 
      Printf.sprintf "(forall %s . %s)" 
        (String.concat 
          ", "
          (List.map 
            (fun (x, t) -> 
              let t_str = Option.map_default (fun t -> " : " ^ (Type.str t)) "" t in 
              Printf.sprintf "%s%s" x t_str) lvars)) (str a)
  (* e1 --e-- e2 *)
  | SetMem (e1, e2) -> Printf.sprintf "(%s --e-- %s)" (sle e1) (sle e2)
  (* e1 --s-- e2 *)
  | SetSub (e1, e2) -> Printf.sprintf "(%s --s-- %s)" (sle e1) (sle e2)
 
 (** JSIL logic assertions *)
let rec full_str (a : t) : string =
  let f = full_str in 
  let sle = Expr.full_str in
  match a with
  (* a1 /\ a2 *)
  | And (a1, a2) -> Printf.sprintf "(%s /\\ %s)" (f a1) (f a2)
  (* a1 \/ a2 *)
  | Or (a1, a2) -> Printf.sprintf "(%s \\/ %s)" (f a1) (f a2)
  (* ! a *)
  | Not a -> Printf.sprintf "(! %s)" (f a)
  (* true *)
  | True -> "True"
  (* false *)
  | False -> "False"
  (* e1 == e2 *)
  | Eq (e1, e2) -> Printf.sprintf "(%s == %s)" (sle e1) (sle e2)
  (* e1 << e2 *)
  | Less (e1, e2) -> Printf.sprintf "(%s <# %s)" (sle e1) (sle e2)
  (* e1 <<= e2 *)
  | LessEq (e1, e2) -> Printf.sprintf "(%s <=# %s)" (sle e1) (sle e2)
  (* e1 <<s e2 *)
  | StrLess (e1, e2) -> Printf.sprintf "(%s <s# %s)" (sle e1) (sle e2)
  (* forall vars . a *)
  | ForAll (lvars, a) -> 
      Printf.sprintf "(forall %s . %s)" 
        (String.concat 
          ", "
          (List.map 
            (fun (x, t) -> 
              let t_str = Option.map_default (fun t -> " : " ^ (Type.str t)) "" t in 
              Printf.sprintf "%s%s" x t_str) lvars)) (str a)
  (* e1 --e-- e2 *)
  | SetMem (e1, e2) -> Printf.sprintf "(%s --e-- %s)" (sle e1) (sle e2)
  (* e1 --s-- e2 *)
  | SetSub (e1, e2) -> Printf.sprintf "(%s --s-- %s)" (sle e1) (sle e2)
 

let rec lift_logic_expr (e : Expr.t) : (t * t) option = 
  let f = lift_logic_expr in 
  match e with 
    | LVar x                         
    | PVar x                         -> Some (Eq (e, Lit (Bool true)), Eq (e, Lit (Bool false)))
    | Lit (Bool true)                -> Some (True, False) 
    | Lit (Bool false)               -> Some (False, True)
    | BinOp (e1, Equal, e2)          -> (let a = Eq (e1, e2)      in Some (a, Not a))
    | BinOp (e1, LessThan, e2)       -> (let a = Less (e1, e2)    in Some (a, Not a))
    | BinOp (e1, LessThanString, e2) -> (let a = StrLess (e1, e2) in Some (a, Not a))
    | BinOp (e1, LessThanEqual, e2)  -> (let a = LessEq (e1, e2)  in Some (a, Not a))
    | BinOp (e1, SetMem, e2)         -> (let a = SetMem (e1, e2)  in Some (a, Not a))
    | BinOp (e1, SetSub, e2)         -> (let a = SetSub (e1, e2)  in Some (a, Not a))
    | BinOp (e1, And, e2) -> 
        (match f e1, f e2 with 
        | Some (a1, na1), Some (a2, na2) -> Some (And (a1, a2), Or (na1, na2))
        | _ -> None) 
    | BinOp (e1, Or, e2) -> 
        (match f e1, f e2 with 
        | Some (a1, na1), Some (a2, na2) -> Some (Or (a1, a2), And (na1, na2))
        | _ -> None)
    | UnOp (Not, e') -> Option.map (fun (a, na) -> na, a) (f e')   
    | _              -> None 


let rec to_expr (a : t) : Expr.t option = 
  let f = to_expr in 
  match a with 
  | True    -> Some (Expr.Lit (Bool true))
  | False   -> Some (Expr.Lit (Bool false))
  
  | Not a' -> Option.map (fun a -> Expr.UnOp (UnOp.Not, a)) (f a')
  
  | And (a1, a2)  -> 
      (match f a1, f a2 with 
      | Some le1, Some le2 -> Some (Expr.BinOp (le1, BinOp.And, le2))
      | _ -> None)
  
  | Or (a1, a2)   -> 
      (match f a1, f a2 with 
      | Some le1, Some le2 -> Some (Expr.BinOp (le1, BinOp.And, le2))
      | _ -> None)
  
  | ForAll _ -> None

  | Eq (le1, le2)      -> Some (Expr.BinOp (le1, BinOp.Equal, le2))

  | Less (le1 , le2)   -> Some (Expr.BinOp (le1, BinOp.LessThan, le2))

  | LessEq (le1, le2)  -> Some (Expr.BinOp (le1, BinOp.LessThanEqual, le2))

  | StrLess (le1, le2) -> Some (Expr.BinOp (le1, BinOp.LessThanString, le2))

  | SetMem (le1, le2) -> Some (Expr.BinOp (le1, BinOp.SetMem, le2))

  | SetSub (le1, le2) -> Some (Expr.BinOp (le1, BinOp.SetSub, le2))

   
 (* creates a list of equalities from the substitution table *)
 (* before substitution_to_list *)
 let assertions (subst : SSubst.t) : t list =
    List.map (fun (x, x_val) -> Eq (LVar x, SVal.M.to_expr x_val)) (SVal.SSubst.to_list subst)  


let rec conjunct (asrts : t list) : t = 
  match asrts with 
    | []    -> True 
    | [ a ] -> a
    | a :: r_asrts -> And (a, conjunct r_asrts)



let rec disjunct (asrts : t list) : t = 
  match asrts with 
    | []    -> True 
    | [ a ] -> a
    | a :: r_asrts -> Or (a, disjunct r_asrts)


let substitution (subst : SSubst.t) (partial : bool) (a : t) : t = 
  let old_binders_substs = ref [] in 
  let f_before a = match a with 
    | ForAll (bt, _) -> 
      let binders, _     = List.split bt in
      let binders_substs = List.map (fun x -> Option.map (fun x_v -> x, x_v) (SSubst.get subst x)) binders in 
      let binders_substs = try List.map Option.get (List.filter (fun x -> not (x = None)) binders_substs) 
        with _ -> raise (Failure "DEATH. asrt_substitution") in 
      old_binders_substs := binders_substs; 
      List.iter 
        (fun x ->
           match SVal.M.from_expr (LVar x) with 
             | None -> raise (Failure "DEATH")
             | Some sval -> SSubst.put subst x sval)
        binders;
      a, true 
    | _ -> a, true in 
  let f_after a = match a with 
    | ForAll _ -> List.iter (fun (x, le_x) -> SSubst.put subst x le_x) !old_binders_substs; a 
    | _ -> a in 
  map (Some f_before) (Some f_after) (Some (SSubst.subst_in_expr subst partial)) a


let subst_clocs (subst : string -> Expr.t) (f : t) : t = 
  map None None (Some (Expr.subst_clocs subst)) f 


let rec get_disjuncts (fo : t) : t list = 
  (* Printf.printf "I am getting disjuncts every day!!\n"; *)
    match fo with 
      | Or (fo1, fo2) -> 
          (* Printf.printf "More than one disjunct!\n"; *)
          (get_disjuncts fo1) @ (get_disjuncts fo2)
      | _             -> [ fo ]
