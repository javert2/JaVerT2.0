open CCommon
open SCommon

(** JSIL Expressions *)
type t =
  | Lit   of Literal.t       (** JSIL literals           *)
  | PVar  of string          (** JSIL program variables  *)
  | LVar  of string          (** JSIL logical variables  *)
  | ALoc  of string          (** JSIL abstract locations *)
  | UnOp  of UnOp.t * t      (** Unary operators         *)
  | BinOp of t * BinOp.t * t (** Binary operators        *)
  | NOp   of NOp.t * t list  (** n-ary operators         *)
  | EList of t list          (** Lists of expressions    *)
  | ESet  of t list          (** Sets of expressions     *)
  | Nono                     (** Absence of resource     *)

module MyExpr =
  struct
    type nonrec t = t
    let compare = Pervasives.compare
  end

module Set = Set.Make(MyExpr)
module Map = Map.Make(MyExpr)

(** Map over expressions *)
let rec map 
  (f_before : t  -> t * bool) 
  (f_after  : (t -> t) option)
  (expr    : t) : t =
  (* Apply the mapping *)
  let map_e   = map f_before f_after in
  let f_after = Option.default (fun x -> x) f_after in 
  
  let (mapped_expr, recurse) = f_before expr in
  if not recurse then
    mapped_expr
  else ( 
    (* Map recursively to expressions *)
    let mapped_expr = 
      match mapped_expr with
        | Lit _  | PVar _ 
        | LVar _ | ALoc _     
        | Nono                -> mapped_expr
        | UnOp (op, e)        -> UnOp (op, map_e e)
        | BinOp (e1, op, e2)  -> BinOp (map_e e1, op, map_e e2)
        | NOp (op, es)        -> NOp (op, List.map map_e es)
        | EList es            -> EList (List.map map_e es)
        | ESet es             -> ESet (List.map map_e es) in 
    f_after mapped_expr
  )

(** Optional map over expressions *)
let rec map_opt
  (f_before : t -> (t option) * bool) 
  (f_after  : (t -> t) option)
  (expr     : t) : t option =
  (* Apply the mapping *)
  let map_e   = map_opt f_before f_after in
  let f_after = Option.default (fun x -> x) f_after in 
  
  let aux args f = 
    let args' = List.map map_e args in 
    if (List.exists (fun arg -> arg = None) args') 
      then None 
      else Some (f (List.map Option.get args')) in 

  match f_before expr with 
  | None, _ -> None 
  | mapped_expr, false -> mapped_expr
  | Some mapped_expr, true -> 
    (* Map recursively to expressions *)
      let mapped_expr = 
        (match mapped_expr with
        | Lit _ | Nono | LVar _ | ALoc _ | PVar _ -> Some mapped_expr
        | UnOp (op, e)       -> Option.map (fun e -> UnOp (op, e)) (map_e e)
        | BinOp (e1, op, e2) -> 
            (match map_e e1, map_e e2 with 
            | Some e1', Some e2' -> Some (BinOp (e1', op, e2'))
            | _ -> None)
        | NOp (op, les)      -> aux les (fun les -> NOp (op, les)) 
        | EList les          -> aux les (fun les -> EList les) 
        | ESet les           -> aux les (fun les -> ESet les)) in   
      Option.map f_after mapped_expr

(** Printer *)
let rec str (e : t) : string  =
  match e with
  | Lit l -> Literal.str l
  | PVar v | LVar v | ALoc v -> v
  (* (e1 bop e2) *)
  | BinOp (e1, op, e2) -> 
    (match op with 
    | LstNth 
    | StrNth -> Printf.sprintf "%s(%s, %s)" (BinOp.str op) (str e1) (str e2)
    | _      -> Printf.sprintf "(%s %s %s)" (str e1) (BinOp.str op) (str e2))
  (* (uop e) *)
  | UnOp (op, e) -> Printf.sprintf "(%s %s)" (UnOp.str op) (str e)
  | EList ll -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map str ll))
  (* -{ e1, e2, ... }- *)
  | ESet ll -> Printf.sprintf "-{ %s }-" (String.concat ", " (List.map str ll))
  | NOp (op, le) -> Printf.sprintf "%s (%s)" (NOp.str op) (String.concat ", " (List.map str le))
  | Nono -> "none"

(** Explicit Printer *)
let rec full_str (e : t) : string  =
  let str = full_str in 
  match e with
  | Lit l -> "(Lit " ^ Literal.str l ^ ")"
  | PVar v -> "PVar " ^ v  
  | LVar v -> "LVar " ^ v 
  | ALoc v -> "ALoc " ^ v
  (* (e1 bop e2) *)
  | BinOp (e1, op, e2) -> 
    (match op with 
    | LstNth 
    | StrNth -> Printf.sprintf "(BinOp: %s(%s, %s))" (BinOp.str op) (str e1) (str e2)
    | _      -> Printf.sprintf "(BinOp: (%s %s %s))" (str e1) (BinOp.str op) (str e2))
  (* (uop e) *)
  | UnOp (op, e) -> Printf.sprintf "(UnOp (%s %s))" (UnOp.str op) (str e)
  | EList ll -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map str ll))
  (* -{ e1, e2, ... }- *)
  | ESet ll -> Printf.sprintf "-{ %s }-" (String.concat ", " (List.map str ll))
  | NOp (op, le) -> Printf.sprintf "(NOp %s (%s))" (NOp.str op) (String.concat ", " (List.map str le))
  | Nono -> "none"

(** From expression to expression *)
let to_expr (le : t) : t = le 

(** From expression to list, if possible *)
let to_list (le : t) : t list option = (match le with 
  | EList les -> Some les 
  | Lit (LList les) -> Some (List.map (fun x -> Lit x) les)
  | _ -> None) 

(** From list to expression *)
let from_list les = EList les 

(** Fold *)
let rec fold 
  (f_ac    : t -> 'b -> 'b -> 'a list -> 'a) 
  (f_state : (t -> 'b -> 'b) option)
  (state   : 'b) 
  (expr    : t) : 'a =

  let new_state = (Option.default (fun le x -> x) f_state) expr state in
  let fold_e    = fold f_ac f_state new_state in
  let f_ac      = f_ac expr new_state state in

    match expr with
    | Lit _  | Nono 
    | LVar _ | ALoc _ 
    | PVar _             -> f_ac []
    | UnOp (op, e)       -> f_ac [ (fold_e e) ]
    | BinOp (e1, op, e2) -> f_ac [ (fold_e e1); (fold_e e2) ]
    | NOp (_, les)        
    | EList les            
    | ESet les           -> f_ac (List.map fold_e les)


(** Get all the program variables in --e-- *)
let pvars (e : t) : SS.t =
  let fe_ac e _ _ ac = match e with
    | PVar x -> [ x ]
    | _      -> List.concat ac in 
  SS.of_list (fold fe_ac None None e)

(** Get all the logical variables in --e-- *)
let lvars (le : t) : SS.t =
  let fe_ac le _ _ ac = match le with
    | LVar x -> [ x ]
    | _      -> List.concat ac in 
  SS.of_list (fold fe_ac None None le)

(** Get all the abstract locations in --e-- *)
let alocs (le : t) : SS.t =
  let fe_ac le _ _ ac = match le with
    | ALoc x -> [ x ]
    | _      -> List.concat ac in 
  SS.of_list (fold fe_ac None None le)

(** Get all the concrete locations in --e-- *)
let rec clocs (le : t) : SS.t =
  let fe_ac le _ _ ac =
    match le with
    | Lit (Loc l) -> l :: (List.concat ac)
    | _ -> List.concat ac in
  SS.of_list (fold fe_ac None None le)

(** Get all substitutables in --e-- *)
let substitutables (le : t) : SS.t = 
  let fe_ac le _ _ ac = match le with
    | LVar x 
    | ALoc x -> [ x ]
    | _      -> List.concat ac in 
  SS.of_list (fold fe_ac None None le)

(** Is --e-- concrete? *)
let rec is_concrete (le : t) : bool =
  let f = is_concrete in 

  let rec loop les =
    (match les with 
    | [] -> true
    | le :: rest -> 
        if (f le) 
          then loop rest
          else false) in 

  (match le with
  | Lit   _    
  | PVar  _ 
  | Nono  -> true
  | LVar  _
  | ALoc  _ -> false
  | UnOp  (_, e) -> loop [ e ]
  | BinOp (e1, _, e2) -> loop [ e1; e2 ]
  | NOp   (_, les)  
  | EList les
  | ESet  les -> loop les)

(** Get all the variables in --e-- *)
let vars (le : t) : SS.t =
  let fe_ac le _ _ ac = match le with
    | PVar x
    | LVar x 
    | ALoc x 
    | Lit (Loc x) -> [ x ]
    | _      -> List.concat ac in 
  SS.of_list (fold fe_ac None None le)

(** Are all expressions in the list literals? *)
let all_literals les = List.for_all (fun x -> (match x with | Lit _ -> true | _ -> false)) les 

(** Lifting literal lists to lists of expressions *)
let rec from_lit_list (lit : Literal.t) : t =
  let f = from_lit_list in 
  match lit with
  | LList lst -> EList (List.map f lst)
  | _ -> Lit lit

(** Get all non-list literals that occur in --e-- *)
let non_list_lits (le : t) : Literal.t list =
  let fe_ac le _ _ ac = match le with
    | Lit lit -> lit :: (List.concat ac)
    | _       -> List.concat ac in 

  let flit_ac (lit : Literal.t) _ _ ac = match lit with 
    | LList lst -> List.concat ac 
    | _         -> [ lit ] in 

  let lits : Literal.t list = fold fe_ac None None le in
  List.concat (List.map (Literal.fold flit_ac None None) lits) 

(** Get all sub-expressions of --e-- of the form (Lit (LList lst)) and (EList lst)  *)
let lists (le : t) : t list =
  let fe_ac le _ _ ac =
    match le with
    | Lit (LList ls)           -> [ (EList (List.map (fun x -> Lit x) ls)) ]
    | EList les                -> (EList les) :: (List.concat ac)
    | BinOp(le1, LstCat, le2)  -> le :: le1 :: le2 :: (List.concat ac)
    | BinOp(_, LstCons, tail)  -> le :: tail :: (List.concat ac)
    | _               -> List.concat ac in 
  fold fe_ac None None le 

(** Base elements for predicate unfolding *)
let rec base_elements (e : t) : t list = 
  let f = base_elements in 
  (match e with 
  | Lit lit -> List.map (fun lit -> Lit lit) (Literal.base_elements lit)
  | PVar  _  -> []
  | LVar x 
  | ALoc x   -> [ e ]
  | UnOp (_, e) -> f e 
  | BinOp (e1, _, e2) -> f e1 @ f e2
  | NOp (_, es) 
  | EList es 
  | ESet es -> List.concat (List.map f es)
  | Nono -> [])


let subst_clocs (subst : string -> t) (e : t) : t = 
  let f_before e = 
    match e with 
      | Lit (Loc loc) -> subst loc, false 
      | _ -> e, true in 
  map f_before None e 
   