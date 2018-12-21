module L = Logging

module SSubst = SVal.SSubst

(* ******************** *)
(* ** TYPE INFERENCE ** *)
(* ******************** *)

let rec infer_types_to_gamma 
  flag 
  (gamma      : TypEnv.t) 
  (new_gamma  : TypEnv.t) 
  (le         : Expr.t) 
  (tt         : Type.t) : bool =

  let f = infer_types_to_gamma flag gamma new_gamma in
  
  (match le with
  (* Literals are always typable *)
  | Lit lit -> (Literal.type_of lit = tt)

  (* Variables are reverse-typable if they are already typable *)
  (* with the target type or if they are not typable           *)
  | LVar var
  | PVar var ->
    (match (TypEnv.get gamma var), (TypEnv.get new_gamma var) with
    | Some t, None
    | None, Some t     -> (t = tt)
    | None, None       -> (TypEnv.update new_gamma var (Some tt)); true
    | Some t1, Some t2 -> t1 = t2)

  (* Abstract locations are reverse-typable if the target type is ObjectType *)
  | ALoc _ -> tt = ObjectType

    (* EList and ESet are not reverse typable because we lose type information *)
  | EList _ -> if flag then (tt = ListType) else false      
  | ESet  _ -> if flag then (tt =  SetType) else false      

  (* Members of unions and intersections must all be sets *)
  | NOp (SetUnion, les)
  | NOp (SetInter, les) -> (tt = SetType) && (List.for_all (fun x -> f x SetType) les) 

  | UnOp (unop, le) ->
    (match unop with
    | Not -> (tt = BooleanType) && (f le BooleanType)

    | M_isNaN -> (tt = BooleanType) && (f le NumberType)

    | UnaryMinus  | BitwiseNot  | M_sgn   | M_abs   
    | M_acos    | M_asin    | M_atan  | M_ceil
    | M_cos     | M_exp     | M_floor | M_log   
    | M_round   | M_sin     | M_sqrt  | M_tan
    | ToIntOp   | ToUint16Op  | ToInt32Op | ToUint32Op -> (tt = NumberType) && (f le NumberType)

    | ToStringOp -> (tt = StringType) && (f le NumberType)
    | ToNumberOp -> (tt = NumberType) && (f le StringType)

    | TypeOf      -> (tt = TypeType)

    | Cdr    -> (tt = ListType) && (f le ListType)
    | Car    -> f le ListType
    | LstLen -> (tt = NumberType) && (f le ListType)
    | LstRev -> (tt = ListType) && (f le ListType)
    | StrLen -> (tt = NumberType) && (f le StringType))


  | BinOp (le1, op, le2) ->
    let (rqt1 : Type.t option), (rqt2 : Type.t option), (rt : Type.t option) =
      (match op with
      | Equal          ->             None,             None, Some BooleanType
      | LessThan            
      | LessThanEqual  ->  Some NumberType,  Some NumberType, Some BooleanType
      | LessThanString ->  Some StringType,  Some StringType, Some BooleanType
      | And            -> Some BooleanType, Some BooleanType, Some BooleanType
      | Or             -> Some BooleanType, Some BooleanType, Some BooleanType
      | LstCons        ->             None,    Some ListType, Some ListType   
      | LstCat         ->    Some ListType,    Some ListType, Some ListType   
      | StrCat         ->  Some StringType,  Some StringType, Some StringType
      | SetMem         ->             None,     Some SetType, Some BooleanType
      | SetDiff        ->     Some SetType,     Some SetType, Some SetType
      | SetSub         ->     Some SetType,     Some SetType, Some BooleanType   
      | LstNth         ->    Some ListType,  Some NumberType, None 
      | StrNth         ->    Some ListType,  Some NumberType, None
      | _              ->  Some NumberType,  Some NumberType, Some NumberType
      ) in
    (Option.map_default (fun t -> f le1 t) true rqt1) &&
    (Option.map_default (fun t -> f le2 t) true rqt2) && 
    (match rt with 
    | None -> true
    | Some rt -> (tt = rt))

    | Nono -> (tt = NoneType))

let reverse_type_lexpr flag gamma le le_type : TypEnv.t option =
  let new_gamma = TypEnv.init () in
  let ret = infer_types_to_gamma flag gamma new_gamma le le_type in
    if (ret) then Some new_gamma else None

let safe_extend_gamma (gamma : TypEnv.t) (le : Expr.t) (t : Type.t) : unit = 
  let new_gamma = reverse_type_lexpr true gamma le t in
    (match new_gamma with
    | Some new_gamma -> TypEnv.extend gamma new_gamma
    | None -> 
      let msg = Printf.sprintf "ERROR: Safe Extend Gamma: Untypable expression: %s in %s" (Expr.str le) (TypEnv.str gamma) in
        L.fail msg) 


(* Destructively extend gamma with typing information from logic expressions *)
let rec infer_types_expr gamma le : unit =
  let f = infer_types_expr gamma in
  let e = safe_extend_gamma gamma in

    (match (le : Expr.t) with
    
    (* Do nothing, these cases do not provide additional information *)
    | Lit  _
    | ALoc  _
    | LVar  _
    | PVar  _
    | Nono   -> ()

    (* Set union and intersection - all members must be sets, plus any additional information from the members themselves *)
    | NOp (SetUnion, lle)
    | NOp (SetInter, lle) -> 
        e le SetType;
        List.iter (fun le -> f le) lle
        
    | EList lle 
    | ESet  lle -> 
      List.iter (fun le -> f le) lle
    
    | BinOp (le1, op, le2) ->
      (match op with
      | Plus | Minus | Times | Div | Mod ->
          e le1 NumberType;
          e le2 NumberType;
      | LstCons ->
          f le1;
          e le2 ListType;
      | LstCat ->
          e le1 ListType;
          e le2 ListType
      | LstNth ->
          e le1 ListType;
          e le2 NumberType
      
      | StrNth ->
        e le1 StringType;
        e le2 NumberType

      | _ -> ())
  
    | _ -> ())



let rec infer_types_formula (gamma : TypEnv.t) (a : Formula.t) : unit =
  let f  = infer_types_formula gamma in
  let fe = infer_types_expr gamma in
  let e  = safe_extend_gamma gamma in

  (match a with
    (* LForAll can be more precise *)
    | True | False | ForAll _         -> ()
    | Not a                           -> f a
    | And  (a1, a2) | Or (a1, a2)     -> f a1; f a2
    | Less (e1, e2) | LessEq (e1, e2) -> e e1 NumberType; e e2 NumberType
    | StrLess (e1, e2) -> e e1 StringType; e e2 StringType
    | SetMem (e1, e2)  -> e e2 SetType
    | SetSub (e1, e2)  -> e e1 SetType; e e2 SetType
    | _ -> ()) 



let rec infer_types_asrt (gamma : TypEnv.t) (a : Asrt.t) : unit =
  let f  = infer_types_asrt gamma in
  let fe = infer_types_expr gamma in
  let e  = safe_extend_gamma gamma in
  (match a with
    | Pure f                   -> infer_types_formula gamma f 
    | Star (a1, a2)            -> f a1; f a2 
    | PointsTo (le1, le2, le3) -> fe le1; fe le2; fe le3
    | MetaData (le1, le2)      -> fe le1; fe le2 
    | _ -> ()) 
    

(*****************)
(* Type checking *)
(*****************)

let rec type_lexpr (gamma : TypEnv.t) (le : Expr.t) : Type.t option * bool * Formula.t list =

  let f = type_lexpr gamma in
  let def_pos (ot : Type.t option) = (ot, true, []) in
  let def_neg = (None, false, []) in

  let infer_type le tt constraints = 
    let outcome = reverse_type_lexpr true gamma le tt in
      Option.map_default 
      (fun new_gamma -> 
        TypEnv.extend gamma new_gamma;
        (Some tt, true, constraints)
      ) def_neg outcome in

  let typable_list ?(target_type : Type.t option) les = 
    (List.fold_left
      (fun (ac, ac_constraints) elem ->
        if (not ac) then (false, [])
        else 
          let (t, ite, constraints) = 
            let (t, ite, constraints) = f elem in
            (match t with 
            | Some _ -> (t, ite, constraints)
            | None -> (match target_type with 
              | None -> (t, ite, constraints)
              | Some tt -> infer_type elem tt constraints
              )
            ) in 
          let correct_type = (target_type = None) || (t = target_type) in
          (ac && correct_type && ite, constraints @ ac_constraints))
      (true, [])
      les) in

  let result = (match le with

  (* Literals are always typable *)
  | Lit lit -> def_pos (Some (Literal.type_of lit))

  (* Variables are typable if in gamma, otherwise no, but typing continues *)
  | LVar var
  | PVar var -> def_pos (TypEnv.get gamma var)

  (* Abstract locations are always typable, by construction *)
  | ALoc _ -> def_pos (Some ObjectType)

    (* Lists are always typable *)
  | EList les -> Some ListType, true, [] 

  (* Sets are always typable *)
  | ESet les -> Some SetType, true, []

  | UnOp (unop, e) ->
    let (_, ite, constraints) = f e in

    (match ite with
    | false -> def_neg
    | true -> 
      let (tt : Type.t), new_constraints = 
      (match unop with
      | TypeOf      -> TypeType,    []
      | Not         
      | M_isNaN     -> BooleanType, []
      | ToStringOp  -> StringType,  []
      | Car | Cdr   -> ListType,    [ (Formula.LessEq (Lit (Num 1.), UnOp (LstLen, e))) ]
      | LstRev      -> ListType,    []
      | _           -> NumberType,  []
      ) in
      infer_type le tt (new_constraints @ constraints))

  | BinOp (e1, op, e2) ->
    let (_, ite1, constraints1) = f e1 in
    let (_, ite2, constraints2) = f e2 in
    let constraints = constraints1 @ constraints2 in

    (* Both expressions must be typable *)
    (match ite1, ite2 with
    | true, true -> 

      (match op with 

      (* List length is typable with constraints *)
      | LstNth ->
        let _, success, _ = infer_type e1 ListType constraints in
        (match success with
        | false -> def_neg
        | true -> 
          let _, success, _ = infer_type e2 NumberType constraints in
          (match success with
          | false -> def_neg
          | true -> 
            let new_constraint1 : Formula.t = (LessEq (Lit (Num 0.), e2)) in
            let new_constraint2 : Formula.t = (Less (e2, UnOp (LstLen, e1))) in
            (None, true, (new_constraint1 :: (new_constraint2 :: constraints)))
          )
        )

      (* String length is typable with constraints *)
      | StrNth ->
        let _, success, _ = infer_type e1 StringType constraints in
        (match success with
        | false -> def_neg
        | true -> 
          let _, success, _ = infer_type e2 NumberType constraints in
          (match success with
          | false -> def_neg
          | true -> 
            let new_constraint1 : Formula.t = (LessEq (Lit (Num 0.), e2)) in
            let new_constraint2 : Formula.t = (Less (e2, UnOp (StrLen, e1))) in
            (None, true, (new_constraint1 :: (new_constraint2 :: constraints)))
          )
        )

      | _ -> let tt : Type.t =
        (match op with
        | Equal     | LessThan    | LessThanEqual | LessThanString 
        | And     | Or      | SetMem    | SetSub -> BooleanType
        | LstCons   | LstCat -> ListType   
        | SetDiff -> SetType    
        | StrCat  -> StringType
        | _       -> NumberType
        ) in
        infer_type le tt constraints)

    | _, _ -> def_neg)
    
  | NOp (SetUnion, les)
  | NOp (SetInter, les) -> 
      let all_typable, constraints = typable_list ?target_type:(Some SetType) les in
      if (all_typable) then (Some SetType, true, constraints) else def_neg

  | Nono -> (Some NoneType, true, [])) in

  result

let te_of_list (vt : (Expr.t * Type.t) list) : TypEnv.t option = 
  let result = TypEnv.init () in 
    try (List.iter (fun (e, t) -> 
      (match (e : Expr.t) with 
      | Lit l -> let t' = Literal.type_of l in
          if (t <> t') then raise (Failure "TypEnv: of_list: Type mismatch")
      | LVar x
      | PVar x -> if (TypEnv.mem result x) then 
          (let t' = TypEnv.get_unsafe result x in 
            if (t <> t' ) then raise (Failure "TypEnv: of_list: Type mismatch"))
          else TypEnv.update result x (Some t)
      | _ -> 
          let t', _, _ = type_lexpr result e in 
          (match t' with 
          | Some t' when (t = t') -> ()
          | _ -> raise (Failure (Printf.sprintf "TypEnv: of_list: Type mismatch"))))) vt;
    Some result)
    with | Failure "TypEnv: of_list: Type mismatch" -> None


let naively_infer_type_information (p_assertions : PFS.t) (gamma : TypEnv.t) : unit = 
  DynArray.iter 
    (fun a -> 
      match (a : Formula.t) with 
      | Eq (LVar x, le) 
      | Eq (le, LVar x) -> 
        if (not (TypEnv.mem gamma x)) 
          then (
            let le_type, _, _ = type_lexpr gamma le in
            TypEnv.weak_update gamma x le_type
          )
      | Eq ((UnOp (TypeOf, LVar x)), (Lit (Type t))) 
      | Eq ((Lit (Type t)), (UnOp (TypeOf, LVar x))) ->
        TypEnv.weak_update gamma x (Some t)
      | _ -> () 
    ) p_assertions


let rec substitution_in_place (subst : SSubst.t) (gamma : TypEnv.t) : unit =
  TypEnv.iter gamma
    (fun x x_type ->
      let new_x = SSubst.get subst x in
      match new_x with
        | Some (LVar new_x) -> TypEnv.update gamma x (Some x_type)
        | Some (Lit _)      -> TypEnv.update gamma x None
        | Some le           -> safe_extend_gamma gamma le x_type  
        | None              -> ())



