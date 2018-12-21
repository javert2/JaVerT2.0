open CCommon
open SCommon
open SVal

module L = Logging

exception FoundIt of Expr.t
exception UnionInUnion of Expr.t list

let interactive = ref false 

let rec find_me_Im_a_loc pfs lvar = 
  match (pfs : Formula.t list) with 
  | [] -> None 
  | Eq (lvar', Expr.ALoc loc) :: rest
  | Eq (lvar', Lit (Loc loc))  :: rest
  | Eq (ALoc loc, lvar') :: rest
  | Eq ( Lit (Loc loc), lvar') :: rest ->
    if (lvar = lvar') 
      then Some loc 
      else find_me_Im_a_loc rest lvar
  | _ :: rest -> find_me_Im_a_loc rest lvar

let find_me_in_the_pi pfs nle =
  DynArray.fold_left (fun ac a -> 
      (match (a : Formula.t) with 
      | Eq (LVar lvar, le)
      | Eq (le, LVar lvar) -> 
        if (le = nle) 
          then Some lvar
          else ac
      | _ -> ac)
      ) None pfs

let rec replace_nle_with_lvars pfs nle = 
  (match nle with 
  | Expr.BinOp (le, op, le') -> 
    (match find_me_in_the_pi pfs nle with 
    | Some lvar -> (Expr.LVar lvar)
    | None -> 
      let lhs = replace_nle_with_lvars pfs le in
      let rhs = replace_nle_with_lvars pfs le' in
      let lhs_string = Expr.str lhs in
      (BinOp (lhs, op, rhs)))
  | UnOp (op, le) -> 
    (match find_me_in_the_pi pfs nle with 
    | Some lvar -> (LVar lvar)
    | None -> (UnOp (op, (replace_nle_with_lvars pfs le))))
  | EList le ->
    (match find_me_in_the_pi pfs nle with 
    | Some lvar -> (LVar lvar)
    | None -> 
      let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
      (EList le_list))
  | ESet le -> 
    (match find_me_in_the_pi pfs nle with 
    | Some lvar -> (LVar lvar)
    | None -> 
      let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
      (ESet le_list))
  | NOp (op, le) -> 
    (match find_me_in_the_pi pfs nle with 
    | Some lvar -> (LVar lvar)
    | None -> 
      let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
        NOp (op, le_list))
  | _ -> nle)

let all_set_literals lset = List.fold_left (fun x le -> 
  let result = (match le with
    | Expr.ESet _ -> true
    | _ -> false) in
  x && result
  ) true lset 

(* Reduction of assertions *)



let rec reduce_formula ?(no_timing: unit option) ?(gamma : TypEnv.t option) ?(pfs : PFS.t option) (a : Formula.t) : Formula.t =

  (* let start_time = Sys.time () in *)

  let f = reduce_formula ~no_timing:() ?gamma:gamma ?pfs:pfs in
  let fe = Reduction.reduce_lexpr ?gamma:gamma ?pfs:pfs in

  let result : Formula.t = (match a with

  | And (a1, a2) ->
    let fa1 = f a1 in
    let fa2 = f a2 in
    (match fa1, fa2 with
    | False, _
    | _, False -> False
    | True, a
    | a, True -> a
    | _, _ -> And (fa1, fa2)
    )

  | Or (a1, a2) ->
    let fa1 = f a1 in
    let fa2 = f a2 in
    (match fa1, fa2 with
    | False, a
    | a, False -> a
    | True, a
    | a, True -> True
    | _, _ -> Or (fa1, fa2)
    )
  
  (** JOSE: why the recursive call? *)
  | Not a -> 
    let fa = f a in 
    (match a with 
    | True -> False
    | False -> True
    | Not a -> a
    | Or (a1, a2)  -> f (And (Not a1, Not a2))
    | And (a1, a2) -> f (Or (Not a1, Not a2))
    | _ -> Not fa)

   
  | Eq (e1, e2) ->
    let re1 = fe e1 in
    let re2 = fe e2 in
    (* Warning - NaNs, infinities, this and that, this is not good enough *)
    let eq = (re1 = re2) in
    if eq then True
    else
      let n_gamma = (match gamma with | Some gamma -> gamma | None -> TypEnv.init ()) in 
      let t1, s1, _ = Typing.type_lexpr n_gamma re1 in
      let t2, s2, _ = Typing.type_lexpr n_gamma re2 in
      if s1 && s2 && (match t1, t2 with | Some t1, Some t2 -> t1 <> t2 | _, _ -> false) then False else
        let ite a b : Formula.t = if (a = b) then True else False in
        let default e1 e2 re1 re2 : Formula.t = 
          let a' : Formula.t = Eq (re1, re2) in
            if ((re1 = e1) && (re2 = e2))
              then a' else f a' in
        
        (match re1, re2 with
          | EList [], x
          | x, EList []
          | Lit (LList []), x
          | x, Lit (LList []) -> 
            (match x with 
            | Lit (LList lst) when List.length lst > 0 -> False
            | EList lst when List.length lst > 0 -> False
            | BinOp (_, LstCat, EList x) when List.length x > 0 -> False
            | BinOp (EList x, LstCat, _) when List.length x > 0 -> False
            | BinOp (Lit (LList x), LstCat, _) when List.length x > 0 -> False
            | BinOp (_, LstCat, Lit (LList x)) when List.length x > 0 -> False
            | _ -> Eq (re1, re2))

          | UnOp (LstLen, le), Lit (Num n) 
          | Lit (Num n), UnOp (LstLen, le) -> 
              (match (Arith_Utils.is_int n) with 
              | false -> False
              | true -> 
                  let n = int_of_float n in 
                  let le' = Array.to_list (Array.init n (fun _ -> Expr.LVar (fresh_lvar()))) in 
                  Eq (le, EList le'))

          (* 
          | UnOp (Car, ll), le
          | le, UnOp (Car, ll) -> f (Eq (ll, BinOp (le, LstCons, LVar (fresh_lvar ())) ))

          | UnOp (Cdr, ll), ll'
          | ll', UnOp (Cdr, ll) -> f (Eq (ll, BinOp (LVar (fresh_lvar ()), LstCons, ll'))) *)
          
          | UnOp  (LstRev, ll), UnOp (LstRev, rl) -> f (Eq (ll, rl))
          | UnOp  (LstRev, full_list), BinOp (UnOp (LstRev, plist_left), LstCat, plist_right)
          | BinOp (UnOp (LstRev, plist_left), LstCat, plist_right), UnOp (LstRev, full_list) 
              ->
              f (Eq (full_list, BinOp (UnOp (LstRev, plist_right), LstCat, plist_left)))

          | le1, le2 when (
              (match le1 with | LVar _ -> false | _ -> true) &&
              (match le2 with | LVar _ -> false | _ -> true) && 
              (Reduction.lexpr_is_list ?gamma:gamma le1) && 
              (Reduction.lexpr_is_list ?gamma:gamma le2) 
            ) ->
              let htl1, htl2 = Reduction.get_head_and_tail_of_list ?pfs:pfs Expr.Set.empty le1, Reduction.get_head_and_tail_of_list ?pfs:pfs Expr.Set.empty le2 in 
              (match htl1, htl2 with 
              | Some (hl1, tl1), Some (hl2, tl2) -> f (And (Eq (hl1, hl2), Eq (tl1, tl2)))
              | None, Some _ -> (match le1 with | Lit (LList _) | EList _ -> False | _ -> Eq (re1, re2))
              | Some _, None -> (match le2 with | Lit (LList _) | EList _ -> False | _ -> Eq (re1, re2))
              | None, None -> Eq (re1, re2))

          (* Strings #1 *)
          | Lit (String ls), BinOp (Lit (String rs), StrCat, s)
          | BinOp (Lit (String rs), StrCat, s), Lit (String ls) -> 
              let lls = String.length ls in 
              let lrs = String.length rs in 
              (match (Pervasives.compare lls lrs) with 
              | -1 -> False
              |  0 -> if (ls <> rs) then False else (f (Eq (s, Lit (String ""))))
              |  1 -> 
                  let sub = String.sub ls 0 lrs in 
                    if (sub <> rs) then False else (f (Eq (s, Lit (String (String.sub ls lrs (lls - lrs))))))
              )

          (* String #2 *)
          | BinOp (sl1, StrCat, sr1), BinOp (sl2, StrCat, sr2) when sl1 = sl2 -> f (Eq (sr1, sr2))
          | BinOp (sl1, StrCat, sr1), BinOp (sl2, StrCat, sr2) when sr1 = sr2 -> f (Eq (sl1, sl2))

          (* String #3 *)
          | BinOp (sl, StrCat, sr), s when sl = s   -> f (Eq (sr, Lit (String "")))
          | BinOp (sl, StrCat, sr), s when sr = s   -> f (Eq (sl, Lit (String "")))
          | s, BinOp (sl, StrCat, sr) when sl = s   -> f (Eq (sr, Lit (String "")))
          | s, BinOp (sl, StrCat, sr) when sr = s   -> f (Eq (sl, Lit (String "")))
          | BinOp (sl, StrCat, sr), Lit (String "") -> f (And (Eq (sl, Lit (String "")), Eq (sr, Lit (String ""))))

          (* Num-to-String injectivity *)
          | UnOp (ToStringOp, le1), UnOp (ToStringOp, le2) -> f (Eq (le1, le2))

          (* Num-to-String understanding *)
          | UnOp (ToStringOp, le1), Lit (String s)
          | Lit (String s), UnOp (ToStringOp, le1) -> 
              (match s with 
              | "" -> False
              | "Infinity" | "-Infinity" | "NaN" -> default e1 e2 re1 re2
              | _ -> 
                  let num = try Some (Batteries.Float.of_string s) with _ -> None in
                  (match num with 
                  | Some num -> Eq (le1, Lit (Num num))
                  | None -> False
                  )
              )

          | BinOp (le1, Equal, le2), Lit (Bool true) 
          | Lit (Bool true), BinOp (le1, Equal, le2) -> f (Eq (le1, le2))

          | BinOp (le1, Equal, le2), Lit (Bool false) 
          | Lit (Bool false), BinOp (le1, Equal, le2) -> f (Not (Eq (le1, le2)))

          (* The empty business *)
          | _, Lit Empty -> (match re1 with
            | Lit l when (l <> Empty) -> False
            | EList _ 
            | ESet _ -> False
            | _ -> default e1 e2 re1 re2)

          | Lit l1, Lit l2 -> ite l1 l2
          | Nono, PVar x
          | PVar x, Nono -> default e1 e2 re1 re2
          (** JOSE: Why are we considering the case of a logical variable being bound to None? *)
          | Nono, LVar x
          | LVar x, Nono -> 
            (match gamma with
              | None -> default e1 e2 re1 re2
              | Some gamma -> let tx = TypEnv.get gamma x in
                (match tx with 
                  | None -> default e1 e2 re1 re2
                  | Some tx -> if tx = NoneType then default e1 e2 re1 re2 else False))
          | Nono, e
          | e, Nono -> False

          | Lit (Bool true), BinOp (e1, LessThan, e2) -> Less (e1, e2)
          | Lit (Bool false), BinOp (e1, LessThan, e2) -> Not (Less (e1, e2))

          (* Plus theory -> theory? I would not go that far *)
          | BinOp (re1', Plus, Lit (Num n1)), BinOp (re2', Plus, Lit (Num n2))
          | BinOp (re1', Plus, Lit (Num n1)), BinOp (Lit (Num n2), Plus, re2')
          | BinOp (Lit (Num n1), Plus, re1'), BinOp (re2', Plus, Lit (Num n2))
          | BinOp (Lit (Num n1), Plus, re1'), BinOp (Lit (Num n2), Plus, re2') ->
              let isn1 = Arith_Utils.is_normal n1 in
              let isn2 = Arith_Utils.is_normal n2 in
              if (isn1 && isn2)
                then (
                  if (n1 < n2) then f (Eq (re1', BinOp (re2', Plus, Lit (Num (n2 -. n1))))) else
                  if (n1 = n2) then f (Eq (re1', re2')) else
                    f (Eq (BinOp (re1', Plus, Lit (Num (n1 -. n2))), re2'))
                ) else default e1 e2 re1 re2
            
          (* More Plus theory *)
          | BinOp (re1', Plus, Lit (Num n1)), Lit (Num n2)
          | Lit (Num n2), BinOp (re1', Plus, Lit (Num n1)) ->
              let isn1 = Arith_Utils.is_normal n1 in
              let isn2 = Arith_Utils.is_normal n2 in
              if (isn1 && isn2)
                then f (Eq (re1', Lit (Num (n2 -. n1))))
                else default e1 e2 re1 re2

          (* Nil *)
          | BinOp (l1, LstCat, l2), Lit (LList []) ->
              f (And (Eq (l1, Lit (LList [])), Eq (l2, Lit (LList []))))

          (* Very special cases *)
          | UnOp (TypeOf, (BinOp (_, StrCat, _))), Lit (Type t) when (t <> StringType)  -> False
          | UnOp (TypeOf, (BinOp (_, SetMem, _))), Lit (Type t) when (t <> BooleanType) -> False

          (* Set unions *)
          | NOp (SetUnion, [ ls; ESet [ lx ] ]), NOp (SetUnion, [ rs; ESet [ rx ] ]) when (lx = rx) -> 
              (match pfs with 
              | None -> default e1 e2 re1 re2
              | Some pfs -> 
                  if (PFS.mem pfs (Not (SetMem (lx, ls)))) && (PFS.mem pfs (Not (SetMem (lx, rs)))) 
                    then f (Eq (ls, rs))
                    else default e1 e2 re1 re2)
      
          | _, _ -> default e1 e2 re1 re2
    )

  | Less (e1, e2) ->
    let re1 = fe e1 in
    let re2 = fe e2 in
    (match re1, re2 with
    | UnOp (LstLen, _), Lit (Num 0.) -> False
    | UnOp (LstLen, le), Lit (Num 1.) -> Eq (le, EList [])
    | _ -> Less (re1, re2))

  | SetMem (leb, NOp (SetUnion, lle)) -> 
    let rleb = fe leb in
    let formula : Formula.t = (match lle  with
    | [] -> False
    | le :: lle -> 
        let rle = fe le in
          List.fold_left (fun ac le : Formula.t -> 
            let rle = fe le in 
              Or (ac, SetMem (rleb, rle))
          ) (SetMem (rleb, rle)) lle) in
    let result = f formula in
      result

  | SetMem (leb, NOp (SetInter, lle)) -> 
    let rleb = fe leb in
    let formula : Formula.t = (match lle with
    | [] -> False
    | le :: lle -> 
        let rle = fe le in
          List.fold_left (fun ac le : Formula.t -> 
            let rle = fe le in 
              And (ac, SetMem (rleb, rle))
          ) (SetMem (rleb, rle)) lle) in
    let result = f formula in
      result

  | SetMem (leb, BinOp(lel, SetDiff, ler)) -> 
    let rleb = fe leb in
    let rlel = fe lel in
    let rler = fe ler in
    let result = f (And (SetMem (rleb, rlel), Not (SetMem (rleb, rler)))) in
      result
      
  | SetMem (leb, ESet les) -> 
    let rleb = fe leb in
    let rles = List.map (fun le -> fe le) les in
    let result : Formula.t list = List.map (fun le : Formula.t -> Eq (rleb, le)) rles in
    let result = List.fold_left (fun ac eq : Formula.t ->
      (match (ac : Formula.t) with
      | False -> eq
      | _ -> Or (ac, eq))) False result in  
      f result

  | ForAll (bt, a) -> (* Think about quantifier instantiation *)
      let ra = f a in
      let vars = Formula.lvars a in
      let bt = List.filter (fun (b, _) -> SS.mem b vars) bt in
      (match bt with
      | [] -> ra
      | _ -> ForAll (bt, ra))

  | _ -> a) in

  let final_result = if (a <> result) && (not (a == result))
    then (L.log L.TMI (lazy (Printf.sprintf "Reduce_assertion: %s -> %s" (Formula.str a) (Formula.str result))); f result)
    else result in

  (* if (no_timing = None) then (let end_time = Sys.time () in update_statistics "reduce_pure_assertion" (end_time -. start_time)); *)
  final_result


(*************************************)
(** Symbolic state simplification   **)
(*************************************)

let reduce_pfs_in_place store gamma pfs =
  DynArray.iteri (fun i pf ->
    let rpf = reduce_formula ?gamma:(Some gamma) ?pfs:(Some pfs) pf in
    DynArray.set pfs i rpf) pfs
  
let sanitise_pfs store gamma pfs =
  
  reduce_pfs_in_place store gamma pfs;
  
  let length = DynArray.length pfs in
  let dindex = DynArray.init length (fun x -> false) in
  let clc = ref 0 in
  let rec find_duplicates l =
    (match (l : Formula.t list) with
    | [] -> ()
    | a :: l ->
      let imem = List.mem a l in
      (if (imem || (a = True)) then
        DynArray.set dindex !clc true);
      clc := !clc + 1;
      find_duplicates l) in
  let ll = DynArray.to_list pfs in
  find_duplicates ll;
  for i = 0 to (length - 1) do
    if (DynArray.get dindex (length - 1 - i))
      then DynArray.delete pfs (length - 1 - i)
  done

let sanitise_pfs_no_store_no_gamma = sanitise_pfs (Hashtbl.create 1) (TypEnv.init())
let sanitise_pfs_no_store          = sanitise_pfs (Hashtbl.create 1)
  
let filter_gamma_pfs pfs gamma = 
  let pfs_vars = PFS.lvars pfs in
  TypEnv.filter_vars_in_place gamma pfs_vars
  
(* *********** *)
(*   CLEANUP   *)
(* *********** *)

let clean_up_stuff exists left right =
  let sleft = Formula.Set.of_list (DynArray.to_list left) in
  let i = ref 0 in
  while (!i < DynArray.length right) do
    let pf = DynArray.get right !i in
    let pf_sym pf = (match (pf : Formula.t) with
      | Eq (e1, e2) -> Formula.Set.mem (Eq (e2, e1)) sleft
      | Not (Eq (e1, e2)) -> Formula.Set.mem (Not (Eq (e2, e1))) sleft
      | _ -> false) in
    (match ((Formula.Set.mem pf sleft) || (pf_sym pf)) with
    | false -> 
      let npf = (match pf with
          | Not pf -> pf
          | _ -> Not pf) in
        (match ((Formula.Set.mem npf sleft) || (pf_sym npf)) with
        | false -> i := !i + 1
        | true -> 
            DynArray.clear left; DynArray.clear right;
            DynArray.add left False)
     | true -> DynArray.delete right !i
    )
  done;
  
  i := 0;
  while (!i < DynArray.length right) do
    let pf = DynArray.get right !i in
    (match pf with
    | Not (Eq (le, Lit Empty)) ->
      (match le with
      | EList _ 
      | BinOp (_, _, _)  
      | UnOp (_, _) -> DynArray.delete right !i 
      | _ -> i := !i + 1
      )
    | _ -> i := !i + 1)
  done
  
(* Set intersections *)
let get_set_intersections pfs =
  let lvars = Hashtbl.create 23 in
  let rvars = Hashtbl.create 23 in
  
  List.iter
    (fun pf -> 
      (match (pf : Formula.t) with
      | ForAll ([ (x, Some NumberType) ], Or (Not (SetMem (LVar y, LVar set)), Less (LVar elem, LVar z))) when (x = y && x = z) -> 
          L.log L.Verboser (lazy (Printf.sprintf "Got left: %s, %s" elem set));
          Hashtbl.add lvars elem set;
      | ForAll ([ (x, Some NumberType) ], Or (Not (SetMem (LVar y, LVar set)), Less (LVar z, LVar elem))) when (x = y && x = z) -> 
          L.log L.Verboser (lazy (Printf.sprintf "Got right: %s, %s" elem set));
          Hashtbl.add rvars elem set;
      | _ -> ())
    ) pfs;
    
  L.log L.Verboser (lazy "v <# set :");  Hashtbl.iter (fun v s -> L.log L.Verboser (lazy (Printf.sprintf "\t%s, %s" v s))) lvars;
  L.log L.Verboser (lazy "set <# v :"); Hashtbl.iter (fun v s -> L.log L.Verboser (lazy (Printf.sprintf "\t%s, %s" v s))) rvars;
  
  (* 
   *   1. forall (v, s) in lvars -> inter { v }, s = 0
   *   2. forall (v, s) in rvars -> inter { v }, s = 0
   *   3. if (v, s1) in lvars and (v, s2) in rvars, then inter s1 s2 = 0
   *   4. if v1 < v2 and (v1, s1) in lvars and (v2, s2) in lvars, then inter { v1 } { v2 } = 0 and inter { v1 } s2 = 0
   * 
   *   THERE ARE MORE
   *)
  let intersections = ref [] in
  
  (* 1. *)
  Hashtbl.iter (fun v s -> intersections := (Expr.Set.of_list [ ESet [ LVar v ]; LVar s ] ) :: !intersections) lvars;
  (* 2. *)
  Hashtbl.iter (fun v s -> intersections := (Expr.Set.of_list [ ESet [ LVar v ]; LVar s ] ) :: !intersections) rvars;
  (* 3. *)
  Hashtbl.iter (fun v s1 -> if (Hashtbl.mem rvars v) then
    let rsets = Hashtbl.find_all rvars v in
    List.iter (fun s2 -> intersections := (Expr.Set.of_list [ LVar s1; LVar s2 ] ) :: !intersections) rsets) lvars;
  (* 4. *)
  List.iter (fun a -> 
    (match (a : Formula.t) with
    | Less (LVar v1, LVar v2) -> 
      (match (Hashtbl.mem lvars v1), (Hashtbl.mem lvars v2) with
      | true, true -> 
          intersections := (Expr.Set.of_list [ ESet [ LVar v1 ]; ESet [ LVar v2 ] ] ) :: !intersections;
          let rsets = Hashtbl.find_all lvars v2 in
          List.iter (fun s2 -> intersections := (Expr.Set.of_list [ ESet [ LVar v1 ]; LVar s2 ] ) :: !intersections) rsets;
      | true, false 
      | false, true ->
          intersections := (Expr.Set.of_list [ ESet [ LVar v1 ]; ESet [ LVar v2 ] ] ) :: !intersections;
      | _, _ -> ()
      );
    | _ -> ())) pfs;
  let intersections = List.map (fun s -> Expr.Set.elements s) !intersections in
  List.sort compare intersections
  
let resolve_set_existentials lpfs rpfs exists (gamma : TypEnv.t) =

  let exists = ref exists in

  let set_exists = SS.filter (fun x -> TypEnv.get gamma x = Some SetType) !exists in
  if (SS.cardinal set_exists > 0) then (
  let intersections = get_set_intersections ((DynArray.to_list lpfs) @ (DynArray.to_list rpfs)) in
  L.log L.Verboser (lazy (Printf.sprintf "Intersections we have:\n%s"
    (String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> Expr.str e) s)) intersections))));
          
  let i = ref 0 in
  while (!i < DynArray.length rpfs) do
    let a = DynArray.get rpfs !i in
    (match a with
    | Eq (NOp (SetUnion, ul), NOp (SetUnion, ur)) -> 
        (* Expand ESets *)
        let ul = List.flatten (List.map (fun (u : Expr.t) : Expr.t list -> (match (u : Expr.t) with | ESet x -> List.map (fun (x : Expr.t) : Expr.t -> ESet [ x ]) x | _ -> [ u ])) ul) in
        let ur = List.flatten (List.map (fun (u : Expr.t) : Expr.t list -> (match u with | ESet x -> List.map (fun x : Expr.t -> ESet [ x ]) x | _ -> [ u ])) ur) in

        let sul = Expr.Set.of_list ul in
        let sur = Expr.Set.of_list ur in
        L.log L.Verboser (lazy "Resolve set existentials: I have found a union equality.");
        L.log L.Verboser (lazy (Formula.str a));
        
        (* Trying to cut the union *)
        let same_parts = Expr.Set.inter sul sur in
        L.log L.Verboser (lazy (Printf.sprintf "Same parts: %s" (String.concat ", " (List.map (fun x -> Expr.str x) (Expr.Set.elements same_parts)))));
        if (Expr.Set.cardinal same_parts = 1) then (
          let must_not_intersect = Expr.Set.diff (Expr.Set.union sul sur) same_parts in
          L.log L.Verboser (lazy (Printf.sprintf "%s must not intersect any of %s" 
            (String.concat ", " (List.map (fun x -> Expr.str x) (Expr.Set.elements same_parts)))
            (String.concat ", " (List.map (fun x -> Expr.str x) (Expr.Set.elements must_not_intersect)))));
          let element : Expr.t = List.hd (Expr.Set.elements same_parts) in 
          let must_not_intersect = List.map (fun s -> List.sort compare [ s; element ]) (Expr.Set.elements must_not_intersect) in
          L.log L.Verboser (lazy (Printf.sprintf "Intersections we need:\n%s"
              (String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> Expr.str e) s)) must_not_intersect))));
          let must_not_intersect = List.map (fun s -> List.mem s intersections) must_not_intersect in
          L.log L.Verboser (lazy (Printf.sprintf "And we have: %s" (String.concat ", " (List.map (fun (x : bool) -> if (x = true) then "true" else "false") must_not_intersect))));
          let must_not_intersect = SB.elements (SB.of_list must_not_intersect) in
          if (must_not_intersect = [ true ]) then (
            let success = ref true in
            let cl = Expr.Set.diff sul same_parts in
            let cr = Expr.Set.diff sur same_parts in
            let lhs = if (Expr.Set.cardinal cl = 1) then (List.hd (Expr.Set.elements cl)) else NOp (SetUnion, (Expr.Set.elements cl)) in
            let rhs = if (Expr.Set.cardinal cr = 1) then (List.hd (Expr.Set.elements cr)) else NOp (SetUnion, (Expr.Set.elements cr)) in
            (* CAREFULLY substitute *)
            (match lhs with
            | LVar v when (SS.mem v set_exists) ->
                L.log L.Verboser (lazy (Printf.sprintf "Managed to instantiate a set existential: %s" v));
                let temp_subst = SSubst.init [] in
                SSubst.put temp_subst v rhs;
                PFS.substitution_in_place temp_subst rpfs;
                exists := SS.remove v !exists;
                while (TypEnv.mem gamma v) do TypEnv.update gamma v None done;
                DynArray.delete rpfs !i
            | _ -> DynArray.set rpfs !i (Eq (lhs, rhs)); i := !i + 1;)
            ) else i := !i + 1
        ) else i := !i + 1;
        
    | _ -> i := !i + 1;);
  done;

  rpfs, !exists, gamma) else rpfs, !exists, gamma
  
  
  
let find_impossible_unions lpfs rpfs exists (gamma : TypEnv.t) =
  
  let exists = ref exists in

  let set_exists = SS.filter (fun x -> TypEnv.get gamma x = Some SetType) !exists in
  if (SS.cardinal set_exists > 0) then (
  let intersections = get_set_intersections ((DynArray.to_list lpfs) @ (DynArray.to_list rpfs)) in
  L.log L.Verboser (lazy (Printf.sprintf "Intersections we have:\n%s"
    (String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> Expr.str e) s)) intersections))));
  
  try (
  let i = ref 0 in
  while (!i < DynArray.length rpfs) do
    let a = DynArray.get rpfs !i in
    (match a with
    | Eq (NOp (SetUnion, ul), NOp (SetUnion, ur)) -> 
        let sul = Expr.Set.of_list ul in
        let sur = Expr.Set.of_list ur in
        L.log L.Verboser (lazy ("Find impossible unions: I have found a union equality."));
        
        (* Just for the left *)
        Expr.Set.iter (fun s1 ->
          let must_not_intersect = List.map (fun s -> List.sort compare [ s; s1 ]) (Expr.Set.elements sur) in
          L.log L.Verboser (lazy (Printf.sprintf "Intersections we need:\n%s"
              (String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> Expr.str e) s)) must_not_intersect))));
          let must_not_intersect = List.map (fun s -> List.mem s intersections) must_not_intersect in
          L.log L.Verboser (lazy (Printf.sprintf "And we have: %s" (String.concat ", " (List.map (fun (x : bool) -> if (x = true) then "true" else "false") must_not_intersect))));
          let must_not_intersect = SB.elements (SB.of_list must_not_intersect) in
          if (must_not_intersect = [ true ]) then raise (Failure "Oopsie!");
        ) sul;
        
        (* Continue if we survived *)
        i := !i + 1;
    
    | _ -> i := !i + 1;);
    done; 
  
    rpfs, !exists, gamma) with
    | Failure _ -> DynArray.of_list [ Formula.False ], SS.empty, TypEnv.init()) else rpfs, !exists, gamma

let trim_down (exists : SS.t) (lpfs : Formula.t DynArray.t) (rpfs : Formula.t DynArray.t) gamma = 
  try (
    let lhs_lvars = PFS.lvars lpfs in
    let rhs_lvars = PFS.lvars rpfs in
    let diff = SS.diff (SS.diff rhs_lvars lhs_lvars) exists in
    
    if (DynArray.length rpfs = 1) then (
      let pf = DynArray.get rpfs 0 in
      (match pf with
      | Eq (LVar v1, LVar v2)
      | Less (LVar v1, LVar v2)
      | LessEq (LVar v1, LVar v2) 
      | Not (Eq (LVar v1, LVar v2))
      | Not (Less (LVar v1, LVar v2))
      | Not (LessEq (LVar v1, LVar v2)) ->
          if (v1 <> v2 && (SS.mem v1 diff || SS.mem v2 diff)) then raise (Failure "")
      | _ -> ())
    );
    
    (* THIS IS UNSOUND, FIX *)
    let i = ref 0 in
    while (!i < DynArray.length lpfs) do
      let pf = DynArray.get lpfs !i in
      let pf_lvars = Formula.lvars pf in
      let inter_empty = (SS.inter rhs_lvars pf_lvars = SS.empty) in 
      (match inter_empty with
      | true -> DynArray.delete lpfs !i 
      | false -> i := !i + 1)
    done;
    true, exists, lpfs, rpfs, gamma)
  with
  | Failure _ -> false, exists, lpfs, rpfs, gamma



(** 
  Pure entailment: simplify pure formulae and typing environment

  @param pfs Pure formulae (modified destructively)
  @param pfs Typing environment (modified destructively)
  @param vars_to_save Logical variables that cannot be deleted
  @return Substitution from logical variables to logical expressions
*)
let simplify_pfs_and_gamma ?(kill : bool option) (gamma : TypEnv.t) (lpfs : PFS.t) ?(rpfs: PFS.t option) ?(existentials: SS.t option) (vars_to_save : SS.t option option) : SSubst.t * SS.t = 

  L.log L.Verboser (lazy "Simplifications.simplify_pfs_and_gamma");

  let n = ref 0 in 
  let result = SSubst.init [] in 

  let vars_to_save, save_all = 
    (match vars_to_save with
    | Some (Some v) -> v, false 
    | Some None     -> SS.empty, true
    | None          -> SS.empty, false) in

  let kill = match kill with None -> false | Some b -> b in 

  let rpfs : PFS.t = Option.default (PFS.init()) rpfs in 
  let existentials : SS.t ref = ref (Option.default SS.empty existentials) in 

  (* Unit types *)
  let simplify_unit_types () = 
    TypEnv.iter gamma (fun x t -> 
      match t with 
      | UndefinedType -> SSubst.put result x (Lit Undefined)
      | NullType      -> SSubst.put result x (Lit Null)
      | EmptyType     -> SSubst.put result x (Lit Empty)
      | NoneType      -> SSubst.put result x Nono
      | _ -> ()
    ) in 

  (* Pure formulae false *)
  let pfs_false (msg : string) : unit =
    L.log L.Verboser (lazy ("Pure formulae false: " ^ msg));
    PFS.clear lpfs;
    PFS.extend lpfs False;
    PFS.clear rpfs;
    PFS.extend rpfs True;
    n := 1 in 

  (* PF simplification *)
  let simplify_pf (pf : Formula.t): unit = 
      L.log L.TMI (lazy (Printf.sprintf "SPF: %d: %s" !n (Formula.str pf)));
    (* Reduce current assertion *)
      (match pf with 

      (* These we must not encounter here *)
      | ForAll (bt, _) -> 
          let lx, _ = List.split bt in 
          List.iter (fun x -> TypEnv.update gamma x None) lx;
          n := !n + 1;

      (* And is expanded *)
      | And (a1, a2) -> 
          PFS.nth_set lpfs !n a1;
          PFS.extend lpfs a2 

      (* If we find true, we can delete it *)
      | True  -> PFS.nth_delete lpfs !n
      
      (* If we find false, the entire pfs are false *)
      | False -> pfs_false "false in pure formulae"

      (* Inequality of things with different types *)
      | Not (Eq (le1, le2)) ->
        let te1, _, _ = Typing.type_lexpr gamma le1 in
        let te2, _, _ = Typing.type_lexpr gamma le2 in
        (match te1, te2 with
        | Some te1, Some te2 when (te1 <> te2) -> PFS.nth_delete lpfs !n
        | Some te1, Some te2 when (te1 = te2 && (te1 = UndefinedType || te1 = NullType || te1 = EmptyType || te1 = NoneType)) -> pfs_false ("Inequality of two undefined/null/empty/none")
        | _ -> n := !n + 1)

      | Eq (le1, le2) ->
        let te1, _, _ = Typing.type_lexpr gamma le1 in
        let te2, _, _ = Typing.type_lexpr gamma le2 in
        (match te1, te2 with
        | Some te1, Some te2 when (te1 <> te2) -> 
            pfs_false (Printf.sprintf "Type mismatch: %s:%s -> %s:%s"  (Expr.str le1) (Type.str te1) (Expr.str le2) (Type.str te2))

        | _, _ -> 

          L.log L.Verboser (lazy "Match");
          (match le1, le2 with
          
          | Lit (Loc lloc), ALoc aloc
          | ALoc aloc, Lit (Loc lloc) -> 
              SSubst.put result aloc (Lit (Loc lloc));
              let temp_subst = SSubst.init [ aloc, Lit (Loc lloc) ] in 
                PFS.substitution_in_place temp_subst lpfs

          | ALoc alocl, ALoc alocr -> 
            SSubst.put result alocr (ALoc alocl);
              let temp_subst = SSubst.init [ alocr, ALoc alocl ] in 
                PFS.substitution_in_place temp_subst lpfs

          (* Equal variables - what happens if they are numbers? *)
          | LVar v1, LVar v2 when (v1 = v2) -> DynArray.delete lpfs !n
          
          (* Variable and something else *)
          | LVar v, le 
          | le, LVar v ->     

            (* Understand, if there are two lvars, which should be substituted *)
            let v, (le : Expr.t) = (match le with
            | LVar w -> 
              let save_v = save_all || SS.mem v vars_to_save in 
              let save_w = save_all || SS.mem w vars_to_save in 
                (match save_v, save_w with
                | true, false -> w, LVar v
                | true, true 
                | false, true -> v, le
                | false, false -> 
                  if (is_spec_var_name v) && (not (is_spec_var_name w))
                    then w, LVar v else v, le)
            | _ -> v, le) in
          
            let lvars_le = Expr.lvars le in
            (match (SS.mem v lvars_le) with
            (* Cannot substitute if variable on both sides *)
            | true -> 
                n := !n + 1
            | false -> 
                DynArray.delete lpfs !n;
                
                let tv, _, _ = Typing.type_lexpr gamma (LVar v) in
                let tle, _, _ = Typing.type_lexpr gamma le in 
                (match tv, tle with
                | Some tv, Some tle when (tv <> tle) -> pfs_false "Type mismatch"
                | _ -> 
                    let temp_subst = SSubst.init [ v, le ] in 
                    PFS.substitution_in_place temp_subst lpfs;

                    if (SSubst.mem result v) then (
                      let le' = Option.get (SSubst.get result v) in (if le <> le' then raise (Failure ("Impossible variable in subst: " ^ v))));
                    SSubst.iter result (fun x le -> 
                      let sle = SSubst.subst_in_expr temp_subst true le in 
                        SSubst.put result x sle);
                    SSubst.put result v le;

                    existentials := SS.remove v !existentials;

                (* Understand gamma if subst is another LVar *)
                (match le with
                | LVar v' ->
                  (match (TypEnv.get gamma v) with | None -> ()
                  | Some t -> 
                    (match (TypEnv.get gamma v') with | None -> TypEnv.update gamma v' (Some t)
                    | Some t' -> 
                        if (t <> t') then pfs_false "Type mismatch")
                  )
                | _ -> ());
                
                (* Remove (or add) from (or to) gamma *)
                (match (save_all || SS.mem v vars_to_save) with
                | true -> 
                  let le_type, _, _ = Typing.type_lexpr gamma le in
                  (match le_type with
                  | None -> ()
                  | Some t -> (match TypEnv.get gamma v with
                    | None -> TypEnv.update gamma v (Some t)
                    | Some tv -> 
                        if (t <> tv) then pfs_false "Type mismatch"))
                | false -> TypEnv.update gamma v None)
                )
              )

            | UnOp (TypeOf, LVar v), Lit (Type t)
            | Lit (Type t), UnOp (TypeOf, LVar v) -> 
                (match TypEnv.get gamma v with
                | None -> TypEnv.update gamma v (Some t)
                | Some tv -> if (t <> tv) then pfs_false "Type mismatch");
                DynArray.delete lpfs !n

            | _, _ -> n := !n + 1
            )
          )

        (* All other cases *)
        | _ -> n := !n + 1
      )
  in 

  (*****************************************
   ********* THIS IS THE BEGINNING *********
   *****************************************)

  (* Step 1 - Simplify unit types *)
  simplify_unit_types ();

  (* Step 2 - Main loop *)
  n := 0;
  while (!n < PFS.length lpfs) do
    let pf = PFS.nth_get lpfs !n in   
    let pf = reduce_formula ?gamma:(Some gamma) ?pfs:(Some lpfs) pf in 
      PFS.nth_set lpfs !n pf;
      simplify_pf pf
  done;

  L.log L.Verboser (lazy (Printf.sprintf "Substitution:\n\t%s" (SSubst.str result)));
  PFS.substitution_in_place result lpfs;

  L.log L.Verboser (lazy (Printf.sprintf "PFS:\n\t%s" (PFS.str lpfs)));

  (* Step 3 - Bring back my variables *)
  SSubst.iter result (fun v le ->
    if (save_all || (kill && SS.mem v vars_to_save) || (not kill && (vars_to_save <> SS.empty))) then
      PFS.extend lpfs (Eq (LVar v, le)));

  sanitise_pfs_no_store gamma lpfs;

  (* Step 4 - Return *)
  result, !existentials

let simplify_for_sat_check ?(subst: SVal.SSubst.t option) ?(rpfs : PFS.t option) ?(existentials:SS.t option) (gamma : TypEnv.t) (pfs : PFS.t) : SS.t =

  let exists = ref (Option.default SS.empty existentials) in 
  let rpfs = Option.default (PFS.init ()) rpfs in 

  (* L.log L.Verboser (lazy (Printf.sprintf "Simplify_for_sat_check rpfs:\n%s" (PFS.str rpfs))); *)

  (* Main loop *)
  let n = ref 0 in 
  while (!n < PFS.length pfs) do
    let pf = PFS.nth_get pfs !n in   
    (* L.log L.Verboser (lazy (Printf.sprintf "Checking for quantifiers: %s" (Formula.str pf))); *)
    (match (pf : Formula.t) with 
    | ForAll ([ (x, Some NumberType) ], Or (Not (SetMem (LVar y, LVar set)), _)) when (x = y) ->
      (* Does the set variable appear anywhere else? *)
      if (PFS.count pfs set = 1) && (PFS.count rpfs set = 0) then (
          PFS.nth_delete pfs !n; 
          TypEnv.update gamma set None; 
          exists := SS.remove set !exists; 
          (match subst with 
          | None -> ()
          | Some subst -> SSubst.extend subst [set, ESet []])
        ) 
      else n := !n + 1
    | _ -> n := !n + 1
    )
  done;
  !exists

let simplify_implication (exists : SS.t) (lpfs : PFS.t) (rpfs : PFS.t) (gamma : TypEnv.t) =
  let subst, exists = simplify_pfs_and_gamma gamma lpfs ~rpfs:rpfs ~existentials:exists None in
  PFS.substitution_in_place subst rpfs;
  sanitise_pfs_no_store gamma rpfs;
  clean_up_stuff exists lpfs rpfs;
  let exists = simplify_for_sat_check gamma lpfs ~subst:subst ~rpfs:rpfs ~existentials:exists in 

  L.log L.Verboser (lazy (Printf.sprintf "Finished existential simplification.\nExistentials:\n%s\nLeft:\n%s\nRight:\n%s\nGamma:\n%s\n"
    (String.concat ", " (SS.elements exists)) (PFS.str lpfs) (PFS.str rpfs) (TypEnv.str gamma)));

  exists

(* Reduction of assertions *)
let rec reduce_assertion ?(no_timing: unit option) ?(gamma : TypEnv.t option) ?(pfs : PFS.t option) (a : Asrt.t) : Asrt.t =

  let f = reduce_assertion ~no_timing:() ?gamma:gamma ?pfs:pfs in
  let fe = Reduction.reduce_lexpr ?gamma:gamma ?pfs:pfs in

  let result = (match a with

  | Types lvt -> 
      (try (
        let lvt = List.fold_right (fun (e, t) ac -> 
          (match (e : Expr.t) with 
          | Lit lit -> if (t <> Literal.type_of lit) then raise (Failure "Wrong type") else ac
          | _ -> (e, t) :: ac
          )
        ) lvt [] in 
        if (lvt = []) then Asrt.Pure True else Types lvt
      ) with (Failure "Wrong type") -> Pure False)

  | Star (a1, a2) ->
    let fa1  = f a1 in
    let fa2 = f a2 in
    (match (fa1 : Asrt.t), (fa2 : Asrt.t) with
    | Pure False, _
    | _, Pure False -> Pure False
    | Pure True, a
    | a, Pure True -> a
    | _, _ -> Star (fa1, fa2)
    )

  | Pure f -> Pure (reduce_formula ?gamma:gamma ?pfs:pfs f) 

  | _ -> a) in

  if (a <> result) && (not (a == result))
    then (L.log L.TMI (lazy (Printf.sprintf "Reduce_assertion: %s -> %s" (Asrt.str a) (Asrt.str result)))); 
  
  result 