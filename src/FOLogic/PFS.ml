(** JSIL Pure Formulae *)

open CCommon
open SCommon
open SVal

module L = Logging

type t = Formula.t DynArray.t

(**************************************)
(** Pure formulae functions          **)
(**************************************)

(** Returns a new (empty) predicate set *)
let init () : t = DynArray.make medium_tbl_size

(** Returns the serialization of --pfs-- as a list *)
let to_list (pfs : t) : Formula.t list = DynArray.to_list pfs

(** Returns a PFS given a list of assertions *)
let of_list (pfs : Formula.t list) : t = DynArray.of_list pfs

let mem (pfs : t) (a : Formula.t) : bool = 
	Array.mem a (DynArray.to_array pfs)

(** Extends --pfs-- with --a-- *)
let extend (pfs : t) (a : Formula.t) : unit = 
	if not (mem pfs a) then 
	(
		L.log L.Verboser (lazy (Printf.sprintf "PFS Extend: %s" (Formula.str a)));
		DynArray.add pfs a
	)

(** Get nth *)
let nth_get (pfs : t) (n : int) =
	DynArray.get pfs n  

(** Set nth *)
let nth_set (pfs : t) (n : int) =
	DynArray.set pfs n  

(** Delete nth *)
let nth_delete (pfs : t) (n : int) : unit = 
	DynArray.delete pfs n 

(** Kill all *)
let clear (pfs : t) : unit = DynArray.clear pfs

(** Length *)
let length (pfs : t) = DynArray.length pfs

(** Returns a copy of --pfs-- *)
let copy (pfs : t) : t = DynArray.copy pfs

(** Extend --pfs_l-- with --pfs_r-- *)
let merge (pfs_l : t) (pfs_r : t) : unit = DynArray.append pfs_r pfs_l

(** Returns subst(pf) *)
let substitution (subst : SSubst.t) (partial : bool) (pf : t) : t =
	let asrts   = to_list pf in 
	let s_asrts = List.map (Formula.substitution subst partial) asrts in 
	of_list s_asrts

(** Updates pfs to subst(pfs) *)
let substitution_in_place (subst : SSubst.t) (pfs : t) : unit =
	DynArray.iteri (fun i a ->
		let s_a = Formula.substitution subst true a in
		DynArray.set pfs i s_a) pfs

(** Returns the set containing all the lvars occurring in --pfs-- *)
let lvars (pfs : t) : SS.t  =
	DynArray.fold_left (fun ac a -> SS.union ac (Formula.lvars a)) SS.empty pfs

(** Returns the set containing all the alocs occurring in --pfs-- *)
let alocs (pfs : t) : SS.t =
	DynArray.fold_left (fun ac a -> SS.union ac (Formula.alocs a)) SS.empty pfs

(** Returns the set containing all the locs occurring in --pfs-- *)
let clocs (pfs : t) : SS.t =
	DynArray.fold_left (fun ac a -> SS.union ac (Formula.clocs a)) SS.empty pfs

(** Counter: in how many pfs does a variable occur *)
let count (p_formulae : t) (x : string) : int = 
  let count = ref 0 in 
  DynArray.iter (fun pf -> 
    if (SS.mem x (Formula.lvars pf)) then count := !count + 1;
  ) p_formulae;
  !count

(** Printing function *)
let str (p_formulae : t) : string =
	DynArray.fold_left
		(fun ac cur_ass ->
			let cur_ass_str = Formula.str cur_ass in
			if (ac = "") then cur_ass_str else ac ^ "\n\t" ^ cur_ass_str)
		"\t"
    p_formulae
    
