(**
	Common - JaVerT
*)

open CCommon

(**
  Symbolic execution
*)
let javert    = ref false
let cosette   = ref false
let bi        = ref false
let js        = ref false
let unfolding = ref true

let bi_dflt   = ref true

(*********************)
(** Fresh Variables **)
(*********************)

let dashes         = "-----------------------------------------\n"

let lloc_prefix = "$l"                  (* Literal location prefix  *)
let pvar_prefix = "_pvar_"              (* Program variable prefix  *)

let fresh_loc   = fresh_sth lloc_prefix (* Literal location counter *)
let fresh_pvar  = fresh_sth pvar_prefix (* Program variable counter *)

(* Program variable recogniser *)
let is_pvar_name (name : string) : bool =
  try (let first = String.sub name 0 1 in (first <> "_" && first <> "#" && first <> "$")) with _ -> false

let aloc_prefix    = "_$l_"               (* Abstract location prefix  *)
let lvar_prefix    = "_lvar_"             (* Logical  variable prefix  *)
let lvar_prefix_bi = "_lvar_bi_"          (* Logical  variable prefix  *)

let fresh_aloc = fresh_sth aloc_prefix (* Abstract location counter *)
let fresh_lvar = fresh_sth lvar_prefix (* Logical  variable counter *)
let fresh_lvar_bi = fresh_sth lvar_prefix_bi (* Logical  variable counter *)

 

let lvar_from_str (name : string) : string = lvar_prefix ^ name
let svar_from_str (name : string) : string = "#" ^ name


(* Abstract location recogniser *)
let is_aloc_name (name : string) : bool =
  try (String.sub name 0 4 = aloc_prefix) with _ -> false

(* Logical variable recogniser *)
let is_lvar_name (name : string) : bool =
  try ((String.sub name 0 1 = "#") || (String.sub name 0 6 = lvar_prefix)) with _ -> false

(* Spec variables *)
let is_spec_var_name (name : string) : bool =
  try (String.sub name 0 1 = "#") with _ -> false

(* Literal location recogniser *)
let is_lloc_name (name : string) : bool =
  try (String.sub name 0 2 = lloc_prefix) with | _ -> false

let it_must_hold_that (x : 'a Lazy.t) =
  if !sanity then
    (
      assert (Lazy.force x)
    )