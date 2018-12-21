
open CCommon
open SCommon

(*********************)
(*                   *)
(*  Symbolic values  *)
(*                   *)
(*********************)

module L = Logging

module rec M : (Val.M with type t = Expr.t and type st = SSubst.t) = struct 
  
  type t = Expr.t
  type st = SSubst.t 

  let str = Expr.str

  let full_str = Expr.full_str 

  let to_literal le = 
    (match (le : Expr.t) with 
    | Lit lit -> Some lit
    | _ -> None)

  let from_literal lit = Expr.Lit lit

  let to_expr   le = le 
  
  let from_expr le = Some le

  let from_list = Expr.from_list
  
  let to_list   = Expr.to_list

  let base_elements = Expr.base_elements

  let is_concrete = Expr.is_concrete
end 

and 
  SSubst : (Subst.M with type vt = M.t) = MakeSubst.M(M) 