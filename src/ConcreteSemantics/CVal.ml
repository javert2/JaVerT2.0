(*********************)
(*                   *)
(*  Concrete values  *)
(*                   *)
(*********************)

module rec M : (Val.M with type st = CSubst.t and type t = Literal.t) = struct 
  type t  = Literal.t
  type st = CSubst.t 

  let str = Literal.str
 
  let full_str = Literal.str

  let to_literal   lit = Some lit
  
  let from_literal lit = lit

  let to_expr lit = Expr.Lit lit 

  let from_expr (le : Expr.t) = 
    match le with 
    | Lit l -> Some l 
    | _ -> None 

  let from_list   = Literal.from_list
  
  let to_list     = Literal.to_list

  let base_elements (v : t) : t list = Literal.base_elements v

  let is_concrete (v : t) = true

end 
and CSubst : (Subst.M with type vt = M.t) = MakeSubst.M(M)