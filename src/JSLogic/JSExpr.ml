type t =
  | Lit    of Literal.t
  | Nono
  | LVar   of string
  | ALoc   of string
  | PVar   of string
  | UnOp   of UnOp.t * t
  | BinOp  of t * BinOp.t * t
  | NOp    of NOp.t * t list
  | EList  of t list
  | ESet   of t list
  | This
  | Scope


let rec js2jsil (scope_le : Expr.t option) (le : t) : Expr.t =
  let fe = js2jsil scope_le in
  match le with
  | Lit lit              -> Expr.Lit lit
  | Nono                 -> Expr.Nono
  | LVar x               -> Expr.LVar x
  | ALoc l               -> Expr.ALoc l
  | PVar x               -> Expr.PVar x
  | UnOp (op, le)        -> Expr.UnOp (op, fe le)
  | BinOp (le1, op, le2) -> Expr.BinOp (fe le1, op, fe le2)
  | NOp (op, les)        -> Expr.NOp (op, List.map fe les)
  | EList les            -> Expr.EList (List.map fe les)
  | ESet les             -> Expr.ESet (List.map fe les)
  | This                 -> Expr.LVar JSLogicCommon.this_logic_var_name
  | Scope                ->
      (match scope_le with
      | None           -> raise (Failure "DEATH: js2jsil_lexpr")
      | Some scope_le -> scope_le)


module MyJSExpr =
  struct
    type nonrec t = t
    let compare = Pervasives.compare
  end

module SJSExpr = Set.Make(MyJSExpr)


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
  | This  -> "this"
  | Scope -> "$$scope"



