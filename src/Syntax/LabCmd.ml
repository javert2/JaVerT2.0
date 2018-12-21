(***************************************************************)
(***************************************************************)
(** JSIL Labelled Commmands                                   **)
(***************************************************************)
(***************************************************************)

type t =
  | LBasic          of BCmd.t
  | LLogic          of LCmd.t 
  | LGoto           of string
  | LGuardedGoto    of Expr.t * string * string
  | LCall           of string  * Expr.t * Expr.t list * string option * (string * (string * Expr.t) list) option
  | LECall          of string  * Expr.t * Expr.t list * string option 
  | LApply          of string  * Expr.t * string option
  | LArguments      of string
  | LPhiAssignment  of (string * Expr.t list) list
  | LReturnNormal
  | LReturnError

let str (lcmd : t) : string =
    let se = Expr.str in
    let ret : string = 
      (match lcmd with
      (* Basic command *)
      | LBasic bcmd -> (BCmd.str None bcmd)
      (* Logic command *)
      | LLogic lcmd -> (LCmd.str lcmd)
      (* goto j *)
      | LGoto j -> Printf.sprintf "goto %s" j
      (* goto [e] j k *)
      | LGuardedGoto (e, j, k) ->
          Printf.sprintf "goto [%s] %s %s" (se e) j k
      (* x := f(y1, ..., yn) with j *)
      | LCall (var, name, args, error, subst) ->
          Printf.sprintf "%s := %s(%s)%s" var (se name) (String.concat ", " (List.map se args))
            (
              (match error with
                | None -> ""
                | Some label -> (" with " ^ label)
              ) ^ 
              (match subst with 
                | None -> ""
                | Some (lab, subst_lst) 
                    when List.length subst_lst > 0 -> 
                      Printf.sprintf " use_subst [%s - %s]" lab (String.concat ", " (List.map (fun (x, le) -> x ^ ": " ^ Expr.str le) subst_lst))
                | Some (lab, subst_lst) 
                    when List.length subst_lst = 0 -> 
                      Printf.sprintf " use_subst [%s]" lab
              )
            )
      | LECall (var, name, args, error) ->
          Printf.sprintf "%s := extern %s(%s)%s" var (se name) (String.concat ", " (List.map se args))
            (match error with
              | None -> ""
              | Some label -> (" with " ^ label))
      (* x := apply(y1, ..., yn) with j *)
      | LApply (var, args, error) ->
          Printf.sprintf "%s := apply(%s)%s" var (se args)
            (match error with
              | None -> ""
              | Some label -> (" with " ^ label))
      (* x := args *)
      | LArguments var -> Printf.sprintf "%s := args" var
      (* var := PHI(var_1, var_2, ..., var_n) *)
      | LPhiAssignment lva ->
        let strs = List.map (fun (v, es) -> v ^ ": " ^ (String.concat ", " (List.map se es))) lva in 
          Printf.sprintf "PHI(%s)" (String.concat "; " strs)
      | LReturnNormal -> "return"
      | LReturnError  -> "throw") in 
    ret 
