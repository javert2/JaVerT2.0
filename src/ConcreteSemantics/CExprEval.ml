open Batteries
open Arith_Utils

module CStore = MakeStore.M(CVal.M)

(* Expression Evaluation *)

exception TypeError       of string
exception EvaluationError of string

let unary_int_thing (lit : CVal.M.t) (f : float -> float) emsg : CVal.M.t =
  let num =
    (match lit with
      | Num n -> n
      | _ -> raise (TypeError (Printf.sprintf "%s %s" emsg (Literal.str lit)))) in
  let res = f num in
    Num res

let evaluate_unop (op : UnOp.t) (lit : CVal.M.t) : CVal.M.t =
  match op with
  | Not -> (match (lit : CVal.M.t) with
  | Bool b -> (Bool (not b))
  | _ -> raise (TypeError (Printf.sprintf "Type Error: Negation: expected boolean, got %s" (Literal.str lit))))
  | UnaryMinus -> unary_int_thing lit (fun x -> (-. x)) "Type Error: Unary minus: expected number, got "
  | BitwiseNot -> unary_int_thing lit int32_bitwise_not "Type Error: Bitwise not: expected number, got"
  | M_abs      -> unary_int_thing lit abs_float         "Type Error: Absolute value: expected number, got"
  | M_acos     -> unary_int_thing lit acos              "Type Error: Arc cosine: expected number, got"
  | M_asin     -> unary_int_thing lit asin              "Type Error: Arc sine: expected number, got"
  | M_atan     -> unary_int_thing lit atan              "Type Error: Arc tangent: expected number, got"
  | M_ceil     -> unary_int_thing lit ceil              "Type Error: Ceiling: expected number, got"
  | M_cos      -> unary_int_thing lit cos               "Type Error: Cosine: expected number, got"
  | M_exp      -> unary_int_thing lit exp               "Type Error: Exponentiation: expected number, got"
  | M_floor    -> unary_int_thing lit floor             "Type Error: Floor: expected number, got"
  | M_log      -> unary_int_thing lit log               "Type Error: Unary minus: expected number, got"
  | M_round    -> (match lit with
  | Num n -> Num (let sign = copysign 1.0 n in if ((sign < 0.0) && (n >= -0.5)) then (-0.0) else (floor (n +. 0.5)))
  | _ -> raise (TypeError (Printf.sprintf "Type Error: Round: expected number, got %s" (Literal.str lit))))
  | M_sgn  -> unary_int_thing lit (fun x -> copysign 1.0 x) "Type Error: Sign: expected number, got"
  | M_sin  -> unary_int_thing lit sin                       "Type Error: Sine: expected number, got"
  | M_sqrt -> unary_int_thing lit sqrt                      "Type Error: Square root: expected number, got"
  | M_tan  -> unary_int_thing lit tan                       "Type Error: Tangent: expected number, got"
  | ToStringOp -> (match lit with
  | Num n -> String (float_to_string_inner n)
  | _ -> raise (TypeError (Printf.sprintf "Type Error: Number to string: expected number, got %s" (Literal.str lit))))
  | ToIntOp    -> unary_int_thing lit to_int     "Type Error: Number to integer: expected number, got"
  | ToUint16Op -> unary_int_thing lit to_uint16  "Type Error: Number to unsigned 16-bit integer: expected number, got"
  | ToInt32Op  -> unary_int_thing lit to_int32   "Type Error: Number to 32-bit integer: expected number, got"
  | ToUint32Op -> unary_int_thing lit to_uint32  "Type Error: Number to unsigned 32-bit integer: expected number, got"
  | ToNumberOp -> (match lit with
    | String s -> 
      if s = "" then Num 0. else
        let num = try Float.of_string s with Failure "float_of_string" -> nan in
          Num num
    | _ -> raise (TypeError (Printf.sprintf "Type Error: ToNumber: expected string, got %s" (Literal.str lit))))
  | TypeOf -> Type (Literal.type_of lit)
  | Car -> (match lit with
    | LList ll ->
      (match ll with
      | [] -> raise (EvaluationError "Evaluation Error: List head of empty list")
      | lit :: _ -> lit)
    | _ -> raise (TypeError (Printf.sprintf "Type Error: List head: expected list, got %s" (Literal.str lit))))
  | Cdr -> (match lit with
  | LList ll ->
      (match ll with
      | [] -> raise (EvaluationError "Evaluation Error: List tail of empty list")
      | _ :: ll -> LList ll)
    | _ -> raise (TypeError (Printf.sprintf "Type Error: List tail: expected list, got %s" (Literal.str lit))))
| LstLen ->
  (match lit with
  | LList l -> Num (float_of_int (List.length l))
  | _ -> raise (TypeError (Printf.sprintf "Type Error: List length: expected list, got: %s" (Literal.str lit))))
| LstRev ->
  (match lit with
  | LList l -> LList (List.rev l)
  | _ -> raise (TypeError (Printf.sprintf "Type Error: List reverse: expected list, got: %s" (Literal.str lit))))
| StrLen ->
  (match lit with
  | String s -> Num (float_of_int (String.length s))
  | _ -> raise (TypeError (Printf.sprintf "Type Error: String length: expected string, got: %s" (Literal.str lit))))
  

let binary_num_thing (lit1 : CVal.M.t) (lit2 : CVal.M.t) (f : float -> float -> float) emsg : CVal.M.t =
  let num1, num2 =
    (match lit1, lit2 with
      | Num n1, Num n2 -> n1, n2
      | _ -> raise (TypeError (Printf.sprintf "%s %s and %s" emsg (Literal.str lit1) (Literal.str lit2)))) in
    Num (f num1 num2)

let binary_bool_thing (lit1 : CVal.M.t) (lit2 : CVal.M.t) (f : float -> float -> bool) emsg : CVal.M.t =
  let num1, num2 =
    (match lit1, lit2 with
      | Num n1, Num n2 -> n1, n2
      | _ -> raise (TypeError (Printf.sprintf "%s %s and %s" emsg (Literal.str lit1) (Literal.str lit2)))) in
  Bool (f num1 num2)

let rec evaluate_binop (store: CStore.t) (op : BinOp.t) (e1 : Expr.t) (e2 : Expr.t) : CVal.M.t =
  let ee = evaluate_expr store in 
  let lit1 = ee e1 in 
  (match op with
  | And -> (match lit1 with
    | Bool false -> Bool false
    | Bool true -> (match ee e2 with
      | Bool b2 -> Bool b2
      | _ -> raise (TypeError (Printf.sprintf "Type Error: Conjunction: expected boolean, got: %s" (Literal.str lit1)))
    | _ -> raise (TypeError (Printf.sprintf "Type Error: Conjunction: expected boolean, got: %s" (Literal.str lit1)))))
  | Or -> (match lit1 with
    | Bool true -> Bool true
    | Bool false -> 
      let lit2 = ee e2 in
        (match lit2 with
        | Bool b2 -> Bool b2
        | _ -> raise (TypeError (Printf.sprintf "Type Error: Disjunction: expected boolean, got: %s" (Literal.str lit2)))
    | _ -> raise (TypeError (Printf.sprintf "Type Error: Disjunction: expected boolean, got: %s" (Literal.str lit2)))))
  | _ -> 
    let lit2 = ee e2 in 
    (match op with
    | Equal ->
      (match lit1, lit2 with
      | Undefined, Undefined -> (Bool true)
      | Null, Null -> (Bool true)
      | Empty, Empty -> (Bool true)
      | Constant c1, Constant c2 -> (Bool (c1 = c2))
      | Bool b1, Bool b2 -> (Bool (b1 = b2))
      | Num n1, Num n2 -> (Bool (n1 = n2))
      | String s1, String s2 -> (Bool (s1 = s2))
      | Loc l1, Loc l2 -> (Bool (l1 = l2))
      | Type t1, Type t2 -> (Bool (t1 = t2))
      | LList l1, LList l2 -> (Bool (l1 = l2))
      | _, _ -> Bool false)

    | LstNth ->
      (match lit1, lit2 with
      | LList list, Num n when (is_int n) -> List.nth list (int_of_float n)
      | LList list, Num -0. -> List.nth list 0
      | _, _ -> raise (TypeError (Printf.sprintf "Type Error: List indexing: expected list and number, got %s and %s" (Literal.str lit1) (Literal.str lit2))))

    | StrNth ->
      (match lit1, lit2 with
      | String s, Num n when (is_int n) -> String (String.make 1 (String.get s (int_of_float n)))
      | String s, Num -0. -> String (String.make 1 (String.get s 0))
      | _, _ -> raise (TypeError (Printf.sprintf "Type Error: List indexing: expected string and number, got %s and %s" (Literal.str lit1) (Literal.str lit2))))

    | LessThan -> binary_bool_thing lit1 lit2 (fun x y -> x < y) "Type Error: Less than: expected numbers, got "
    | LessThanString ->
      (match lit1, lit2 with
      | String s1, String s2 -> (Bool (s1 < s2))
      | _, _ -> raise (Failure "Non-string arguments to LessThanString"))
    | LessThanEqual      -> binary_bool_thing lit1 lit2 (fun x y -> x <= y) "Type Error: Less than or equal: expected numbers, got "
    | Plus               -> binary_num_thing lit1 lit2 (fun x y -> x +. y)  "Type Error: Addition: expected numbers, got "
    | Minus              -> binary_num_thing lit1 lit2 (fun x y -> x -. y)  "Type Error: Subtraction: expected numbers, got "
    | Times              -> binary_num_thing lit1 lit2 (fun x y -> x *. y)  "Type Error: Multiplication: expected numbers, got "
    | Div                -> binary_num_thing lit1 lit2 (fun x y -> x /. y)  "Type Error: Division: expected numbers, got "
    | Mod                -> binary_num_thing lit1 lit2 mod_float            "Type Error: Modulus: expected numbers, got "
    | BitwiseAnd         -> binary_num_thing lit1 lit2 int32_bitwise_and    "Type Error: Bitwise conjunction: expected numbers, got "
    | BitwiseOr          -> binary_num_thing lit1 lit2 int32_bitwise_or     "Type Error: Bitwise disjunction: expected numbers, got "
    | BitwiseXor         -> binary_num_thing lit1 lit2 int32_bitwise_xor    "Type Error: Bitwise exclusive disjunction: expected numbers, got "
    | LeftShift          -> binary_num_thing lit1 lit2 int32_left_shift     "Type Error: Left shift: expected numbers, got "
    | SignedRightShift   -> binary_num_thing lit1 lit2 int32_right_shift    "Type Error: Signed right shift: expected numbers, got "
    | UnsignedRightShift -> binary_num_thing lit1 lit2 uint32_right_shift   "Type Error: Unsigned right shift: expected numbers, got "
    | M_atan2            -> binary_num_thing lit1 lit2 atan2                "Type Error: Arc tangent: expected numbers, got "
    | M_pow              -> binary_num_thing lit1 lit2 (fun x y -> x ** y)  "Type Error: Exponentiation: expected numbers, got "
    | LstCons ->
      (match lit2 with
      | LList list -> 
        (* TODO: Change to normal semantics and re-test (this is here because of problems with apply) *)
        (match lit1 with LList [] -> lit2 | _ -> LList (lit1 :: list))
      | _ -> raise (Failure (Printf.sprintf "Type Error: List cons: expected anything and list, got %s and %s" (Literal.str lit1) (Literal.str lit2))))
    | LstCat ->
      (match lit1, lit2 with
      | LList l1, LList l2 -> (LList (List.append l1 l2))
      | _, _ -> raise (Failure (Printf.sprintf "Type Error: List concatenation: expected lists, got %s and %s" (Literal.str lit1) (Literal.str lit2))))
    | StrCat ->
      (match lit1, lit2 with
      | String s1, String s2 -> (String (s1 ^ s2))
      | _, _ -> raise (Failure (Printf.sprintf "Type Error: List concatenation: expected lists, got %s and %s" (Literal.str lit1) (Literal.str lit2))))
    ))
and
evaluate_expr (store : CStore.t) (e : Expr.t) : CVal.M.t =
  try (
    let ee = evaluate_expr store in
    match e with
    | Lit l ->
      (match l with
      | Constant c -> Literal.evaluate_constant c
      | x -> x)

    | PVar x ->
      (match CStore.get store x with
      | None ->
        let err_msg = Printf.sprintf "Variable %s not found in the store" x in
        let store_str = CStore.str store in
        (* if (!verbose) then Printf.printf "The current store is: \n%s" store_str; *) 
        raise (Failure err_msg)
      | Some v -> v)

    | BinOp (e1, bop, e2) -> 
        evaluate_binop store bop e1 e2

    | UnOp (unop, e) ->
        evaluate_unop unop (ee e)

    | EList ll ->
      (match ll with
      | [] -> LList []
      | e :: ll ->
        let ve = ee e in
        let vll = ee (EList ll) in
          (match vll with | LList vll -> LList (ve :: vll)))
  ) with 
  | TypeError msg -> raise (TypeError msg)
  | EvaluationError msg -> raise (EvaluationError msg)
  | Division_by_zero -> raise (EvaluationError "Division by zero")
  | e -> 
      let msg = Printexc.to_string e in 
      let stack = Printexc.get_backtrace () in
        Printf.eprintf "Expression evaluation: Untreatable Exception: %s%s\n" msg stack;
        exit 1