open SVal 

(** {b Single JSIL specifications}. *)
type st = {
	pre                    : Asrt.t;      (** Precondition *)
	posts                  : Asrt.t list; (** Postcondition *)
	flag                   : Flag.t;      (** Return flag ({!type:jsil_return_flag}) *)
  to_verify              : bool;        (** Should the spec be verified? *) 
  label                  : (string * string list) option
}

(** {b Full JSIL specifications}. *)
type t = {
	name       : string;      (** Procedure/spec name *)
	params     : string list; (** Procedure/spec parameters *)
  sspecs     : st list;     (** List of single specifications *)
  normalised : bool;        (** If the spec is already normalised *)
  to_verify  : bool         (** Should the spec be verified? *)     
}

(**/**)
(** Creates a JSIL specification given its components *)
let s_init ?(label : (string * string list) option) (pre : Asrt.t) (posts : Asrt.t list) (flag : Flag.t) (to_verify : bool) : st =
	{
		pre       = pre;
		posts     = posts;
		flag      = flag;
    to_verify = to_verify; 
    label     = label 
	}

let init (name : string) (params : string list) (sspecs : st list) (normalised : bool) (to_verify : bool) : t =
	{
    name       = name;
    params     = params;
    sspecs     = sspecs;
    normalised = normalised;
    to_verify  = to_verify
	}


let extend (spec : t) (sspecs : st list) : t = 
  { spec with sspecs = sspecs @ spec.sspecs }


let get_params (spec : t) : string list = 
  spec.params


let replace_keywords
    (ret_var : string option)
    (err_var : string option)
    (spec : t) : t =

  (** Step 1 - Create a substitution mapping err and ret to the appropriate variables *)
  let subst_lst = match ret_var with | None -> []         | Some x -> [ "ret", SVal.M.from_expr (Expr.PVar x) ] in
  let subst_lst = match err_var with | None -> subst_lst  | Some x -> ("err", SVal.M.from_expr (Expr.PVar x)) :: subst_lst in 
  let subst_lst = List.map (fun (x, le_x) -> x, Option.get le_x) subst_lst in 
  let subst     = SSubst.init subst_lst in 

  (** Step 2 - Construct a new spec with the return and error keywords replaced by 
    * the appropriate program variables *)
  { 
    name   = spec.name;
    params = spec.params;
    sspecs = 
      List.map
        (fun cur ->
          {
            pre       = cur.pre;
            posts     = List.map (Asrt.substitution subst true) cur.posts;
            flag      = cur.flag;
            to_verify = cur.to_verify; 
            label     = cur.label 
          }) spec.sspecs;
    normalised = spec.normalised;
    to_verify  = spec.to_verify
  }


let string_of_sspec (prefix: string) (sspec : st) = 
  	let sa = Asrt.str in 
  	let sal asrts = String.concat "; " (List.map sa asrts) in 
    let label_str = 
      Option.map_default 
        (fun (lab, existentials) ->
          match existentials with 
            | [] -> Printf.sprintf "%s<%s>\n" prefix lab
            | _  -> Printf.sprintf "%s<%s: %s>\n" prefix lab (String.concat ", " existentials))
        "" 
        sspec.label in 
  	( label_str ^ 
      prefix ^ "[[ " ^ (sa sspec.pre) ^ " ]]\n" ^
   		prefix ^ "[[ " ^ (sal sspec.posts) ^ " ]]\n" ^
   		prefix ^ (Flag.str sspec.flag)) 

let str (spec : t) : string =
	let sspecs_str = String.concat ";\n " (List.map (string_of_sspec "\t") spec.sspecs) in 
  	Printf.sprintf "spec %s (%s)\n %s\n" spec.name (String.concat ", " spec.params) sspecs_str 


let parameter_types 
    (preds : (string, Pred.t) Hashtbl.t) 
    (spec  : t) : t = 
  
  let pt_asrt (a : Asrt.t) : Asrt.t = 
    let f_a_after a : Asrt.t = 
      match (a : Asrt.t) with 
        | Pred (name, les) -> 
          let pred     = try Hashtbl.find preds name with _ -> raise (Failure ("DEATH. parameter_types: predicate " ^ name ^ " does not exist.")) in 
          (*   Printf.printf "Pred: %s\n\tParams1: %s\n\tParams2: %s\n" name
              (String.concat ", " (let x, _ = List.split pred.params in x)) (String.concat ", " (List.map Expr.str les)); *)
            let ac_types = 
              List.fold_left (fun ac_types ((x, t_x), le) -> 
                match t_x with 
                | None     ->  ac_types  
                | Some t_x -> (le, t_x) :: ac_types) [] (List.combine pred.params les) in 
            Star (Types(ac_types), a) 
        | _ -> a in   
    Asrt.map None (Some f_a_after) None None a in 
              
  let pt_sspec (sspec : st) : st = 
    { sspec with pre = (pt_asrt sspec.pre); posts = List.map pt_asrt sspec.posts } in 

  { spec with sspecs = List.map pt_sspec spec.sspecs }


