open CCommon

type t = {
	name         : string;                (* Name of the lemma *)
  params       : string list;           (* Params *)
	pre          : Asrt.t;                (* Pre *)
  posts        : Asrt.t list;           (* Post *)
  proof        : LCmd.t list option;    (* (Optional) Proof body *)
  variant      : Expr.t option;         (* The paramater to treat as the variant. Will trigger termination checks *)
  existentials : string list 
}

let init_tbl () : (string, t) Hashtbl.t = Hashtbl.create small_tbl_size 

(** JSIL Lemmas *)
let str (lemma : t) : string =
  	let sa = Asrt.str in 
  	let sal asrts = String.concat "; " (List.map sa asrts) in

  	let string_of_params  = (String.concat ", " lemma.params) in
  	let string_of_pre     = "\t[[ " ^ (sa lemma.pre) ^ " ]]\n" in
  	let string_of_post    = "\t[[ " ^ (sal lemma.posts) ^ " ]]\n" in
  	let string_of_proof =
    		(match lemma.proof with
     		  | None -> ""
     	      | Some lemma_proof -> "\t[* " ^ (String.concat ";\n\t   " (List.map LCmd.str lemma_proof)) ^ " *]\n") in
  	"lemma " ^ lemma.name ^ "(" ^ string_of_params ^ ")\n" ^ string_of_pre ^ string_of_post ^ string_of_proof


let parameter_types 
    (preds  : (string, Pred.t) Hashtbl.t) 
    (lemma  : t) : t = 
 
  (** copied from spec - needs refactoring *)  
  let pt_asrt (a : Asrt.t) : Asrt.t = 
    let f_a_after a : Asrt.t = 
      match (a : Asrt.t) with 
        | Pred (name, les) -> 
          let pred     = try Hashtbl.find preds name with _ -> raise (Failure ("DEATH. parameter_types: predicate " ^ name ^ " does not exist.")) in 
          (*   Printf.printf "Pred: %s\n\tParams1: %s\n\tParams2: %s\n" name
              (String.concat ", " (let x, _ = List.split pred.params in x)) (String.concat ", " (List.map Expr.str les)); *)
          let ac_types = 
            List.fold_left 
              (fun ac_types ((x, t_x), le) -> 
                match t_x with 
                | None     ->  ac_types  
                | Some t_x -> (le, t_x) :: ac_types) 
              [] (List.combine pred.params les) in 
          Star (Types(ac_types), a) 
        | _ -> a in   
    Asrt.map None (Some f_a_after) None None a in 
              
  { lemma with pre = (pt_asrt lemma.pre); posts = List.map pt_asrt lemma.posts } 

  