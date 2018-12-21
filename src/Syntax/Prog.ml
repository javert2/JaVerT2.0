open CCommon 
open SCommon

type predecessors = (string * int * int, int) Hashtbl.t

type t = { 
  (* Lemmas *)
  lemmas : (string, Lemma.t) Hashtbl.t;
  (* Predicates = Name : String --> Definition *)
  preds : (string, Pred.t) Hashtbl.t;
  (* Specs = Name : String --> Spec *)
  only_specs : (string, Spec.t) Hashtbl.t;
  (* JSIL extended procedures = Name : String --> Procedure *)
  procs : (string, Proc.t) Hashtbl.t;
  (* which pred*)
  predecessors : predecessors; 
  (* macros *)
  macros : (string, Macro.t) Hashtbl.t;
  (* bispecs *)
  bi_specs : (string, BiSpec.t) Hashtbl.t
}

let init
  (lemmas       : (string, Lemma.t) Hashtbl.t)
  (preds        : (string, Pred.t) Hashtbl.t)
  (only_specs   : (string, Spec.t) Hashtbl.t)
  (procs        : Proc.t list) 
  (predecessors : (string * int * int * int) list)
  (macros       :  (string, Macro.t) Hashtbl.t) 
  (bi_specs     :  (string, BiSpec.t) Hashtbl.t): t = 

  let procs_tbl      = Hashtbl.create big_tbl_size in 
  let predecessors'  = Hashtbl.create big_tbl_size in
  List.iter (fun (proc   : Proc.t)  -> Hashtbl.replace procs_tbl     proc.name proc) procs;
  List.iter (fun (name, j, i, k) -> Hashtbl.replace predecessors' (name, j, i) k) predecessors; 

  {
    lemmas       = lemmas; 
    preds        = preds; 
    only_specs   = only_specs; 
    procs        = procs_tbl;    
    predecessors = predecessors'; 
    macros       = macros; 
    bi_specs     = bi_specs  
  }
 
let get_bispec (prog : t) (name : string) : BiSpec.t option = 
  Hashtbl.find_opt prog.bi_specs name 


(* Retrieves the lemma with the given name from the given program *)
let get_lemma 
    (prog : t) 
    (name : string) : Lemma.t =
  try 
    Hashtbl.find prog.lemmas name
  with Not_found -> raise (Failure (Printf.sprintf "DEATH. Lemma %s does not exist" name))

(* Retrieves the pred with the given name from the given program *)
let get_pred 
    (prog : t) 
    (name : string) : Pred.t option =
  Hashtbl.find_opt prog.preds name

(* Retrieves the spec with the given name from the given program *)
let get_spec 
    (prog : t) 
    (name : string) : Spec.t option =
  let spec = Hashtbl.find_opt prog.only_specs name in 
  let proc = Hashtbl.find_opt prog.procs name in 
  match spec, proc with 
  | Some spec, _ -> Some spec
  | None, Some proc -> proc.spec 
  | _ -> None 

(* Retrieves the procedure with the given name from the given program *)
let get_proc 
    (prog : t) 
    (proc_name : string) : Proc.t option =
  Hashtbl.find_opt prog.procs proc_name

let get_lemmas (prog : t) : Lemma.t list = 
  List.rev (Hashtbl.fold 
    (fun  _ lemma ac -> lemma :: ac) 
    prog.lemmas 
    [])

let get_preds (prog : t) : Pred.t list = 
  List.rev (Hashtbl.fold (fun _ pred ac -> pred :: ac) prog.preds []) 

let get_ospecs (prog : t) : Spec.t list = 
  List.rev (Hashtbl.fold (fun _ spec ac -> spec :: ac) prog.only_specs [])  

let get_proc_specs (prog : t) : Spec.t list = 
  List.rev (Hashtbl.fold (fun _ (proc : Proc.t) ac -> Option.map_default (fun spec -> spec :: ac) ac proc.spec) prog.procs [])

let get_specs (prog : t) : Spec.t list = 
  (get_ospecs prog) @ (get_proc_specs prog)

let get_procs (prog : t) : Proc.t list = 
  Hashtbl.fold (fun _ proc ac -> proc :: ac) prog.procs []
     
let get_bispecs (prog : t) : BiSpec.t list = 
  Hashtbl.fold (fun _ bi_spec ac -> bi_spec :: ac) prog.bi_specs []

let line_info (prog : t) : (string * int * int) list =
  List.concat (List.map Proc.line_info (get_procs prog)) 


let str (prog : t) : string =
  let lemmas_strs = List.map Lemma.str (get_lemmas prog) in 
  let preds_strs  = List.map Pred.str (get_preds prog) in 
  let specs_strs  = List.map (fun spec -> "only " ^ (Spec.str spec)) (get_ospecs prog) in 
  let procs_str   = List.map Proc.str (get_procs prog) in 
  let strs        = lemmas_strs @ preds_strs @ specs_strs @ procs_str in 
  String.concat "\n" strs 