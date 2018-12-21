open CCommon
open SCommon

module L = Logging

type t = {
  imports    : string list;                  (* Import statements = [Filename : String] *)
  lemmas     : (string, Lemma.t)  Hashtbl.t; (* Lemmas *)
  preds      : (string, Pred.t)   Hashtbl.t; (* Predicates = Name : String --> Definition *)
  only_specs : (string, Spec.t)   Hashtbl.t; (* Specs = Name : String --> Spec *)
  procs      : (string, EProc.t)  Hashtbl.t; (* JSIL extended procedures = Name : String --> Procedure *)
  macros     : (string, Macro.t)  Hashtbl.t; (* macros *)
  bi_specs   : (string, BiSpec.t) Hashtbl.t; (* Hints for bi-abduction *)
  proc_names : string list
}


let init
  (imports      : string list)
  (lemmas       : (string, Lemma.t) Hashtbl.t)
  (preds        : (string, Pred.t) Hashtbl.t)
  (only_specs   : (string, Spec.t) Hashtbl.t)
  (procs        : (string, EProc.t) Hashtbl.t) 
  (macros       : (string, Macro.t) Hashtbl.t)
  (bi_specs     : (string, BiSpec.t) Hashtbl.t)
  (proc_names   : string list) : t = 
  {
    imports      = imports; 
    lemmas       = lemmas; 
    preds        = preds; 
    only_specs   = only_specs; 
    procs        = procs;  
    macros       = macros; 
    bi_specs     = bi_specs; 
    proc_names   = proc_names 
  }
 

let get_lemmas (prog : t) : Lemma.t list = 
  Hashtbl.fold (fun _ lemma ac -> lemma :: ac)  prog.lemmas [] 


let get_preds (prog : t) : Pred.t list = 
  Hashtbl.fold (fun _ lemma ac -> lemma :: ac)  prog.preds [] 


let get_ospecs (prog : t) : Spec.t list = 
  Hashtbl.fold (fun _ spec ac -> spec :: ac) prog.only_specs []  


let get_specs (prog : t) : Spec.t list = 
  Hashtbl.fold 
    (fun _ (proc : EProc.t) ac -> Option.map_default (fun spec -> spec :: ac) ac proc.spec) 
    prog.procs (get_ospecs prog) 


let get_procs ?(proc_names : (string list) option) (prog : t) : EProc.t list = 

  let proc_names = 
    match proc_names with 
      | Some proc_names -> 
        (* Printf.printf "GET PROCS with proc_names: %s\n" (String.concat ", " proc_names); *)
        proc_names 
      | None -> Hashtbl.fold (fun proc_name _ proc_names -> proc_name :: proc_names) prog.procs [] in 
  List.map (fun proc_name -> Hashtbl.find prog.procs proc_name) proc_names 


let get_proc (prog : t) (proc_name : string) : EProc.t option = 
    Hashtbl.find_opt prog.procs proc_name 


let get_bispecs (prog : t) : BiSpec.t list = 
  Hashtbl.fold (fun _ bi_spec ac -> bi_spec :: ac) prog.bi_specs []


let str (prog : t) : string =
  let imports = prog.imports in 
  let imports_str = 
    if (imports = []) then "" else "import " ^ (String.concat ", " imports) ^ ";" in 

  let lemmas_strs  = List.map Lemma.str (get_lemmas prog) in 
  let preds_strs   = List.map Pred.str (get_preds prog) in 
  let specs_strs   = List.map (fun spec -> "only " ^ (Spec.str spec)) (get_ospecs prog) in 
  let procs_str    = List.map EProc.str (get_procs ~proc_names:prog.proc_names prog) in 
  let bi_specs_str = List.map BiSpec.str (get_bispecs prog) in 
  let strs         = imports_str :: (lemmas_strs @ preds_strs @ specs_strs @ bi_specs_str @ procs_str) in 
  String.concat "\n" strs 


let line_info (prog : t) : (string * int * int) list =
  List.concat (List.map EProc.line_info (get_procs prog)) 


let perform_syntax_checks (ext_prog : t) (prog : Prog.t) : unit =
  let which_pred = prog.predecessors in 
  if (!CCommon.perform_syntax_checks)
  then (
    L.log L.Normal (lazy (Printf.sprintf "Running syntax checks:"));
    L.log L.Normal (lazy (Printf.sprintf "Checking predicate definitions only use program variables they are allowed to."));
    Pred.check_pvars ext_prog.preds;
    L.log L.Normal (lazy (Printf.sprintf "Checking spec definitions only use program variables they're allowed to."));
    EProc.check_spec_pvars ext_prog.procs;
    L.log L.Normal (lazy (Printf.sprintf "Checking specs correspond directly to procedures"));
    EProc.check_proc_spec_correspondence ext_prog.procs;
  )


let update_specs (eprog : t) (prog : Prog.t) : unit = 
  Hashtbl.iter 
    (fun (proc_name : string) (proc : Proc.t) -> 
      match proc.spec, Hashtbl.find_opt eprog.procs proc_name with 
        | Some spec, Some eproc -> 
            Hashtbl.replace eprog.procs proc_name { eproc with spec = Some spec } 
        | _ -> () 
    ) prog.procs; 
  Hashtbl.clear eprog.bi_specs
