open CCommon

type jp_token = [%import: JSIL_Parser.token] [@@deriving show]

let parse start (lexbuf : Lexing.lexbuf) =

  let print_position
      (outx : Format.formatter)
      (lexbuf : Lexing.lexbuf) : unit =
    let pos = lexbuf.lex_curr_p in
    Format.fprintf outx "%s:%d:%d" pos.pos_fname
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) in 

  let module JPMI = JSIL_Parser.MenhirInterpreter in

  let last_token = ref JSIL_Parser.EOF
  in let lexer lexbuf =
       let token = JSIL_Lexer.read lexbuf in
       last_token := token; token
  in

  (** ----------------------------------------------------
      Start the interpreter
      -----------------------------------------------------
  *)
  JPMI.loop_handle
    (fun result -> result)

    (** ----------------------------------------------------
        Terminate if an error occurs
        -----------------------------------------------------
    *)
    (function JPMI.Rejected -> failwith "Parser rejected input"
            | JPMI.HandlingError e ->
              let csn = JPMI.current_state_number e in
              Format.eprintf "%a, last token: %s: %s.@."
                print_position lexbuf
                (show_jp_token !last_token)
                "Error message found";
              raise JSIL_Parser.Error
            | _ -> failwith "Unexpected state in failure handler!"
    )
    (JPMI.lexer_lexbuf_to_supplier lexer lexbuf)
    (start lexbuf.Lexing.lex_curr_p)



let parse_eprog_from_string (str : string) : EProg.t =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  let prog = parse JSIL_Parser.Incremental.main_target lexbuf in
    prog

let parse_js_pre_from_string (str : string) : (string * string list) option * JSAsrt.t =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  try 
    parse JSIL_Parser.Incremental.top_level_js_pre_target lexbuf
  with _ -> 
    let msg = Printf.sprintf "Parsing error with: %s" str in 
    raise (Failure msg)

let parse_js_logic_assertion_from_string (str : string) : JSAsrt.t =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  try 
    parse JSIL_Parser.Incremental.top_level_js_assertion_target lexbuf
  with _ -> 
    let msg = Printf.sprintf "Parsing error with: %s" str in 
    raise (Failure msg)

let parse_js_logic_assertion_list_from_string (str : string) : JSAsrt.t list =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  try 
    parse JSIL_Parser.Incremental.top_level_js_assertion_list_target lexbuf
  with _ -> 
    let msg = Printf.sprintf "Parsing error with: %s" str in 
    raise (Failure msg)
    
let parse_expr_from_string (str : string) : Expr.t =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  try 
    parse JSIL_Parser.Incremental.top_level_expr_target lexbuf
  with _ -> 
    let msg = Printf.sprintf "Parsing error with: %s" str in 
    raise (Failure msg)

let parse_js_logic_predicate_from_string (str : string) : JSPred.t =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  try 
    parse JSIL_Parser.Incremental.js_pred_target lexbuf
  with _ -> 
    let msg = Printf.sprintf "Parsing error with: %s" str in 
    raise (Failure msg)

let parse_js_only_spec_from_string (str : string) : JSSpec.t =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  try 
    parse JSIL_Parser.Incremental.js_only_spec_target lexbuf
  with _ -> 
    let msg = Printf.sprintf "Parsing error with: %s" str in 
    raise (Failure msg)

let parse_js_logic_commands_from_string (str : string) : JSLCmd.t list =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  try 
    parse JSIL_Parser.Incremental.js_logic_cmds_target lexbuf
  with _ -> 
    let msg = Printf.sprintf "Parsing error with: %s" str in 
    raise (Failure msg)

let parse_eprog_from_file (path : string) : EProg.t =
  let extension = List.hd (List.rev (Str.split (Str.regexp "\.") path)) in
  let file_previously_normalised = String.equal "njsil" extension in

  CCommon.previously_normalised := file_previously_normalised;

  (* Check that the file is of a valid type *)
  (match (file_previously_normalised || (String.equal "jsil" extension)) with
    | true -> ()
    | false -> raise (Failure (Printf.sprintf "Failed to import %s: not a .jsil or .njsil file." path)));

  let inx = open_in path in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
  let prog = parse JSIL_Parser.Incremental.main_target lexbuf in
  close_in inx;

  prog

let eprog_to_prog (ext_program : EProg.t) : Prog.t =

  (** ----------------------------------------------------
      Add the declarations in 'program_from' to 'program_to'.
      -----------------------------------------------------
  *)
  let extend_declarations
      (program_to : EProg.t)
      (program_from : EProg.t) : unit =

    (** Step 1 - Extend the predicates
      * -----------------------------------------------------------------------------------
      *)
    Hashtbl.iter
      (fun pred_name pred ->
        (if (Hashtbl.mem program_to.preds pred_name)
         then L.log L.Verboser (lazy (Printf.sprintf "*** WARNING: Predicate %s already exists.\n" pred_name))
         else L.log L.Verboser (lazy (Printf.sprintf "*** MESSAGE: Adding predicate %s.\n" pred_name)));
        Hashtbl.add program_to.preds pred_name pred)
     program_from.preds;

   (** Step 2 - Extend the procedures, except where a procedure with the same name already exists
     * -----------------------------------------------------------------------------------
     *)
    Hashtbl.iter
      (fun proc_name (proc : EProc.t) ->
        if (not (Hashtbl.mem program_to.procs proc_name))
          then (L.log L.Verboser (lazy (Printf.sprintf "*** MESSAGE: Adding procedure: %s.\n" proc_name)); 
            let adjusted_proc : EProc.t = { proc with 
              spec = Option.map (fun (spec : Spec.t) -> { spec with to_verify = false }) proc.spec } in 
            Hashtbl.add program_to.procs proc_name adjusted_proc)
          else (L.log L.Verboser (lazy (Printf.sprintf "*** WARNING: Procedure %s already exists.\n" proc_name))))
      program_from.procs;
      
    (** Step 3 - Extend the onlyspecs
      * -----------------------------------------------------------------------------------
      *)
     Hashtbl.iter
      (fun proc_name proc ->
        if (not (Hashtbl.mem program_to.only_specs proc_name))
          then (L.log L.Verboser (lazy (Printf.sprintf "*** MESSAGE: Adding onlyspec procedure: %s.\n" proc_name)); Hashtbl.add program_to.only_specs proc_name proc)
          else (L.log L.Verboser (lazy (Printf.sprintf "*** WARNING: Procedure %s already exists.\n" proc_name))))
      program_from.only_specs; 

    (** Step 4 - Extend the macros
      * -----------------------------------------------------------------------------------
      *)
     Hashtbl.iter
      (fun macro_name macro ->
        if (not (Hashtbl.mem program_to.macros macro_name))
          then (L.log L.Verboser (lazy (Printf.sprintf "*** MESSAGE: Adding macro: %s.\n" macro_name)); Hashtbl.add program_to.macros macro_name macro)
          else (L.log L.Verboser (lazy (Printf.sprintf "*** WARNING: Procedure %s already exists.\n" macro_name))))
      program_from.macros in

  let resolve_imports (program : EProg.t) : unit =

    (* 'added_imports' keeps track of the loaded files *)
    (** Step 1 - Create a hashtable 'added_imports' which keeps track of the loaded files
      * -----------------------------------------------------------------------------------
      *)
    let added_imports = Hashtbl.create 32 in

    (** Step 2 - Extend the program with each of the programs in imports
      * -----------------------------------------------------------------------------------
      *)
    let rec resolve_imports_iter imports =
      (match imports with
      | [] -> ()
      | file :: rest_imports ->
        if (not (Hashtbl.mem added_imports file))
          then
            (Hashtbl.replace added_imports file true;
            let imported_program = parse_eprog_from_file file in
            extend_declarations program imported_program;
       resolve_imports_iter (rest_imports @ imported_program.imports))) in
    resolve_imports_iter program.imports in 


  (** Step 1 - Add the declarations from the imported files
    * -----------------------------------------------------------------------------------
    *)
  resolve_imports ext_program;

  let proc_of_ext_proc (proc : EProc.t) : Proc.t * (string * int * int * int ) list = 
    let name = proc.name in 

    (** Step 2.1 - Desugar labels
     * -----------------------------------------------------------------------------------
     *)
    let proc = EProc.to_proc proc in

    (** Step 2.2 - Get the succ and pred tables
     * -----------------------------------------------------------------------------------
     *)
    let succ_table, pred_table = PreProcessing_Utils.get_succ_pred proc.body in

    (** Step 2.3 - Compute the which_pred table
     * -----------------------------------------------------------------------------------
     *)
    let predecessors = PreProcessing_Utils.compute_which_preds pred_table in
    
    (** Step 2.4 - Update the global_which_pred table with the correct indexes
      * -----------------------------------------------------------------------------------
      *)
    let predecessors' = 
      List.map 
        (fun (prev_cmd, cur_cmd, i) -> (name, prev_cmd, cur_cmd, i))
        predecessors in 

     proc, predecessors' in 


  let procs, predecessors = 
    Hashtbl.fold 
      (fun (name : string) (proc : EProc.t) (procs, predecessors)  ->
        let proc, new_predecessors = proc_of_ext_proc proc in 
        (proc :: procs, new_predecessors @ predecessors))
    ext_program.procs ([], []) in 
  
  Prog.init ext_program.lemmas ext_program.preds ext_program.only_specs procs predecessors ext_program.macros ext_program.bi_specs

(** ----------------------------------------------------
    Parse a line_numbers file. 
    Proc: proc_name 
    (0, 0)
    ...
    -----------------------------------------------------
*)
let parse_line_numbers (ln_str : string) : (string * int, int * bool) Hashtbl.t = 
  
  let strs            = Str.split (Str.regexp_string "Proc: ") ln_str in
  let line_info       = Hashtbl.create big_tbl_size in 
  List.iter (fun str -> 
    let memory         = Hashtbl.create small_tbl_size in 
    let index          = String.index str '\n' in 
    let proc_name      = String.sub str 0 index in 
    let proc_line_info = String.sub str (index+1) ((String.length str) - (index+1))  in 
    let lines          = Str.split (Str.regexp_string "\n") proc_line_info in 
    List.iter 
      (fun line -> Scanf.sscanf line "(%d, %d)" 
        (fun x y -> 
            if (Hashtbl.mem memory y)
              then Hashtbl.replace line_info (proc_name, x) (y, false)
              else (
                Hashtbl.replace memory y true; 
                Hashtbl.replace line_info (proc_name, x) (y, true) 
              )
        )) lines;  
  ) strs; 

  line_info 