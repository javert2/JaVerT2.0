(** Logging levels *)
type t = 
  | Normal    (** Normal output *)
  | Verbose   (** Verbose output *)
  | Verboser  (** More verbose output *)
  | TMI       (** Too much information *)

(** Logging enabled *)
let silent = ref false

(** File prefix for log files *)
let log_prefix = "log_"

(** File extension for log files *)
let log_extension = "log"

(** 
  Log filenames 

  @param lvl Logging level
  @return Filename of the level
*)
let filename (lvl : t) : string = log_prefix ^ 
  (match lvl with
  | Normal ->  "normal"
  | Verbose -> "verbose"
  | Verboser -> "verboser"
  | TMI -> "TMI") ^ "." ^ log_extension

(** File descriptors for log files *)
let log_normal = ref (open_out (filename Normal))
let log_verbose = ref (open_out (filename Verbose))
let log_verboser = ref (open_out (filename Verboser))
let log_TMI = ref (open_out (filename TMI))

let wrap_up () : unit = 
  close_out !log_normal;
  close_out !log_verbose;
  close_out !log_verboser;
  close_out !log_TMI

(** 
  Actual logging

  @param lvl Logging level
  @param msg Log message
*)
let log lvl (msg : string lazy_t) : unit = 
  if (not !silent) then 
    let msg = Lazy.force msg in 
    let msg = Printf.sprintf "%s\n%!" msg in 
    (match lvl with 
    | Normal -> output_string !log_normal msg; output_string !log_verbose msg; output_string !log_verboser msg; output_string !log_TMI msg
    | Verbose -> output_string !log_verbose msg; output_string !log_verboser msg; output_string !log_TMI msg
    | Verboser -> output_string !log_verboser msg; output_string !log_TMI msg
    | TMI -> output_string !log_TMI msg) 

(** Closing file descriptors *)

let log_with_close lvl (msg : string lazy_t) : unit = 
  if (not !silent) then 
    let msg = Lazy.force msg in 
    let msg = Printf.sprintf "%s\n%!" msg in 
    (match lvl with 
    | Normal -> output_string !log_normal msg; output_string !log_verbose msg; output_string !log_verboser msg; output_string !log_TMI msg
    | Verbose -> output_string !log_verbose msg; output_string !log_verboser msg; output_string !log_TMI msg
    | Verboser -> output_string !log_verboser msg; output_string !log_TMI msg
    | TMI -> output_string !log_TMI msg);
    wrap_up ();
    log_normal := open_out_gen [Open_creat; Open_text; Open_append] 0o640 (filename Normal);
    log_verbose := open_out_gen [Open_creat; Open_text; Open_append] 0o640 (filename Verbose);
    log_verboser := open_out_gen [Open_creat; Open_text; Open_append] 0o640 (filename Verboser);
    log_TMI := open_out_gen [Open_creat; Open_text; Open_append] 0o640 (filename TMI)

(** Failure *)
let fail msg = 
  log Normal (lazy msg);
  raise (Failure msg)