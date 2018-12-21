open CCommon
open SCommon

module Error :
  sig
    type vt = SVal.M.t
    type st = SVal.SSubst.t
    type fix_t 
    type up_error
    type t = MakeError.M(SVal.M)(SVal.SSubst).t 
    exception ThrowError of t
    val str : t -> string
    val can_fix : t list -> bool
    val get_recovery_vals : t list -> vt list
    val get_failing_constraint : t -> Formula.t
    val string_of_fix : fix_t -> string
    val sanitise : t list -> t list
  end

type t 

type pred = {
  pred : Pred.t; 
  pure : bool;
  up   : t 	
}

type spec = { 
  spec: Spec.t; 
  up  : t 
}

type lemma = { 
  lemma: Lemma.t; 
  up   : t 
}

type prog = { 
  preds    : (string, pred) Hashtbl.t; 
  specs    : (string, spec) Hashtbl.t; 
  lemmas   : (string, lemma) Hashtbl.t;
  coverage : (string * int, int) Hashtbl.t;  
  prog     : Prog.t
}

type preds_tbl_t = (string, pred) Hashtbl.t


val collect_simple_asrts : Asrt.t -> Asrt.t list

val init : ?use_params:bool -> SS.t -> SS.t -> (string, Pred.t) Hashtbl.t -> (Asrt.t * ((string * SS.t) option * (Flag.t * (Asrt.t list)) option)) list -> (t, Asrt.t list list) result

val next : ?lab:string -> t -> ((t  * (string * SS.t) option) list) option

val head : t -> Asrt.t option 

val posts : t -> (Flag.t *  (Asrt.t list)) option

val init_prog : Prog.t -> (prog, Error.t) result 

val str : t -> string 

val create_partial_match_spec : Spec.t -> Spec.st option

val get_pred_def : preds_tbl_t -> string -> pred 

val init_pred_defs : unit -> preds_tbl_t

val string_of_pred_defs : preds_tbl_t -> string 

val get_procs : prog -> Proc.t list 

val get_bispecs : prog -> BiSpec.t list 

val string_of_asrt : ?preds_printer:(string * (Expr.t list) -> string option) -> preds_tbl_t -> Asrt.t -> string 
 
val string_of_spec : ?preds_printer:(string * (Expr.t list) -> string option) -> preds_tbl_t -> Spec.t -> string 

val string_of_normal_spec : ?preds_printer:(string * (Expr.t list) -> string option) -> preds_tbl_t -> Spec.t -> string 

val outs_expr : Expr.t -> SS.t

val add_spec : prog -> Spec.t -> unit

val get_lemma : prog -> string -> (lemma, unit) result

val update_coverage : prog -> string -> int -> unit  

val first_time_running : prog -> string -> int -> bool 
