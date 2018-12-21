open CCommon
open SCommon
(**
    Interface for JSIL General States.
    They are considered to be mutable.
*)

module type M = sig 
      (** Type of JSIL values *)
      type vt

      (** Type of JSIL general states *)
      type t

      (** Type of JSIL substitutions *)
      type st 

      (** Type of JSIL stores *)
      type store_t

      (** Errors *)
      type err_t 

      exception Internal_State_Error of (err_t list) * t

      type gc_ret = 
        | GCSucc  of (t * vt * vt * (vt option)) list
        | GCFail  of err_t list  

      type gd_ret = 
        | GDSucc  of (t * vt) list
        | GDFail  of err_t list  

      type gm_ret = 
        | GMSucc  of (t * vt * vt) list 
        | GMFail  of err_t list 

      type u_res = 
        | UWTF    
        | USucc   of t
        | UFail   of err_t list  

      (** Initialisation *)
      val init : UP.preds_tbl_t option -> t 

      val get_pred_defs : t -> UP.preds_tbl_t option

      (** Expression Evaluation *)
      val eval_expr : t -> Expr.t -> vt

      (** Get store of given symbolic state *)
      val get_store : t -> store_t 

      (** Set store of given symbolic state *)
      val set_store : t -> store_t -> t 

      (** Object Allocation *)
      val alloc : t -> vt option -> vt -> (vt * t) 

      (** Convert value to object location, with possible allocation *)
      val to_loc : t -> vt -> (t * vt) option 

      (** Get cell *)
      val get_cell : ?remove:bool -> t -> vt -> vt -> gc_ret 

      (** Set cell *)
      val set_cell : t -> vt -> vt -> vt option -> t 

      (** Get domain of given object *)
      val get_domain : ?expected_props:vt -> ?remove:bool -> t -> vt -> gd_ret 

      (** Set domain of given object to given set of properties *)
      val set_domain : t -> vt -> vt -> t

      (** Get metadata of given object *)
      val get_metadata : ?remove:bool -> t -> vt -> gm_ret

      (** Set metadata of given object to given value *)
      val set_metadata : t -> vt -> vt -> t 

      (** Object deletion *)
      val delete_object : t -> Expr.t -> t 

      (** Assume expression *)
      val assume : t -> vt -> t list

      (** Assume assertion *)
      val assume_a : t -> Formula.t list -> t option 

      (** Assume type *)
      val assume_t : t -> vt -> Type.t -> t option 

      (** Satisfiability check *)
      val sat_check : t -> vt -> bool
 
      val sat_check_f : t -> Formula.t list -> st option 

      (** Assert assertion *)
      val assert_a : t -> Formula.t list -> bool 

      (** Value Equality *)
      val equals : t -> vt -> vt -> bool  

      (** Value Type *)
      val get_type : t -> vt -> Type.t option 

      (** State simplification *)
      val simplify : ?kill:bool -> t -> st

      (** Value simplification *)
      val simplify_val : t -> vt -> vt 

      (** Printer *)
      val str : t -> string 

      (** State Copy *)
      val copy : t -> t

      (** Add Spec Var *)
      val add_spec_vars : t -> Var.Set.t -> t 

      (** Get Spec Vars *)
      val get_spec_vars : t -> Var.Set.t

      (** Get all logical variables *)
      val get_lvars : t -> Var.Set.t

      (** Turns a state into a list of assertions *)
      val to_assertions : ?to_keep:SS.t -> t -> Asrt.t list  

      val evaluate_slcmd : UP.prog -> SLCmd.t -> t -> t list 

      val run_spec : UP.spec -> t -> vt list -> (string * (string * vt) list) option -> (t * vt option * Flag.t) list

      val unfolding_vals : t -> Formula.t list -> vt list

      val substitution_in_place : st -> t -> unit 

      val fresh_val : t -> vt 

      val fresh_loc : ?loc:vt -> t -> vt 

      val get_locs : t -> vt list 

      val get_locs_and_props : t -> (vt * vt) list 

      val clean_up : t -> unit

      val unify_assertion : t -> st -> Asrt.t -> u_res

      val produce_posts : t -> st -> Asrt.t list -> t list

      val produce : t -> st -> Asrt.t -> t option  

      val update_subst : t -> st -> unit 
end