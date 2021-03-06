module type M = 
  sig 

  type vt 
  type st 
  type err_t 
  type state_t 
  type preds_t 


  type t = state_t * preds_t * UP.preds_tbl_t

  type post_res = (Flag.t * (Asrt.t list)) option

  type search_state = (t * st * UP.t) list * err_t list 

  type up_u_res = 
    | UPUSucc of (t * st * post_res) list
    | UPUFail of err_t list 

  type gp_ret = 
    | GPSucc  of (t * (vt list)) list 
    | GPFail  of err_t list 

  type u_res = 
    | UWTF    
    | USucc   of t
    | UFail   of err_t list  

  type unfold_info_t = string * ((string * Expr.t) list)  

  val produce_assertion : t -> st -> Asrt.t -> t option 

  val produce : t -> st -> Asrt.t -> t option 

  val produce_posts : t -> st -> Asrt.t list -> t list 

  val unfold : t -> string -> vt list -> unfold_info_t option -> (st * t) list 

  val rec_unfold : t -> string -> vt list -> t 
  
  val unfold_all : t -> string -> t 

  val unfold_with_vals : t -> vt list -> (st * t) list * bool 

  val unify_assertion : t -> st -> Asrt.t -> u_res

  val unify_up : search_state -> up_u_res 

  val unify : ?in_unification:bool -> t -> st -> UP.t -> up_u_res

  val get_pred : ?in_unification:bool -> t -> string -> vt list -> gp_ret
    

  end 


