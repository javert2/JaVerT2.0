(** {b Single JSIL specifications}. *)
type t = {
  name       : string;       (** Procedure/spec name               *) 
  params     : string list;  (** Procedure/spec parameters         *)
  pre        : Asrt.t;       (** Precondition                      *)
  normalised : bool;         (** If the spec is already normalised *)
}

type t_tbl = (string, t) Hashtbl.t

let init (name : string) (params : string list) (pre : Asrt.t) (normalised : bool) : t =
  {
    name       = name;
    params     = params;
    pre        = pre;
    normalised = normalised
  }


let init_tbl () : t_tbl = Hashtbl.create CCommon.medium_tbl_size 


let str (bi_spec : t) : string = 
  Printf.sprintf "bispec %s (%s) :  [[ %s ]] \n"
    bi_spec.name 
    (String.concat ", " bi_spec.params)
    (Asrt.str bi_spec.pre)
