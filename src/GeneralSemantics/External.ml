open CCommon
open Literal

(** JSIL external procedure calls *)
module M
  (Val   : Val.M) 
  (Subst : Subst.M with type vt = Val.t and type t = Val.st)
  (Store : Store.M with type vt = Val.t) 
  (State : State.M with type vt = Val.t and type st = Subst.t and type store_t = Store.t) = struct 

  module CallStack = CallStack.M(Val)(Store)

  let update_store state x v = 
    let store  = State.get_store state in 
    let _      = Store.put store x v in 
    let state' = State.set_store state store in 
      state'

  (** 
    JavaScript Eval

    @param prog JSIL program
    @param state Current state
    @param preds Current predicates
    @param cs Current call stack
    @param i Current index
    @param x Variable that stores the result
    @param v_args Parameters
    @param j Optional error index
    @return Resulting configuration
  *)
  let execute_eval prog state cs i x v_args j =  
    let store  = State.get_store state in 
    let v_args = v_args @ [ Val.from_literal Undefined ] in 
    (match v_args with 
    | x_scope :: x_this :: v_code :: _ -> 
      let opt_lit_code = Val.to_literal v_code in 
      (match opt_lit_code with 
      | None -> raise (Failure "Eval statement argument not a literal string")
      | Some (String code) ->
          let code = Str.global_replace (Str.regexp (Str.quote "\\\"")) "\"" code in
          let opt_proc_eval = (try
            let e_js = JSParserMain.exp_from_string ~force_strict:true code in
            let cur_proc_id = CallStack.get_cur_proc_id cs in 
              Some (JS2JSIL_Compiler.js2jsil_eval prog cur_proc_id e_js)
            with _ -> None) in 
          (match opt_proc_eval with
          | Some proc_eval ->
              let eval_v_args = [ x_scope; x_this ] in 
              let proc = Prog.get_proc prog proc_eval in 
              let proc = (match proc with | Some proc -> proc | None -> raise (Failure ("The eval procedure does not exist."))) in 
              let params = Proc.get_params proc in
              let prmlen = List.length params in 

              let args   = Array.make prmlen (Val.from_literal Undefined) in 
              let _      = List.iteri (fun i v_arg -> if (i < prmlen) then (args.(i) <- v_arg)) eval_v_args in 
              let args   = Array.to_list args in 

              let new_store  = Store.init (List.combine params args) in
              let old_store  = State.get_store state in 
              let state'     = State.set_store state new_store in 
              let cs'        = (proc_eval, eval_v_args, Some old_store, x, i, i+1, j) :: cs in 
                [ state', cs', -1, 0 ]

          | None -> 
            (match Store.get store (JS2JSIL_Constants.var_se), j with
            | Some v, Some j ->
                update_store state x v;
                [ state, cs, i, j ] 
            | _, None -> raise (Failure ("Eval triggered an error, but no error label was provided"))
            | _, _ -> raise (Failure "JavaScript SyntaxError object undefined")))

      | _ -> update_store state x v_code;
             [ state, cs, i, i+1 ])) 

  (** 
    JavaScript Function Constructor

    @param prog JSIL program
    @param state Current state
    @param cs Current call stack
    @param i Current index
    @param x Variable that stores the result
    @param v_args Parameters
    @param j Optional error index
    @return Resulting configuration
  *)
  (* Two arguments only, the parameters and the function body *)
  let execute_function_constructor prog state cs i x v_args j = 

      let throw message = 
        update_store state x (Val.from_literal (String message));
        [ state, cs, i, Option.get j ] in 

      (* Initialise parameters and body *)
      let params : Literal.t = Option.get (Val.to_literal (List.nth v_args 0)) in
      let body   : Literal.t = Option.get (Val.to_literal (List.nth v_args 1)) in 

      (match params, body with
      | String params, String code -> 

          let code = Str.global_replace (Str.regexp (Str.quote "\\\"")) "\"" code in
          let code = "function THISISANELABORATENAME (" ^ params ^ ") {" ^ code ^ "}" in

          let e_js = (try (Some (JSParserMain.exp_from_string ~force_strict:true code)) with | _ -> None) in
          (match e_js with
          | None -> throw "Body not parsable."
          | Some e_js ->
              (match e_js.JSParserSyntax.exp_stx with
                | Script (_, e :: []) ->
                  (match e.JSParserSyntax.exp_stx with
                  | JSParserSyntax.Function (_, Some "THISISANELABORATENAME", params, body) ->
                      let cur_proc_id = CallStack.get_cur_proc_id cs in 
                      let new_proc = JS2JSIL_Compiler.js2jsil_function_constructor_prop prog cur_proc_id params body in
                      let fun_name = String new_proc.name in
                      let params = LList (List.map (fun x -> String x) params) in 
                      let return_value = LList [ fun_name; params ] in 
                      update_store state x (Val.from_literal return_value);
                      [ state, cs, i, i+1 ]

                  | _ -> throw "Body incorrectly parsed.")
                | _ -> throw "Not a script."))
        | _, _ -> throw "Body or parameters not a string.")

  (** 
    General External Procedure Treatment

    @param prog JSIL program
    @param state Current state
    @param cs Current call stack
    @param i Current index
    @param x Variable that stores the result
    @param pid Procedure identifier
    @param v_args Parameters
    @param j Optional error index
    @return Resulting configuration
  *)
  let execute 
      (prog   : Prog.t) 
      (state  : State.t)
      (cs     : CallStack.t) 
      (i      : int) 
      (x      : string) 
      (pid    : string) 
      (v_args : Val.t list) 
      (j      : int option) = 
    (match pid with 
    | "ExecuteEval"                -> execute_eval                 prog state cs i x v_args j
    | "ExecuteFunctionConstructor" -> execute_function_constructor prog state cs i x v_args j
    | _ -> raise (Failure ("Unsupported external procedure call: " ^ pid)))

end