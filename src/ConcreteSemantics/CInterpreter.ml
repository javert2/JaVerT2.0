module M = struct 
  include MakeInterpreter.M(CVal.M)(CVal.CSubst)(CStore.M)(CError.M)(CState)

  let string_of_js_error (heap : CHeap.t) (err_val : Literal.t) =
    match err_val with
    | Loc loc ->
    (* Get the error object in the heap *)
    let err_obj = CHeap.get heap loc in
    (match err_obj with
      | None -> raise (Failure "Error object doesn't exist in the heap.")
      | Some (err_obj, Loc err_obj_metadata) ->
        (* Get its metadata *)
        let err_obj_metadata = CHeap.get heap err_obj_metadata in
        (match err_obj_metadata with
        | None -> raise (Failure "Error metadata object doesn't exist in the heap.")
        | Some (err_obj_metadata, _) ->
            (* Get the proto field *)
            let lproto = CObject.get err_obj_metadata "@proto" in
            (match lproto with
            | None -> raise (Failure "Error object without a prototype.")
            | Some (Loc lproto) ->
                (* Get the proto object *)
                let objproto = CHeap.get heap lproto in
                (match objproto with
                | None -> raise (Failure "Prototype object doesn't exist in the heap.")
                | Some (objproto, _) -> 
                    let eType = (match CObject.get objproto "name" with | None -> Literal.String "" | Some name -> name) in
                    let message = (match CObject.get err_obj "message" with | None -> Literal.String "" | Some message -> message) in 
                      (Literal.str eType) ^ " : " ^ (Literal.str message)
                )
            | _ -> raise (Failure "Prototype is not an object."))
        )
      | _ -> raise (Failure "Metadata is not an object."))
    | _ -> "Error not an object location: " ^ Literal.str err_val


  let valid_concrete_result (ret : result_t list) : bool = 
    assert(List.length ret = 1);
    let ret = List.hd ret in 
    (match ret with 
    | RSucc (Flag.Normal, _, _) -> true
    | _ -> false
    )
end 