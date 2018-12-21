let get_succ_pred cmds =

  let cmds = Array.map (fun x -> match x with (_, cmd) -> cmd) cmds in

  let number_of_cmds = Array.length cmds in
  let succ_table = Array.make number_of_cmds [] in
  let pred_table = Array.make number_of_cmds [] in

  (* adding i to the predecessors of j *)
  let update_pred_table i j =
    (if ((j < number_of_cmds) && (i < number_of_cmds))
      then pred_table.(j) <- i :: pred_table.(j)
      else ()) in

  (* adding i to the successors of j *)
  let update_succ_table i j =
    (if ((j < number_of_cmds) && (i < number_of_cmds))
      then succ_table.(j) <- i :: succ_table.(j)
      else ()) in

  for u=0 to number_of_cmds-1 do
      (match (cmds.(u) : Cmd.t) with
      | Logic _ 
      | Basic _
      | Arguments _
      | PhiAssignment _ -> 
          update_succ_table (u + 1) u;
          update_pred_table u (u + 1)

      | Goto i ->
          update_succ_table i u;
          update_pred_table u i

      | GuardedGoto (e, i, j) ->
          update_succ_table i u;
          update_pred_table u i;
          update_succ_table j u;
          update_pred_table u j

      | Call  (_, _, _, i, _) 
      | ECall (_, _, _, i)
      | Apply (_, _, i) ->
        (match i with
        | None -> ()
        | Some i -> (update_succ_table i u; update_pred_table u i));
            update_succ_table (u+1) u;
            update_pred_table u (u+1)

      | ReturnNormal
      | ReturnError -> ())
  done;

  for k = 0 to (number_of_cmds - 1) do
    succ_table.(k) <- List.rev succ_table.(k);
    pred_table.(k) <- List.rev pred_table.(k);
  done;
  succ_table, pred_table

let compute_which_preds pred =
  List.concat 
    (List.mapi
      (fun u u_preds -> List.mapi (fun i v -> (v, u, i)) u_preds)
      (Array.to_list pred))

let extend_which_pred (global_which_pred : Prog.predecessors) (proc : Proc.t) : unit =
  let succ_table, pred_table = get_succ_pred proc.body in
  let which_pred = compute_which_preds pred_table in
  let proc_name = proc.name in
  List.iter
    (fun (prev_cmd, cur_cmd, i) ->
      Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
    which_pred