let dot_of_graph succ_table nodes string_of_node graphname = 
  
  let number_of_nodes = Array.length succ_table in 
  
  let rec dot_of_graph_nodes_iter cur_node cur_str = 
    (if (cur_node < number_of_nodes)
      then 
        let node_str = (string_of_node nodes.(cur_node) cur_node) in 
        let cur_str = cur_str ^ "\t" ^ (string_of_int cur_node) ^ "[shape=box, label=\"" ^ node_str ^ "\"];\n" in 
          dot_of_graph_nodes_iter (cur_node+1) cur_str
      else 
        cur_str) in
  
  let rec dot_of_graph_edges_iter cur_node cur_edges cur_str = 
    (match cur_edges with 
    | [] -> 
        (if ((cur_node + 1) < number_of_nodes)
          then 
            let cur_node = cur_node + 1 in 
            let cur_edges = succ_table.(cur_node) in 
              dot_of_graph_edges_iter cur_node cur_edges cur_str 
          else 
            cur_str)
    | node :: rest_edges ->
        let cur_node_str = (string_of_int cur_node) in
        let node_str = (string_of_int node) in 
        let cur_str = cur_str ^ "\t" ^ cur_node_str ^ " -> " ^ node_str ^ ";\n" in
          print_debug_petar (Printf.sprintf "adding the edge (%s, %s) to the cfg\n" cur_node_str node_str); 
          dot_of_graph_edges_iter cur_node rest_edges cur_str) in 
  
  let str = "digraph " ^ graphname ^ "{\n" in 
  let str_nodes = dot_of_graph_nodes_iter 0 "" in 
  let str_edges = dot_of_graph_edges_iter 0 succ_table.(0) "" in 
  print_debug_petar "Finished printing edges";  
  let str = str ^ str_nodes ^ str_edges ^ "}" in
    str

let dot_of_tree parent_table nodes string_of_node graphname = 
  
  let number_of_nodes = Array.length parent_table in 
  
  let rec dot_of_tree_nodes_iter cur_node cur_str = 
    (if (cur_node < number_of_nodes)
      then 
        let node_str = (string_of_node nodes.(cur_node)) in 
        let cur_str = cur_str ^ "\t" ^ (string_of_int cur_node) ^ "[shape=box, label=\"" ^ node_str ^ "\"];\n" in 
          dot_of_tree_nodes_iter (cur_node+1) cur_str
      else 
        cur_str) in
  
  let rec dot_of_tree_edges_iter cur_node cur_str = 
    (if (cur_node < number_of_nodes)
      then 
        let cur_node_str = string_of_int cur_node in
        let p_cur_node = parent_table.(cur_node) in 
        let cur_str = 
          (match p_cur_node with 
            | Some p_cur_node -> 
                let p_cur_node_str = string_of_int p_cur_node in 
                  cur_str ^ "\t" ^ p_cur_node_str ^ " -> " ^ cur_node_str ^ ";\n"
            | None -> cur_str) in 
        dot_of_tree_edges_iter (cur_node+1) cur_str
      else 
        cur_str) in
  
  let str = "digraph " ^ graphname ^ "{\n" in 
  let str_nodes = dot_of_tree_nodes_iter 0 "" in 
  let str_edges = dot_of_tree_edges_iter 0 "" in 
  print_debug_petar "Finished printing edges";  
  let str = str ^ str_nodes ^ str_edges ^ "}" in
    str