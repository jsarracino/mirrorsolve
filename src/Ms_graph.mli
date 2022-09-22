type str_graph = {
  nodes : string list ;
  edges : (string * string) list ;
}

val empty : str_graph

val add_node : str_graph -> string -> str_graph
val add_edge : str_graph -> string -> string -> str_graph

val topo_sort : str_graph -> string list 