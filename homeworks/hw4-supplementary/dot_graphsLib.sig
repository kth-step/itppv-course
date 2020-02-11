signature dot_graphsLib =
sig
  type array_graph

  (* binary for running dot *)
  val dot_binary : string ref;

  (* a fresh, empty one *)
  val new_array_graph : array_graph

  (* add a node to a graph with number n and the term option content *)
  val add_node : array_graph -> int -> Abbrev.term option -> array_graph

  (* adds a link between two nodes in the graph *)
  val add_node_link : array_graph -> int -> int -> string -> array_graph

  (* Various outputs *)
  val print_graph : array_graph -> unit
  val graph_to_string : array_graph -> string
  val show_graph : array_graph -> unit
  val write_graph_to_dot_file : array_graph -> string -> unit
  val write_graph_to_png_file : array_graph -> string -> unit

end
