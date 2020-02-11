structure dot_graphsLib :> dot_graphsLib =
struct

open HolKernel Parse 

datatype array_graph = AG of string

val new_array_graph = AG "";

(* Auxiliary functions *)
fun AG_add (AG s) s' = AG (s ^ "   " ^ s' ^ "\n")
fun node_name n = ("node_"^(int_to_string n))

(* create a new node with number n and value v in  graph ag *)
fun add_node ag (n:int) (v : term option) = let
  val n_s = node_name n;
  val v_s = case v of NONE => "-" 
		   |  SOME t => "'" ^ (term_to_string t) ^ "'" 
  val new_s = (n_s ^ " [label=\"" ^ (int_to_string n) ^": "^v_s^"\"]")
in
  AG_add ag new_s
end

(* Add a link between nodes n1 and n2 *)
fun add_node_link ag (n1:int) (n2 : int) (label : string) = let
  val new_s = (node_name n1) ^ " -> " ^ (node_name n2) ^ " [label=\""^label^"\"]";
in
  AG_add ag new_s
end
			
fun graph_to_string (AG s) = "digraph G {\n" ^ s ^ "}\n\n"
fun print_graph ag = (TextIO.print (graph_to_string ag))

fun write_graph_to_dot_file ag file_name = let
  val os = TextIO.openOut file_name;
  val _ = TextIO.output (os, graph_to_string ag);
  val _ = TextIO.closeOut os
in
  ()
end

val dot_binary = ref "/usr/bin/dot";

fun show_graph ag = let
  val p = Unix.execute (!dot_binary, ["-Tx11"])
  val os = Unix.textOutstreamOf p
  val _ = TextIO.output (os, graph_to_string ag)
  val _ = TextIO.closeOut os
in
  ()
end

fun write_graph_to_png_file ag filename = let
  val p = Unix.execute (!dot_binary, ["-Tpng", "-o", filename])
  val os = Unix.textOutstreamOf p
  val _ = TextIO.output (os, graph_to_string ag)
  val _ = TextIO.closeOut os
in
  ()
end

end
