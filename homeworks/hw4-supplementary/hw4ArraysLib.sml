structure hw4ArraysLib =
struct

open HolKernel Parse bossLib hw4ArraysTheory dot_graphsLib

(* Example

val ag = let
  val ag = new_array_graph 
  val ag = add_node ag 1 NONE
  val ag = add_node ag 2 NONE
  val ag = add_node ag 3 NONE
  val ag = add_node ag 4 (SOME ``A /\ B``)
  val ag = add_node ag 5 NONE
  val ag = add_node_link ag 1 2 "a";
  val ag = add_node_link ag 1 3 "b";
  val ag = add_node_link ag 3 4 "c";
  val ag = add_node_link ag 4 5 "d";
in
  ag
end

val _ = (dot_binary := "/usr/bin/dot");


val _ = print_graph ag
val _ = show_graph ag


*)

fun simple_array n = let
  val n_t = numSyntax.term_of_int n
  val thm = EVAL ``FOLDL (\a n. UPDATE n a n) EMPTY_ARRAY (COUNT_LIST ^n_t)``
in
  rhs (concl thm)
end

fun sparse_array n = let
  val n_t = numSyntax.term_of_int n
  val thm = EVAL ``FOLDL (\a n. UPDATE n a (n*3)) EMPTY_ARRAY (COUNT_LIST ^n_t)``
in
  rhs (concl thm)
end

val a1 = simple_array 10;
val a2 = sparse_array 10;
val a3 = simple_array 20;
val a4 = simple_array 100;

fun is_array_leaf t = same_const t ``Leaf``

fun dest_array_node t = let
  val (c, args) = strip_comb t
  val _ = if (same_const c ``Node``) then () else fail()

  val vo = SOME (optionSyntax.dest_some (el 2 args)) handle HOL_ERR _ => NONE 
in
  (el 1 args, vo, el 3 args)
end

val is_array_node = can dest_array_node

fun graph_of_array_aux ag level suff t = 
  if (is_array_leaf t) then (NONE, ag) else
  let
    val (l, vo, r) = dest_array_node t
    val n = level + suff
    val m = n - 1;
    val ag = add_node ag m vo
    val (l_n, ag) = graph_of_array_aux ag (level*2) n l
    val ag = case l_n of NONE => ag 
	               | SOME ln => add_node_link ag m ln "l"
    val (r_n, ag) = graph_of_array_aux ag (level*2) suff r
    val ag = case r_n of NONE => ag 
	               | SOME rn => add_node_link ag m rn "r"
  in
    (SOME m, ag)
  end handle HOL_ERR _ => (NONE, ag)

fun graph_of_array t =
  snd (graph_of_array_aux new_array_graph 1 0 t)

val _ = show_graph (graph_of_array a1)

val _ = show_graph (graph_of_array a2)

val _ = print_graph (graph_of_array a1)

end
