structure bqutils = QueueUtil(BatchedQueue)

fun main () =
    let val q0 = BatchedQueue.empty;
	val q1 = BatchedQueue.snoc (q0, 5);
	val q2 = BatchedQueue.snoc (q1, 3);
	val q3 = BatchedQueue.snoc (q2, 2);
	val qs = bqutils.string_of_queue Int.toString q3;
	val s = qs ^ "\n"
    in
	print s
    end
