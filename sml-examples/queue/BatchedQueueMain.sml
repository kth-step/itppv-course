fun main () =
    let val q = BatchedQueue.empty in
	let val q' = BatchedQueue.snoc (q, 5) in 
	    ()
	end
    end
