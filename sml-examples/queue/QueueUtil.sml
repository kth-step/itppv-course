functor QueueUtil (Q : Queue) =
struct
  fun string_of_queue s q =
      if Q.isEmpty q then ""
      else s (Q.head q) ^ "; " ^ string_of_queue s (Q.tail q)
end
