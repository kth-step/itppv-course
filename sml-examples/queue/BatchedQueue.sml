structure BatchedQueue : Queue =
struct
  type 'a Queue = 'a list * 'a list

  val empty = ([], [])
  fun isEmpty (f, r) = null f

  fun checkf ([], r) = (rev r, [])
    | checkf q = q

  fun snoc ((f, r), x) = checkf (f, x :: r)

  fun head ([], _) = raise Empty
    | head (x :: f, r) = x
  fun tail ([], _) = raise Empty
    | tail (x :: f, r) = checkf (f, r)
end
