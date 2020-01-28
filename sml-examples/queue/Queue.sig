exception Empty

signature Queue =
sig
  type 'a Queue
	  
  val empty   : 'a Queue
  val isEmpty : 'a Queue -> bool
  
  val snoc    : 'a Queue * 'a -> 'a Queue
  val head    : 'a Queue -> 'a       (* raises Empty if queue is empty *)
  val tail    : 'a Queue -> 'a Queue (* raises Empty if queue is empty *)
end
