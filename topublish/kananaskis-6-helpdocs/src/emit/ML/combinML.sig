signature combinML = 
sig
  val S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c
  val K : 'a -> 'b -> 'a
  val I : 'a -> 'a
  val W : ('a -> 'a -> 'b) -> 'a -> 'b
  val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val o : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
  val UPDATE : ''a -> 'b -> (''a -> 'b) -> ''a -> 'b
end
