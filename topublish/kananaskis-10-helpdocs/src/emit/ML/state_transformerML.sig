signature state_transformerML =
sig
  val UNIT : 'b -> 'a -> 'b * 'a
  val BIND : ('a -> 'b * 'a) -> ('b -> 'a -> 'c * 'a) -> 'a -> 'c * 'a
  val IGNORE_BIND : ('a -> 'c * 'a) -> ('a -> 'b * 'a) -> 'a -> 'b * 'a
  val MMAP : ('c -> 'b) -> ('a -> 'c * 'a) -> 'a -> 'b * 'a
  val JOIN : ('a -> ('a -> 'b * 'a) * 'a) -> 'a -> 'b * 'a
  val READ : ('state -> 'a) -> 'state -> 'a * 'state
  val WRITE : ('state -> 'state) -> 'state -> unit * 'state
end
