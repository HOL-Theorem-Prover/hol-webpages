signature pairML =
sig
  val CURRY : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val UNCURRY : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val FST : 'a * 'b -> 'a
  val SND : 'a * 'b -> 'b
  val ## : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val LEX
     : (''a -> ''a -> bool) ->
       ('b -> 'b -> bool) -> ''a * 'b -> ''a * 'b -> bool
end
