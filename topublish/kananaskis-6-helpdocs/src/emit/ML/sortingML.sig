signature sortingML = 
sig
  val PART
     : ('a -> bool) ->
       'a list -> 'a list -> 'a list -> 'a list * 'a list
  val PARTITION : ('a -> bool) -> 'a list -> 'a list * 'a list
  val QSORT : ('a -> 'a -> bool) -> 'a list -> 'a list
  val SORTED : ('a -> 'a -> bool) -> 'a list -> bool
end
