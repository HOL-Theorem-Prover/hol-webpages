signature listML = 
sig
  type num = numML.num
  val NULL : 'a list -> bool
  val HD : 'a list -> 'a
  val TL : 'a list -> 'a list
  val APPEND : 'a list -> 'a list -> 'a list
  val FLAT : 'a list list -> 'a list
  val MAP : ('a -> 'b) -> 'a list -> 'b list
  val MEM : ''a -> ''a list -> bool
  val FILTER : ('a -> bool) -> 'a list -> 'a list
  val FOLDR : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val FOLDL : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
  val EVERY : ('a -> bool) -> 'a list -> bool
  val EXISTS : ('a -> bool) -> 'a list -> bool
  val MAP2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val ZIP : 'a list * 'b list -> ('a * 'b) list
  val UNZIP : ('a * 'b) list -> 'a list * 'b list
  val REVERSE : 'a list -> 'a list
  val LAST : 'a list -> 'a
  val FRONT : 'a list -> 'a list
  val ALL_DISTINCT : ''a list -> bool
  val EL : num -> 'a list -> 'a
  val LENGTH : 'a list -> num
  val LEN : 'a list -> num -> num
  val REV : 'a list -> 'a list -> 'a list
  val list_size : ('a -> num) -> 'a list -> num
end
