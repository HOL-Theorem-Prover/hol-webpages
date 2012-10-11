signature setML =
sig
  type 'a set
  type num = numML.num
  val EMPTY    : 'a set
  val INSERT   : 'a * 'a set -> 'a set
  val IN       : ''a -> ''a set -> bool
  val UNION    : ''a set -> ''a set -> ''a set
  val INTER    : ''a set -> ''a set -> ''a set
  val DELETE   : ''a set -> ''a -> ''a set
  val DIFF     : ''a set -> ''a set -> ''a set
  val SUBSET   : ''a set -> ''a set -> bool
  val PSUBSET  : ''a set -> ''a set -> bool
  val IMAGE    : ('a -> 'b) -> 'a set -> 'b set
  val BIGUNION : ''a set set -> ''a set
  val BIGINTER : ''a set set -> ''a set
  val CARD     : ''a set -> num
  val DISJOINT : ''a set -> ''a set -> bool
  val CROSS    : ''a set -> ''b set -> (''a * ''b) set
  val LIST_TO_SET : 'a list -> 'a set
  val IS_EMPTY : 'a set -> bool
  val SUM_IMAGE : (''a -> num) -> ''a set -> num
  val SUM_SET  : num set -> num
  val MAX_SET  : num set -> num
  val MIN_SET  : num set -> num
  val count    : num -> num set
  val POW      : ''a set -> ''a set set
  val fromList : 'a list -> 'a set
  val toList   : 'a set -> 'a list
end
