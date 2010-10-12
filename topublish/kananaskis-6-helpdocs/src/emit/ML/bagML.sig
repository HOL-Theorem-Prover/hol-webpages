signature bagML = 
sig
  type 'a bag
  type num = numML.num
  type 'a set = 'a setML.set
  val EMPTY_BAG    : 'a bag
  val BAG_INSERT   : 'a * 'a bag -> 'a bag
  val BAG_VAL      : ''a bag -> ''a -> num
  val BAG_IN       : ''a -> ''a bag -> bool
  val BAG_INN      : ''a -> num -> ''a bag -> bool
  val BAG_UNION    : ''a bag -> ''a bag -> ''a bag
  val BAG_DIFF     : ''a bag -> ''a bag -> ''a bag
  val BAG_INTER    : ''a bag -> ''a bag -> ''a bag
  val BAG_MERGE    : ''a bag -> ''a bag -> ''a bag
  val SUB_BAG      : ''a bag -> ''a bag -> bool
  val PSUB_BAG     : ''a bag -> ''a bag -> bool
  val BAG_DISJOINT : ''a bag -> ''a bag -> bool
  val BAG_FILTER   : ('a -> bool) -> 'a bag -> 'a bag
  val BAG_IMAGE    : ('a -> 'b) -> 'a bag -> 'b bag
  val BAG_CARD     : 'a bag -> num
  val SET_OF_BAG   : 'a bag -> 'a set
end
