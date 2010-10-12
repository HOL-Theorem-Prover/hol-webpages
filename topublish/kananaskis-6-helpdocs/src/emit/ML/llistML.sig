signature llistML = 
sig
  type 'a llist
  val LNIL : 'a llist
  val LLCONS : 'a -> (unit -> 'a llist) -> 'a llist
  val LCONS : 'a -> 'a llist -> 'a llist
  val ::: : 'a * 'a llist -> 'a llist
  val llcases : 'b -> ('a * 'a llist -> 'b) -> 'a llist -> 'b
  val LUNFOLD : ('a -> ('a * 'b) option) -> 'a -> 'b llist
  type num = numML.num
  val LAPPEND : 'a llist -> 'a llist -> 'a llist
  val LMAP : ('b -> 'a) -> 'b llist -> 'a llist
  val LFILTER : ('a -> bool) -> 'a llist -> 'a llist
  val LHD : 'a llist -> 'a option
  val LTL : 'a llist -> 'a llist option
  val LTAKE : num -> 'a llist -> 'a list option
  val toList : 'a llist -> 'a list option
end
