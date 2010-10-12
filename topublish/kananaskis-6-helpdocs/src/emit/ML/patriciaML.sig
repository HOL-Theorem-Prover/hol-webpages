signature patriciaML = 
sig
  type num = numML.num
  datatype 'a ptree
       = Empty
       | Leaf of num * 'a
       | Branch of num * num * 'a ptree * 'a ptree
  val toList : 'a ptree -> (num * 'a) list
  val BRANCHING_BIT : num -> num -> num
  val PEEK : 'a ptree -> num -> 'a option
  val JOIN : num * ('a ptree * (num * 'a ptree)) -> 'a ptree
  val ADD : 'a ptree -> num * 'a -> 'a ptree
  val BRANCH : num * (num * ('a ptree * 'a ptree)) -> 'a ptree
  val REMOVE : 'a ptree -> num -> 'a ptree
  val TRAVERSE : 'a ptree -> num list
  val KEYS : 'a ptree -> num list
  val TRANSFORM : ('b -> 'a) -> 'b ptree -> 'a ptree
  val EVERY_LEAF : (num -> 'a -> bool) -> 'a ptree -> bool
  val EXISTS_LEAF : (num -> 'a -> bool) -> 'a ptree -> bool
  val SIZE : 'a ptree -> num
  val DEPTH : 'a ptree -> num
  val IS_PTREE : ''a ptree -> bool
  val IN_PTREE : num -> unit ptree -> bool
  val INSERT_PTREE : num -> unit ptree -> unit ptree
  val IS_EMPTY : 'a ptree -> bool
  val FIND : 'a ptree -> num -> 'a
  val ADD_LIST : 'a ptree -> (num * 'a) list -> 'a ptree
end
