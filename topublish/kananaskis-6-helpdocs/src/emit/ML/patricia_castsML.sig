signature patricia_castsML = 
sig
  type 'a ptree = 'a patriciaML.ptree
  type 'a word = 'a wordsML.word
  type num = numML.num
  type string = stringML.string
  val SKIP1 : string -> string
  val string_to_num : string -> num
  datatype ('a,'b)word_ptree = Word_ptree of ('a -> unit) * 'b ptree
  val THE_PTREE : ('b, 'a) word_ptree -> 'a ptree
  val SOME_PTREE : 'b ptree -> ('a, 'b) word_ptree
  val PEEKw : ('a, 'b) word_ptree -> 'a word -> 'b option
  val ADDw : ('a, 'b) word_ptree -> 'a word * 'b -> ('a, 'b) word_ptree
  val REMOVEw : ('a, 'b) word_ptree -> 'a word -> ('a, 'b) word_ptree
  val TRANSFORMw
     : ('a -> 'b) -> ('c, 'a) word_ptree -> ('c, 'b) word_ptree
  val SIZEw : ('a, 'b) word_ptree -> num
  val DEPTHw : ('a, 'b) word_ptree -> num
  val IN_PTREEw : 'a word -> ('a, unit) word_ptree -> bool
  val INSERT_PTREEw
     : 'a word -> ('a, unit) word_ptree -> ('a, unit) word_ptree
  val FINDw : ('b, 'a) word_ptree -> 'b word -> 'a
  val ADD_LISTw
     : ('a, 'b) word_ptree -> ('a word * 'b) list -> ('a, 'b) word_ptree
  val num_to_string : num -> string
  val PEEKs : 'a ptree -> string -> 'a option
  val FINDs : 'a ptree -> string -> 'a
  val ADDs : 'a ptree -> string * 'a -> 'a ptree
  val ADD_LISTs : 'a ptree -> (string * 'a) list -> 'a ptree
  val REMOVEs : 'a ptree -> string -> 'a ptree
  val TRAVERSEs : 'a ptree -> string list
  val KEYSs : 'a ptree -> string list
  val IN_PTREEs : string -> unit ptree -> bool
  val INSERT_PTREEs : string -> unit ptree -> unit ptree
end
