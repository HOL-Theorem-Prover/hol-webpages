signature optionML = 
sig
  datatype option = datatype Option.option
  
  val OPTION_MAP : ('a -> 'b) -> 'a option -> 'b option
  val IS_SOME : 'a option -> bool
  val IS_NONE : 'a option -> bool
  val THE : 'a option -> 'a
  val OPTION_JOIN : 'a option option -> 'a option
end
