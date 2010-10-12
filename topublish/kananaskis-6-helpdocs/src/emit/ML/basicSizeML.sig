signature basicSizeML = 
sig
  type num = numML.num
  type 'a  option = 'a optionML.option
  type ('a,'b) sum = ('a,'b) sumML.sum
  val bool_size : bool -> num
  val pair_size : ('a -> num) -> ('b -> num) -> 'a * 'b -> num
  val one_size : unit -> num
  val option_size : ('a -> num) -> 'a option -> num
end
