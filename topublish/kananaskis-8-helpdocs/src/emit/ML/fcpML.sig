signature fcpML =
sig
  type num = numML.num
  datatype 'b itself = ITSELF of num
  type ('a,'b) cart
  eqtype 'a bit0
  eqtype 'a bit1
  val SUMi : 'b itself * 'c itself -> 'a itself
  val MULi : 'b itself * 'c itself -> 'a itself
  val EXPi : 'b itself * 'c itself -> 'a itself
  val dimindex : 'a itself -> num
  val mk_fcp : (num -> 'a) * 'b itself -> ('a, 'b) cart
  val fcp_index : ('a, 'b) cart -> num -> 'a
  val :+ : num -> 'a -> ('a, 'b) cart -> ('a, 'b) cart
end
