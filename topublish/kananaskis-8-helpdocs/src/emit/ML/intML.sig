signature intML =
sig
  eqtype int
  type num = numML.num
  type 'a itself = 'a fcpML.itself
  type 'a word = 'a wordsML.word
  val int_of_num : num -> int
  val fromInt : Int.int -> int
  val toInt : int -> Int.int option
  val fromString : string -> int
  val int_neg : int -> int
  val Num : int -> num
  val int_lt : int -> int -> bool
  val int_le : int -> int -> bool
  val int_gt : int -> int -> bool
  val int_ge : int -> int -> bool
  val ABS : int -> int
  val int_add : int -> int -> int
  val int_sub : int -> int -> int
  val int_mul : int -> int -> int
  val int_exp : int -> num -> int
  val int_div : int -> int -> int
  val int_mod : int -> int -> int
  val int_quot : int -> int -> int
  val int_rem : int -> int -> int
  val INT_MAX : 'a itself -> int
  val INT_MIN : 'a itself -> int
  val UINT_MAX : 'a itself -> int
  val i2w_itself : int * 'a itself -> 'a word
  val w2i : 'a word -> int
end
