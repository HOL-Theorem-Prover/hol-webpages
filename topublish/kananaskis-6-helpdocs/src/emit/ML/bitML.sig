signature bitML = 
sig
  type num = numML.num
  val TIMES_2EXP : num -> num -> num
  val BITWISE : num -> (bool -> bool -> bool) -> num -> num -> num
  val LOG : num -> num -> num
  val LOWEST_SET_BIT : num -> num
  val l2n : num -> num list -> num
  val n2l : num -> num -> num list
  val s2n : num -> (char -> num) -> string -> num
  val n2s : num -> (num -> char) -> num -> string
  val HEX : num -> char
  val UNHEX : char -> num
  val num_from_bin_list : num list -> num
  val num_from_oct_list : num list -> num
  val num_from_dec_list : num list -> num
  val num_from_hex_list : num list -> num
  val num_to_bin_list : num -> num list
  val num_to_oct_list : num -> num list
  val num_to_dec_list : num -> num list
  val num_to_hex_list : num -> num list
  val num_from_bin_string : string -> num
  val num_from_oct_string : string -> num
  val num_from_dec_string : string -> num
  val num_from_hex_string : string -> num
  val num_to_bin_string : num -> string
  val num_to_oct_string : num -> string
  val num_to_dec_string : num -> string
  val num_to_hex_string : num -> string
  val BIT_MODF
     : num -> (num -> bool -> bool) -> num -> num -> num -> num -> num
  val BIT_MODIFY : num -> (num -> bool -> bool) -> num -> num
  val BIT_REV : num -> num -> num -> num
  val BIT_REVERSE : num -> num -> num
  val LOG2 : num -> num
  val DIVMOD_2EXP : num -> num -> num * num
  val SBIT : bool -> num -> num
  val BITS : num -> num -> num -> num
  val MOD_2EXP_EQ : num -> num -> num -> bool
  val BITV : num -> num -> num
  val BIT : num -> num -> bool
  val SLICE : num -> num -> num -> num
  val LSB : num -> bool
  val SIGN_EXTEND : num -> num -> num -> num
  val BOOLIFY : num -> num -> bool list -> bool list
end
