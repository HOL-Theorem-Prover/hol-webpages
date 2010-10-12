signature wordsML = 
sig
  type ('a, 'b) sum = ('a, 'b) sumML.sum
  type 'a itself = 'a fcpML.itself
  type 'a bit0 = 'a fcpML.bit0
  type 'a bit1 = 'a fcpML.bit1
  type num = numML.num
  datatype 'a word = n2w_itself of num * 'a itself
  val dimword : 'a itself -> num
  val fromNum : num * 'a itself -> 'a word
  type word1 = unit word
  val toWord1 : numML.num -> word1
  val fromString1 : string -> word1
  type word2 = unit bit0 word
  val toWord2 : numML.num -> word2
  val fromString2 : string -> word2
  type word3 = unit bit1 word
  val toWord3 : numML.num -> word3
  val fromString3 : string -> word3
  type word4 = unit bit0 bit0 word
  val toWord4 : numML.num -> word4
  val fromString4 : string -> word4
  type word5 = unit bit0 bit1 word
  val toWord5 : numML.num -> word5
  val fromString5 : string -> word5
  type word6 = unit bit1 bit0 word
  val toWord6 : numML.num -> word6
  val fromString6 : string -> word6
  type word7 = unit bit1 bit1 word
  val toWord7 : numML.num -> word7
  val fromString7 : string -> word7
  type word8 = unit bit0 bit0 bit0 word
  val toWord8 : numML.num -> word8
  val fromString8 : string -> word8
  type word12 = unit bit1 bit0 bit0 word
  val toWord12 : numML.num -> word12
  val fromString12 : string -> word12
  type word16 = unit bit0 bit0 bit0 bit0 word
  val toWord16 : numML.num -> word16
  val fromString16 : string -> word16
  type word20 = unit bit0 bit1 bit0 bit0 word
  val toWord20 : numML.num -> word20
  val fromString20 : string -> word20
  type word24 = unit bit1 bit0 bit0 bit0 word
  val toWord24 : numML.num -> word24
  val fromString24 : string -> word24
  type word28 = unit bit1 bit1 bit0 bit0 word
  val toWord28 : numML.num -> word28
  val fromString28 : string -> word28
  type word30 = unit bit1 bit1 bit1 bit0 word
  val toWord30 : numML.num -> word30
  val fromString30 : string -> word30
  type word32 = unit bit0 bit0 bit0 bit0 bit0 word
  val toWord32 : numML.num -> word32
  val fromString32 : string -> word32
  type word64 = unit bit0 bit0 bit0 bit0 bit0 bit0 word
  val toWord64 : numML.num -> word64
  val fromString64 : string -> word64
  val INT_MIN : 'a itself -> num
  val UINT_MAX : 'a itself -> num
  val INT_MAX : 'a itself -> num
  val w2n : 'a word -> num
  val word_eq : 'a word -> 'a word -> bool
  val w2w_itself : 'b itself -> 'a word -> 'b word
  val word_or : 'a word -> 'a word -> 'a word
  val word_lsl : 'a word -> num -> 'a word
  val word_bits : num -> num -> 'a word -> 'a word
  val word_signed_bits : num -> num -> 'a word -> 'a word
  val word_bit : num -> 'a word -> bool
  val word_join : 'a word -> 'b word -> ('a, 'b) sum word
  val sw2sw_itself : 'b itself -> 'a word -> 'b word
  val word_extract_itself
     : 'b itself -> num -> num -> 'a word -> 'b word
  val word_slice : num -> num -> 'a word -> 'a word
  val word_concat_itself : 'c itself -> 'a word -> 'b word -> 'c word
  val word_log2 : 'a word -> 'a word
  val word_reverse : 'a word -> 'a word
  val word_modify : (num -> bool -> bool) -> 'a word -> 'a word
  val word_lsb : 'a word -> bool
  val word_msb : 'a word -> bool
  val add_with_carry
     : 'a word * ('a word * bool) -> 'a word * (bool * bool)
  val word_1comp : 'a word -> 'a word
  val word_and : 'a word -> 'a word -> 'a word
  val word_xor : 'a word -> 'a word -> 'a word
  val word_2comp : 'a word -> 'a word
  val word_div : 'a word -> 'a word -> 'a word
  val word_sdiv : 'a word -> 'a word -> 'a word
  val word_add : 'a word -> 'a word -> 'a word
  val word_sub : 'a word -> 'a word -> 'a word
  val word_mul : 'a word -> 'a word -> 'a word
  val word_lsr : 'a word -> num -> 'a word
  val word_asr : 'a word -> num -> 'a word
  val word_ror : 'a word -> num -> 'a word
  val word_rol : 'a word -> num -> 'a word
  val word_rrx : bool * 'a word -> bool * 'a word
  val word_index : 'a word -> num -> bool
  val word_ge : 'a word -> 'a word -> bool
  val word_gt : 'a word -> 'a word -> bool
  val word_hi : 'a word -> 'a word -> bool
  val word_hs : 'a word -> 'a word -> bool
  val word_le : 'a word -> 'a word -> bool
  val word_lo : 'a word -> 'a word -> bool
  val word_ls : 'a word -> 'a word -> bool
  val word_lt : 'a word -> 'a word -> bool
  val word_reduce : (bool -> bool -> bool) -> 'a word -> word1
  val reduce_and : ''a word -> word1
  val reduce_or : ''a word -> word1
  val reduce_xor : 'a word -> word1
  val reduce_xnor : 'a word -> word1
  val reduce_nand : 'a word -> word1
  val reduce_nor : 'a word -> word1
  val bit_field_insert : num -> num -> 'a word -> 'b word -> 'b word
  val w2l : num -> 'a word -> num list
  val w2s : num -> (num -> char) -> 'a word -> string
  val word_to_bin_list : 'a word -> num list
  val word_to_oct_list : 'a word -> num list
  val word_to_dec_list : 'a word -> num list
  val word_to_hex_list : 'a word -> num list
  val word_to_bin_string : 'a word -> string
  val word_to_oct_string : 'a word -> string
  val word_to_dec_string : 'a word -> string
  val word_to_hex_string : 'a word -> string
end
