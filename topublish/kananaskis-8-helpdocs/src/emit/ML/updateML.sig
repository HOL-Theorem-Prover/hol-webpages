signature updateML =
sig
  type 'a word = 'a wordsML.word
  type num = numML.num
  type word2 = wordsML.word2
  type word8 = wordsML.word8
  type word16 = wordsML.word16
  type word30 = wordsML.word30
  type word32 = wordsML.word32
  type mem
  val mem_updates : word30 list ref
  datatype formats
       = SignedByte
       | UnsignedByte
       | SignedHalfWord
       | UnsignedHalfWord
       | UnsignedWord
  datatype data = Byte of word8 | Half of word16 | Word of word32
  val |: : 'a word -> 'b list -> ('a word -> 'b) -> 'a word -> 'b
  val mem_read : mem * word30 -> word32
  val mem_write : mem -> word30 -> word32 -> mem
  val mem_write_block : mem -> word30 -> word32 list -> mem
  val empty_memory : mem
  val mem_items : mem -> (word30 * word32) list
  val addr30 : word32 -> word30
  val GET_HALF : word2 -> word32 -> word16
  val GET_BYTE : word2 -> word32 -> word8
  val FORMAT : formats -> word2 -> word32 -> word32
  val SET_BYTE : word2 -> word8 -> word32 -> word32
  val SET_HALF : bool -> word16 -> word32 -> word32
  val MEM_WRITE_BYTE : mem -> word32 -> word8 -> mem
  val MEM_WRITE_HALF : mem -> word32 -> word16 -> mem
  val MEM_WRITE_WORD : mem -> word32 -> word32 -> mem
  val MEM_WRITE : mem -> word32 -> data -> mem
end
