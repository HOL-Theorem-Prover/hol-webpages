signature stringML = 
sig
  type num = numML.num
  type char = Char.char
  type string = String.string
  val CHR : num -> char
  val ORD : char -> num
  val string_lt : string -> string -> bool
  val IMPLODE : char list -> string
  val EXPLODE : string -> char list
  val STRLEN : string -> num
  val char_size : char -> num
  val STRCAT : string -> string -> string
  val isPREFIX : string -> string -> bool
  val isLower : char -> bool
  val isUpper : char -> bool
  val isDigit : char -> bool
  val isAlpha : char -> bool
  val isHexDigit : char -> bool
  val isAlphaNum : char -> bool
  val isPrint : char -> bool
  val isSpace : char -> bool
  val isGraph : char -> bool
  val isPunct : char -> bool
  val isAscii : char -> bool
  val isCntrl : char -> bool
  val toLower : char -> char
  val toUpper : char -> char
  val PAD_LEFT : char -> num -> string -> string
  val PAD_RIGHT : char -> num -> string -> string
  val char_lt : char -> char -> bool
  val char_le : char -> char -> bool
  val char_gt : char -> char -> bool
  val char_ge : char -> char -> bool
  val string_le : string -> string -> bool
  val string_gt : string -> string -> bool
  val string_ge : string -> string -> bool
end
