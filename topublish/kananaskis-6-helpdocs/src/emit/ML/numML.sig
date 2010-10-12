signature numML = 
sig
  eqtype num
  val SUC : num -> num
  val iZ : num -> num
  val iiSUC : num -> num
  val + : num -> num -> num
  val < : num -> num -> bool
  val <= : num -> num -> bool
  val > : num -> num -> bool
  val >= : num -> num -> bool
  val PRE : num -> num
  val iDUB : num -> num
  val iSUB : bool -> num -> num -> num
  val - : num -> num -> num
  val  *  : num -> num -> num
  val iSQR : num -> num
  val EXP : num -> num -> num
  val EVEN : num -> bool
  val ODD : num -> bool
  val FACT : num -> num
  val FUNPOW : ('a -> 'a) -> num -> 'a -> 'a
  val MIN : num -> num -> num
  val MAX : num -> num -> num
  val WHILE : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
  val LEAST : (num -> bool) -> num
  val findq : num * (num * num) -> num
  val DIVMOD : num * (num * num) -> num * num
  val DIV : num -> num -> num
  val MOD : num -> num -> num
  val DIV2 : num -> num
  val MOD_2EXP : num -> num -> num
  val DIV_2EXP : num -> num -> num
  val measure : ('a -> num) -> 'a -> 'a -> bool
  val num_size : num -> num
  val NUMERAL  :num -> num
  val ZERO :num
  val BIT1 :num -> num
  val BIT2 :num -> num
  val ONE :num
  val TWO :num
  val fromInt       : int -> num
  val toInt         : num -> int option
  val toBinString   : num -> string
  val toOctString   : num -> string
  val toDecString   : num -> string
  val toHexString   : num -> string
  val toString      : num -> string
  val fromBinString : string -> num
  val fromOctString : string -> num
  val fromDecString : string -> num
  val fromHexString : string -> num
  val fromString    : string -> num
  val ppBin  : ppstream -> num -> unit
  val ppOct  : ppstream -> num -> unit
  val ppDec  : ppstream -> num -> unit
  val ppHex  : ppstream -> num -> unit
  val pp_num : ppstream -> num -> unit
end
