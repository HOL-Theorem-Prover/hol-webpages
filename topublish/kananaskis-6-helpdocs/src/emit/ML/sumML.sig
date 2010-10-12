signature sumML = 
sig
  datatype ('a,'b)sum = INL of 'a | INR of 'b
  val OUTL : ('a, 'b) sum -> 'a
  val OUTR : ('a, 'b) sum -> 'b
  val ISL : ('a, 'b) sum -> bool
  val ISR : ('a, 'b) sum -> bool
end
