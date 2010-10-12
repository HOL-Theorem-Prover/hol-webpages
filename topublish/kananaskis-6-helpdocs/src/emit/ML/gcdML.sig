signature gcdML = 
sig
  type num = numML.num
  val divides : num -> num -> bool
  val gcd : num -> num -> num
  val lcm : num -> num -> num
end
