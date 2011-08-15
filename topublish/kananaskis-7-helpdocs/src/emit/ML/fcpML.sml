structure fcpML :> fcpML =
struct
  nonfix :+ fcp_index mk_fcp dimindex EXPi MULi SUMi BIT1C BIT1B BIT1A
         BIT0B BIT0A FCPi ITSELF * / div mod + - ^ @ <> > < >= <= := o
         before;
  
  open numML
  
  datatype 'b itself = ITSELF of num
  datatype ('a,'b)cart = FCPi of ((num -> 'a) * 'b itself)
  datatype 'a bit0 = BIT0A of 'a | BIT0B of 'a
  datatype 'a bit1 = BIT1A of 'a | BIT1B of 'a | BIT1C
  fun SUMi (ITSELF a,ITSELF b) = ITSELF (+ a b)
    
  fun MULi (ITSELF a,ITSELF b) = ITSELF ( *  a b)
    
  fun EXPi (ITSELF a,ITSELF b) = ITSELF (EXP a b)
    
  fun dimindex (ITSELF a) = a
    
  val mk_fcp = FCPi
    
  fun fcp_index (FCPi (f,b)) n =
        if < n (dimindex b) then f n
        else raise (Fail "fcp_index: FCP out of bounds")
    
  fun :+ x y (FCPi (f,b)) = FCPi (fn c => if x = c then y else f c,b)
    
end
