structure sumML :> sumML =
struct
  nonfix ISR ISL OUTR OUTL INR INL * / div mod + - ^ @ <> > < >= <= := o
         before;
  
  datatype ('a,'b)sum = INL of 'a | INR of 'b
  fun OUTL (INL(x)) = x
    | OUTL (INR(y)) = raise (Fail "OUTL: applied to INR")
    
  fun OUTR (INL(x)) = raise (Fail "OUTR: applied to INL")
    | OUTR (INR(y)) = y
    
  fun ISL (INL(x)) = true
    | ISL (INR(y)) = false
    
  fun ISR (INL(x)) = false
    | ISR (INR(y)) = true
    
end
