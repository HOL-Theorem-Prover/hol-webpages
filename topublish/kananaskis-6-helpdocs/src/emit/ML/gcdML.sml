structure gcdML :> gcdML =
struct
  nonfix lcm gcd divides * / div mod + - ^ @ <> > < >= <= := o before;
  
  open numML
  
  fun divides a b =
        if a = ZERO then b = ZERO
        else
          if a = ONE then
          true
        else if b = ZERO then true else MOD b a = ZERO
    
  fun gcd a b = if a = ZERO then b else gcd (MOD b a) a
    
  fun lcm m n =
        if (m = ZERO) orelse (n = ZERO) then ZERO
        else DIV ( *  m n) (gcd m n)
    
end
