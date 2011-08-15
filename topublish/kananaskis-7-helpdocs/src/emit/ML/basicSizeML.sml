structure basicSizeML :> basicSizeML =
struct
  nonfix option_size one_size pair_size bool_size * / div mod + - ^ @ <>
         > < >= <= := o before;
  
  open numML
  open sumML
  open optionML
  
  fun bool_size b = ZERO
    
  fun pair_size f g = fn (x,y) => + (f x) (g y)
    
  fun one_size x = ZERO
    
  fun option_size f NONE = ZERO
    | option_size f (SOME(x)) = SUC (f x)
    
end
