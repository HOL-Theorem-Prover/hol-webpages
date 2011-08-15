structure combinML :> combinML =
struct
  nonfix UPDATE C W I K S * / div mod + - ^ @ <> > < >= <= := o before;
  
  fun S f g x = f x (g x)
    
  fun K x y = x
    
  fun I x = x
    
  fun W f x = f x x
    
  fun C f x y = f y x
    
  fun o f g x = f (g x)
    
  fun UPDATE a b f c = if a = c then b else f c
    
end
