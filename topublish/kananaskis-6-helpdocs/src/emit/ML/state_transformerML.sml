structure state_transformerML :> state_transformerML =
struct
  nonfix JOIN MMAP BIND UNIT * / div mod + - ^ @ <> > < >= <= := o
         before;
  
  fun UNIT x = fn s => (x,s)
    
  fun BIND g f = combinML.o (pairML.UNCURRY f) g
    
  fun MMAP f m = BIND m (combinML.o UNIT f)
    
  fun JOIN z = BIND z combinML.I
    
end
