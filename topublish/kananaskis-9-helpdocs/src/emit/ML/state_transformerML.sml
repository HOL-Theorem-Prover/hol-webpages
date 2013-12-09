structure state_transformerML :> state_transformerML =
struct
  nonfix WRITE READ JOIN MMAP IGNORE_BIND BIND UNIT * / div mod + - ^ @
         <> > < >= <= := o before;

  fun UNIT x = fn s => (x,s)

  fun BIND g f = combinML.o (pairML.UNCURRY f) g

  fun IGNORE_BIND f g = BIND f (fn x => g)

  fun MMAP f m = BIND m (combinML.o UNIT f)

  fun JOIN z = BIND z combinML.I

  fun READ f = fn s => (f s,s)

  fun WRITE f = fn s => ((),f s)

end
