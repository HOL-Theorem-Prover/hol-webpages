structure pairML :> pairML =
struct
  nonfix LEX ## SND FST UNCURRY CURRY * / div mod + - ^ @ <> > < >= <=
         := o before;

  fun CURRY f x y = f (x,y)

  fun UNCURRY f (x,y) = f x y

  fun FST (x,y) = x

  fun SND (x,y) = y

  fun ## f g (x,y) = (f x,g y)

  fun LEX R1 R2 (a,b) (c,d) = R1 a c orelse (a = c) andalso R2 b d

end
