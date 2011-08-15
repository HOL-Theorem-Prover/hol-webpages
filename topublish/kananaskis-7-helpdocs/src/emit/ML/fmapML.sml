structure fmapML :> fmapML =
struct
  nonfix FEVERY o_f FRANGE RRESTRICT DRESTRICT SUBMAP \\ FUNION
         FUPDATE_LIST FLOOKUP FCARD FAPPLY FDOM FUPDATE FEMPTY * / div
         mod + - ^ @ <> > < >= <= := o before;
  
  datatype ('a,'b)fmap = FEMPTY | FUPDATE of ('a, 'b) fmap * ('a * 'b)
  open numML
  open listML
  open setML
  open optionML
  
  fun FDOM FEMPTY = EMPTY
    | FDOM (FUPDATE (f,(a,b))) = INSERT (a,FDOM f)
    
  fun FAPPLY FEMPTY x = raise (Fail "FAPPLY: empty map")
    | FAPPLY (FUPDATE (f,(a,b))) x = (if x = a then b else FAPPLY f x)
    
  fun FCARD fm = CARD (FDOM fm)
    
  fun FLOOKUP f x = if IN x (FDOM f) then SOME(FAPPLY f x) else NONE
    
  fun FUPDATE_LIST x x' = FOLDL (fn v0 => fn v1 => FUPDATE (v0,v1)) x x'
    
  fun FUNION FEMPTY g = g
    | FUNION f FEMPTY = f
    | FUNION (FUPDATE (f,(x,y))) g = FUPDATE (FUNION f g,(x,y))
    
  fun \\ FEMPTY k = FEMPTY
    | \\ (FUPDATE (fm,(k1,v))) k2 =
        (if k1 = k2 then \\ fm k2 else FUPDATE (\\ fm k2,(k1,v)))
    
  fun SUBMAP FEMPTY f = true
    | SUBMAP (FUPDATE (f,(x,y))) g =
        IN x (FDOM g) andalso
        ((FAPPLY g x = y) andalso SUBMAP (\\ f x) (\\ g x))
    
  fun DRESTRICT FEMPTY r = FEMPTY
    | DRESTRICT (FUPDATE (f,(x,y))) r =
        (if r x then FUPDATE (DRESTRICT f r,(x,y)) else DRESTRICT f r)
    
  fun RRESTRICT FEMPTY P = FEMPTY
    | RRESTRICT (FUPDATE (f,(x,y))) P =
        (if P y then
           FUPDATE (RRESTRICT f P,(x,y))
         else RRESTRICT (DRESTRICT f (fn a => not (a = x))) P)
    
  fun FRANGE FEMPTY = EMPTY
    | FRANGE (FUPDATE (f,(x,y))) =
        INSERT (y,FRANGE (DRESTRICT f (fn a => not (a = x))))
    
  fun o_f f FEMPTY = FEMPTY
    | o_f f (FUPDATE (fm,(k,v))) = FUPDATE (o_f f (\\ fm k),(k,f v))
    
  fun FEVERY P FEMPTY = true
    | FEVERY P (FUPDATE (f,(x,y))) =
        P (x,y) andalso FEVERY P (DRESTRICT f (fn a => not (a = x)))
    
end
