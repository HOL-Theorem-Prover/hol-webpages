structure bagML :> bagML =
struct
  nonfix BAG_DISJOINT SET_OF_BAG BAG_CARD BAG_IMAGE BAG_FILTER PSUB_BAG
         SUB_BAG BAG_MERGE BAG_INTER BAG_DIFF BAG_UNION BAG_INN BAG_IN
         BAG_VAL BAG_INSERT EMPTY_BAG * / div mod + - ^ @ <> > < >= <=
         := o before;
  
  datatype 'a bag = EMPTY_BAG | BAG_INSERT of 'a * 'a bag
  open numML
  open setML
  
  fun BAG_VAL EMPTY_BAG x = ZERO
    | BAG_VAL (BAG_INSERT (e,b)) x =
        (if e = x then + ONE (BAG_VAL b x) else BAG_VAL b x)
    
  fun BAG_IN x EMPTY_BAG = false
    | BAG_IN x (BAG_INSERT (y,b)) = (x = y) orelse BAG_IN x b
    
  fun BAG_INN e n b = >= (BAG_VAL b e) n
    
  fun BAG_UNION EMPTY_BAG b = b
    | BAG_UNION (BAG_INSERT (x,b1)) b2 = BAG_INSERT (x,BAG_UNION b1 b2)
    
  fun BAG_DIFF b EMPTY_BAG = b
    | BAG_DIFF EMPTY_BAG b = EMPTY_BAG
    | BAG_DIFF (BAG_INSERT (x,b)) (BAG_INSERT (y,EMPTY_BAG)) =
        (if x = y then
           b
         else BAG_INSERT (x,BAG_DIFF b (BAG_INSERT (y,EMPTY_BAG))))
    | BAG_DIFF b1 (BAG_INSERT (y,b2)) =
        BAG_DIFF (BAG_DIFF b1 (BAG_INSERT (y,EMPTY_BAG))) b2
    
  fun BAG_INTER EMPTY_BAG b = EMPTY_BAG
    | BAG_INTER b EMPTY_BAG = EMPTY_BAG
    | BAG_INTER (BAG_INSERT (x,b1)) b2 =
        (if BAG_IN x b2 then
           BAG_INSERT
             (x,BAG_INTER b1 (BAG_DIFF b2 (BAG_INSERT (x,EMPTY_BAG))))
         else BAG_INTER b1 b2)
    
  fun BAG_MERGE EMPTY_BAG b = b
    | BAG_MERGE b EMPTY_BAG = b
    | BAG_MERGE (BAG_INSERT (x,b1)) b2 =
        BAG_INSERT
          (x,BAG_MERGE b1 (BAG_DIFF b2 (BAG_INSERT (x,EMPTY_BAG))))
    
  fun SUB_BAG EMPTY_BAG b = true
    | SUB_BAG (BAG_INSERT (x,b1)) b2 =
        BAG_IN x b2 andalso
        SUB_BAG b1 (BAG_DIFF b2 (BAG_INSERT (x,EMPTY_BAG)))
    
  fun PSUB_BAG b1 b2 = SUB_BAG b1 b2 andalso not (SUB_BAG b2 b1)
    
  fun BAG_FILTER P EMPTY_BAG = EMPTY_BAG
    | BAG_FILTER P (BAG_INSERT (e,b)) =
        (if P e then BAG_INSERT (e,BAG_FILTER P b) else BAG_FILTER P b)
    
  fun BAG_IMAGE f EMPTY_BAG = EMPTY_BAG
    | BAG_IMAGE f (BAG_INSERT (e,b)) = BAG_INSERT (f e,BAG_IMAGE f b)
    
  fun BAG_CARD EMPTY_BAG = ZERO
    | BAG_CARD (BAG_INSERT (e,b)) = + (BAG_CARD b) ONE
    
  fun SET_OF_BAG EMPTY_BAG = EMPTY
    | SET_OF_BAG (BAG_INSERT (x,b)) = INSERT (x,SET_OF_BAG b)
    
  fun BAG_DISJOINT b1 b2 = DISJOINT (SET_OF_BAG b1) (SET_OF_BAG b2)
    
end
