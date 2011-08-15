structure patricia_castsML :> patricia_castsML =
struct
  nonfix INSERT_PTREEs IN_PTREEs KEYSs TRAVERSEs REMOVEs ADD_LISTs ADDs
         FINDs PEEKs num_to_string ADD_LISTw FINDw INSERT_PTREEw
         IN_PTREEw DEPTHw SIZEw TRANSFORMw REMOVEw ADDw PEEKw SOME_PTREE
         THE_PTREE Word_ptree * / div mod + - ^ @ <> > < >= <= := o
         before;
  
  open numML
  open optionML
  open setML
  open bitML
  open wordsML
  open patriciaML
  
  type string = stringML.string
  fun SKIP1 s = String.extract(s,1,NONE)
  fun string_to_num s = s2n (numML.fromInt 256) stringML.ORD
                            (String.^(String.str (Char.chr 1), s))
  datatype ('a,'b)word_ptree = Word_ptree of ('a -> unit) * 'b ptree
  fun THE_PTREE (Word_ptree(a,t)) = t
    
  fun SOME_PTREE t = Word_ptree(combinML.K (),t)
    
  fun PEEKw t w = PEEK (THE_PTREE t) (w2n w)
    
  fun ADDw t (w,d) = SOME_PTREE (ADD (THE_PTREE t) (w2n w,d))
    
  fun REMOVEw t w = SOME_PTREE (REMOVE (THE_PTREE t) (w2n w))
    
  fun TRANSFORMw f t = SOME_PTREE (TRANSFORM f (THE_PTREE t))
    
  fun SIZEw t = SIZE (THE_PTREE t)
    
  fun DEPTHw t = DEPTH (THE_PTREE t)
    
  fun IN_PTREEw w t = IN_PTREE (w2n w) (THE_PTREE t)
    
  fun INSERT_PTREEw w t =
        SOME_PTREE (INSERT_PTREE (w2n w) (THE_PTREE t))
    
  fun FINDw t w = THE (PEEKw t w)
    
  fun ADD_LISTw x x' = listML.FOLDL ADDw x x'
    
  fun num_to_string n = SKIP1 (n2s (fromString "256") stringML.CHR n)
    
  fun PEEKs t w = PEEK t (string_to_num w)
    
  fun FINDs t w = THE (PEEKs t w)
    
  fun ADDs t (w,d) = ADD t (string_to_num w,d)
    
  fun ADD_LISTs x x' = listML.FOLDL ADDs x x'
    
  fun REMOVEs t w = REMOVE t (string_to_num w)
    
  fun TRAVERSEs t = listML.MAP num_to_string (TRAVERSE t)
    
  fun KEYSs t = sortingML.QSORT stringML.string_lt (TRAVERSEs t)
    
  fun IN_PTREEs w t = IN_PTREE (string_to_num w) t
    
  fun INSERT_PTREEs w t = INSERT_PTREE (string_to_num w) t
    
end
