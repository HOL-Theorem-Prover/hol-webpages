structure optionML :> optionML =
struct
  nonfix OPTION_JOIN THE IS_NONE IS_SOME OPTION_MAP * / div mod + - ^ @
         <> > < >= <= := o before;
  
  datatype option = datatype Option.option
  
  fun OPTION_MAP f (SOME(x)) = SOME(f x)
    | OPTION_MAP f NONE = NONE
    
  fun IS_SOME (SOME(x)) = true
    | IS_SOME NONE = false
    
  fun IS_NONE (SOME(x)) = false
    | IS_NONE NONE = true
    
  fun THE NONE = raise (Fail "THE: applied to NONE")
    | THE (SOME(x)) = x
    
  fun OPTION_JOIN NONE = NONE
    | OPTION_JOIN (SOME(x)) = x
    
end
