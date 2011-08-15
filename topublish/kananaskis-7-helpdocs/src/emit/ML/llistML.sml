structure llistML :> llistML =
struct
  nonfix toList LTAKE LTL LHD LFILTER LMAP LAPPEND * / div mod + - ^ @
         <> > < >= <= := o before;
  
  open numML
  open listML
  
  type 'a llist = 'a seq.seq
  fun llcases n c seq = seq.fcases seq (n,c)
  fun LLCONS h t = seq.cons h (seq.delay t)
  fun LCONS h t = seq.cons h t
  val LNIL = seq.empty
  fun :::(h,t) = LCONS h t
  fun LUNFOLD f x = seq.delay (fn () => case f x of NONE => LNIL | SOME (y,e) => LCONS e (LUNFOLD f y))
  fun LAPPEND l1 l2 =
        llcases l2 (fn (h,t) => LLCONS h (fn () => LAPPEND t l2)) l1
    
  fun LMAP f l =
        llcases LNIL (fn (h,t) => LLCONS (f h) (fn () => LMAP f t)) l
    
  fun LFILTER P l =
        llcases LNIL (fn (h,t) => if P h then
            LLCONS h (fn () => LFILTER P t) else LFILTER P t) l
    
  fun LHD ll = llcases optionML.NONE (fn (h,t) => SOME(h)) ll
    
  fun LTL ll = llcases optionML.NONE (fn (h,t) => SOME(t)) ll
    
  fun LTAKE n ll =
        if n = ZERO then SOME([])
        else
          case LHD ll
           of optionML.NONE => optionML.NONE
            | SOME(h) =>
                 optionML.OPTION_MAP (fn t => h::t)
                   (LTAKE (- n ONE) (optionML.THE (LTL ll)))
    
  fun toList ll =
        llcases (SOME([])) (fn (h,t) =>
          optionML.OPTION_MAP (fn t => h::t) (toList t)) ll
    
end
