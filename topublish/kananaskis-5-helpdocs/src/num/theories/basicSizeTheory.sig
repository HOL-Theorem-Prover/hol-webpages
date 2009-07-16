signature basicSizeTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val bool_size_def : thm
    val one_size_def : thm
    val option_size_def : thm
    val pair_size_def : thm
    val sum_size_def : thm
  
  val basicSize_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [numeral] Parent theory of "basicSize"
   
   [option] Parent theory of "basicSize"
   
   [bool_size_def]  Definition
      
      |- !b. bool_size b = 0
   
   [one_size_def]  Definition
      
      |- !x. one_size x = 0
   
   [option_size_def]  Definition
      
      |- (!f. option_size f NONE = 0) /\
         !f x. option_size f (SOME x) = SUC (f x)
   
   [pair_size_def]  Definition
      
      |- !f g. pair_size f g = (\(x,y). f x + g y)
   
   [sum_size_def]  Definition
      
      |- (!f g x. sum_size f g (INL x) = f x) /\
         !f g y. sum_size f g (INR y) = g y
   
   
*)
end
