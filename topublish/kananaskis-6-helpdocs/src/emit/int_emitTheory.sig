signature int_emitTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val i2w_itself_primitive_def : thm
    val neg_int_of_num_def : thm
  
  (*  Theorems  *)
    val i2w_itself_def : thm
    val i2w_itself_ind : thm
  
  val int_emit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [integer_word] Parent theory of "int_emit"
   
   [words_emit] Parent theory of "int_emit"
   
   [i2w_itself_primitive_def]  Definition
      
      |- i2w_itself =
         WFREC (@R. WF R) (λi2w_itself a. case a of (i,(:α)) -> I (i2w i))
   
   [neg_int_of_num_def]  Definition
      
      |- ∀n. neg_int_of_num n = -int_of_num (n + 1)
   
   [i2w_itself_def]  Theorem
      
      |- i2w_itself (i,(:α)) = i2w i
   
   [i2w_itself_ind]  Theorem
      
      |- ∀P. (∀i. P (i,(:α))) ⇒ ∀v v1. P (v,v1)
   
   
*)
end
