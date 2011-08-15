signature normalFormsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val EXT_POINT_DEF : thm
    val UNIV_POINT_DEF : thm
  
  (*  Theorems  *)
    val EXT_POINT : thm
    val UNIV_POINT : thm
  
  val normalForms_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bool] Parent theory of "normalForms"
   
   [EXT_POINT_DEF]  Definition
      
      |- ∀f g. (f (EXT_POINT f g) = g (EXT_POINT f g)) ⇒ (f = g)
   
   [UNIV_POINT_DEF]  Definition
      
      |- ∀p. p (UNIV_POINT p) ⇒ ∀x. p x
   
   [EXT_POINT]  Theorem
      
      |- ∀f g. (f (EXT_POINT f g) = g (EXT_POINT f g)) ⇔ (f = g)
   
   [UNIV_POINT]  Theorem
      
      |- ∀p. p (UNIV_POINT p) ⇔ ∀x. p x
   
   
*)
end
