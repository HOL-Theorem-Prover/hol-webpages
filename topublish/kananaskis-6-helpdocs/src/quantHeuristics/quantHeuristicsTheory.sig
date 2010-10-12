signature quantHeuristicsTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val CONJ_NOT_OR_THM : thm
    val EXISTS_NOT_FORALL_THM : thm
    val EXISTS_UNIQUE_INSTANTIATE_THM : thm
    val IS_SOME_EQ_NOT_NONE : thm
    val LEFT_IMP_AND_INTRO : thm
    val LEFT_IMP_OR_INTRO : thm
    val MOVE_EXISTS_IMP_THM : thm
    val PAIR_EQ_EXPAND : thm
    val PAIR_EQ_SIMPLE_EXPAND : thm
    val RIGHT_IMP_AND_INTRO : thm
    val RIGHT_IMP_OR_INTRO : thm
    val UNWIND_EXISTS_THM : thm
  
  val quantHeuristics_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "quantHeuristics"
   
   [CONJ_NOT_OR_THM]  Theorem
      
      |- ∀A B. A ∧ B ⇔ ¬(¬A ∨ ¬B)
   
   [EXISTS_NOT_FORALL_THM]  Theorem
      
      |- ∀P. (∃x. P x) ⇔ ¬∀x. ¬P x
   
   [EXISTS_UNIQUE_INSTANTIATE_THM]  Theorem
      
      |- ∀P i. (∀v. v ≠ i ⇒ ¬P v) ⇒ ((∃!v. P v) ⇔ P i)
   
   [IS_SOME_EQ_NOT_NONE]  Theorem
      
      |- ∀x. IS_SOME x ⇔ x ≠ NONE
   
   [LEFT_IMP_AND_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ x ∧ t1 ⇒ x ∧ t2
   
   [LEFT_IMP_OR_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ x ∨ t1 ⇒ x ∨ t2
   
   [MOVE_EXISTS_IMP_THM]  Theorem
      
      |- (∃x. (∀y. ¬P x y ⇒ R y) ⇒ Q x) ⇔ (∀y. ¬(∀x. P x y) ⇒ R y) ⇒ ∃x. Q x
   
   [PAIR_EQ_EXPAND]  Theorem
      
      |- (((x,y) = X) ⇔ (x = FST X) ∧ (y = SND X)) ∧
         ((X = (x,y)) ⇔ (FST X = x) ∧ (SND X = y))
   
   [PAIR_EQ_SIMPLE_EXPAND]  Theorem
      
      |- (((x,y) = (x,y')) ⇔ (y = y')) ∧ (((y,x) = (y',x)) ⇔ (y = y')) ∧
         (((FST X,y) = X) ⇔ (y = SND X)) ∧ (((x,SND X) = X) ⇔ (x = FST X)) ∧
         ((X = (FST X,y)) ⇔ (SND X = y)) ∧ ((X = (x,SND X)) ⇔ (FST X = x))
   
   [RIGHT_IMP_AND_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ t1 ∧ x ⇒ t2 ∧ x
   
   [RIGHT_IMP_OR_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ t1 ∨ x ⇒ t2 ∨ x
   
   [UNWIND_EXISTS_THM]  Theorem
      
      |- ∀a P. (∃x. P x) ⇔ (∀x. x ≠ a ⇒ ¬P x) ⇒ P a
   
   
*)
end
