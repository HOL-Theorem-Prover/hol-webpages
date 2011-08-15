signature satTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val AND_IMP : thm
    val AND_INV : thm
    val AND_INV2 : thm
    val AND_INV_IMP : thm
    val EQF_Imp1 : thm
    val EQT_Imp1 : thm
    val NOT_ELIM2 : thm
    val NOT_NOT : thm
    val OR_DUAL : thm
    val OR_DUAL2 : thm
    val OR_DUAL3 : thm
    val dc_cond : thm
    val dc_conj : thm
    val dc_disj : thm
    val dc_eq : thm
    val dc_imp : thm
    val dc_neg : thm
    val pth_an1 : thm
    val pth_an2 : thm
    val pth_ni1 : thm
    val pth_ni2 : thm
    val pth_nn : thm
    val pth_no1 : thm
    val pth_no2 : thm
  
  val sat_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bool] Parent theory of "sat"
   
   [AND_IMP]  Theorem
      
      |- ∀A B C. A ∧ B ⇒ C ⇔ A ⇒ B ⇒ C
   
   [AND_INV]  Theorem
      
      |- ∀A. ¬A ∧ A ⇔ F
   
   [AND_INV2]  Theorem
      
      |- (¬A ⇒ F) ⇒ (A ⇒ F) ⇒ F
   
   [AND_INV_IMP]  Theorem
      
      |- ∀A. A ⇒ ¬A ⇒ F
   
   [EQF_Imp1]  Theorem
      
      |- ∀b. ¬b ⇒ (b ⇔ F)
   
   [EQT_Imp1]  Theorem
      
      |- ∀b. b ⇒ (b ⇔ T)
   
   [NOT_ELIM2]  Theorem
      
      |- ¬A ⇒ F ⇔ A
   
   [NOT_NOT]  Theorem
      
      |- ∀t. ¬ ¬t ⇔ t
   
   [OR_DUAL]  Theorem
      
      |- ¬(A ∨ B) ⇒ F ⇔ ¬A ⇒ ¬B ⇒ F
   
   [OR_DUAL2]  Theorem
      
      |- ¬(A ∨ B) ⇒ F ⇔ (A ⇒ F) ⇒ ¬B ⇒ F
   
   [OR_DUAL3]  Theorem
      
      |- ¬(¬A ∨ B) ⇒ F ⇔ A ⇒ ¬B ⇒ F
   
   [dc_cond]  Theorem
      
      |- (p ⇔ if q then r else s) ⇔
         (p ∨ q ∨ ¬s) ∧ (p ∨ ¬r ∨ ¬q) ∧ (p ∨ ¬r ∨ ¬s) ∧ (¬q ∨ r ∨ ¬p) ∧
         (q ∨ s ∨ ¬p)
   
   [dc_conj]  Theorem
      
      |- (p ⇔ q ∧ r) ⇔ (p ∨ ¬q ∨ ¬r) ∧ (q ∨ ¬p) ∧ (r ∨ ¬p)
   
   [dc_disj]  Theorem
      
      |- (p ⇔ q ∨ r) ⇔ (p ∨ ¬q) ∧ (p ∨ ¬r) ∧ (q ∨ r ∨ ¬p)
   
   [dc_eq]  Theorem
      
      |- (p ⇔ (q ⇔ r)) ⇔
         (p ∨ q ∨ r) ∧ (p ∨ ¬r ∨ ¬q) ∧ (q ∨ ¬r ∨ ¬p) ∧ (r ∨ ¬q ∨ ¬p)
   
   [dc_imp]  Theorem
      
      |- (p ⇔ q ⇒ r) ⇔ (p ∨ q) ∧ (p ∨ ¬r) ∧ (¬q ∨ r ∨ ¬p)
   
   [dc_neg]  Theorem
      
      |- (p ⇔ ¬q) ⇔ (p ∨ q) ∧ (¬q ∨ ¬p)
   
   [pth_an1]  Theorem
      
      |- p ∧ q ⇒ p
   
   [pth_an2]  Theorem
      
      |- p ∧ q ⇒ q
   
   [pth_ni1]  Theorem
      
      |- ¬(p ⇒ q) ⇒ p
   
   [pth_ni2]  Theorem
      
      |- ¬(p ⇒ q) ⇒ ¬q
   
   [pth_nn]  Theorem
      
      |- ¬ ¬p ⇒ p
   
   [pth_no1]  Theorem
      
      |- ¬(p ∨ q) ⇒ ¬p
   
   [pth_no2]  Theorem
      
      |- ¬(p ∨ q) ⇒ ¬q
   
   
*)
end
