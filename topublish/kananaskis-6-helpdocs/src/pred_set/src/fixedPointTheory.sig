signature fixedPointTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val closed_def : thm
    val dense_def : thm
    val empty_def : thm
    val fnsum_def : thm
    val gfp_def : thm
    val lfp_def : thm
    val monotone_def : thm
  
  (*  Theorems  *)
    val empty_monotone : thm
    val fnsum_ASSOC : thm
    val fnsum_COMM : thm
    val fnsum_SUBSET : thm
    val fnsum_empty : thm
    val fnsum_monotone : thm
    val gfp_coinduction : thm
    val gfp_greatest_dense : thm
    val gfp_greatest_fixedpoint : thm
    val gfp_strong_coinduction : thm
    val lfp_empty : thm
    val lfp_fixedpoint : thm
    val lfp_fnsum : thm
    val lfp_induction : thm
    val lfp_least_closed : thm
    val lfp_rule_applied : thm
    val lfp_strong_induction : thm
  
  val fixedPoint_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [pred_set] Parent theory of "fixedPoint"
   
   [closed_def]  Definition
      
      |- ∀f X. closed f X ⇔ f X ⊆ X
   
   [dense_def]  Definition
      
      |- ∀f X. dense f X ⇔ X ⊆ f X
   
   [empty_def]  Definition
      
      |- empty = (λX. ∅)
   
   [fnsum_def]  Definition
      
      |- ∀f1 f2 X. (f1 ++ f2) X = f1 X ∪ f2 X
   
   [gfp_def]  Definition
      
      |- ∀f. gfp f = BIGUNION {X | X ⊆ f X}
   
   [lfp_def]  Definition
      
      |- ∀f. lfp f = BIGINTER {X | f X ⊆ X}
   
   [monotone_def]  Definition
      
      |- ∀f. monotone f ⇔ ∀X Y. X ⊆ Y ⇒ f X ⊆ f Y
   
   [empty_monotone]  Theorem
      
      |- monotone empty
   
   [fnsum_ASSOC]  Theorem
      
      |- ∀f g h. f ++ (g ++ h) = f ++ g ++ h
   
   [fnsum_COMM]  Theorem
      
      |- ∀f g. f ++ g = g ++ f
   
   [fnsum_SUBSET]  Theorem
      
      |- ∀f g X. f X ⊆ (f ++ g) X ∧ g X ⊆ (f ++ g) X
   
   [fnsum_empty]  Theorem
      
      |- ∀f. (f ++ empty = f) ∧ (empty ++ f = f)
   
   [fnsum_monotone]  Theorem
      
      |- ∀f1 f2. monotone f1 ∧ monotone f2 ⇒ monotone (f1 ++ f2)
   
   [gfp_coinduction]  Theorem
      
      |- ∀f. monotone f ⇒ ∀X. X ⊆ f X ⇒ X ⊆ gfp f
   
   [gfp_greatest_dense]  Theorem
      
      |- ∀f. monotone f ⇒ dense f (gfp f) ∧ ∀X. dense f X ⇒ X ⊆ gfp f
   
   [gfp_greatest_fixedpoint]  Theorem
      
      |- ∀f. monotone f ⇒ (gfp f = f (gfp f)) ∧ ∀X. (X = f X) ⇒ X ⊆ gfp f
   
   [gfp_strong_coinduction]  Theorem
      
      |- ∀f. monotone f ⇒ ∀X. X ⊆ f (X ∪ gfp f) ⇒ X ⊆ gfp f
   
   [lfp_empty]  Theorem
      
      |- ∀f x. monotone f ∧ x ∈ f ∅ ⇒ x ∈ lfp f
   
   [lfp_fixedpoint]  Theorem
      
      |- ∀f. monotone f ⇒ (lfp f = f (lfp f)) ∧ ∀X. (X = f X) ⇒ lfp f ⊆ X
   
   [lfp_fnsum]  Theorem
      
      |- ∀f1 f2.
           monotone f1 ∧ monotone f2 ⇒
           lfp f1 ⊆ lfp (f1 ++ f2) ∧ lfp f2 ⊆ lfp (f1 ++ f2)
   
   [lfp_induction]  Theorem
      
      |- ∀f. monotone f ⇒ ∀X. f X ⊆ X ⇒ lfp f ⊆ X
   
   [lfp_least_closed]  Theorem
      
      |- ∀f. monotone f ⇒ closed f (lfp f) ∧ ∀X. closed f X ⇒ lfp f ⊆ X
   
   [lfp_rule_applied]  Theorem
      
      |- ∀f X y. monotone f ∧ X ⊆ lfp f ∧ y ∈ f X ⇒ y ∈ lfp f
   
   [lfp_strong_induction]  Theorem
      
      |- ∀f. monotone f ⇒ ∀X. f (X ∩ lfp f) ⊆ X ⇒ lfp f ⊆ X
   
   
*)
end
