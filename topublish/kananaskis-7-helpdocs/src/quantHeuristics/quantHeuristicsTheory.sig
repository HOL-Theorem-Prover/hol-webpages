signature quantHeuristicsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val GUESS_EXISTS_STRONG_def : thm
    val GUESS_EXISTS_def : thm
    val GUESS_FALSE_def : thm
    val GUESS_FORALL_STRONG_def : thm
    val GUESS_FORALL_def : thm
    val GUESS_TRUE_def : thm
  
  (*  Theorems  *)
    val CONJ_NOT_OR_THM : thm
    val EXISTS_NOT_FORALL_THM : thm
    val GUESSES_NEG_DUALITY : thm
    val GUESSES_NEG_REWRITE : thm
    val GUESSES_UEXISTS_THM1 : thm
    val GUESSES_UEXISTS_THM2 : thm
    val GUESSES_UEXISTS_THM3 : thm
    val GUESSES_WEAKEN_THM : thm
    val GUESS_EXISTS_FORALL_REWRITES : thm
    val GUESS_EXISTS_THM : thm
    val GUESS_FALSE_THM : thm
    val GUESS_FORALL_THM : thm
    val GUESS_REWRITES : thm
    val GUESS_RULES_BOOL : thm
    val GUESS_RULES_COND : thm
    val GUESS_RULES_CONJ : thm
    val GUESS_RULES_CONSTANT_EXISTS : thm
    val GUESS_RULES_CONSTANT_FORALL : thm
    val GUESS_RULES_DISJ : thm
    val GUESS_RULES_ELIM_UNIT : thm
    val GUESS_RULES_EQUATION_EXISTS_STRONG : thm
    val GUESS_RULES_EQUATION_FALSE : thm
    val GUESS_RULES_EQUATION_TRUE : thm
    val GUESS_RULES_EQUIV : thm
    val GUESS_RULES_EXISTS : thm
    val GUESS_RULES_EXISTS_UNIQUE : thm
    val GUESS_RULES_EXISTS___NEW_FV : thm
    val GUESS_RULES_EXISTS___NEW_FV_1 : thm
    val GUESS_RULES_FORALL : thm
    val GUESS_RULES_FORALL___NEW_FV : thm
    val GUESS_RULES_FORALL___NEW_FV_1 : thm
    val GUESS_RULES_IMP : thm
    val GUESS_RULES_NEG : thm
    val GUESS_RULES_ONE_CASE___EXISTS_STRONG : thm
    val GUESS_RULES_ONE_CASE___FORALL_STRONG : thm
    val GUESS_RULES_TWO_CASES : thm
    val GUESS_TRUE_FALSE_THM : thm
    val GUESS_TRUE_THM : thm
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
   [ConseqConv] Parent theory of "quantHeuristics"
   
   [list] Parent theory of "quantHeuristics"
   
   [GUESS_EXISTS_STRONG_def]  Definition
      
      |- ∀i P. GUESS_EXISTS_STRONG i P ⇔ ∀v. P v ⇒ ∃fv. v = i fv
   
   [GUESS_EXISTS_def]  Definition
      
      |- ∀i P. GUESS_EXISTS i P ⇔ ((∃v. P v) ⇔ ∃fv. P (i fv))
   
   [GUESS_FALSE_def]  Definition
      
      |- ∀i P. GUESS_FALSE i P ⇔ ∀fv. ¬P (i fv)
   
   [GUESS_FORALL_STRONG_def]  Definition
      
      |- ∀i P. GUESS_FORALL_STRONG i P ⇔ ∀v. ¬P v ⇒ ∃fv. v = i fv
   
   [GUESS_FORALL_def]  Definition
      
      |- ∀i P. GUESS_FORALL i P ⇔ ((∀v. P v) ⇔ ∀fv. P (i fv))
   
   [GUESS_TRUE_def]  Definition
      
      |- ∀i P. GUESS_TRUE i P ⇔ ∀fv. P (i fv)
   
   [CONJ_NOT_OR_THM]  Theorem
      
      |- ∀A B. A ∧ B ⇔ ¬(¬A ∨ ¬B)
   
   [EXISTS_NOT_FORALL_THM]  Theorem
      
      |- ∀P. (∃x. P x) ⇔ ¬∀x. ¬P x
   
   [GUESSES_NEG_DUALITY]  Theorem
      
      |- (GUESS_EXISTS i ($~ o P) ⇔ GUESS_FORALL i P) ∧
         (GUESS_FORALL i ($~ o P) ⇔ GUESS_EXISTS i P) ∧
         (GUESS_EXISTS_STRONG i ($~ o P) ⇔ GUESS_FORALL_STRONG i P) ∧
         (GUESS_FORALL_STRONG i ($~ o P) ⇔ GUESS_EXISTS_STRONG i P) ∧
         (GUESS_TRUE i ($~ o P) ⇔ GUESS_FALSE i P) ∧
         (GUESS_FALSE i ($~ o P) ⇔ GUESS_TRUE i P)
   
   [GUESSES_NEG_REWRITE]  Theorem
      
      |- (GUESS_EXISTS i (λx. ¬P x) ⇔ GUESS_FORALL i (λx. P x)) ∧
         (GUESS_FORALL i (λx. ¬P x) ⇔ GUESS_EXISTS i (λx. P x)) ∧
         (GUESS_EXISTS_STRONG i (λx. ¬P x) ⇔
          GUESS_FORALL_STRONG i (λx. P x)) ∧
         (GUESS_FORALL_STRONG i (λx. ¬P x) ⇔
          GUESS_EXISTS_STRONG i (λx. P x)) ∧
         (GUESS_TRUE i (λx. ¬P x) ⇔ GUESS_FALSE i (λx. P x)) ∧
         (GUESS_FALSE i (λx. ¬P x) ⇔ GUESS_TRUE i (λx. P x))
   
   [GUESSES_UEXISTS_THM1]  Theorem
      
      |- ∀i P. GUESS_EXISTS (λx. i) P ⇒ ($?! P ⇔ P i ∧ ∀v. P v ⇒ (v = i))
   
   [GUESSES_UEXISTS_THM2]  Theorem
      
      |- ∀i P. GUESS_EXISTS_STRONG (λx. i) P ⇒ ($?! P ⇔ P i)
   
   [GUESSES_UEXISTS_THM3]  Theorem
      
      |- ∀i P. GUESS_TRUE (λx. i) P ⇒ ($?! P ⇔ ∀v. P v ⇒ (v = i))
   
   [GUESSES_WEAKEN_THM]  Theorem
      
      |- (GUESS_FORALL_STRONG i P ⇒ GUESS_FORALL i P) ∧
         (GUESS_FALSE i P ⇒ GUESS_FORALL i P) ∧
         (GUESS_TRUE i P ⇒ GUESS_EXISTS i P) ∧
         (GUESS_EXISTS_STRONG i P ⇒ GUESS_EXISTS i P)
   
   [GUESS_EXISTS_FORALL_REWRITES]  Theorem
      
      |- (GUESS_EXISTS i P ⇔ ∀v. P v ⇒ ∃fv. P (i fv)) ∧
         (GUESS_FORALL i P ⇔ ∀v. ¬P v ⇒ ∃fv. ¬P (i fv))
   
   [GUESS_EXISTS_THM]  Theorem
      
      |- ∀i P. GUESS_EXISTS i P ⇒ ($? P ⇔ ∃fv. P (i fv))
   
   [GUESS_FALSE_THM]  Theorem
      
      |- ∀i P. GUESS_FALSE i P ⇒ ($! P ⇔ F)
   
   [GUESS_FORALL_THM]  Theorem
      
      |- ∀i P. GUESS_FORALL i P ⇒ ($! P ⇔ ∀fv. P (i fv))
   
   [GUESS_REWRITES]  Theorem
      
      |- ((GUESS_EXISTS i P ⇔ ∀v. P v ⇒ ∃fv. P (i fv)) ∧
          (GUESS_FORALL i P ⇔ ∀v. ¬P v ⇒ ∃fv. ¬P (i fv))) ∧
         (∀i P. GUESS_TRUE i P ⇔ ∀fv. P (i fv)) ∧
         (∀i P. GUESS_FALSE i P ⇔ ∀fv. ¬P (i fv)) ∧
         (∀i P. GUESS_EXISTS_STRONG i P ⇔ ∀v. P v ⇒ ∃fv. v = i fv) ∧
         ∀i P. GUESS_FORALL_STRONG i P ⇔ ∀v. ¬P v ⇒ ∃fv. v = i fv
   
   [GUESS_RULES_BOOL]  Theorem
      
      |- GUESS_TRUE (λARB. T) (λx. x) ∧ GUESS_FALSE (λARB. F) (λx. x) ∧
         GUESS_EXISTS_STRONG (λARB. T) (λx. x) ∧
         GUESS_FORALL_STRONG (λARB. F) (λx. x)
   
   [GUESS_RULES_COND]  Theorem
      
      |- (GUESS_FALSE i (λx. P x) ∧ GUESS_FALSE i (λx. Q x) ⇒
          GUESS_FALSE i (λx. if b x then P x else Q x)) ∧
         (GUESS_TRUE i (λx. P x) ∧ GUESS_TRUE i (λx. Q x) ⇒
          GUESS_TRUE i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ∧ GUESS_EXISTS i (λx. Q x) ⇒
          GUESS_EXISTS i (λx. if bc then P x else Q x)) ∧
         (GUESS_FORALL i (λx. P x) ∧ GUESS_FORALL i (λx. Q x) ⇒
          GUESS_FORALL i (λx. if bc then P x else Q x)) ∧
         (GUESS_EXISTS_STRONG i (λx. P x) ∧
          GUESS_EXISTS_STRONG i (λx. Q x) ⇒
          GUESS_EXISTS_STRONG i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. P x) ∧
          GUESS_FORALL_STRONG i (λx. Q x) ⇒
          GUESS_FORALL_STRONG i (λx. if b x then P x else Q x)) ∧
         (GUESS_FALSE i (λx. b x) ∧ GUESS_FALSE i (λx. Q x) ⇒
          GUESS_FALSE i (λx. if b x then P x else Q x)) ∧
         (GUESS_FALSE i (λx. b x) ∧ GUESS_TRUE i (λx. Q x) ⇒
          GUESS_TRUE i (λx. if b x then P x else Q x)) ∧
         (GUESS_TRUE i (λx. b x) ∧ GUESS_FALSE i (λx. P x) ⇒
          GUESS_FALSE i (λx. if b x then P x else Q x)) ∧
         (GUESS_TRUE i (λx. b x) ∧ GUESS_TRUE i (λx. P x) ⇒
          GUESS_TRUE i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. b x) ∧
          GUESS_EXISTS_STRONG i (λx. P x) ⇒
          GUESS_EXISTS_STRONG i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS_STRONG i (λx. b x) ∧
          GUESS_EXISTS_STRONG i (λx. Q x) ⇒
          GUESS_EXISTS_STRONG i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS_STRONG i (λx. b x) ∧
          GUESS_FORALL_STRONG i (λx. Q x) ⇒
          GUESS_FORALL_STRONG i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. b x) ∧
          GUESS_FORALL_STRONG i (λx. P x) ⇒
          GUESS_FORALL_STRONG i (λx. if b x then P x else Q x))
   
   [GUESS_RULES_CONJ]  Theorem
      
      |- (GUESS_FALSE i (λx. P x) ⇒ GUESS_FALSE i (λx. P x ∧ Q x)) ∧
         (GUESS_FALSE i (λx. Q x) ⇒ GUESS_FALSE i (λx. P x ∧ Q x)) ∧
         (GUESS_FORALL i (λx. P x) ∧ GUESS_FORALL i (λx. Q x) ⇒
          GUESS_FORALL i (λx. P x ∧ Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. P x) ∧
          GUESS_FORALL_STRONG i (λx. Q x) ⇒
          GUESS_FORALL_STRONG i (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS (λxxx. iK) (λx. P x) ∧
          GUESS_EXISTS (λxxx. iK) (λx. Q x) ⇒
          GUESS_EXISTS (λxxx. iK) (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ⇒ GUESS_EXISTS i (λx. P x ∧ q)) ∧
         (GUESS_EXISTS i (λx. Q x) ⇒ GUESS_EXISTS i (λx. p ∧ Q x)) ∧
         (GUESS_TRUE i (λx. P x) ∧ GUESS_TRUE i (λx. Q x) ⇒
          GUESS_TRUE i (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS_STRONG i (λx. P x) ⇒
          GUESS_EXISTS_STRONG i (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS_STRONG i (λx. Q x) ⇒
          GUESS_EXISTS_STRONG i (λx. P x ∧ Q x))
   
   [GUESS_RULES_CONSTANT_EXISTS]  Theorem
      
      |- GUESS_EXISTS i (λx. p) ⇔ T
   
   [GUESS_RULES_CONSTANT_FORALL]  Theorem
      
      |- GUESS_FORALL i (λx. p) ⇔ T
   
   [GUESS_RULES_DISJ]  Theorem
      
      |- (GUESS_TRUE i (λx. P x) ⇒ GUESS_TRUE i (λx. P x ∨ Q x)) ∧
         (GUESS_TRUE i (λx. Q x) ⇒ GUESS_TRUE i (λx. P x ∨ Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ∧ GUESS_EXISTS i (λx. Q x) ⇒
          GUESS_EXISTS i (λx. P x ∨ Q x)) ∧
         (GUESS_EXISTS_STRONG i (λx. P x) ∧
          GUESS_EXISTS_STRONG i (λx. Q x) ⇒
          GUESS_EXISTS_STRONG i (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL (λxxx. iK) (λx. P x) ∧
          GUESS_FORALL (λxxx. iK) (λx. Q x) ⇒
          GUESS_FORALL (λxxx. iK) (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL i (λx. P x) ⇒ GUESS_FORALL i (λx. P x ∨ q)) ∧
         (GUESS_FORALL i (λx. Q x) ⇒ GUESS_FORALL i (λx. p ∨ Q x)) ∧
         (GUESS_FALSE i (λx. P x) ∧ GUESS_FALSE i (λx. Q x) ⇒
          GUESS_FALSE i (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. P x) ⇒
          GUESS_FORALL_STRONG i (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. Q x) ⇒
          GUESS_FORALL_STRONG i (λx. P x ∨ Q x))
   
   [GUESS_RULES_ELIM_UNIT]  Theorem
      
      |- (GUESS_FALSE i vt ⇔ GUESS_FALSE (λx. i (x,())) vt) ∧
         (GUESS_TRUE i vt ⇔ GUESS_TRUE (λx. i (x,())) vt) ∧
         (GUESS_EXISTS i vt ⇔ GUESS_EXISTS (λx. i (x,())) vt) ∧
         (GUESS_FORALL i vt ⇔ GUESS_FORALL (λx. i (x,())) vt) ∧
         (GUESS_EXISTS_STRONG i vt ⇔
          GUESS_EXISTS_STRONG (λx. i (x,())) vt) ∧
         (GUESS_FORALL_STRONG i vt ⇔ GUESS_FORALL_STRONG (λx. i (x,())) vt)
   
   [GUESS_RULES_EQUATION_EXISTS_STRONG]  Theorem
      
      |- ∀i. GUESS_EXISTS_STRONG (λxxx. i) (λx. x = i)
   
   [GUESS_RULES_EQUATION_FALSE]  Theorem
      
      |- ∀i P Q. (∀fv. P (i fv) ≠ Q (i fv)) ⇒ GUESS_FALSE i (λx. P x = Q x)
   
   [GUESS_RULES_EQUATION_TRUE]  Theorem
      
      |- ∀i P Q. (P i = Q i) ⇒ GUESS_TRUE (λxxx. i) (λx. P x = Q x)
   
   [GUESS_RULES_EQUIV]  Theorem
      
      |- (GUESS_TRUE i (λx. P x) ∧ GUESS_TRUE i (λx. Q x) ⇒
          GUESS_TRUE i (λx. P x ⇔ Q x)) ∧
         (GUESS_FALSE i (λx. P x) ∧ GUESS_FALSE i (λx. Q x) ⇒
          GUESS_TRUE i (λx. P x ⇔ Q x)) ∧
         (GUESS_TRUE i (λx. P x) ∧ GUESS_FALSE i (λx. Q x) ⇒
          GUESS_FALSE i (λx. P x ⇔ Q x)) ∧
         (GUESS_FALSE i (λx. P x) ∧ GUESS_TRUE i (λx. Q x) ⇒
          GUESS_FALSE i (λx. P x ⇔ Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. P1 x) ∧
          GUESS_FORALL_STRONG i (λx. P2 x) ⇒
          GUESS_FORALL_STRONG i (λx. P1 x ⇔ P2 x)) ∧
         (GUESS_EXISTS_STRONG i (λx. P1 x) ∧
          GUESS_EXISTS_STRONG i (λx. P2 x) ⇒
          GUESS_FORALL_STRONG i (λx. P1 x ⇔ P2 x)) ∧
         (GUESS_EXISTS_STRONG i (λx. P1 x) ∧
          GUESS_FORALL_STRONG i (λx. P2 x) ⇒
          GUESS_EXISTS_STRONG i (λx. P1 x ⇔ P2 x)) ∧
         (GUESS_FORALL_STRONG i (λx. P1 x) ∧
          GUESS_EXISTS_STRONG i (λx. P2 x) ⇒
          GUESS_EXISTS_STRONG i (λx. P1 x ⇔ P2 x))
   
   [GUESS_RULES_EXISTS]  Theorem
      
      |- ((∀y. GUESS_TRUE i (λx. P x y)) ⇒ GUESS_TRUE i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS i (λx. P x y)) ⇒
          GUESS_EXISTS i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS_STRONG i (λx. P x y)) ⇒
          GUESS_EXISTS_STRONG i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FALSE i (λx. P x y)) ⇒
          GUESS_FALSE i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL (λxxx. iK) (λx. P x y)) ⇒
          GUESS_FORALL (λxxx. iK) (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL_STRONG i (λx. P x y)) ⇒
          GUESS_FORALL_STRONG i (λx. ∃y. P x y))
   
   [GUESS_RULES_EXISTS_UNIQUE]  Theorem
      
      |- ((∀y. GUESS_FALSE i (λx. P x y)) ⇒
          GUESS_FALSE i (λx. ∃!y. P x y)) ∧
         ((∀y. GUESS_EXISTS_STRONG i (λx. P x y)) ⇒
          GUESS_EXISTS_STRONG i (λx. ∃!y. P x y))
   
   [GUESS_RULES_EXISTS___NEW_FV]  Theorem
      
      |- ((∀y. GUESS_TRUE (iy y) (λx. P x y)) ⇒
          GUESS_TRUE (λfv. iy (FST fv) (SND fv)) (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS (iy y) (λx. P x y)) ⇒
          GUESS_EXISTS (λfv. iy (FST fv) (SND fv)) (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS_STRONG (iy y) (λx. P x y)) ⇒
          GUESS_EXISTS_STRONG (λfv. iy (FST fv) (SND fv))
            (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL_STRONG (iy y) (λx. P x y)) ⇒
          GUESS_FORALL_STRONG (λfv. iy (FST fv) (SND fv)) (λx. ∃y. P x y))
   
   [GUESS_RULES_EXISTS___NEW_FV_1]  Theorem
      
      |- ((∀y. GUESS_TRUE (λxxx. i y) (λx. P x y)) ⇒
          GUESS_TRUE i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS (λxxx. i y) (λx. P x y)) ⇒
          GUESS_EXISTS i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS_STRONG (λxxx. i y) (λx. P x y)) ⇒
          GUESS_EXISTS_STRONG i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL_STRONG (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FORALL_STRONG i (λx. ∃y. P x y))
   
   [GUESS_RULES_FORALL]  Theorem
      
      |- ((∀y. GUESS_FALSE i (λx. P x y)) ⇒
          GUESS_FALSE i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL i (λx. P x y)) ⇒
          GUESS_FORALL i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL_STRONG i (λx. P x y)) ⇒
          GUESS_FORALL_STRONG i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_TRUE i (λx. P x y)) ⇒ GUESS_TRUE i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS (λxxx. iK) (λx. P x y)) ⇒
          GUESS_EXISTS (λxxx. iK) (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS_STRONG i (λx. P x y)) ⇒
          GUESS_EXISTS_STRONG i (λx. ∀y. P x y))
   
   [GUESS_RULES_FORALL___NEW_FV]  Theorem
      
      |- ((∀y. GUESS_FALSE (iy y) (λx. P x y)) ⇒
          GUESS_FALSE (λfv. iy (FST fv) (SND fv)) (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL (iy y) (λx. P x y)) ⇒
          GUESS_FORALL (λfv. iy (FST fv) (SND fv)) (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL_STRONG (iy y) (λx. P x y)) ⇒
          GUESS_FORALL_STRONG (λfv. iy (FST fv) (SND fv))
            (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS_STRONG (iy y) (λx. P x y)) ⇒
          GUESS_EXISTS_STRONG (λfv. iy (FST fv) (SND fv)) (λx. ∀y. P x y))
   
   [GUESS_RULES_FORALL___NEW_FV_1]  Theorem
      
      |- ((∀y. GUESS_FALSE (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FALSE i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FORALL i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL_STRONG (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FORALL_STRONG i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS_STRONG (λxxx. i y) (λx. P x y)) ⇒
          GUESS_EXISTS_STRONG i (λx. ∀y. P x y))
   
   [GUESS_RULES_IMP]  Theorem
      
      |- (GUESS_FALSE i (λx. P x) ⇒ GUESS_TRUE i (λx. P x ⇒ Q x)) ∧
         (GUESS_TRUE i (λx. Q x) ⇒ GUESS_TRUE i (λx. P x ⇒ Q x)) ∧
         (GUESS_FORALL i (λx. P x) ∧ GUESS_EXISTS i (λx. Q x) ⇒
          GUESS_EXISTS i (λx. P x ⇒ Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. P x) ∧
          GUESS_EXISTS_STRONG i (λx. Q x) ⇒
          GUESS_EXISTS_STRONG i (λx. P x ⇒ Q x)) ∧
         (GUESS_EXISTS (λxxx. iK) (λx. P x) ∧
          GUESS_FORALL (λxxx. iK) (λx. Q x) ⇒
          GUESS_FORALL (λxxx. iK) (λx. P x ⇒ Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ⇒ GUESS_FORALL i (λx. P x ⇒ q)) ∧
         (GUESS_FORALL i (λx. Q x) ⇒ GUESS_FORALL i (λx. p ⇒ Q x)) ∧
         (GUESS_TRUE i (λx. P x) ∧ GUESS_FALSE i (λx. Q x) ⇒
          GUESS_FALSE i (λx. P x ⇒ Q x)) ∧
         (GUESS_EXISTS_STRONG i (λx. P x) ⇒
          GUESS_FORALL_STRONG i (λx. P x ⇒ Q x)) ∧
         (GUESS_FORALL_STRONG i (λx. Q x) ⇒
          GUESS_FORALL_STRONG i (λx. P x ⇒ Q x))
   
   [GUESS_RULES_NEG]  Theorem
      
      |- (GUESS_EXISTS i (λx. P x) ⇒ GUESS_FORALL i (λx. ¬P x)) ∧
         (GUESS_EXISTS_STRONG i (λx. P x) ⇒
          GUESS_FORALL_STRONG i (λx. ¬P x)) ∧
         (GUESS_TRUE i (λx. P x) ⇒ GUESS_FALSE i (λx. ¬P x)) ∧
         (GUESS_FORALL i (λx. P x) ⇒ GUESS_EXISTS i (λx. ¬P x)) ∧
         (GUESS_FORALL_STRONG i (λx. P x) ⇒
          GUESS_EXISTS_STRONG i (λx. ¬P x)) ∧
         (GUESS_FALSE i (λx. P x) ⇒ GUESS_TRUE i (λx. ¬P x))
   
   [GUESS_RULES_ONE_CASE___EXISTS_STRONG]  Theorem
      
      |- ∀P Q. (∀x. ∃fv. x = Q fv) ⇒ GUESS_EXISTS_STRONG Q P
   
   [GUESS_RULES_ONE_CASE___FORALL_STRONG]  Theorem
      
      |- ∀P Q. (∀x. ∃fv. x = Q fv) ⇒ GUESS_FORALL_STRONG Q P
   
   [GUESS_RULES_TWO_CASES]  Theorem
      
      |- ∀y Q.
           (∀x. (x = y) ∨ ∃fv. x = Q fv) ⇒
           GUESS_FORALL_STRONG Q (λx. x = y)
   
   [GUESS_TRUE_FALSE_THM]  Theorem
      
      |- (GUESS_TRUE i P ⇒ ((∃v. P v) ⇔ T)) ∧
         (GUESS_FALSE i P ⇒ ((∀v. P v) ⇔ F))
   
   [GUESS_TRUE_THM]  Theorem
      
      |- ∀i P. GUESS_TRUE i P ⇒ ($? P ⇔ T)
   
   [IS_SOME_EQ_NOT_NONE]  Theorem
      
      |- ∀x. IS_SOME x ⇔ x ≠ NONE
   
   [LEFT_IMP_AND_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ x ∧ t1 ⇒ x ∧ t2
   
   [LEFT_IMP_OR_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ x ∨ t1 ⇒ x ∨ t2
   
   [MOVE_EXISTS_IMP_THM]  Theorem
      
      |- (∃x. (∀y. ¬P x y ⇒ R y) ⇒ Q x) ⇔
         (∀y. ¬(∀x. P x y) ⇒ R y) ⇒ ∃x. Q x
   
   [PAIR_EQ_EXPAND]  Theorem
      
      |- (((x,y) = X) ⇔ (x = FST X) ∧ (y = SND X)) ∧
         ((X = (x,y)) ⇔ (FST X = x) ∧ (SND X = y))
   
   [PAIR_EQ_SIMPLE_EXPAND]  Theorem
      
      |- (((x,y) = (x,y')) ⇔ (y = y')) ∧ (((y,x) = (y',x)) ⇔ (y = y')) ∧
         (((FST X,y) = X) ⇔ (y = SND X)) ∧
         (((x,SND X) = X) ⇔ (x = FST X)) ∧
         ((X = (FST X,y)) ⇔ (SND X = y)) ∧ ((X = (x,SND X)) ⇔ (FST X = x))
   
   [RIGHT_IMP_AND_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ t1 ∧ x ⇒ t2 ∧ x
   
   [RIGHT_IMP_OR_INTRO]  Theorem
      
      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ t1 ∨ x ⇒ t2 ∨ x
   
   [UNWIND_EXISTS_THM]  Theorem
      
      |- ∀a P. (∃x. P x) ⇔ (∀x. x ≠ a ⇒ ¬P x) ⇒ P a
   
   
*)
end
