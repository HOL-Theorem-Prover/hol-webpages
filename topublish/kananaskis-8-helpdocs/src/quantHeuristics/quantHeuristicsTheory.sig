signature quantHeuristicsTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val GUESS_EXISTS_GAP_def : thm
    val GUESS_EXISTS_POINT_def : thm
    val GUESS_EXISTS_def : thm
    val GUESS_FORALL_GAP_def : thm
    val GUESS_FORALL_POINT_def : thm
    val GUESS_FORALL_def : thm
    val IS_REMOVABLE_QUANT_FUN_def : thm

  (*  Theorems  *)
    val CONJ_NOT_OR_THM : thm
    val EXISTS_NOT_FORALL_THM : thm
    val GUESSES_NEG_DUALITY : thm
    val GUESSES_NEG_REWRITE : thm
    val GUESSES_UEXISTS_THM1 : thm
    val GUESSES_UEXISTS_THM2 : thm
    val GUESSES_UEXISTS_THM3 : thm
    val GUESSES_UEXISTS_THM4 : thm
    val GUESSES_WEAKEN_THM : thm
    val GUESS_EXISTS_FORALL_REWRITES : thm
    val GUESS_EXISTS_POINT_THM : thm
    val GUESS_EXISTS_THM : thm
    val GUESS_FORALL_POINT_THM : thm
    val GUESS_FORALL_THM : thm
    val GUESS_POINT_THM : thm
    val GUESS_REWRITES : thm
    val GUESS_RULES_BOOL : thm
    val GUESS_RULES_COND : thm
    val GUESS_RULES_CONJ : thm
    val GUESS_RULES_CONSTANT_EXISTS : thm
    val GUESS_RULES_CONSTANT_FORALL : thm
    val GUESS_RULES_DISJ : thm
    val GUESS_RULES_ELIM_UNIT : thm
    val GUESS_RULES_EQUATION_EXISTS_GAP : thm
    val GUESS_RULES_EQUATION_EXISTS_POINT : thm
    val GUESS_RULES_EQUATION_FORALL_POINT : thm
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
    val GUESS_RULES_ONE_CASE___EXISTS_GAP : thm
    val GUESS_RULES_ONE_CASE___FORALL_GAP : thm
    val GUESS_RULES_STRENGTHEN_EXISTS_POINT : thm
    val GUESS_RULES_STRENGTHEN_FORALL_GAP : thm
    val GUESS_RULES_TRIVIAL_EXISTS_POINT : thm
    val GUESS_RULES_TRIVIAL_FORALL_POINT : thm
    val GUESS_RULES_TWO_CASES : thm
    val GUESS_RULES_WEAKEN_EXISTS_GAP : thm
    val GUESS_RULES_WEAKEN_FORALL_POINT : thm
    val IMP_NEG_CONTRA : thm
    val ISL_ISR_NEG : thm
    val ISL_exists : thm
    val ISR_exists : thm
    val IS_REMOVABLE_QUANT_FUN___EXISTS_THM : thm
    val IS_REMOVABLE_QUANT_FUN___FORALL_THM : thm
    val IS_SOME_EQ_NOT_NONE : thm
    val LEFT_IMP_AND_INTRO : thm
    val LEFT_IMP_OR_INTRO : thm
    val LENGTH_LE_NUM : thm
    val LENGTH_LE_PLUS : thm
    val LENGTH_NIL_SYM : thm
    val LIST_LENGTH_0 : thm
    val LIST_LENGTH_1 : thm
    val LIST_LENGTH_10 : thm
    val LIST_LENGTH_15 : thm
    val LIST_LENGTH_2 : thm
    val LIST_LENGTH_20 : thm
    val LIST_LENGTH_25 : thm
    val LIST_LENGTH_3 : thm
    val LIST_LENGTH_4 : thm
    val LIST_LENGTH_5 : thm
    val LIST_LENGTH_7 : thm
    val LIST_LENGTH_COMPARE_1 : thm
    val LIST_LENGTH_COMPARE_SUC : thm
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

   [GUESS_EXISTS_GAP_def]  Definition

      |- ∀i P. GUESS_EXISTS_GAP i P ⇔ ∀v. P v ⇒ ∃fv. v = i fv

   [GUESS_EXISTS_POINT_def]  Definition

      |- ∀i P. GUESS_EXISTS_POINT i P ⇔ ∀fv. P (i fv)

   [GUESS_EXISTS_def]  Definition

      |- ∀i P. GUESS_EXISTS i P ⇔ ((∃v. P v) ⇔ ∃fv. P (i fv))

   [GUESS_FORALL_GAP_def]  Definition

      |- ∀i P. GUESS_FORALL_GAP i P ⇔ ∀v. ¬P v ⇒ ∃fv. v = i fv

   [GUESS_FORALL_POINT_def]  Definition

      |- ∀i P. GUESS_FORALL_POINT i P ⇔ ∀fv. ¬P (i fv)

   [GUESS_FORALL_def]  Definition

      |- ∀i P. GUESS_FORALL i P ⇔ ((∀v. P v) ⇔ ∀fv. P (i fv))

   [IS_REMOVABLE_QUANT_FUN_def]  Definition

      |- ∀f. IS_REMOVABLE_QUANT_FUN f ⇔ ∀v. ∃x. f x = v

   [CONJ_NOT_OR_THM]  Theorem

      |- ∀A B. A ∧ B ⇔ ¬(¬A ∨ ¬B)

   [EXISTS_NOT_FORALL_THM]  Theorem

      |- ∀P. (∃x. P x) ⇔ ¬∀x. ¬P x

   [GUESSES_NEG_DUALITY]  Theorem

      |- (GUESS_EXISTS i ($~ o P) ⇔ GUESS_FORALL i P) ∧
         (GUESS_FORALL i ($~ o P) ⇔ GUESS_EXISTS i P) ∧
         (GUESS_EXISTS_GAP i ($~ o P) ⇔ GUESS_FORALL_GAP i P) ∧
         (GUESS_FORALL_GAP i ($~ o P) ⇔ GUESS_EXISTS_GAP i P) ∧
         (GUESS_EXISTS_POINT i ($~ o P) ⇔ GUESS_FORALL_POINT i P) ∧
         (GUESS_FORALL_POINT i ($~ o P) ⇔ GUESS_EXISTS_POINT i P)

   [GUESSES_NEG_REWRITE]  Theorem

      |- (GUESS_EXISTS i (λx. ¬P x) ⇔ GUESS_FORALL i (λx. P x)) ∧
         (GUESS_FORALL i (λx. ¬P x) ⇔ GUESS_EXISTS i (λx. P x)) ∧
         (GUESS_EXISTS_GAP i (λx. ¬P x) ⇔ GUESS_FORALL_GAP i (λx. P x)) ∧
         (GUESS_FORALL_GAP i (λx. ¬P x) ⇔ GUESS_EXISTS_GAP i (λx. P x)) ∧
         (GUESS_EXISTS_POINT i (λx. ¬P x) ⇔
          GUESS_FORALL_POINT i (λx. P x)) ∧
         (GUESS_FORALL_POINT i (λx. ¬P x) ⇔ GUESS_EXISTS_POINT i (λx. P x))

   [GUESSES_UEXISTS_THM1]  Theorem

      |- ∀i P. GUESS_EXISTS (λx. i) P ⇒ ($?! P ⇔ P i ∧ ∀v. P v ⇒ (v = i))

   [GUESSES_UEXISTS_THM2]  Theorem

      |- ∀i P. GUESS_EXISTS_GAP (λx. i) P ⇒ ($?! P ⇔ P i)

   [GUESSES_UEXISTS_THM3]  Theorem

      |- ∀i P. GUESS_EXISTS_POINT (λx. i) P ⇒ ($?! P ⇔ ∀v. P v ⇒ (v = i))

   [GUESSES_UEXISTS_THM4]  Theorem

      |- ∀i P.
           GUESS_EXISTS_POINT (λx. i) P ⇒
           GUESS_EXISTS_GAP (λx. i) P ⇒
           ($?! P ⇔ T)

   [GUESSES_WEAKEN_THM]  Theorem

      |- (GUESS_FORALL_GAP i P ⇒ GUESS_FORALL i P) ∧
         (GUESS_FORALL_POINT i P ⇒ GUESS_FORALL i P) ∧
         (GUESS_EXISTS_POINT i P ⇒ GUESS_EXISTS i P) ∧
         (GUESS_EXISTS_GAP i P ⇒ GUESS_EXISTS i P)

   [GUESS_EXISTS_FORALL_REWRITES]  Theorem

      |- (GUESS_EXISTS i P ⇔ ∀v. P v ⇒ ∃fv. P (i fv)) ∧
         (GUESS_FORALL i P ⇔ ∀v. ¬P v ⇒ ∃fv. ¬P (i fv))

   [GUESS_EXISTS_POINT_THM]  Theorem

      |- ∀i P. GUESS_EXISTS_POINT i P ⇒ ($? P ⇔ T)

   [GUESS_EXISTS_THM]  Theorem

      |- ∀i P. GUESS_EXISTS i P ⇒ ($? P ⇔ ∃fv. P (i fv))

   [GUESS_FORALL_POINT_THM]  Theorem

      |- ∀i P. GUESS_FORALL_POINT i P ⇒ ($! P ⇔ F)

   [GUESS_FORALL_THM]  Theorem

      |- ∀i P. GUESS_FORALL i P ⇒ ($! P ⇔ ∀fv. P (i fv))

   [GUESS_POINT_THM]  Theorem

      |- (GUESS_EXISTS_POINT i P ⇒ ((∃v. P v) ⇔ T)) ∧
         (GUESS_FORALL_POINT i P ⇒ ((∀v. P v) ⇔ F))

   [GUESS_REWRITES]  Theorem

      |- ((GUESS_EXISTS i P ⇔ ∀v. P v ⇒ ∃fv. P (i fv)) ∧
          (GUESS_FORALL i P ⇔ ∀v. ¬P v ⇒ ∃fv. ¬P (i fv))) ∧
         (∀i P. GUESS_EXISTS_POINT i P ⇔ ∀fv. P (i fv)) ∧
         (∀i P. GUESS_FORALL_POINT i P ⇔ ∀fv. ¬P (i fv)) ∧
         (∀i P. GUESS_EXISTS_GAP i P ⇔ ∀v. P v ⇒ ∃fv. v = i fv) ∧
         ∀i P. GUESS_FORALL_GAP i P ⇔ ∀v. ¬P v ⇒ ∃fv. v = i fv

   [GUESS_RULES_BOOL]  Theorem

      |- GUESS_EXISTS_POINT (λARB. T) (λx. x) ∧
         GUESS_FORALL_POINT (λARB. F) (λx. x) ∧
         GUESS_EXISTS_GAP (λARB. T) (λx. x) ∧
         GUESS_FORALL_GAP (λARB. F) (λx. x)

   [GUESS_RULES_COND]  Theorem

      |- (GUESS_FORALL_POINT i (λx. P x) ∧ GUESS_FORALL_POINT i (λx. Q x) ⇒
          GUESS_FORALL_POINT i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. P x) ∧ GUESS_EXISTS_POINT i (λx. Q x) ⇒
          GUESS_EXISTS_POINT i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ∧ GUESS_EXISTS i (λx. Q x) ⇒
          GUESS_EXISTS i (λx. if bc then P x else Q x)) ∧
         (GUESS_FORALL i (λx. P x) ∧ GUESS_FORALL i (λx. Q x) ⇒
          GUESS_FORALL i (λx. if bc then P x else Q x)) ∧
         (GUESS_EXISTS_GAP i (λx. P x) ∧ GUESS_EXISTS_GAP i (λx. Q x) ⇒
          GUESS_EXISTS_GAP i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_GAP i (λx. P x) ∧ GUESS_FORALL_GAP i (λx. Q x) ⇒
          GUESS_FORALL_GAP i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_POINT i (λx. b x) ∧ GUESS_FORALL_POINT i (λx. Q x) ⇒
          GUESS_FORALL_POINT i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_POINT i (λx. b x) ∧ GUESS_EXISTS_POINT i (λx. Q x) ⇒
          GUESS_EXISTS_POINT i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. b x) ∧ GUESS_FORALL_POINT i (λx. P x) ⇒
          GUESS_FORALL_POINT i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. b x) ∧ GUESS_EXISTS_POINT i (λx. P x) ⇒
          GUESS_EXISTS_POINT i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_GAP i (λx. b x) ∧ GUESS_EXISTS_GAP i (λx. P x) ⇒
          GUESS_EXISTS_GAP i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS_GAP i (λx. b x) ∧ GUESS_EXISTS_GAP i (λx. Q x) ⇒
          GUESS_EXISTS_GAP i (λx. if b x then P x else Q x)) ∧
         (GUESS_EXISTS_GAP i (λx. b x) ∧ GUESS_FORALL_GAP i (λx. Q x) ⇒
          GUESS_FORALL_GAP i (λx. if b x then P x else Q x)) ∧
         (GUESS_FORALL_GAP i (λx. b x) ∧ GUESS_FORALL_GAP i (λx. P x) ⇒
          GUESS_FORALL_GAP i (λx. if b x then P x else Q x))

   [GUESS_RULES_CONJ]  Theorem

      |- (GUESS_FORALL_POINT i (λx. P x) ⇒
          GUESS_FORALL_POINT i (λx. P x ∧ Q x)) ∧
         (GUESS_FORALL_POINT i (λx. Q x) ⇒
          GUESS_FORALL_POINT i (λx. P x ∧ Q x)) ∧
         (GUESS_FORALL i (λx. P x) ∧ GUESS_FORALL i (λx. Q x) ⇒
          GUESS_FORALL i (λx. P x ∧ Q x)) ∧
         (GUESS_FORALL_GAP i (λx. P x) ∧ GUESS_FORALL_GAP i (λx. Q x) ⇒
          GUESS_FORALL_GAP i (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS (λxxx. iK) (λx. P x) ∧
          GUESS_EXISTS (λxxx. iK) (λx. Q x) ⇒
          GUESS_EXISTS (λxxx. iK) (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ⇒ GUESS_EXISTS i (λx. P x ∧ q)) ∧
         (GUESS_EXISTS i (λx. Q x) ⇒ GUESS_EXISTS i (λx. p ∧ Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. P x) ∧ GUESS_EXISTS_POINT i (λx. Q x) ⇒
          GUESS_EXISTS_POINT i (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS_GAP i (λx. P x) ⇒
          GUESS_EXISTS_GAP i (λx. P x ∧ Q x)) ∧
         (GUESS_EXISTS_GAP i (λx. Q x) ⇒
          GUESS_EXISTS_GAP i (λx. P x ∧ Q x))

   [GUESS_RULES_CONSTANT_EXISTS]  Theorem

      |- GUESS_EXISTS i (λx. p) ⇔ T

   [GUESS_RULES_CONSTANT_FORALL]  Theorem

      |- GUESS_FORALL i (λx. p) ⇔ T

   [GUESS_RULES_DISJ]  Theorem

      |- (GUESS_EXISTS_POINT i (λx. P x) ⇒
          GUESS_EXISTS_POINT i (λx. P x ∨ Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. Q x) ⇒
          GUESS_EXISTS_POINT i (λx. P x ∨ Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ∧ GUESS_EXISTS i (λx. Q x) ⇒
          GUESS_EXISTS i (λx. P x ∨ Q x)) ∧
         (GUESS_EXISTS_GAP i (λx. P x) ∧ GUESS_EXISTS_GAP i (λx. Q x) ⇒
          GUESS_EXISTS_GAP i (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL (λxxx. iK) (λx. P x) ∧
          GUESS_FORALL (λxxx. iK) (λx. Q x) ⇒
          GUESS_FORALL (λxxx. iK) (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL i (λx. P x) ⇒ GUESS_FORALL i (λx. P x ∨ q)) ∧
         (GUESS_FORALL i (λx. Q x) ⇒ GUESS_FORALL i (λx. p ∨ Q x)) ∧
         (GUESS_FORALL_POINT i (λx. P x) ∧ GUESS_FORALL_POINT i (λx. Q x) ⇒
          GUESS_FORALL_POINT i (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL_GAP i (λx. P x) ⇒
          GUESS_FORALL_GAP i (λx. P x ∨ Q x)) ∧
         (GUESS_FORALL_GAP i (λx. Q x) ⇒
          GUESS_FORALL_GAP i (λx. P x ∨ Q x))

   [GUESS_RULES_ELIM_UNIT]  Theorem

      |- (GUESS_FORALL_POINT i vt ⇔ GUESS_FORALL_POINT (λx. i (x,())) vt) ∧
         (GUESS_EXISTS_POINT i vt ⇔ GUESS_EXISTS_POINT (λx. i (x,())) vt) ∧
         (GUESS_EXISTS i vt ⇔ GUESS_EXISTS (λx. i (x,())) vt) ∧
         (GUESS_FORALL i vt ⇔ GUESS_FORALL (λx. i (x,())) vt) ∧
         (GUESS_EXISTS_GAP i vt ⇔ GUESS_EXISTS_GAP (λx. i (x,())) vt) ∧
         (GUESS_FORALL_GAP i vt ⇔ GUESS_FORALL_GAP (λx. i (x,())) vt)

   [GUESS_RULES_EQUATION_EXISTS_GAP]  Theorem

      |- ∀i. GUESS_EXISTS_GAP (λxxx. i) (λx. x = i)

   [GUESS_RULES_EQUATION_EXISTS_POINT]  Theorem

      |- ∀i P Q. (P i = Q i) ⇒ GUESS_EXISTS_POINT (λxxx. i) (λx. P x = Q x)

   [GUESS_RULES_EQUATION_FORALL_POINT]  Theorem

      |- ∀i P Q.
           (∀fv. P (i fv) ≠ Q (i fv)) ⇒
           GUESS_FORALL_POINT i (λx. P x = Q x)

   [GUESS_RULES_EQUIV]  Theorem

      |- (GUESS_EXISTS_POINT i (λx. P x) ∧ GUESS_EXISTS_POINT i (λx. Q x) ⇒
          GUESS_EXISTS_POINT i (λx. P x ⇔ Q x)) ∧
         (GUESS_FORALL_POINT i (λx. P x) ∧ GUESS_FORALL_POINT i (λx. Q x) ⇒
          GUESS_EXISTS_POINT i (λx. P x ⇔ Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. P x) ∧ GUESS_FORALL_POINT i (λx. Q x) ⇒
          GUESS_FORALL_POINT i (λx. P x ⇔ Q x)) ∧
         (GUESS_FORALL_POINT i (λx. P x) ∧ GUESS_EXISTS_POINT i (λx. Q x) ⇒
          GUESS_FORALL_POINT i (λx. P x ⇔ Q x)) ∧
         (GUESS_FORALL_GAP i (λx. P1 x) ∧ GUESS_FORALL_GAP i (λx. P2 x) ⇒
          GUESS_FORALL_GAP i (λx. P1 x ⇔ P2 x)) ∧
         (GUESS_EXISTS_GAP i (λx. P1 x) ∧ GUESS_EXISTS_GAP i (λx. P2 x) ⇒
          GUESS_FORALL_GAP i (λx. P1 x ⇔ P2 x)) ∧
         (GUESS_EXISTS_GAP i (λx. P1 x) ∧ GUESS_FORALL_GAP i (λx. P2 x) ⇒
          GUESS_EXISTS_GAP i (λx. P1 x ⇔ P2 x)) ∧
         (GUESS_FORALL_GAP i (λx. P1 x) ∧ GUESS_EXISTS_GAP i (λx. P2 x) ⇒
          GUESS_EXISTS_GAP i (λx. P1 x ⇔ P2 x))

   [GUESS_RULES_EXISTS]  Theorem

      |- ((∀y. GUESS_EXISTS_POINT i (λx. P x y)) ⇒
          GUESS_EXISTS_POINT i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS i (λx. P x y)) ⇒
          GUESS_EXISTS i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS_GAP i (λx. P x y)) ⇒
          GUESS_EXISTS_GAP i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL_POINT i (λx. P x y)) ⇒
          GUESS_FORALL_POINT i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL (λxxx. iK) (λx. P x y)) ⇒
          GUESS_FORALL (λxxx. iK) (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL_GAP i (λx. P x y)) ⇒
          GUESS_FORALL_GAP i (λx. ∃y. P x y))

   [GUESS_RULES_EXISTS_UNIQUE]  Theorem

      |- ((∀y. GUESS_FORALL_POINT i (λx. P x y)) ⇒
          GUESS_FORALL_POINT i (λx. ∃!y. P x y)) ∧
         ((∀y. GUESS_EXISTS_GAP i (λx. P x y)) ⇒
          GUESS_EXISTS_GAP i (λx. ∃!y. P x y))

   [GUESS_RULES_EXISTS___NEW_FV]  Theorem

      |- ((∀y. GUESS_EXISTS_POINT (iy y) (λx. P x y)) ⇒
          GUESS_EXISTS_POINT (λfv. iy (FST fv) (SND fv)) (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS (iy y) (λx. P x y)) ⇒
          GUESS_EXISTS (λfv. iy (FST fv) (SND fv)) (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS_GAP (iy y) (λx. P x y)) ⇒
          GUESS_EXISTS_GAP (λfv. iy (FST fv) (SND fv)) (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL_GAP (iy y) (λx. P x y)) ⇒
          GUESS_FORALL_GAP (λfv. iy (FST fv) (SND fv)) (λx. ∃y. P x y))

   [GUESS_RULES_EXISTS___NEW_FV_1]  Theorem

      |- ((∀y. GUESS_EXISTS_POINT (λxxx. i y) (λx. P x y)) ⇒
          GUESS_EXISTS_POINT i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS (λxxx. i y) (λx. P x y)) ⇒
          GUESS_EXISTS i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_EXISTS_GAP (λxxx. i y) (λx. P x y)) ⇒
          GUESS_EXISTS_GAP i (λx. ∃y. P x y)) ∧
         ((∀y. GUESS_FORALL_GAP (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FORALL_GAP i (λx. ∃y. P x y))

   [GUESS_RULES_FORALL]  Theorem

      |- ((∀y. GUESS_FORALL_POINT i (λx. P x y)) ⇒
          GUESS_FORALL_POINT i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL i (λx. P x y)) ⇒
          GUESS_FORALL i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL_GAP i (λx. P x y)) ⇒
          GUESS_FORALL_GAP i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS_POINT i (λx. P x y)) ⇒
          GUESS_EXISTS_POINT i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS (λxxx. iK) (λx. P x y)) ⇒
          GUESS_EXISTS (λxxx. iK) (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS_GAP i (λx. P x y)) ⇒
          GUESS_EXISTS_GAP i (λx. ∀y. P x y))

   [GUESS_RULES_FORALL___NEW_FV]  Theorem

      |- ((∀y. GUESS_FORALL_POINT (iy y) (λx. P x y)) ⇒
          GUESS_FORALL_POINT (λfv. iy (FST fv) (SND fv)) (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL (iy y) (λx. P x y)) ⇒
          GUESS_FORALL (λfv. iy (FST fv) (SND fv)) (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL_GAP (iy y) (λx. P x y)) ⇒
          GUESS_FORALL_GAP (λfv. iy (FST fv) (SND fv)) (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS_GAP (iy y) (λx. P x y)) ⇒
          GUESS_EXISTS_GAP (λfv. iy (FST fv) (SND fv)) (λx. ∀y. P x y))

   [GUESS_RULES_FORALL___NEW_FV_1]  Theorem

      |- ((∀y. GUESS_FORALL_POINT (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FORALL_POINT i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FORALL i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_FORALL_GAP (λxxx. i y) (λx. P x y)) ⇒
          GUESS_FORALL_GAP i (λx. ∀y. P x y)) ∧
         ((∀y. GUESS_EXISTS_GAP (λxxx. i y) (λx. P x y)) ⇒
          GUESS_EXISTS_GAP i (λx. ∀y. P x y))

   [GUESS_RULES_IMP]  Theorem

      |- (GUESS_FORALL_POINT i (λx. P x) ⇒
          GUESS_EXISTS_POINT i (λx. P x ⇒ Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. Q x) ⇒
          GUESS_EXISTS_POINT i (λx. P x ⇒ Q x)) ∧
         (GUESS_FORALL i (λx. P x) ∧ GUESS_EXISTS i (λx. Q x) ⇒
          GUESS_EXISTS i (λx. P x ⇒ Q x)) ∧
         (GUESS_FORALL_GAP i (λx. P x) ∧ GUESS_EXISTS_GAP i (λx. Q x) ⇒
          GUESS_EXISTS_GAP i (λx. P x ⇒ Q x)) ∧
         (GUESS_EXISTS (λxxx. iK) (λx. P x) ∧
          GUESS_FORALL (λxxx. iK) (λx. Q x) ⇒
          GUESS_FORALL (λxxx. iK) (λx. P x ⇒ Q x)) ∧
         (GUESS_EXISTS i (λx. P x) ⇒ GUESS_FORALL i (λx. P x ⇒ q)) ∧
         (GUESS_FORALL i (λx. Q x) ⇒ GUESS_FORALL i (λx. p ⇒ Q x)) ∧
         (GUESS_EXISTS_POINT i (λx. P x) ∧ GUESS_FORALL_POINT i (λx. Q x) ⇒
          GUESS_FORALL_POINT i (λx. P x ⇒ Q x)) ∧
         (GUESS_EXISTS_GAP i (λx. P x) ⇒
          GUESS_FORALL_GAP i (λx. P x ⇒ Q x)) ∧
         (GUESS_FORALL_GAP i (λx. Q x) ⇒
          GUESS_FORALL_GAP i (λx. P x ⇒ Q x))

   [GUESS_RULES_NEG]  Theorem

      |- (GUESS_EXISTS i (λx. P x) ⇒ GUESS_FORALL i (λx. ¬P x)) ∧
         (GUESS_EXISTS_GAP i (λx. P x) ⇒ GUESS_FORALL_GAP i (λx. ¬P x)) ∧
         (GUESS_EXISTS_POINT i (λx. P x) ⇒
          GUESS_FORALL_POINT i (λx. ¬P x)) ∧
         (GUESS_FORALL i (λx. P x) ⇒ GUESS_EXISTS i (λx. ¬P x)) ∧
         (GUESS_FORALL_GAP i (λx. P x) ⇒ GUESS_EXISTS_GAP i (λx. ¬P x)) ∧
         (GUESS_FORALL_POINT i (λx. P x) ⇒ GUESS_EXISTS_POINT i (λx. ¬P x))

   [GUESS_RULES_ONE_CASE___EXISTS_GAP]  Theorem

      |- ∀P Q. (∀x. ∃fv. x = Q fv) ⇒ GUESS_EXISTS_GAP Q P

   [GUESS_RULES_ONE_CASE___FORALL_GAP]  Theorem

      |- ∀P Q. (∀x. ∃fv. x = Q fv) ⇒ GUESS_FORALL_GAP Q P

   [GUESS_RULES_STRENGTHEN_EXISTS_POINT]  Theorem

      |- ∀P Q.
           (∀x. P x ⇒ Q x) ⇒
           GUESS_EXISTS_POINT i P ⇒
           GUESS_EXISTS_POINT i Q

   [GUESS_RULES_STRENGTHEN_FORALL_GAP]  Theorem

      |- ∀P Q.
           (∀x. P x ⇒ Q x) ⇒ GUESS_FORALL_GAP i P ⇒ GUESS_FORALL_GAP i Q

   [GUESS_RULES_TRIVIAL_EXISTS_POINT]  Theorem

      |- ∀i P. P i ⇒ GUESS_EXISTS_POINT (λxxx. i) P

   [GUESS_RULES_TRIVIAL_FORALL_POINT]  Theorem

      |- ∀i P. ¬P i ⇒ GUESS_FORALL_POINT (λxxx. i) P

   [GUESS_RULES_TWO_CASES]  Theorem

      |- ∀y Q.
           (∀x. (x = y) ∨ ∃fv. x = Q fv) ⇒ GUESS_FORALL_GAP Q (λx. x = y)

   [GUESS_RULES_WEAKEN_EXISTS_GAP]  Theorem

      |- ∀P Q.
           (∀x. Q x ⇒ P x) ⇒ GUESS_EXISTS_GAP i P ⇒ GUESS_EXISTS_GAP i Q

   [GUESS_RULES_WEAKEN_FORALL_POINT]  Theorem

      |- ∀P Q.
           (∀x. Q x ⇒ P x) ⇒
           GUESS_FORALL_POINT i P ⇒
           GUESS_FORALL_POINT i Q

   [IMP_NEG_CONTRA]  Theorem

      |- ∀P i x. ¬P i ⇒ P x ⇒ x ≠ i

   [ISL_ISR_NEG]  Theorem

      |- (¬ISR x ⇔ ISL x) ∧ (¬ISL x ⇔ ISR x)

   [ISL_exists]  Theorem

      |- ISL x ⇔ ∃l. x = INL l

   [ISR_exists]  Theorem

      |- ISR x ⇔ ∃r. x = INR r

   [IS_REMOVABLE_QUANT_FUN___EXISTS_THM]  Theorem

      |- ∀f P. IS_REMOVABLE_QUANT_FUN f ⇒ ((∃x. P (f x)) ⇔ ∃x'. P x')

   [IS_REMOVABLE_QUANT_FUN___FORALL_THM]  Theorem

      |- ∀f P. IS_REMOVABLE_QUANT_FUN f ⇒ ((∀x. P (f x)) ⇔ ∀x'. P x')

   [IS_SOME_EQ_NOT_NONE]  Theorem

      |- ∀x. IS_SOME x ⇔ x ≠ NONE

   [LEFT_IMP_AND_INTRO]  Theorem

      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ x ∧ t1 ⇒ x ∧ t2

   [LEFT_IMP_OR_INTRO]  Theorem

      |- ∀x t1 t2. (t1 ⇒ t2) ⇒ x ∨ t1 ⇒ x ∨ t2

   [LENGTH_LE_NUM]  Theorem

      |- n ≤ LENGTH l ⇔ ∃l1 l2. (LENGTH l1 = n) ∧ (l = l1 ++ l2)

   [LENGTH_LE_PLUS]  Theorem

      |- n + m ≤ LENGTH l ⇔
         ∃l1 l2. (LENGTH l1 = n) ∧ m ≤ LENGTH l2 ∧ (l = l1 ++ l2)

   [LENGTH_NIL_SYM]  Theorem

      |- (0 = LENGTH l) ⇔ (l = [])

   [LIST_LENGTH_0]  Theorem

      |- ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_1]  Theorem

      |- ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_10]  Theorem

      |- ((LENGTH l = 10) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         ((10 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         (9 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l > 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l ≥ 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ 10 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (x + 10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ x + 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 10 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((10 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = x + 10) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((x + 10 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 9) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         ((9 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         (8 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l > 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l ≥ 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ 9 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (x + 9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ x + 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 9 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((9 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = x + 9) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((x + 9 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 8) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         ((8 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         (7 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l > 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l ≥ 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ 8 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (x + 8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ x + 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 8 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((8 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = x + 8) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((x + 8 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 7) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         ((7 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         (6 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l > 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l ≥ 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ 7 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (x + 7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ x + 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 7 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((7 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = x + 7) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((x + 7 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 6) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         ((6 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         (5 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l > 5 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l ≥ 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ 6 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (x + 6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ x + 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 6 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((6 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = x + 6) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((x + 6 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 5) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         ((5 = LENGTH l) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         (4 < LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l > 4 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l ≥ 5 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ 5 + x ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (x + 5 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ x + 5 ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 5 + x) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((5 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = x + 5) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((x + 5 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 4) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         ((4 = LENGTH l) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         (3 < LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l > 3 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l ≥ 4 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ 4 + x ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (x + 4 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ x + 4 ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 4 + x) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((4 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = x + 4) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((x + 4 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_15]  Theorem

      |- ((LENGTH l = 15) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15]) ∧
         ((15 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15]) ∧
         (14 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (LENGTH l > 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (15 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (LENGTH l ≥ 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (15 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (LENGTH l ≥ 15 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (x + 15 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (LENGTH l ≥ x + 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = 15 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((15 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = x + 15) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((x + 15 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = 14) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13;
             e14]) ∧
         ((14 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13;
             e14]) ∧
         (13 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (LENGTH l > 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (14 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (LENGTH l ≥ 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (14 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (LENGTH l ≥ 14 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (x + 14 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (LENGTH l ≥ x + 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = 14 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((14 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = x + 14) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((x + 14 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = 13) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13]) ∧
         ((13 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13]) ∧
         (12 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (LENGTH l > 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (13 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (LENGTH l ≥ 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (13 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (LENGTH l ≥ 13 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (x + 13 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (LENGTH l ≥ x + 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = 13 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((13 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = x + 13) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((x + 13 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = 12) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12]) ∧
         ((12 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12]) ∧
         (11 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (LENGTH l > 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (12 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (LENGTH l ≥ 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (12 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (LENGTH l ≥ 12 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (x + 12 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (LENGTH l ≥ x + 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = 12 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((12 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = x + 12) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((x + 12 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = 11) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11]) ∧
         ((11 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11]) ∧
         (10 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (LENGTH l > 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (11 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (LENGTH l ≥ 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (11 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (LENGTH l ≥ 11 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (x + 11 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (LENGTH l ≥ x + 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = 11 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((11 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = x + 11) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((x + 11 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = 10) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         ((10 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         (9 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l > 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l ≥ 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ 10 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (x + 10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ x + 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 10 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((10 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = x + 10) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((x + 10 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 9) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         ((9 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         (8 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l > 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l ≥ 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ 9 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (x + 9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ x + 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 9 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((9 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = x + 9) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((x + 9 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 8) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         ((8 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         (7 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l > 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l ≥ 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ 8 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (x + 8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ x + 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 8 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((8 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = x + 8) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((x + 8 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 7) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         ((7 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         (6 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l > 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l ≥ 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ 7 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (x + 7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ x + 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 7 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((7 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = x + 7) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((x + 7 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 6) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         ((6 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         (5 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l > 5 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l ≥ 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ 6 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (x + 6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ x + 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 6 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((6 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = x + 6) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((x + 6 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 5) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         ((5 = LENGTH l) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         (4 < LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l > 4 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l ≥ 5 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ 5 + x ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (x + 5 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ x + 5 ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 5 + x) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((5 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = x + 5) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((x + 5 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 4) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         ((4 = LENGTH l) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         (3 < LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l > 3 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l ≥ 4 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ 4 + x ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (x + 4 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ x + 4 ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 4 + x) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((4 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = x + 4) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((x + 4 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_2]  Theorem

      |- ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_20]  Theorem

      |- ((LENGTH l = 20) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20]) ∧
         ((20 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20]) ∧
         (19 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (LENGTH l > 19 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (20 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (LENGTH l ≥ 20 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (20 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         (LENGTH l ≥ 20 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         (x + 20 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         (LENGTH l ≥ x + 20 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((LENGTH l = 20 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((20 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((LENGTH l = x + 20) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((x + 20 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((LENGTH l = 19) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19]) ∧
         ((19 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19]) ∧
         (18 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (LENGTH l > 18 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (19 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (LENGTH l ≥ 19 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (19 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         (LENGTH l ≥ 19 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         (x + 19 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         (LENGTH l ≥ x + 19 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((LENGTH l = 19 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((19 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((LENGTH l = x + 19) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((x + 19 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((LENGTH l = 18) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18]) ∧
         ((18 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18]) ∧
         (17 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (LENGTH l > 17 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (18 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (LENGTH l ≥ 18 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (18 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         (LENGTH l ≥ 18 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         (x + 18 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         (LENGTH l ≥ x + 18 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((LENGTH l = 18 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((18 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((LENGTH l = x + 18) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((x + 18 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((LENGTH l = 17) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17]) ∧
         ((17 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17]) ∧
         (16 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (LENGTH l > 16 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (17 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (LENGTH l ≥ 17 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (17 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         (LENGTH l ≥ 17 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         (x + 17 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         (LENGTH l ≥ x + 17 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((LENGTH l = 17 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((17 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((LENGTH l = x + 17) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((x + 17 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((LENGTH l = 16) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16]) ∧
         ((16 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16]) ∧
         (15 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (LENGTH l > 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (16 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (LENGTH l ≥ 16 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (16 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         (LENGTH l ≥ 16 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         (x + 16 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         (LENGTH l ≥ x + 16 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((LENGTH l = 16 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((16 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((LENGTH l = x + 16) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((x + 16 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((LENGTH l = 15) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15]) ∧
         ((15 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15]) ∧
         (14 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (LENGTH l > 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (15 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (LENGTH l ≥ 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (15 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (LENGTH l ≥ 15 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (x + 15 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (LENGTH l ≥ x + 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = 15 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((15 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = x + 15) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((x + 15 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = 14) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13;
             e14]) ∧
         ((14 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13;
             e14]) ∧
         (13 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (LENGTH l > 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (14 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (LENGTH l ≥ 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (14 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (LENGTH l ≥ 14 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (x + 14 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (LENGTH l ≥ x + 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = 14 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((14 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = x + 14) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((x + 14 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = 13) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13]) ∧
         ((13 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13]) ∧
         (12 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (LENGTH l > 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (13 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (LENGTH l ≥ 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (13 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (LENGTH l ≥ 13 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (x + 13 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (LENGTH l ≥ x + 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = 13 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((13 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = x + 13) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((x + 13 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = 12) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12]) ∧
         ((12 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12]) ∧
         (11 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (LENGTH l > 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (12 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (LENGTH l ≥ 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (12 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (LENGTH l ≥ 12 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (x + 12 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (LENGTH l ≥ x + 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = 12 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((12 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = x + 12) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((x + 12 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = 11) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11]) ∧
         ((11 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11]) ∧
         (10 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (LENGTH l > 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (11 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (LENGTH l ≥ 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (11 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (LENGTH l ≥ 11 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (x + 11 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (LENGTH l ≥ x + 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = 11 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((11 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = x + 11) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((x + 11 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = 10) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         ((10 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         (9 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l > 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l ≥ 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ 10 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (x + 10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ x + 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 10 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((10 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = x + 10) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((x + 10 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 9) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         ((9 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         (8 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l > 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l ≥ 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ 9 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (x + 9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ x + 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 9 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((9 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = x + 9) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((x + 9 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 8) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         ((8 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         (7 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l > 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l ≥ 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ 8 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (x + 8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ x + 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 8 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((8 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = x + 8) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((x + 8 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 7) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         ((7 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         (6 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l > 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l ≥ 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ 7 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (x + 7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ x + 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 7 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((7 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = x + 7) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((x + 7 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 6) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         ((6 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         (5 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l > 5 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l ≥ 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ 6 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (x + 6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ x + 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 6 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((6 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = x + 6) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((x + 6 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 5) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         ((5 = LENGTH l) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         (4 < LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l > 4 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l ≥ 5 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ 5 + x ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (x + 5 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ x + 5 ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 5 + x) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((5 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = x + 5) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((x + 5 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 4) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         ((4 = LENGTH l) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         (3 < LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l > 3 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l ≥ 4 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ 4 + x ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (x + 4 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ x + 4 ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 4 + x) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((4 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = x + 4) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((x + 4 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_25]  Theorem

      |- ((LENGTH l = 25) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22 e23 e24 e25.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22; e23; e24; e25]) ∧
         ((25 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22 e23 e24 e25.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22; e23; e24; e25]) ∧
         (24 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                l') ∧
         (LENGTH l > 24 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                l') ∧
         (25 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                l') ∧
         (LENGTH l ≥ 25 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                l') ∧
         (25 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         (LENGTH l ≥ 25 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         (x + 25 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         (LENGTH l ≥ x + 25 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         ((LENGTH l = 25 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         ((25 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         ((LENGTH l = x + 25) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         ((x + 25 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24 e25.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::e25::
                 l')) ∧
         ((LENGTH l = 24) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22 e23 e24.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22; e23; e24]) ∧
         ((24 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22 e23 e24.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22; e23; e24]) ∧
         (23 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l') ∧
         (LENGTH l > 23 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l') ∧
         (24 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l') ∧
         (LENGTH l ≥ 24 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l') ∧
         (24 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         (LENGTH l ≥ 24 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         (x + 24 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         (LENGTH l ≥ x + 24 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         ((LENGTH l = 24 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         ((24 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         ((LENGTH l = x + 24) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         ((x + 24 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23 e24.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::e24::l')) ∧
         ((LENGTH l = 23) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22 e23.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22; e23]) ∧
         ((23 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22 e23.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22; e23]) ∧
         (22 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::l') ∧
         (LENGTH l > 22 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::l') ∧
         (23 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::l') ∧
         (LENGTH l ≥ 23 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::e23::l') ∧
         (23 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         (LENGTH l ≥ 23 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         (x + 23 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         (LENGTH l ≥ x + 23 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         ((LENGTH l = 23 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         ((23 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         ((LENGTH l = x + 23) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         ((x + 23 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22 e23.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::e23::l')) ∧
         ((LENGTH l = 22) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22]) ∧
         ((22 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21 e22.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21; e22]) ∧
         (21 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::l') ∧
         (LENGTH l > 21 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::l') ∧
         (22 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::l') ∧
         (LENGTH l ≥ 22 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::e22::l') ∧
         (22 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         (LENGTH l ≥ 22 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         (x + 22 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         (LENGTH l ≥ x + 22 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         ((LENGTH l = 22 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         ((22 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         ((LENGTH l = x + 22) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         ((x + 22 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21 e22.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::e22::l')) ∧
         ((LENGTH l = 21) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21]) ∧
         ((21 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20 e21.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20; e21]) ∧
         (20 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::l') ∧
         (LENGTH l > 20 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::l') ∧
         (21 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::l') ∧
         (LENGTH l ≥ 21 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::e21::l') ∧
         (21 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         (LENGTH l ≥ 21 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         (x + 21 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         (LENGTH l ≥ x + 21 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         ((LENGTH l = 21 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         ((21 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         ((LENGTH l = x + 21) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         ((x + 21 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20 e21.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::e21::l')) ∧
         ((LENGTH l = 20) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20]) ∧
         ((20 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19 e20.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19; e20]) ∧
         (19 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (LENGTH l > 19 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (20 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (LENGTH l ≥ 20 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::e20::l') ∧
         (20 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         (LENGTH l ≥ 20 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         (x + 20 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         (LENGTH l ≥ x + 20 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((LENGTH l = 20 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((20 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((LENGTH l = x + 20) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((x + 20 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19 e20.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::e20::l')) ∧
         ((LENGTH l = 19) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19]) ∧
         ((19 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
             e19.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18; e19]) ∧
         (18 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (LENGTH l > 18 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (19 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (LENGTH l ≥ 19 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::e19::l') ∧
         (19 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         (LENGTH l ≥ 19 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         (x + 19 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         (LENGTH l ≥ x + 19 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((LENGTH l = 19 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((19 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((LENGTH l = x + 19) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((x + 19 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18 e19.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::e19::l')) ∧
         ((LENGTH l = 18) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18]) ∧
         ((18 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17; e18]) ∧
         (17 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (LENGTH l > 17 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (18 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (LENGTH l ≥ 18 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::e18::l') ∧
         (18 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         (LENGTH l ≥ 18 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         (x + 18 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         (LENGTH l ≥ x + 18 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((LENGTH l = 18 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((18 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((LENGTH l = x + 18) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((x + 18 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
             e18.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::e18::l')) ∧
         ((LENGTH l = 17) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17]) ∧
         ((17 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16; e17]) ∧
         (16 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (LENGTH l > 16 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (17 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (LENGTH l ≥ 17 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::e17::l') ∧
         (17 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         (LENGTH l ≥ 17 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         (x + 17 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         (LENGTH l ≥ x + 17 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((LENGTH l = 17 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((17 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((LENGTH l = x + 17) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((x + 17 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::e17::l')) ∧
         ((LENGTH l = 16) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16]) ∧
         ((16 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15; e16]) ∧
         (15 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (LENGTH l > 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (16 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (LENGTH l ≥ 16 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::e16::l') ∧
         (16 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         (LENGTH l ≥ 16 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         (x + 16 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         (LENGTH l ≥ x + 16 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((LENGTH l = 16 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((16 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((LENGTH l = x + 16) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((x + 16 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::e16::l')) ∧
         ((LENGTH l = 15) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15]) ∧
         ((15 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14;
             e15]) ∧
         (14 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (LENGTH l > 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (15 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (LENGTH l ≥ 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                e15::l') ∧
         (15 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (LENGTH l ≥ 15 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (x + 15 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         (LENGTH l ≥ x + 15 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = 15 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((15 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = x + 15) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((x + 15 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 e15::l')) ∧
         ((LENGTH l = 14) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13;
             e14]) ∧
         ((14 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13;
             e14]) ∧
         (13 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (LENGTH l > 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (14 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (LENGTH l ≥ 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                l') ∧
         (14 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (LENGTH l ≥ 14 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (x + 14 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         (LENGTH l ≥ x + 14 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = 14 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((14 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = x + 14) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((x + 14 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::e14::
                 l')) ∧
         ((LENGTH l = 13) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13]) ∧
         ((13 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13]) ∧
         (12 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (LENGTH l > 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (13 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (LENGTH l ≥ 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            l =
            e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l') ∧
         (13 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (LENGTH l ≥ 13 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (x + 13 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         (LENGTH l ≥ x + 13 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            x ≤ LENGTH l' ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = 13 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((13 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = x + 13) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((x + 13 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
            (LENGTH l' = x) ∧
            (l =
             e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::e13::l')) ∧
         ((LENGTH l = 12) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12]) ∧
         ((12 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12]) ∧
         (11 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (LENGTH l > 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (12 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (LENGTH l ≥ 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l') ∧
         (12 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (LENGTH l ≥ 12 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (x + 12 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         (LENGTH l ≥ x + 12 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = 12 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((12 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = x + 12) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((x + 12 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::e12::l')) ∧
         ((LENGTH l = 11) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11]) ∧
         ((11 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11]) ∧
         (10 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (LENGTH l > 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (11 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (LENGTH l ≥ 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l') ∧
         (11 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (LENGTH l ≥ 11 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (x + 11 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         (LENGTH l ≥ x + 11 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = 11 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((11 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = x + 11) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((x + 11 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::e11::l')) ∧
         ((LENGTH l = 10) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         ((10 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10]) ∧
         (9 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l > 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (LENGTH l ≥ 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l') ∧
         (10 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ 10 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (x + 10 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         (LENGTH l ≥ x + 10 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            x ≤ LENGTH l' ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 10 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((10 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = x + 10) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((x + 10 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::e10::l')) ∧
         ((LENGTH l = 9) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         ((9 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = [e1; e2; e3; e4; e5; e6; e7; e8; e9]) ∧
         (8 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l > 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (LENGTH l ≥ 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l') ∧
         (9 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ 9 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (x + 9 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         (LENGTH l ≥ x + 9 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 9 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((9 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = x + 9) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((x + 9 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8 e9.
            (LENGTH l' = x) ∧
            (l = e1::e2::e3::e4::e5::e6::e7::e8::e9::l')) ∧
         ((LENGTH l = 8) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         ((8 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7 e8. l = [e1; e2; e3; e4; e5; e6; e7; e8]) ∧
         (7 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l > 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (LENGTH l ≥ 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            l = e1::e2::e3::e4::e5::e6::e7::e8::l') ∧
         (8 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ 8 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (x + 8 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         (LENGTH l ≥ x + 8 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 8 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((8 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = x + 8) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((x + 8 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7 e8.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::e8::l')) ∧
         ((LENGTH l = 7) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         ((7 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         (6 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l > 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l ≥ 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ 7 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (x + 7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ x + 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 7 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((7 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = x + 7) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((x + 7 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 6) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         ((6 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         (5 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l > 5 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l ≥ 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ 6 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (x + 6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ x + 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 6 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((6 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = x + 6) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((x + 6 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 5) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         ((5 = LENGTH l) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         (4 < LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l > 4 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l ≥ 5 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ 5 + x ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (x + 5 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ x + 5 ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 5 + x) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((5 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = x + 5) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((x + 5 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 4) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         ((4 = LENGTH l) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         (3 < LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l > 3 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l ≥ 4 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ 4 + x ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (x + 4 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ x + 4 ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 4 + x) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((4 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = x + 4) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((x + 4 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_3]  Theorem

      |- ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_4]  Theorem

      |- ((LENGTH l = 4) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         ((4 = LENGTH l) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         (3 < LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l > 3 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l ≥ 4 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ 4 + x ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (x + 4 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ x + 4 ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 4 + x) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((4 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = x + 4) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((x + 4 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_5]  Theorem

      |- ((LENGTH l = 5) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         ((5 = LENGTH l) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         (4 < LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l > 4 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l ≥ 5 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ 5 + x ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (x + 5 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ x + 5 ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 5 + x) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((5 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = x + 5) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((x + 5 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 4) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         ((4 = LENGTH l) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         (3 < LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l > 3 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l ≥ 4 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ 4 + x ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (x + 4 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ x + 4 ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 4 + x) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((4 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = x + 4) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((x + 4 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_7]  Theorem

      |- ((LENGTH l = 7) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         ((7 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6 e7. l = [e1; e2; e3; e4; e5; e6; e7]) ∧
         (6 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l > 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (LENGTH l ≥ 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7. l = e1::e2::e3::e4::e5::e6::e7::l') ∧
         (7 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ 7 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (x + 7 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         (LENGTH l ≥ x + 7 ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 7 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((7 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = x + 7) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((x + 7 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6 e7.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::e7::l')) ∧
         ((LENGTH l = 6) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         ((6 = LENGTH l) ⇔
          ∃e1 e2 e3 e4 e5 e6. l = [e1; e2; e3; e4; e5; e6]) ∧
         (5 < LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l > 5 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (LENGTH l ≥ 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6. l = e1::e2::e3::e4::e5::e6::l') ∧
         (6 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ 6 + x ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (x + 6 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         (LENGTH l ≥ x + 6 ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 6 + x) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((6 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = x + 6) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((x + 6 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5 e6.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::e6::l')) ∧
         ((LENGTH l = 5) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         ((5 = LENGTH l) ⇔ ∃e1 e2 e3 e4 e5. l = [e1; e2; e3; e4; e5]) ∧
         (4 < LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l > 4 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (LENGTH l ≥ 5 ⇔ ∃l' e1 e2 e3 e4 e5. l = e1::e2::e3::e4::e5::l') ∧
         (5 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ 5 + x ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (x + 5 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         (LENGTH l ≥ x + 5 ⇔
          ∃l' e1 e2 e3 e4 e5.
            x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 5 + x) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((5 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = x + 5) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((x + 5 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4 e5.
            (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::e5::l')) ∧
         ((LENGTH l = 4) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         ((4 = LENGTH l) ⇔ ∃e1 e2 e3 e4. l = [e1; e2; e3; e4]) ∧
         (3 < LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l > 3 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 ≤ LENGTH l ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (LENGTH l ≥ 4 ⇔ ∃l' e1 e2 e3 e4. l = e1::e2::e3::e4::l') ∧
         (4 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ 4 + x ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (x + 4 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         (LENGTH l ≥ x + 4 ⇔
          ∃l' e1 e2 e3 e4. x ≤ LENGTH l' ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 4 + x) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((4 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = x + 4) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((x + 4 = LENGTH l) ⇔
          ∃l' e1 e2 e3 e4. (LENGTH l' = x) ∧ (l = e1::e2::e3::e4::l')) ∧
         ((LENGTH l = 3) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         ((3 = LENGTH l) ⇔ ∃e1 e2 e3. l = [e1; e2; e3]) ∧
         (2 < LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l > 2 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 ≤ LENGTH l ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (LENGTH l ≥ 3 ⇔ ∃l' e1 e2 e3. l = e1::e2::e3::l') ∧
         (3 + x ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ 3 + x ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (x + 3 ≤ LENGTH l ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         (LENGTH l ≥ x + 3 ⇔
          ∃l' e1 e2 e3. x ≤ LENGTH l' ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 3 + x) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((3 + x = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = x + 3) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((x + 3 = LENGTH l) ⇔
          ∃l' e1 e2 e3. (LENGTH l' = x) ∧ (l = e1::e2::e3::l')) ∧
         ((LENGTH l = 2) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         ((2 = LENGTH l) ⇔ ∃e1 e2. l = [e1; e2]) ∧
         (1 < LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l > 1 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 ≤ LENGTH l ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (LENGTH l ≥ 2 ⇔ ∃l' e1 e2. l = e1::e2::l') ∧
         (2 + x ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ 2 + x ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (x + 2 ≤ LENGTH l ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         (LENGTH l ≥ x + 2 ⇔ ∃l' e1 e2. x ≤ LENGTH l' ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 2 + x) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((2 + x = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = x + 2) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((x + 2 = LENGTH l) ⇔
          ∃l' e1 e2. (LENGTH l' = x) ∧ (l = e1::e2::l')) ∧
         ((LENGTH l = 1) ⇔ ∃e1. l = [e1]) ∧
         ((1 = LENGTH l) ⇔ ∃e1. l = [e1]) ∧
         (0 < LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l > 0 ⇔ ∃l' e1. l = e1::l') ∧
         (1 ≤ LENGTH l ⇔ ∃l' e1. l = e1::l') ∧
         (LENGTH l ≥ 1 ⇔ ∃l' e1. l = e1::l') ∧
         (1 + x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ 1 + x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (x + 1 ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ x + 1 ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = 1 + x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((1 + x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = x + 1) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((x + 1 = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((LENGTH l = 0) ⇔ (l = [])) ∧ ((0 = LENGTH l) ⇔ (l = [])) ∧
         (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_COMPARE_1]  Theorem

      |- (LENGTH l < 1 ⇔ (l = [])) ∧ (1 > LENGTH l ⇔ (l = [])) ∧
         (0 ≥ LENGTH l ⇔ (l = [])) ∧ (LENGTH l ≤ 0 ⇔ (l = []))

   [LIST_LENGTH_COMPARE_SUC]  Theorem

      |- (SUC x ≤ LENGTH l ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         (LENGTH l ≥ SUC x ⇔ ∃l' e1. x ≤ LENGTH l' ∧ (l = e1::l')) ∧
         ((LENGTH l = SUC x) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l')) ∧
         ((SUC x = LENGTH l) ⇔ ∃l' e1. (LENGTH l' = x) ∧ (l = e1::l'))

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
