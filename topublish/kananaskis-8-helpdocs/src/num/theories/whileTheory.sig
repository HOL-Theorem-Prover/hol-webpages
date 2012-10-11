signature whileTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val HOARE_SPEC_DEF : thm
    val LEAST_DEF : thm
    val OWHILE_def : thm
    val WHILE : thm

  (*  Theorems  *)
    val FULL_LEAST_INTRO : thm
    val ITERATION : thm
    val LEAST_ELIM : thm
    val LEAST_EQ : thm
    val LEAST_EXISTS : thm
    val LEAST_EXISTS_IMP : thm
    val LEAST_INTRO : thm
    val LESS_LEAST : thm
    val OWHILE_ENDCOND : thm
    val OWHILE_EQ_NONE : thm
    val OWHILE_IND : thm
    val OWHILE_INV_IND : thm
    val OWHILE_THM : thm
    val OWHILE_WHILE : thm
    val WHILE_INDUCTION : thm
    val WHILE_RULE : thm

  val while_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [arithmetic] Parent theory of "while"

   [option] Parent theory of "while"

   [HOARE_SPEC_DEF]  Definition

      |- ∀P C Q. HOARE_SPEC P C Q ⇔ ∀s. P s ⇒ Q (C s)

   [LEAST_DEF]  Definition

      |- ∀P. $LEAST P = WHILE ($~ o P) SUC 0

   [OWHILE_def]  Definition

      |- ∀G f s.
           OWHILE G f s =
           if ∃n. ¬G (FUNPOW f n s) then
             SOME (FUNPOW f (LEAST n. ¬G (FUNPOW f n s)) s)
           else
             NONE

   [WHILE]  Definition

      |- ∀P g x. WHILE P g x = if P x then WHILE P g (g x) else x

   [FULL_LEAST_INTRO]  Theorem

      |- ∀x. P x ⇒ P ($LEAST P) ∧ $LEAST P ≤ x

   [ITERATION]  Theorem

      |- ∀P g. ∃f. ∀x. f x = if P x then x else f (g x)

   [LEAST_ELIM]  Theorem

      |- ∀Q P.
           (∃n. P n) ∧ (∀n. (∀m. m < n ⇒ ¬P m) ∧ P n ⇒ Q n) ⇒ Q ($LEAST P)

   [LEAST_EQ]  Theorem

      |- ((LEAST n. n = x) = x) ∧ ((LEAST n. x = n) = x)

   [LEAST_EXISTS]  Theorem

      |- ∀p. (∃n. p n) ⇔ p ($LEAST p) ∧ ∀n. n < $LEAST p ⇒ ¬p n

   [LEAST_EXISTS_IMP]  Theorem

      |- ∀p. (∃n. p n) ⇒ p ($LEAST p) ∧ ∀n. n < $LEAST p ⇒ ¬p n

   [LEAST_INTRO]  Theorem

      |- ∀P x. P x ⇒ P ($LEAST P)

   [LESS_LEAST]  Theorem

      |- ∀P m. m < $LEAST P ⇒ ¬P m

   [OWHILE_ENDCOND]  Theorem

      |- (OWHILE G f s = SOME s') ⇒ ¬G s'

   [OWHILE_EQ_NONE]  Theorem

      |- (OWHILE G f s = NONE) ⇔ ∀n. G (FUNPOW f n s)

   [OWHILE_IND]  Theorem

      |- ∀P G f.
           (∀s. ¬G s ⇒ P s s) ∧ (∀s1 s2. G s1 ∧ P (f s1) s2 ⇒ P s1 s2) ⇒
           ∀s1 s2. (OWHILE G f s1 = SOME s2) ⇒ P s1 s2

   [OWHILE_INV_IND]  Theorem

      |- ∀G f s.
           P s ∧ (∀x. P x ∧ G x ⇒ P (f x)) ⇒
           ∀s'. (OWHILE G f s = SOME s') ⇒ P s'

   [OWHILE_THM]  Theorem

      |- OWHILE G f s = if G s then OWHILE G f (f s) else SOME s

   [OWHILE_WHILE]  Theorem

      |- (OWHILE G f s = SOME s') ⇒ (WHILE G f s = s')

   [WHILE_INDUCTION]  Theorem

      |- ∀B C R.
           WF R ∧ (∀s. B s ⇒ R (C s) s) ⇒
           ∀P. (∀s. (B s ⇒ P (C s)) ⇒ P s) ⇒ ∀v. P v

   [WHILE_RULE]  Theorem

      |- ∀R B C.
           WF R ∧ (∀s. B s ⇒ R (C s) s) ⇒
           HOARE_SPEC (λs. P s ∧ B s) C P ⇒
           HOARE_SPEC P (WHILE B C) (λs. P s ∧ ¬B s)


*)
end
