signature markerTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val AC_DEF : thm
    val Abbrev_def : thm
    val Cong_def : thm
    val IfCases_def : thm
    val label_def : thm
    val stmarker_def : thm
    val unint_def : thm

  (*  Theorems  *)
    val move_left_conj : thm
    val move_left_disj : thm
    val move_right_conj : thm
    val move_right_disj : thm

  val marker_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bool] Parent theory of "marker"

   [AC_DEF]  Definition

      |- ∀b1 b2. AC b1 b2 ⇔ b1 ∧ b2

   [Abbrev_def]  Definition

      |- ∀x. Abbrev x ⇔ x

   [Cong_def]  Definition

      |- ∀x. Cong x ⇔ x

   [IfCases_def]  Definition

      |- IfCases ⇔ T

   [label_def]  Definition

      |- ∀lab argument. (lab :- argument) ⇔ argument

   [stmarker_def]  Definition

      |- ∀x. stmarker x = x

   [unint_def]  Definition

      |- ∀x. unint x = x

   [move_left_conj]  Theorem

      |- ∀p q m.
           (p ∧ stmarker m ⇔ stmarker m ∧ p) ∧
           ((stmarker m ∧ p) ∧ q ⇔ stmarker m ∧ p ∧ q) ∧
           (p ∧ stmarker m ∧ q ⇔ stmarker m ∧ p ∧ q)

   [move_left_disj]  Theorem

      |- ∀p q m.
           (p ∨ stmarker m ⇔ stmarker m ∨ p) ∧
           ((stmarker m ∨ p) ∨ q ⇔ stmarker m ∨ p ∨ q) ∧
           (p ∨ stmarker m ∨ q ⇔ stmarker m ∨ p ∨ q)

   [move_right_conj]  Theorem

      |- ∀p q m.
           (stmarker m ∧ p ⇔ p ∧ stmarker m) ∧
           (p ∧ q ∧ stmarker m ⇔ (p ∧ q) ∧ stmarker m) ∧
           ((p ∧ stmarker m) ∧ q ⇔ (p ∧ q) ∧ stmarker m)

   [move_right_disj]  Theorem

      |- ∀p q m.
           (stmarker m ∨ p ⇔ p ∨ stmarker m) ∧
           (p ∨ q ∨ stmarker m ⇔ (p ∨ q) ∨ stmarker m) ∧
           ((p ∨ stmarker m) ∨ q ⇔ (p ∨ q) ∨ stmarker m)


*)
end
