signature operatorTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ASSOC_DEF : thm
    val COMM_DEF : thm
    val FCOMM_DEF : thm
    val LEFT_ID_DEF : thm
    val MONOID_DEF : thm
    val RIGHT_ID_DEF : thm

  (*  Theorems  *)
    val ASSOC_CONJ : thm
    val ASSOC_DISJ : thm
    val ASSOC_SYM : thm
    val FCOMM_ASSOC : thm
    val MONOID_CONJ_T : thm
    val MONOID_DISJ_F : thm

  val operator_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bool] Parent theory of "operator"

   [ASSOC_DEF]  Definition

      |- ∀f. ASSOC f ⇔ ∀x y z. f x (f y z) = f (f x y) z

   [COMM_DEF]  Definition

      |- ∀f. COMM f ⇔ ∀x y. f x y = f y x

   [FCOMM_DEF]  Definition

      |- ∀f g. FCOMM f g ⇔ ∀x y z. g x (f y z) = f (g x y) z

   [LEFT_ID_DEF]  Definition

      |- ∀f e. LEFT_ID f e ⇔ ∀x. f e x = x

   [MONOID_DEF]  Definition

      |- ∀f e. MONOID f e ⇔ ASSOC f ∧ RIGHT_ID f e ∧ LEFT_ID f e

   [RIGHT_ID_DEF]  Definition

      |- ∀f e. RIGHT_ID f e ⇔ ∀x. f x e = x

   [ASSOC_CONJ]  Theorem

      |- ASSOC $/\

   [ASSOC_DISJ]  Theorem

      |- ASSOC $\/

   [ASSOC_SYM]  Theorem

      |- ∀f. ASSOC f ⇔ ∀x y z. f (f x y) z = f x (f y z)

   [FCOMM_ASSOC]  Theorem

      |- ∀f. FCOMM f f ⇔ ASSOC f

   [MONOID_CONJ_T]  Theorem

      |- MONOID $/\ T

   [MONOID_DISJ_F]  Theorem

      |- MONOID $\/ F


*)
end
