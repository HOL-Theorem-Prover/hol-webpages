signature res_quanTheory =
sig
  type thm = Thm.thm

  (*  Theorems  *)
    val RES_ABSTRACT : thm
    val RES_ABSTRACT_EQUAL : thm
    val RES_ABSTRACT_EQUAL_EQ : thm
    val RES_ABSTRACT_IDEMPOT : thm
    val RES_DISJ_EXISTS_DIST : thm
    val RES_EXISTS : thm
    val RES_EXISTS_ALT : thm
    val RES_EXISTS_DISJ_DIST : thm
    val RES_EXISTS_EMPTY : thm
    val RES_EXISTS_EQUAL : thm
    val RES_EXISTS_NULL : thm
    val RES_EXISTS_REORDER : thm
    val RES_EXISTS_UNIQUE : thm
    val RES_EXISTS_UNIQUE_ALT : thm
    val RES_EXISTS_UNIQUE_EMPTY : thm
    val RES_EXISTS_UNIQUE_NULL : thm
    val RES_EXISTS_UNIQUE_UNIV : thm
    val RES_EXISTS_UNIV : thm
    val RES_FORALL : thm
    val RES_FORALL_CONJ_DIST : thm
    val RES_FORALL_DISJ_DIST : thm
    val RES_FORALL_EMPTY : thm
    val RES_FORALL_FORALL : thm
    val RES_FORALL_NULL : thm
    val RES_FORALL_REORDER : thm
    val RES_FORALL_UNIQUE : thm
    val RES_FORALL_UNIV : thm
    val RES_SELECT : thm
    val RES_SELECT_EMPTY : thm
    val RES_SELECT_UNIV : thm

  val res_quan_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [pred_set] Parent theory of "res_quan"

   [RES_ABSTRACT]  Theorem

      |- ∀p m x. x ∈ p ⇒ (RES_ABSTRACT p m x = m x)

   [RES_ABSTRACT_EQUAL]  Theorem

      |- ∀p m1 m2.
           (∀x. x ∈ p ⇒ (m1 x = m2 x)) ⇒
           (RES_ABSTRACT p m1 = RES_ABSTRACT p m2)

   [RES_ABSTRACT_EQUAL_EQ]  Theorem

      |- ∀p m1 m2.
           (RES_ABSTRACT p m1 = RES_ABSTRACT p m2) ⇔
           ∀x. x ∈ p ⇒ (m1 x = m2 x)

   [RES_ABSTRACT_IDEMPOT]  Theorem

      |- ∀p m. RES_ABSTRACT p (RES_ABSTRACT p m) = RES_ABSTRACT p m

   [RES_DISJ_EXISTS_DIST]  Theorem

      |- ∀P Q R. (∃i::(λi. P i ∨ Q i). R i) ⇔ (∃i::P. R i) ∨ ∃i::Q. R i

   [RES_EXISTS]  Theorem

      |- ∀P f. RES_EXISTS P f ⇔ ∃x. x ∈ P ∧ f x

   [RES_EXISTS_ALT]  Theorem

      |- ∀p m. RES_EXISTS p m ⇔ RES_SELECT p m ∈ p ∧ m (RES_SELECT p m)

   [RES_EXISTS_DISJ_DIST]  Theorem

      |- ∀P Q R. (∃i::P. Q i ∨ R i) ⇔ (∃i::P. Q i) ∨ ∃i::P. R i

   [RES_EXISTS_EMPTY]  Theorem

      |- ∀p. ¬RES_EXISTS ∅ p

   [RES_EXISTS_EQUAL]  Theorem

      |- ∀P j. (∃i:: $= j. P i) ⇔ P j

   [RES_EXISTS_NULL]  Theorem

      |- ∀p m. (∃x::p. m) ⇔ p ≠ ∅ ∧ m

   [RES_EXISTS_REORDER]  Theorem

      |- ∀P Q R. (∃(i::P) (j::Q). R i j) ⇔ ∃(j::Q) (i::P). R i j

   [RES_EXISTS_UNIQUE]  Theorem

      |- ∀P f.
           RES_EXISTS_UNIQUE P f ⇔
           (∃x::P. f x) ∧ ∀x y::P. f x ∧ f y ⇒ (x = y)

   [RES_EXISTS_UNIQUE_ALT]  Theorem

      |- ∀p m. RES_EXISTS_UNIQUE p m ⇔ ∃x::p. m x ∧ ∀y::p. m y ⇒ (y = x)

   [RES_EXISTS_UNIQUE_EMPTY]  Theorem

      |- ∀p. ¬RES_EXISTS_UNIQUE ∅ p

   [RES_EXISTS_UNIQUE_NULL]  Theorem

      |- ∀p m. (∃!x::p. m) ⇔ (∃x. p = {x}) ∧ m

   [RES_EXISTS_UNIQUE_UNIV]  Theorem

      |- ∀p. RES_EXISTS_UNIQUE pred_set$UNIV p ⇔ $?! p

   [RES_EXISTS_UNIV]  Theorem

      |- ∀p. RES_EXISTS pred_set$UNIV p ⇔ $? p

   [RES_FORALL]  Theorem

      |- ∀P f. RES_FORALL P f ⇔ ∀x. x ∈ P ⇒ f x

   [RES_FORALL_CONJ_DIST]  Theorem

      |- ∀P Q R. (∀i::P. Q i ∧ R i) ⇔ (∀i::P. Q i) ∧ ∀i::P. R i

   [RES_FORALL_DISJ_DIST]  Theorem

      |- ∀P Q R. (∀i::(λj. P j ∨ Q j). R i) ⇔ (∀i::P. R i) ∧ ∀i::Q. R i

   [RES_FORALL_EMPTY]  Theorem

      |- ∀p. RES_FORALL ∅ p

   [RES_FORALL_FORALL]  Theorem

      |- ∀P R x. (∀x (i::P). R i x) ⇔ ∀(i::P) x. R i x

   [RES_FORALL_NULL]  Theorem

      |- ∀p m. (∀x::p. m) ⇔ (p = ∅) ∨ m

   [RES_FORALL_REORDER]  Theorem

      |- ∀P Q R. (∀(i::P) (j::Q). R i j) ⇔ ∀(j::Q) (i::P). R i j

   [RES_FORALL_UNIQUE]  Theorem

      |- ∀P j. (∀i:: $= j. P i) ⇔ P j

   [RES_FORALL_UNIV]  Theorem

      |- ∀p. RES_FORALL pred_set$UNIV p ⇔ $! p

   [RES_SELECT]  Theorem

      |- ∀P f. RES_SELECT P f = @x. x ∈ P ∧ f x

   [RES_SELECT_EMPTY]  Theorem

      |- ∀p. RES_SELECT ∅ p = @x. F

   [RES_SELECT_UNIV]  Theorem

      |- ∀p. RES_SELECT pred_set$UNIV p = $@ p


*)
end
