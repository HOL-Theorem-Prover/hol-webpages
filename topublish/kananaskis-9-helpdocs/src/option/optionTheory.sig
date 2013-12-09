signature optionTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val IS_NONE_DEF : thm
    val IS_SOME_DEF : thm
    val NONE_DEF : thm
    val OPTION_BIND_def : thm
    val OPTION_CHOICE_def : thm
    val OPTION_GUARD_def : thm
    val OPTION_IGNORE_BIND_def : thm
    val OPTION_JOIN_DEF : thm
    val OPTION_MAP2_DEF : thm
    val OPTION_MAP_DEF : thm
    val OPTREL_def : thm
    val SOME_DEF : thm
    val THE_DEF : thm
    val option_REP_ABS_DEF : thm
    val option_TY_DEF : thm
    val option_case_def : thm
    val some_def : thm

  (*  Theorems  *)
    val EXISTS_OPTION : thm
    val FORALL_OPTION : thm
    val IF_EQUALS_OPTION : thm
    val IF_NONE_EQUALS_OPTION : thm
    val IS_NONE_EQ_NONE : thm
    val NOT_IS_SOME_EQ_NONE : thm
    val NOT_NONE_SOME : thm
    val NOT_SOME_NONE : thm
    val OPTION_BIND_EQUALS_OPTION : thm
    val OPTION_BIND_cong : thm
    val OPTION_CHOICE_EQ_NONE : thm
    val OPTION_GUARD_COND : thm
    val OPTION_GUARD_EQ_THM : thm
    val OPTION_JOIN_EQ_SOME : thm
    val OPTION_MAP2_NONE : thm
    val OPTION_MAP2_SOME : thm
    val OPTION_MAP2_THM : thm
    val OPTION_MAP2_cong : thm
    val OPTION_MAP_COMPOSE : thm
    val OPTION_MAP_CONG : thm
    val OPTION_MAP_EQ_NONE : thm
    val OPTION_MAP_EQ_NONE_both_ways : thm
    val OPTION_MAP_EQ_SOME : thm
    val OPTREL_MONO : thm
    val OPTREL_refl : thm
    val SOME_11 : thm
    val option_Axiom : thm
    val option_CLAUSES : thm
    val option_case_ID : thm
    val option_case_SOME_ID : thm
    val option_case_compute : thm
    val option_case_cong : thm
    val option_induction : thm
    val option_nchotomy : thm
    val some_EQ : thm
    val some_F : thm
    val some_elim : thm
    val some_intro : thm

  val option_grammars : type_grammar.grammar * term_grammar.grammar

  val option_Induct : thm
  val option_CASES : thm

(*
   [normalForms] Parent theory of "option"

   [one] Parent theory of "option"

   [sum] Parent theory of "option"

   [IS_NONE_DEF]  Definition

      |- (∀x. IS_NONE (SOME x) ⇔ F) ∧ (IS_NONE NONE ⇔ T)

   [IS_SOME_DEF]  Definition

      |- (∀x. IS_SOME (SOME x) ⇔ T) ∧ (IS_SOME NONE ⇔ F)

   [NONE_DEF]  Definition

      |- NONE = option_ABS (INR ())

   [OPTION_BIND_def]  Definition

      |- (∀f. OPTION_BIND NONE f = NONE) ∧
         ∀x f. OPTION_BIND (SOME x) f = f x

   [OPTION_CHOICE_def]  Definition

      |- (∀m2. OPTION_CHOICE NONE m2 = m2) ∧
         ∀x m2. OPTION_CHOICE (SOME x) m2 = SOME x

   [OPTION_GUARD_def]  Definition

      |- (OPTION_GUARD T = SOME ()) ∧ (OPTION_GUARD F = NONE)

   [OPTION_IGNORE_BIND_def]  Definition

      |- ∀m1 m2. OPTION_IGNORE_BIND m1 m2 = OPTION_BIND m1 (K m2)

   [OPTION_JOIN_DEF]  Definition

      |- (OPTION_JOIN NONE = NONE) ∧ ∀x. OPTION_JOIN (SOME x) = x

   [OPTION_MAP2_DEF]  Definition

      |- ∀f x y.
           OPTION_MAP2 f x y =
           if IS_SOME x ∧ IS_SOME y then SOME (f (THE x) (THE y)) else NONE

   [OPTION_MAP_DEF]  Definition

      |- (∀f x. OPTION_MAP f (SOME x) = SOME (f x)) ∧
         ∀f. OPTION_MAP f NONE = NONE

   [OPTREL_def]  Definition

      |- ∀R x y.
           OPTREL R x y ⇔
           (x = NONE) ∧ (y = NONE) ∨
           ∃x0 y0. (x = SOME x0) ∧ (y = SOME y0) ∧ R x0 y0

   [SOME_DEF]  Definition

      |- ∀x. SOME x = option_ABS (INL x)

   [THE_DEF]  Definition

      |- ∀x. THE (SOME x) = x

   [option_REP_ABS_DEF]  Definition

      |- (∀a. option_ABS (option_REP a) = a) ∧
         ∀r. (λx. T) r ⇔ (option_REP (option_ABS r) = r)

   [option_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λx. T) rep

   [option_case_def]  Definition

      |- (∀v f. option_CASE NONE v f = v) ∧
         ∀x v f. option_CASE (SOME x) v f = f x

   [some_def]  Definition

      |- ∀P. $some P = if ∃x. P x then SOME (@x. P x) else NONE

   [EXISTS_OPTION]  Theorem

      |- (∃opt. P opt) ⇔ P NONE ∨ ∃x. P (SOME x)

   [FORALL_OPTION]  Theorem

      |- (∀opt. P opt) ⇔ P NONE ∧ ∀x. P (SOME x)

   [IF_EQUALS_OPTION]  Theorem

      |- (((if P then SOME x else NONE) = NONE) ⇔ ¬P) ∧
         (((if P then NONE else SOME x) = NONE) ⇔ P) ∧
         (((if P then SOME x else NONE) = SOME y) ⇔ P ∧ (x = y)) ∧
         (((if P then NONE else SOME x) = SOME y) ⇔ ¬P ∧ (x = y))

   [IF_NONE_EQUALS_OPTION]  Theorem

      |- (((if P then X else NONE) = NONE) ⇔ P ⇒ IS_NONE X) ∧
         (((if P then NONE else X) = NONE) ⇔ IS_SOME X ⇒ P) ∧
         (((if P then X else NONE) = SOME x) ⇔ P ∧ (X = SOME x)) ∧
         (((if P then NONE else X) = SOME x) ⇔ ¬P ∧ (X = SOME x))

   [IS_NONE_EQ_NONE]  Theorem

      |- ∀x. IS_NONE x ⇔ (x = NONE)

   [NOT_IS_SOME_EQ_NONE]  Theorem

      |- ∀x. ¬IS_SOME x ⇔ (x = NONE)

   [NOT_NONE_SOME]  Theorem

      |- ∀x. NONE ≠ SOME x

   [NOT_SOME_NONE]  Theorem

      |- ∀x. SOME x ≠ NONE

   [OPTION_BIND_EQUALS_OPTION]  Theorem

      |- ((OPTION_BIND p f = NONE) ⇔
          (p = NONE) ∨ ∃x. (p = SOME x) ∧ (f x = NONE)) ∧
         ((OPTION_BIND p f = SOME y) ⇔ ∃x. (p = SOME x) ∧ (f x = SOME y))

   [OPTION_BIND_cong]  Theorem

      |- ∀o1 o2 f1 f2.
           (o1 = o2) ∧ (∀x. (o2 = SOME x) ⇒ (f1 x = f2 x)) ⇒
           (OPTION_BIND o1 f1 = OPTION_BIND o2 f2)

   [OPTION_CHOICE_EQ_NONE]  Theorem

      |- (OPTION_CHOICE m1 m2 = NONE) ⇔ (m1 = NONE) ∧ (m2 = NONE)

   [OPTION_GUARD_COND]  Theorem

      |- OPTION_GUARD b = if b then SOME () else NONE

   [OPTION_GUARD_EQ_THM]  Theorem

      |- ((OPTION_GUARD b = SOME ()) ⇔ b) ∧ ((OPTION_GUARD b = NONE) ⇔ ¬b)

   [OPTION_JOIN_EQ_SOME]  Theorem

      |- ∀x y. (OPTION_JOIN x = SOME y) ⇔ (x = SOME (SOME y))

   [OPTION_MAP2_NONE]  Theorem

      |- (OPTION_MAP2 f o1 o2 = NONE) ⇔ (o1 = NONE) ∨ (o2 = NONE)

   [OPTION_MAP2_SOME]  Theorem

      |- (OPTION_MAP2 f o1 o2 = SOME v) ⇔
         ∃x1 x2. (o1 = SOME x1) ∧ (o2 = SOME x2) ∧ (v = f x1 x2)

   [OPTION_MAP2_THM]  Theorem

      |- (OPTION_MAP2 f (SOME x) (SOME y) = SOME (f x y)) ∧
         (OPTION_MAP2 f (SOME x) NONE = NONE) ∧
         (OPTION_MAP2 f NONE (SOME y) = NONE) ∧
         (OPTION_MAP2 f NONE NONE = NONE)

   [OPTION_MAP2_cong]  Theorem

      |- ∀x1 x2 y1 y2 f1 f2.
           (x1 = x2) ∧ (y1 = y2) ∧
           (∀x y. (x2 = SOME x) ∧ (y2 = SOME y) ⇒ (f1 x y = f2 x y)) ⇒
           (OPTION_MAP2 f1 x1 y1 = OPTION_MAP2 f2 x2 y2)

   [OPTION_MAP_COMPOSE]  Theorem

      |- OPTION_MAP f (OPTION_MAP g x) = OPTION_MAP (f o g) x

   [OPTION_MAP_CONG]  Theorem

      |- ∀opt1 opt2 f1 f2.
           (opt1 = opt2) ∧ (∀x. (opt2 = SOME x) ⇒ (f1 x = f2 x)) ⇒
           (OPTION_MAP f1 opt1 = OPTION_MAP f2 opt2)

   [OPTION_MAP_EQ_NONE]  Theorem

      |- ∀f x. (OPTION_MAP f x = NONE) ⇔ (x = NONE)

   [OPTION_MAP_EQ_NONE_both_ways]  Theorem

      |- ((OPTION_MAP f x = NONE) ⇔ (x = NONE)) ∧
         ((NONE = OPTION_MAP f x) ⇔ (x = NONE))

   [OPTION_MAP_EQ_SOME]  Theorem

      |- ∀f x y. (OPTION_MAP f x = SOME y) ⇔ ∃z. (x = SOME z) ∧ (y = f z)

   [OPTREL_MONO]  Theorem

      |- (∀x y. P x y ⇒ Q x y) ⇒ OPTREL P x y ⇒ OPTREL Q x y

   [OPTREL_refl]  Theorem

      |- (∀x. R x x) ⇒ ∀x. OPTREL R x x

   [SOME_11]  Theorem

      |- ∀x y. (SOME x = SOME y) ⇔ (x = y)

   [option_Axiom]  Theorem

      |- ∀e f. ∃fn. (fn NONE = e) ∧ ∀x. fn (SOME x) = f x

   [option_CLAUSES]  Theorem

      |- (∀x y. (SOME x = SOME y) ⇔ (x = y)) ∧ (∀x. THE (SOME x) = x) ∧
         (∀x. NONE ≠ SOME x) ∧ (∀x. SOME x ≠ NONE) ∧
         (∀x. IS_SOME (SOME x) ⇔ T) ∧ (IS_SOME NONE ⇔ F) ∧
         (∀x. IS_NONE x ⇔ (x = NONE)) ∧ (∀x. ¬IS_SOME x ⇔ (x = NONE)) ∧
         (∀x. IS_SOME x ⇒ (SOME (THE x) = x)) ∧
         (∀x. option_CASE x NONE SOME = x) ∧
         (∀x. option_CASE x x SOME = x) ∧
         (∀x. IS_NONE x ⇒ (option_CASE x e f = e)) ∧
         (∀x. IS_SOME x ⇒ (option_CASE x e f = f (THE x))) ∧
         (∀x. IS_SOME x ⇒ (option_CASE x e SOME = x)) ∧
         (∀v f. option_CASE NONE v f = v) ∧
         (∀x v f. option_CASE (SOME x) v f = f x) ∧
         (∀f x. OPTION_MAP f (SOME x) = SOME (f x)) ∧
         (∀f. OPTION_MAP f NONE = NONE) ∧ (OPTION_JOIN NONE = NONE) ∧
         ∀x. OPTION_JOIN (SOME x) = x

   [option_case_ID]  Theorem

      |- ∀x. option_CASE x NONE SOME = x

   [option_case_SOME_ID]  Theorem

      |- ∀x. option_CASE x x SOME = x

   [option_case_compute]  Theorem

      |- option_CASE x e f = if IS_SOME x then f (THE x) else e

   [option_case_cong]  Theorem

      |- ∀M M' v f.
           (M = M') ∧ ((M' = NONE) ⇒ (v = v')) ∧
           (∀x. (M' = SOME x) ⇒ (f x = f' x)) ⇒
           (option_CASE M v f = option_CASE M' v' f')

   [option_induction]  Theorem

      |- ∀P. P NONE ∧ (∀a. P (SOME a)) ⇒ ∀x. P x

   [option_nchotomy]  Theorem

      |- ∀opt. (opt = NONE) ∨ ∃x. opt = SOME x

   [some_EQ]  Theorem

      |- ((some x. x = y) = SOME y) ∧ ((some x. y = x) = SOME y)

   [some_F]  Theorem

      |- (some x. F) = NONE

   [some_elim]  Theorem

      |- Q ($some P) ⇒ (∃x. P x ∧ Q (SOME x)) ∨ (∀x. ¬P x) ∧ Q NONE

   [some_intro]  Theorem

      |- (∀x. P x ⇒ Q (SOME x)) ∧ ((∀x. ¬P x) ⇒ Q NONE) ⇒ Q ($some P)


*)
end
