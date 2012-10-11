signature real_sigmaTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val REAL_SUM_IMAGE_DEF : thm

  (*  Theorems  *)
    val NESTED_REAL_SUM_IMAGE_REVERSE : thm
    val REAL_SUM_IMAGE_0 : thm
    val REAL_SUM_IMAGE_ADD : thm
    val REAL_SUM_IMAGE_CMUL : thm
    val REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD : thm
    val REAL_SUM_IMAGE_COUNT : thm
    val REAL_SUM_IMAGE_DISJOINT_UNION : thm
    val REAL_SUM_IMAGE_EQ : thm
    val REAL_SUM_IMAGE_EQ_CARD : thm
    val REAL_SUM_IMAGE_EQ_sum : thm
    val REAL_SUM_IMAGE_FINITE_CONST : thm
    val REAL_SUM_IMAGE_FINITE_SAME : thm
    val REAL_SUM_IMAGE_IF_ELIM : thm
    val REAL_SUM_IMAGE_IMAGE : thm
    val REAL_SUM_IMAGE_INTER_ELIM : thm
    val REAL_SUM_IMAGE_INTER_NONZERO : thm
    val REAL_SUM_IMAGE_INV_CARD_EQ_1 : thm
    val REAL_SUM_IMAGE_IN_IF : thm
    val REAL_SUM_IMAGE_IN_IF_ALT : thm
    val REAL_SUM_IMAGE_MONO : thm
    val REAL_SUM_IMAGE_MONO_SET : thm
    val REAL_SUM_IMAGE_NEG : thm
    val REAL_SUM_IMAGE_NONZERO : thm
    val REAL_SUM_IMAGE_POS : thm
    val REAL_SUM_IMAGE_POS_MEM_LE : thm
    val REAL_SUM_IMAGE_POW : thm
    val REAL_SUM_IMAGE_REAL_SUM_IMAGE : thm
    val REAL_SUM_IMAGE_SING : thm
    val REAL_SUM_IMAGE_SPOS : thm
    val REAL_SUM_IMAGE_SUB : thm
    val REAL_SUM_IMAGE_THM : thm
    val SEQ_REAL_SUM_IMAGE : thm

  val real_sigma_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [poly] Parent theory of "real_sigma"

   [transc] Parent theory of "real_sigma"

   [REAL_SUM_IMAGE_DEF]  Definition

      |- ∀f s. SIGMA f s = ITSET (λe acc. f e + acc) s 0

   [NESTED_REAL_SUM_IMAGE_REVERSE]  Theorem

      |- ∀f s s'.
           FINITE s ∧ FINITE s' ⇒
           (SIGMA (λx. SIGMA (f x) s') s =
            SIGMA (λx. SIGMA (λy. f y x) s) s')

   [REAL_SUM_IMAGE_0]  Theorem

      |- ∀s. FINITE s ⇒ (SIGMA (λx. 0) s = 0)

   [REAL_SUM_IMAGE_ADD]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f f'. SIGMA (λx. f x + f' x) s = SIGMA f s + SIGMA f' s

   [REAL_SUM_IMAGE_CMUL]  Theorem

      |- ∀P. FINITE P ⇒ ∀f c. SIGMA (λx. c * f x) P = c * SIGMA f P

   [REAL_SUM_IMAGE_CONST_EQ_1_EQ_INV_CARD]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f.
             (SIGMA f P = 1) ∧ (∀x y. x ∈ P ∧ y ∈ P ⇒ (f x = f y)) ⇒
             ∀x. x ∈ P ⇒ (f x = inv (&CARD P))

   [REAL_SUM_IMAGE_COUNT]  Theorem

      |- ∀f n. SIGMA f (count n) = sum (0,n) f

   [REAL_SUM_IMAGE_DISJOINT_UNION]  Theorem

      |- ∀P P'.
           FINITE P ∧ FINITE P' ∧ DISJOINT P P' ⇒
           ∀f. SIGMA f (P ∪ P') = SIGMA f P + SIGMA f P'

   [REAL_SUM_IMAGE_EQ]  Theorem

      |- ∀s f f'.
           FINITE s ∧ (∀x. x ∈ s ⇒ (f x = f' x)) ⇒ (SIGMA f s = SIGMA f' s)

   [REAL_SUM_IMAGE_EQ_CARD]  Theorem

      |- ∀P. FINITE P ⇒ (SIGMA (λx. if x ∈ P then 1 else 0) P = &CARD P)

   [REAL_SUM_IMAGE_EQ_sum]  Theorem

      |- ∀n r. sum (0,n) r = SIGMA r (count n)

   [REAL_SUM_IMAGE_FINITE_CONST]  Theorem

      |- ∀P. FINITE P ⇒ ∀f x. (∀y. f y = x) ⇒ (SIGMA f P = &CARD P * x)

   [REAL_SUM_IMAGE_FINITE_SAME]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f p.
             p ∈ P ∧ (∀q. q ∈ P ⇒ (f p = f q)) ⇒
             (SIGMA f P = &CARD P * f p)

   [REAL_SUM_IMAGE_IF_ELIM]  Theorem

      |- ∀s P f.
           FINITE s ∧ (∀x. x ∈ s ⇒ P x) ⇒
           (SIGMA (λx. if P x then f x else 0) s = SIGMA f s)

   [REAL_SUM_IMAGE_IMAGE]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f'.
             INJ f' P (IMAGE f' P) ⇒
             ∀f. SIGMA f (IMAGE f' P) = SIGMA (f o f') P

   [REAL_SUM_IMAGE_INTER_ELIM]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f P'. (∀x. x ∉ P' ⇒ (f x = 0)) ⇒ (SIGMA f (P ∩ P') = SIGMA f P)

   [REAL_SUM_IMAGE_INTER_NONZERO]  Theorem

      |- ∀P. FINITE P ⇒ ∀f. SIGMA f (P ∩ (λp. f p ≠ 0)) = SIGMA f P

   [REAL_SUM_IMAGE_INV_CARD_EQ_1]  Theorem

      |- ∀P.
           P ≠ ∅ ∧ FINITE P ⇒
           (SIGMA (λs. if s ∈ P then inv (&CARD P) else 0) P = 1)

   [REAL_SUM_IMAGE_IN_IF]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f. SIGMA f P = SIGMA (λx. if x ∈ P then f x else 0) P

   [REAL_SUM_IMAGE_IN_IF_ALT]  Theorem

      |- ∀s f z.
           FINITE s ⇒ (SIGMA f s = SIGMA (λx. if x ∈ s then f x else z) s)

   [REAL_SUM_IMAGE_MONO]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f f'. (∀x. x ∈ P ⇒ f x ≤ f' x) ⇒ SIGMA f P ≤ SIGMA f' P

   [REAL_SUM_IMAGE_MONO_SET]  Theorem

      |- ∀f s t.
           FINITE s ∧ FINITE t ∧ s ⊆ t ∧ (∀x. x ∈ t ⇒ 0 ≤ f x) ⇒
           SIGMA f s ≤ SIGMA f t

   [REAL_SUM_IMAGE_NEG]  Theorem

      |- ∀P. FINITE P ⇒ ∀f. SIGMA (λx. -f x) P = -SIGMA f P

   [REAL_SUM_IMAGE_NONZERO]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f.
             (∀x. x ∈ P ⇒ 0 ≤ f x) ∧ (∃x. x ∈ P ∧ f x ≠ 0) ⇒
             (SIGMA f P ≠ 0 ⇔ P ≠ ∅)

   [REAL_SUM_IMAGE_POS]  Theorem

      |- ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ 0 ≤ f x) ⇒ 0 ≤ SIGMA f s

   [REAL_SUM_IMAGE_POS_MEM_LE]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f. (∀x. x ∈ P ⇒ 0 ≤ f x) ⇒ ∀x. x ∈ P ⇒ f x ≤ SIGMA f P

   [REAL_SUM_IMAGE_POW]  Theorem

      |- ∀a s.
           FINITE s ⇒ (SIGMA a s pow 2 = SIGMA (λ(i,j). a i * a j) (s × s))

   [REAL_SUM_IMAGE_REAL_SUM_IMAGE]  Theorem

      |- ∀s s' f.
           FINITE s ∧ FINITE s' ⇒
           (SIGMA (λx. SIGMA (f x) s') s =
            SIGMA (λx. f (FST x) (SND x)) (s × s'))

   [REAL_SUM_IMAGE_SING]  Theorem

      |- ∀f e. SIGMA f {e} = f e

   [REAL_SUM_IMAGE_SPOS]  Theorem

      |- ∀s. FINITE s ∧ s ≠ ∅ ⇒ ∀f. (∀x. x ∈ s ⇒ 0 < f x) ⇒ 0 < SIGMA f s

   [REAL_SUM_IMAGE_SUB]  Theorem

      |- ∀s f f'.
           FINITE s ⇒ (SIGMA (λx. f x − f' x) s = SIGMA f s − SIGMA f' s)

   [REAL_SUM_IMAGE_THM]  Theorem

      |- ∀f.
           (SIGMA f ∅ = 0) ∧
           ∀e s.
             FINITE s ⇒ (SIGMA f (e INSERT s) = f e + SIGMA f (s DELETE e))

   [SEQ_REAL_SUM_IMAGE]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f f'.
             (∀x. x ∈ s ⇒ (λn. f n x) --> f' x) ⇒
             (λn. SIGMA (f n) s) --> SIGMA f' s


*)
end
