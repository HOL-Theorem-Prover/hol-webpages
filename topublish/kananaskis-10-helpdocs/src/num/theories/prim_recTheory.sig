signature prim_recTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val LESS_DEF : thm
    val PRE_DEF : thm
    val PRIM_REC : thm
    val PRIM_REC_FUN : thm
    val SIMP_REC : thm
    val SIMP_REC_REL : thm
    val measure_def : thm
    val wellfounded_def : thm

  (*  Theorems  *)
    val DC : thm
    val EQ_LESS : thm
    val INV_SUC_EQ : thm
    val LESS_0 : thm
    val LESS_0_0 : thm
    val LESS_LEMMA1 : thm
    val LESS_LEMMA2 : thm
    val LESS_MONO : thm
    val LESS_NOT_EQ : thm
    val LESS_REFL : thm
    val LESS_SUC : thm
    val LESS_SUC_IMP : thm
    val LESS_SUC_REFL : thm
    val LESS_SUC_SUC : thm
    val LESS_THM : thm
    val NOT_LESS_0 : thm
    val NOT_LESS_EQ : thm
    val PRE : thm
    val PRIM_REC_EQN : thm
    val PRIM_REC_THM : thm
    val SIMP_REC_EXISTS : thm
    val SIMP_REC_REL_UNIQUE : thm
    val SIMP_REC_REL_UNIQUE_RESULT : thm
    val SIMP_REC_THM : thm
    val SUC_ID : thm
    val SUC_LESS : thm
    val WF_IFF_WELLFOUNDED : thm
    val WF_LESS : thm
    val WF_PRED : thm
    val WF_measure : thm
    val measure_thm : thm
    val num_Axiom : thm
    val num_Axiom_old : thm

  val prim_rec_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [num] Parent theory of "prim_rec"

   [relation] Parent theory of "prim_rec"

   [LESS_DEF]  Definition

      |- ∀m n. m < n ⇔ ∃P. (∀n. P (SUC n) ⇒ P n) ∧ P m ∧ ¬P n

   [PRE_DEF]  Definition

      |- ∀m. PRE m = if m = 0 then 0 else @n. m = SUC n

   [PRIM_REC]  Definition

      |- ∀x f m. PRIM_REC x f m = PRIM_REC_FUN x f m (PRE m)

   [PRIM_REC_FUN]  Definition

      |- ∀x f.
           PRIM_REC_FUN x f = SIMP_REC (λn. x) (λfun n. f (fun (PRE n)) n)

   [SIMP_REC]  Definition

      |- ∀x f' n. ∃g. SIMP_REC_REL g x f' (SUC n) ∧ (SIMP_REC x f' n = g n)

   [SIMP_REC_REL]  Definition

      |- ∀fun x f n.
           SIMP_REC_REL fun x f n ⇔
           (fun 0 = x) ∧ ∀m. m < n ⇒ (fun (SUC m) = f (fun m))

   [measure_def]  Definition

      |- measure = inv_image $<

   [wellfounded_def]  Definition

      |- ∀R. wellfounded R ⇔ ¬∃f. ∀n. R (f (SUC n)) (f n)

   [DC]  Theorem

      |- ∀P R a.
           P a ∧ (∀x. P x ⇒ ∃y. P y ∧ R x y) ⇒
           ∃f. (f 0 = a) ∧ ∀n. P (f n) ∧ R (f n) (f (SUC n))

   [EQ_LESS]  Theorem

      |- ∀n. (SUC m = n) ⇒ m < n

   [INV_SUC_EQ]  Theorem

      |- ∀m n. (SUC m = SUC n) ⇔ (m = n)

   [LESS_0]  Theorem

      |- ∀n. 0 < SUC n

   [LESS_0_0]  Theorem

      |- 0 < SUC 0

   [LESS_LEMMA1]  Theorem

      |- ∀m n. m < SUC n ⇒ (m = n) ∨ m < n

   [LESS_LEMMA2]  Theorem

      |- ∀m n. (m = n) ∨ m < n ⇒ m < SUC n

   [LESS_MONO]  Theorem

      |- ∀m n. m < n ⇒ SUC m < SUC n

   [LESS_NOT_EQ]  Theorem

      |- ∀m n. m < n ⇒ m ≠ n

   [LESS_REFL]  Theorem

      |- ∀n. ¬(n < n)

   [LESS_SUC]  Theorem

      |- ∀m n. m < n ⇒ m < SUC n

   [LESS_SUC_IMP]  Theorem

      |- ∀m n. m < SUC n ⇒ m ≠ n ⇒ m < n

   [LESS_SUC_REFL]  Theorem

      |- ∀n. n < SUC n

   [LESS_SUC_SUC]  Theorem

      |- ∀m. m < SUC m ∧ m < SUC (SUC m)

   [LESS_THM]  Theorem

      |- ∀m n. m < SUC n ⇔ (m = n) ∨ m < n

   [NOT_LESS_0]  Theorem

      |- ∀n. ¬(n < 0)

   [NOT_LESS_EQ]  Theorem

      |- ∀m n. (m = n) ⇒ ¬(m < n)

   [PRE]  Theorem

      |- (PRE 0 = 0) ∧ ∀m. PRE (SUC m) = m

   [PRIM_REC_EQN]  Theorem

      |- ∀x f.
           (∀n. PRIM_REC_FUN x f 0 n = x) ∧
           ∀m n.
             PRIM_REC_FUN x f (SUC m) n = f (PRIM_REC_FUN x f m (PRE n)) n

   [PRIM_REC_THM]  Theorem

      |- ∀x f.
           (PRIM_REC x f 0 = x) ∧
           ∀m. PRIM_REC x f (SUC m) = f (PRIM_REC x f m) m

   [SIMP_REC_EXISTS]  Theorem

      |- ∀x f n. ∃fun. SIMP_REC_REL fun x f n

   [SIMP_REC_REL_UNIQUE]  Theorem

      |- ∀x f g1 g2 m1 m2.
           SIMP_REC_REL g1 x f m1 ∧ SIMP_REC_REL g2 x f m2 ⇒
           ∀n. n < m1 ∧ n < m2 ⇒ (g1 n = g2 n)

   [SIMP_REC_REL_UNIQUE_RESULT]  Theorem

      |- ∀x f n. ∃!y. ∃g. SIMP_REC_REL g x f (SUC n) ∧ (y = g n)

   [SIMP_REC_THM]  Theorem

      |- ∀x f.
           (SIMP_REC x f 0 = x) ∧
           ∀m. SIMP_REC x f (SUC m) = f (SIMP_REC x f m)

   [SUC_ID]  Theorem

      |- ∀n. SUC n ≠ n

   [SUC_LESS]  Theorem

      |- ∀m n. SUC m < n ⇒ m < n

   [WF_IFF_WELLFOUNDED]  Theorem

      |- ∀R. WF R ⇔ wellfounded R

   [WF_LESS]  Theorem

      |- WF $<

   [WF_PRED]  Theorem

      |- WF (λx y. y = SUC x)

   [WF_measure]  Theorem

      |- ∀m. WF (measure m)

   [measure_thm]  Theorem

      |- ∀f x y. measure f x y ⇔ f x < f y

   [num_Axiom]  Theorem

      |- ∀e f. ∃fn. (fn 0 = e) ∧ ∀n. fn (SUC n) = f n (fn n)

   [num_Axiom_old]  Theorem

      |- ∀e f. ∃!fn1. (fn1 0 = e) ∧ ∀n. fn1 (SUC n) = f (fn1 n) n


*)
end
