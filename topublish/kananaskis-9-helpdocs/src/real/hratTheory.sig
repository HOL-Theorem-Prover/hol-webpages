signature hratTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val hrat_1 : thm
    val hrat_ABS_def : thm
    val hrat_REP_def : thm
    val hrat_TY_DEF : thm
    val hrat_add : thm
    val hrat_bijections : thm
    val hrat_inv : thm
    val hrat_mul : thm
    val hrat_sucint : thm
    val trat_1 : thm
    val trat_add : thm
    val trat_eq : thm
    val trat_inv : thm
    val trat_mul : thm
    val trat_sucint : thm

  (*  Theorems  *)
    val HRAT_ADD_ASSOC : thm
    val HRAT_ADD_SYM : thm
    val HRAT_ADD_TOTAL : thm
    val HRAT_ARCH : thm
    val HRAT_LDISTRIB : thm
    val HRAT_MUL_ASSOC : thm
    val HRAT_MUL_LID : thm
    val HRAT_MUL_LINV : thm
    val HRAT_MUL_SYM : thm
    val HRAT_NOZERO : thm
    val HRAT_SUCINT : thm
    val TRAT_ADD_ASSOC : thm
    val TRAT_ADD_SYM : thm
    val TRAT_ADD_SYM_EQ : thm
    val TRAT_ADD_TOTAL : thm
    val TRAT_ADD_WELLDEFINED : thm
    val TRAT_ADD_WELLDEFINED2 : thm
    val TRAT_ARCH : thm
    val TRAT_EQ_AP : thm
    val TRAT_EQ_EQUIV : thm
    val TRAT_EQ_REFL : thm
    val TRAT_EQ_SYM : thm
    val TRAT_EQ_TRANS : thm
    val TRAT_INV_WELLDEFINED : thm
    val TRAT_LDISTRIB : thm
    val TRAT_MUL_ASSOC : thm
    val TRAT_MUL_LID : thm
    val TRAT_MUL_LINV : thm
    val TRAT_MUL_SYM : thm
    val TRAT_MUL_SYM_EQ : thm
    val TRAT_MUL_WELLDEFINED : thm
    val TRAT_MUL_WELLDEFINED2 : thm
    val TRAT_NOZERO : thm
    val TRAT_SUCINT : thm
    val TRAT_SUCINT_0 : thm
    val hrat_ABS_REP_CLASS : thm
    val hrat_QUOTIENT : thm

  val hrat_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [quotient_list] Parent theory of "hrat"

   [quotient_option] Parent theory of "hrat"

   [quotient_pair] Parent theory of "hrat"

   [quotient_sum] Parent theory of "hrat"

   [hrat_1]  Definition

      |- hrat_1 = hrat_ABS trat_1

   [hrat_ABS_def]  Definition

      |- ∀r. hrat_ABS r = hrat_ABS_CLASS ($trat_eq r)

   [hrat_REP_def]  Definition

      |- ∀a. hrat_REP a = $@ (hrat_REP_CLASS a)

   [hrat_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λc. ∃r. r trat_eq r ∧ (c = $trat_eq r)) rep

   [hrat_add]  Definition

      |- ∀T1 T2.
           T1 hrat_add T2 = hrat_ABS (hrat_REP T1 trat_add hrat_REP T2)

   [hrat_bijections]  Definition

      |- (∀a. hrat_ABS_CLASS (hrat_REP_CLASS a) = a) ∧
         ∀r.
           (λc. ∃r. r trat_eq r ∧ (c = $trat_eq r)) r ⇔
           (hrat_REP_CLASS (hrat_ABS_CLASS r) = r)

   [hrat_inv]  Definition

      |- ∀T1. hrat_inv T1 = hrat_ABS (trat_inv (hrat_REP T1))

   [hrat_mul]  Definition

      |- ∀T1 T2.
           T1 hrat_mul T2 = hrat_ABS (hrat_REP T1 trat_mul hrat_REP T2)

   [hrat_sucint]  Definition

      |- ∀T1. hrat_sucint T1 = hrat_ABS (trat_sucint T1)

   [trat_1]  Definition

      |- trat_1 = (0,0)

   [trat_add]  Definition

      |- ∀x y x' y'.
           (x,y) trat_add (x',y') =
           (PRE (SUC x * SUC y' + SUC x' * SUC y),PRE (SUC y * SUC y'))

   [trat_eq]  Definition

      |- ∀x y x' y'.
           (x,y) trat_eq (x',y') ⇔ (SUC x * SUC y' = SUC x' * SUC y)

   [trat_inv]  Definition

      |- ∀x y. trat_inv (x,y) = (y,x)

   [trat_mul]  Definition

      |- ∀x y x' y'.
           (x,y) trat_mul (x',y') =
           (PRE (SUC x * SUC x'),PRE (SUC y * SUC y'))

   [trat_sucint]  Definition

      |- (trat_sucint 0 = trat_1) ∧
         ∀n. trat_sucint (SUC n) = trat_sucint n trat_add trat_1

   [HRAT_ADD_ASSOC]  Theorem

      |- ∀h i j. h hrat_add (i hrat_add j) = h hrat_add i hrat_add j

   [HRAT_ADD_SYM]  Theorem

      |- ∀h i. h hrat_add i = i hrat_add h

   [HRAT_ADD_TOTAL]  Theorem

      |- ∀h i. (h = i) ∨ (∃d. h = i hrat_add d) ∨ ∃d. i = h hrat_add d

   [HRAT_ARCH]  Theorem

      |- ∀h. ∃n d. hrat_sucint n = h hrat_add d

   [HRAT_LDISTRIB]  Theorem

      |- ∀h i j.
           h hrat_mul (i hrat_add j) = h hrat_mul i hrat_add h hrat_mul j

   [HRAT_MUL_ASSOC]  Theorem

      |- ∀h i j. h hrat_mul (i hrat_mul j) = h hrat_mul i hrat_mul j

   [HRAT_MUL_LID]  Theorem

      |- ∀h. hrat_1 hrat_mul h = h

   [HRAT_MUL_LINV]  Theorem

      |- ∀h. hrat_inv h hrat_mul h = hrat_1

   [HRAT_MUL_SYM]  Theorem

      |- ∀h i. h hrat_mul i = i hrat_mul h

   [HRAT_NOZERO]  Theorem

      |- ∀h i. h hrat_add i ≠ h

   [HRAT_SUCINT]  Theorem

      |- (hrat_sucint 0 = hrat_1) ∧
         ∀n. hrat_sucint (SUC n) = hrat_sucint n hrat_add hrat_1

   [TRAT_ADD_ASSOC]  Theorem

      |- ∀h i j. h trat_add (i trat_add j) trat_eq h trat_add i trat_add j

   [TRAT_ADD_SYM]  Theorem

      |- ∀h i. h trat_add i trat_eq i trat_add h

   [TRAT_ADD_SYM_EQ]  Theorem

      |- ∀h i. h trat_add i = i trat_add h

   [TRAT_ADD_TOTAL]  Theorem

      |- ∀h i.
           h trat_eq i ∨ (∃d. h trat_eq i trat_add d) ∨
           ∃d. i trat_eq h trat_add d

   [TRAT_ADD_WELLDEFINED]  Theorem

      |- ∀p q r. p trat_eq q ⇒ p trat_add r trat_eq q trat_add r

   [TRAT_ADD_WELLDEFINED2]  Theorem

      |- ∀p1 p2 q1 q2.
           p1 trat_eq p2 ∧ q1 trat_eq q2 ⇒
           p1 trat_add q1 trat_eq p2 trat_add q2

   [TRAT_ARCH]  Theorem

      |- ∀h. ∃n d. trat_sucint n trat_eq h trat_add d

   [TRAT_EQ_AP]  Theorem

      |- ∀p q. (p = q) ⇒ p trat_eq q

   [TRAT_EQ_EQUIV]  Theorem

      |- ∀p q. p trat_eq q ⇔ ($trat_eq p = $trat_eq q)

   [TRAT_EQ_REFL]  Theorem

      |- ∀p. p trat_eq p

   [TRAT_EQ_SYM]  Theorem

      |- ∀p q. p trat_eq q ⇔ q trat_eq p

   [TRAT_EQ_TRANS]  Theorem

      |- ∀p q r. p trat_eq q ∧ q trat_eq r ⇒ p trat_eq r

   [TRAT_INV_WELLDEFINED]  Theorem

      |- ∀p q. p trat_eq q ⇒ trat_inv p trat_eq trat_inv q

   [TRAT_LDISTRIB]  Theorem

      |- ∀h i j.
           h trat_mul (i trat_add j) trat_eq
           h trat_mul i trat_add h trat_mul j

   [TRAT_MUL_ASSOC]  Theorem

      |- ∀h i j. h trat_mul (i trat_mul j) trat_eq h trat_mul i trat_mul j

   [TRAT_MUL_LID]  Theorem

      |- ∀h. trat_1 trat_mul h trat_eq h

   [TRAT_MUL_LINV]  Theorem

      |- ∀h. trat_inv h trat_mul h trat_eq trat_1

   [TRAT_MUL_SYM]  Theorem

      |- ∀h i. h trat_mul i trat_eq i trat_mul h

   [TRAT_MUL_SYM_EQ]  Theorem

      |- ∀h i. h trat_mul i = i trat_mul h

   [TRAT_MUL_WELLDEFINED]  Theorem

      |- ∀p q r. p trat_eq q ⇒ p trat_mul r trat_eq q trat_mul r

   [TRAT_MUL_WELLDEFINED2]  Theorem

      |- ∀p1 p2 q1 q2.
           p1 trat_eq p2 ∧ q1 trat_eq q2 ⇒
           p1 trat_mul q1 trat_eq p2 trat_mul q2

   [TRAT_NOZERO]  Theorem

      |- ∀h i. ¬(h trat_add i trat_eq h)

   [TRAT_SUCINT]  Theorem

      |- trat_sucint 0 trat_eq trat_1 ∧
         ∀n. trat_sucint (SUC n) trat_eq trat_sucint n trat_add trat_1

   [TRAT_SUCINT_0]  Theorem

      |- ∀n. trat_sucint n trat_eq (n,0)

   [hrat_ABS_REP_CLASS]  Theorem

      |- (∀a. hrat_ABS_CLASS (hrat_REP_CLASS a) = a) ∧
         ∀c.
           (∃r. r trat_eq r ∧ (c = $trat_eq r)) ⇔
           (hrat_REP_CLASS (hrat_ABS_CLASS c) = c)

   [hrat_QUOTIENT]  Theorem

      |- QUOTIENT $trat_eq hrat_ABS hrat_REP


*)
end
