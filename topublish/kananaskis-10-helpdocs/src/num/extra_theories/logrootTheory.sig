signature logrootTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val LOG : thm
    val ROOT : thm
    val SQRTd_def : thm
    val iSQRT0_def : thm
    val iSQRT1_def : thm
    val iSQRT2_def : thm
    val iSQRT3_def : thm

  (*  Theorems  *)
    val EXP_LE_ISO : thm
    val EXP_LT_ISO : thm
    val EXP_MUL : thm
    val LE_EXP_ISO : thm
    val LOG_1 : thm
    val LOG_ADD : thm
    val LOG_ADD1 : thm
    val LOG_BASE : thm
    val LOG_DIV : thm
    val LOG_EQ_0 : thm
    val LOG_EXP : thm
    val LOG_LE_MONO : thm
    val LOG_MOD : thm
    val LOG_MULT : thm
    val LOG_ROOT : thm
    val LOG_RWT : thm
    val LOG_UNIQUE : thm
    val LOG_add_digit : thm
    val LOG_exists : thm
    val LT_EXP_ISO : thm
    val ROOT_COMPUTE : thm
    val ROOT_DIV : thm
    val ROOT_LE_MONO : thm
    val ROOT_UNIQUE : thm
    val ROOT_exists : thm
    val numeral_root2 : thm
    val numeral_sqrt : thm

  val logroot_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [basicSize] Parent theory of "logroot"

   [while] Parent theory of "logroot"

   [LOG]  Definition

      |- ∀a n. 1 < a ∧ 0 < n ⇒ a ** LOG a n ≤ n ∧ n < a ** SUC (LOG a n)

   [ROOT]  Definition

      |- ∀r n. 0 < r ⇒ ROOT r n ** r ≤ n ∧ n < SUC (ROOT r n) ** r

   [SQRTd_def]  Definition

      |- ∀n. SQRTd n = (ROOT 2 n,n − ROOT 2 n * ROOT 2 n)

   [iSQRT0_def]  Definition

      |- ∀n.
           iSQRT0 n =
           (let p = SQRTd n in
            let d = SND p − FST p
            in
              if d = 0 then (2 * FST p,4 * SND p)
              else (SUC (2 * FST p),4 * d − 1))

   [iSQRT1_def]  Definition

      |- ∀n.
           iSQRT1 n =
           (let p = SQRTd n in
            let d = SUC (SND p) − FST p
            in
              if d = 0 then (2 * FST p,SUC (4 * SND p))
              else (SUC (2 * FST p),4 * (d − 1)))

   [iSQRT2_def]  Definition

      |- ∀n.
           iSQRT2 n =
           (let p = SQRTd n in
            let d = 2 * FST p in
            let c = SUC (2 * SND p) in
            let e = c − d
            in
              if e = 0 then (d,2 * c) else (SUC d,2 * e − 1))

   [iSQRT3_def]  Definition

      |- ∀n.
           iSQRT3 n =
           (let p = SQRTd n in
            let d = 2 * FST p in
            let c = SUC (2 * SND p) in
            let e = SUC c − d
            in
              if e = 0 then (d,SUC (2 * c)) else (SUC d,2 * (e − 1)))

   [EXP_LE_ISO]  Theorem

      |- ∀a b r. 0 < r ⇒ (a ≤ b ⇔ a ** r ≤ b ** r)

   [EXP_LT_ISO]  Theorem

      |- ∀a b r. 0 < r ⇒ (a < b ⇔ a ** r < b ** r)

   [EXP_MUL]  Theorem

      |- ∀a b c. (a ** b) ** c = a ** (b * c)

   [LE_EXP_ISO]  Theorem

      |- ∀e a b. 1 < e ⇒ (a ≤ b ⇔ e ** a ≤ e ** b)

   [LOG_1]  Theorem

      |- ∀a. 1 < a ⇒ (LOG a 1 = 0)

   [LOG_ADD]  Theorem

      |- ∀a b c. 1 < a ∧ b < a ** c ⇒ (LOG a (b + a ** c) = c)

   [LOG_ADD1]  Theorem

      |- ∀n a b.
           0 < n ∧ 1 < a ∧ 0 < b ⇒
           (LOG a (a ** SUC n * b) = SUC (LOG a (a ** n * b)))

   [LOG_BASE]  Theorem

      |- ∀a. 1 < a ⇒ (LOG a a = 1)

   [LOG_DIV]  Theorem

      |- ∀a x. 1 < a ∧ a ≤ x ⇒ (LOG a x = 1 + LOG a (x DIV a))

   [LOG_EQ_0]  Theorem

      |- ∀a b. 1 < a ∧ 0 < b ⇒ ((LOG a b = 0) ⇔ b < a)

   [LOG_EXP]  Theorem

      |- ∀n a b. 1 < a ∧ 0 < b ⇒ (LOG a (a ** n * b) = n + LOG a b)

   [LOG_LE_MONO]  Theorem

      |- ∀a x y. 1 < a ∧ 0 < x ⇒ x ≤ y ⇒ LOG a x ≤ LOG a y

   [LOG_MOD]  Theorem

      |- ∀n. 0 < n ⇒ (n = 2 ** LOG 2 n + n MOD 2 ** LOG 2 n)

   [LOG_MULT]  Theorem

      |- ∀b x. 1 < b ∧ 0 < x ⇒ (LOG b (b * x) = SUC (LOG b x))

   [LOG_ROOT]  Theorem

      |- ∀a x r. 1 < a ∧ 0 < x ∧ 0 < r ⇒ (LOG a (ROOT r x) = LOG a x DIV r)

   [LOG_RWT]  Theorem

      |- ∀m n.
           1 < m ∧ 0 < n ⇒
           (LOG m n = if n < m then 0 else SUC (LOG m (n DIV m)))

   [LOG_UNIQUE]  Theorem

      |- ∀a n p. a ** p ≤ n ∧ n < a ** SUC p ⇒ (LOG a n = p)

   [LOG_add_digit]  Theorem

      |- ∀b x y.
           1 < b ∧ 0 < y ∧ x < b ⇒ (LOG b (b * y + x) = SUC (LOG b y))

   [LOG_exists]  Theorem

      |- ∃f. ∀a n. 1 < a ∧ 0 < n ⇒ a ** f a n ≤ n ∧ n < a ** SUC (f a n)

   [LT_EXP_ISO]  Theorem

      |- ∀e a b. 1 < e ⇒ (a < b ⇔ e ** a < e ** b)

   [ROOT_COMPUTE]  Theorem

      |- ∀r n.
           0 < r ⇒
           (ROOT r 0 = 0) ∧
           (ROOT r n =
            (let x = 2 * ROOT r (n DIV 2 ** r)
             in
               if n < SUC x ** r then x else SUC x))

   [ROOT_DIV]  Theorem

      |- ∀r x y. 0 < r ∧ 0 < y ⇒ (ROOT r x DIV y = ROOT r (x DIV y ** r))

   [ROOT_LE_MONO]  Theorem

      |- ∀r x y. 0 < r ⇒ x ≤ y ⇒ ROOT r x ≤ ROOT r y

   [ROOT_UNIQUE]  Theorem

      |- ∀r n p. p ** r ≤ n ∧ n < SUC p ** r ⇒ (ROOT r n = p)

   [ROOT_exists]  Theorem

      |- ∀r n. 0 < r ⇒ ∃rt. rt ** r ≤ n ∧ n < SUC rt ** r

   [numeral_root2]  Theorem

      |- ROOT 2 (NUMERAL n) = FST (SQRTd n)

   [numeral_sqrt]  Theorem

      |- (SQRTd ZERO = (0,0)) ∧ (SQRTd (BIT1 ZERO) = (1,0)) ∧
         (SQRTd (BIT2 ZERO) = (1,1)) ∧ (SQRTd (BIT1 (BIT1 n)) = iSQRT3 n) ∧
         (SQRTd (BIT2 (BIT1 n)) = iSQRT0 (SUC n)) ∧
         (SQRTd (BIT1 (BIT2 n)) = iSQRT1 (SUC n)) ∧
         (SQRTd (BIT2 (BIT2 n)) = iSQRT2 (SUC n)) ∧
         (SQRTd (SUC (BIT1 (BIT1 n))) = iSQRT0 (SUC n)) ∧
         (SQRTd (SUC (BIT2 (BIT1 n))) = iSQRT1 (SUC n)) ∧
         (SQRTd (SUC (BIT1 (BIT2 n))) = iSQRT2 (SUC n)) ∧
         (SQRTd (SUC (BIT2 (BIT2 n))) = iSQRT3 (SUC n))


*)
end
