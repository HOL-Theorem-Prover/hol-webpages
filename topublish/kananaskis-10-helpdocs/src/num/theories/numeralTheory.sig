signature numeralTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val exactlog_def : thm
    val iBIT_cases : thm
    val iDUB : thm
    val iSQR : thm
    val iSUB_DEF : thm
    val iZ : thm
    val iiSUC : thm
    val internal_mult_def : thm
    val onecount_def : thm
    val texp_help_def : thm

  (*  Theorems  *)
    val DIV2_BIT1 : thm
    val DIVMOD_NUMERAL_CALC : thm
    val TWO_EXP_THM : thm
    val bit_induction : thm
    val bit_initiality : thm
    val divmod_POS : thm
    val enumeral_mult : thm
    val exactlog_characterisation : thm
    val iDUB_removal : thm
    val iSUB_THM : thm
    val internal_mult_characterisation : thm
    val numeral_MAX : thm
    val numeral_MIN : thm
    val numeral_add : thm
    val numeral_distrib : thm
    val numeral_div2 : thm
    val numeral_eq : thm
    val numeral_evenodd : thm
    val numeral_exp : thm
    val numeral_fact : thm
    val numeral_funpow : thm
    val numeral_iisuc : thm
    val numeral_lt : thm
    val numeral_lte : thm
    val numeral_mult : thm
    val numeral_pre : thm
    val numeral_sub : thm
    val numeral_suc : thm
    val numeral_texp_help : thm
    val onecount_characterisation : thm
    val texp_help0 : thm
    val texp_help_thm : thm

  val numeral_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [arithmetic] Parent theory of "numeral"

   [exactlog_def]  Definition

      |- (numeral$exactlog ZERO = ZERO) ∧
         (∀n. numeral$exactlog (BIT1 n) = ZERO) ∧
         ∀n.
           numeral$exactlog (BIT2 n) =
           (let x = numeral$onecount n ZERO
            in
              if x = ZERO then ZERO else BIT1 x)

   [iBIT_cases]  Definition

      |- (∀zf bf1 bf2. iBIT_cases ZERO zf bf1 bf2 = zf) ∧
         (∀n zf bf1 bf2. iBIT_cases (BIT1 n) zf bf1 bf2 = bf1 n) ∧
         ∀n zf bf1 bf2. iBIT_cases (BIT2 n) zf bf1 bf2 = bf2 n

   [iDUB]  Definition

      |- ∀x. numeral$iDUB x = x + x

   [iSQR]  Definition

      |- ∀x. numeral$iSQR x = x * x

   [iSUB_DEF]  Definition

      |- (∀b x. numeral$iSUB b ZERO x = ZERO) ∧
         (∀b n x.
            numeral$iSUB b (BIT1 n) x =
            if b then
              iBIT_cases x (BIT1 n) (λm. numeral$iDUB (numeral$iSUB T n m))
                (λm. BIT1 (numeral$iSUB F n m))
            else
              iBIT_cases x (numeral$iDUB n) (λm. BIT1 (numeral$iSUB F n m))
                (λm. numeral$iDUB (numeral$iSUB F n m))) ∧
         ∀b n x.
           numeral$iSUB b (BIT2 n) x =
           if b then
             iBIT_cases x (BIT2 n) (λm. BIT1 (numeral$iSUB T n m))
               (λm. numeral$iDUB (numeral$iSUB T n m))
           else
             iBIT_cases x (BIT1 n) (λm. numeral$iDUB (numeral$iSUB T n m))
               (λm. BIT1 (numeral$iSUB F n m))

   [iZ]  Definition

      |- ∀x. numeral$iZ x = x

   [iiSUC]  Definition

      |- ∀n. numeral$iiSUC n = SUC (SUC n)

   [internal_mult_def]  Definition

      |- internal_mult = $*

   [onecount_def]  Definition

      |- (∀x. numeral$onecount ZERO x = x) ∧
         (∀n x. numeral$onecount (BIT1 n) x = numeral$onecount n (SUC x)) ∧
         ∀n x. numeral$onecount (BIT2 n) x = ZERO

   [texp_help_def]  Definition

      |- (∀acc. numeral$texp_help 0 acc = BIT2 acc) ∧
         ∀n acc.
           numeral$texp_help (SUC n) acc = numeral$texp_help n (BIT1 acc)

   [DIV2_BIT1]  Theorem

      |- DIV2 (BIT1 x) = x

   [DIVMOD_NUMERAL_CALC]  Theorem

      |- (∀m n. m DIV BIT1 n = FST (DIVMOD (ZERO,m,BIT1 n))) ∧
         (∀m n. m DIV BIT2 n = FST (DIVMOD (ZERO,m,BIT2 n))) ∧
         (∀m n. m MOD BIT1 n = SND (DIVMOD (ZERO,m,BIT1 n))) ∧
         ∀m n. m MOD BIT2 n = SND (DIVMOD (ZERO,m,BIT2 n))

   [TWO_EXP_THM]  Theorem

      |- (2 ** 0 = 1) ∧
         (2 ** NUMERAL (BIT1 n) =
          NUMERAL (numeral$texp_help (PRE (BIT1 n)) ZERO)) ∧
         (2 ** NUMERAL (BIT2 n) =
          NUMERAL (numeral$texp_help (BIT1 n) ZERO))

   [bit_induction]  Theorem

      |- ∀P.
           P ZERO ∧ (∀n. P n ⇒ P (BIT1 n)) ∧ (∀n. P n ⇒ P (BIT2 n)) ⇒
           ∀n. P n

   [bit_initiality]  Theorem

      |- ∀zf b1f b2f.
           ∃f.
             (f ZERO = zf) ∧ (∀n. f (BIT1 n) = b1f n (f n)) ∧
             ∀n. f (BIT2 n) = b2f n (f n)

   [divmod_POS]  Theorem

      |- ∀n.
           0 < n ⇒
           (DIVMOD (a,m,n) =
            if m < n then (a,m)
            else (let q = findq (1,m,n) in DIVMOD (a + q,m − n * q,n)))

   [enumeral_mult]  Theorem

      |- (ZERO * n = ZERO) ∧ (n * ZERO = ZERO) ∧
         (BIT1 x * BIT1 y = internal_mult (BIT1 x) (BIT1 y)) ∧
         (BIT1 x * BIT2 y =
          (let n = numeral$exactlog (BIT2 y)
           in
             if ODD n then numeral$texp_help (DIV2 n) (PRE (BIT1 x))
             else internal_mult (BIT1 x) (BIT2 y))) ∧
         (BIT2 x * BIT1 y =
          (let m = numeral$exactlog (BIT2 x)
           in
             if ODD m then numeral$texp_help (DIV2 m) (PRE (BIT1 y))
             else internal_mult (BIT2 x) (BIT1 y))) ∧
         (BIT2 x * BIT2 y =
          (let m = numeral$exactlog (BIT2 x) in
           let n = numeral$exactlog (BIT2 y)
           in
             if ODD m then numeral$texp_help (DIV2 m) (PRE (BIT2 y))
             else if ODD n then numeral$texp_help (DIV2 n) (PRE (BIT2 x))
             else internal_mult (BIT2 x) (BIT2 y)))

   [exactlog_characterisation]  Theorem

      |- ∀n m. (numeral$exactlog n = BIT1 m) ⇒ (n = 2 ** (m + 1))

   [iDUB_removal]  Theorem

      |- ∀n.
           (numeral$iDUB (BIT1 n) = BIT2 (numeral$iDUB n)) ∧
           (numeral$iDUB (BIT2 n) = BIT2 (BIT1 n)) ∧
           (numeral$iDUB ZERO = ZERO)

   [iSUB_THM]  Theorem

      |- ∀b n m.
           (numeral$iSUB b ZERO x = ZERO) ∧ (numeral$iSUB T n ZERO = n) ∧
           (numeral$iSUB F (BIT1 n) ZERO = numeral$iDUB n) ∧
           (numeral$iSUB T (BIT1 n) (BIT1 m) =
            numeral$iDUB (numeral$iSUB T n m)) ∧
           (numeral$iSUB F (BIT1 n) (BIT1 m) = BIT1 (numeral$iSUB F n m)) ∧
           (numeral$iSUB T (BIT1 n) (BIT2 m) = BIT1 (numeral$iSUB F n m)) ∧
           (numeral$iSUB F (BIT1 n) (BIT2 m) =
            numeral$iDUB (numeral$iSUB F n m)) ∧
           (numeral$iSUB F (BIT2 n) ZERO = BIT1 n) ∧
           (numeral$iSUB T (BIT2 n) (BIT1 m) = BIT1 (numeral$iSUB T n m)) ∧
           (numeral$iSUB F (BIT2 n) (BIT1 m) =
            numeral$iDUB (numeral$iSUB T n m)) ∧
           (numeral$iSUB T (BIT2 n) (BIT2 m) =
            numeral$iDUB (numeral$iSUB T n m)) ∧
           (numeral$iSUB F (BIT2 n) (BIT2 m) = BIT1 (numeral$iSUB F n m))

   [internal_mult_characterisation]  Theorem

      |- ∀n m.
           (internal_mult ZERO n = ZERO) ∧ (internal_mult n ZERO = ZERO) ∧
           (internal_mult (BIT1 n) m =
            numeral$iZ (numeral$iDUB (internal_mult n m) + m)) ∧
           (internal_mult (BIT2 n) m =
            numeral$iDUB (numeral$iZ (internal_mult n m + m)))

   [numeral_MAX]  Theorem

      |- (MAX 0 x = x) ∧ (MAX x 0 = x) ∧
         (MAX (NUMERAL x) (NUMERAL y) = NUMERAL (if x < y then y else x))

   [numeral_MIN]  Theorem

      |- (MIN 0 x = 0) ∧ (MIN x 0 = 0) ∧
         (MIN (NUMERAL x) (NUMERAL y) = NUMERAL (if x < y then x else y))

   [numeral_add]  Theorem

      |- ∀n m.
           (numeral$iZ (ZERO + n) = n) ∧ (numeral$iZ (n + ZERO) = n) ∧
           (numeral$iZ (BIT1 n + BIT1 m) = BIT2 (numeral$iZ (n + m))) ∧
           (numeral$iZ (BIT1 n + BIT2 m) = BIT1 (SUC (n + m))) ∧
           (numeral$iZ (BIT2 n + BIT1 m) = BIT1 (SUC (n + m))) ∧
           (numeral$iZ (BIT2 n + BIT2 m) = BIT2 (SUC (n + m))) ∧
           (SUC (ZERO + n) = SUC n) ∧ (SUC (n + ZERO) = SUC n) ∧
           (SUC (BIT1 n + BIT1 m) = BIT1 (SUC (n + m))) ∧
           (SUC (BIT1 n + BIT2 m) = BIT2 (SUC (n + m))) ∧
           (SUC (BIT2 n + BIT1 m) = BIT2 (SUC (n + m))) ∧
           (SUC (BIT2 n + BIT2 m) = BIT1 (numeral$iiSUC (n + m))) ∧
           (numeral$iiSUC (ZERO + n) = numeral$iiSUC n) ∧
           (numeral$iiSUC (n + ZERO) = numeral$iiSUC n) ∧
           (numeral$iiSUC (BIT1 n + BIT1 m) = BIT2 (SUC (n + m))) ∧
           (numeral$iiSUC (BIT1 n + BIT2 m) =
            BIT1 (numeral$iiSUC (n + m))) ∧
           (numeral$iiSUC (BIT2 n + BIT1 m) =
            BIT1 (numeral$iiSUC (n + m))) ∧
           (numeral$iiSUC (BIT2 n + BIT2 m) = BIT2 (numeral$iiSUC (n + m)))

   [numeral_distrib]  Theorem

      |- (∀n. 0 + n = n) ∧ (∀n. n + 0 = n) ∧
         (∀n m. NUMERAL n + NUMERAL m = NUMERAL (numeral$iZ (n + m))) ∧
         (∀n. 0 * n = 0) ∧ (∀n. n * 0 = 0) ∧
         (∀n m. NUMERAL n * NUMERAL m = NUMERAL (n * m)) ∧
         (∀n. 0 − n = 0) ∧ (∀n. n − 0 = n) ∧
         (∀n m. NUMERAL n − NUMERAL m = NUMERAL (n − m)) ∧
         (∀n. 0 ** NUMERAL (BIT1 n) = 0) ∧
         (∀n. 0 ** NUMERAL (BIT2 n) = 0) ∧ (∀n. n ** 0 = 1) ∧
         (∀n m. NUMERAL n ** NUMERAL m = NUMERAL (n ** m)) ∧ (SUC 0 = 1) ∧
         (∀n. SUC (NUMERAL n) = NUMERAL (SUC n)) ∧ (PRE 0 = 0) ∧
         (∀n. PRE (NUMERAL n) = NUMERAL (PRE n)) ∧
         (∀n. (NUMERAL n = 0) ⇔ (n = ZERO)) ∧
         (∀n. (0 = NUMERAL n) ⇔ (n = ZERO)) ∧
         (∀n m. (NUMERAL n = NUMERAL m) ⇔ (n = m)) ∧ (∀n. n < 0 ⇔ F) ∧
         (∀n. 0 < NUMERAL n ⇔ ZERO < n) ∧
         (∀n m. NUMERAL n < NUMERAL m ⇔ n < m) ∧ (∀n. 0 > n ⇔ F) ∧
         (∀n. NUMERAL n > 0 ⇔ ZERO < n) ∧
         (∀n m. NUMERAL n > NUMERAL m ⇔ m < n) ∧ (∀n. 0 ≤ n ⇔ T) ∧
         (∀n. NUMERAL n ≤ 0 ⇔ n ≤ ZERO) ∧
         (∀n m. NUMERAL n ≤ NUMERAL m ⇔ n ≤ m) ∧ (∀n. n ≥ 0 ⇔ T) ∧
         (∀n. 0 ≥ n ⇔ (n = 0)) ∧ (∀n m. NUMERAL n ≥ NUMERAL m ⇔ m ≤ n) ∧
         (∀n. ODD (NUMERAL n) ⇔ ODD n) ∧ (∀n. EVEN (NUMERAL n) ⇔ EVEN n) ∧
         ¬ODD 0 ∧ EVEN 0

   [numeral_div2]  Theorem

      |- (DIV2 0 = 0) ∧ (∀n. DIV2 (NUMERAL (BIT1 n)) = NUMERAL n) ∧
         ∀n. DIV2 (NUMERAL (BIT2 n)) = NUMERAL (SUC n)

   [numeral_eq]  Theorem

      |- ∀n m.
           ((ZERO = BIT1 n) ⇔ F) ∧ ((BIT1 n = ZERO) ⇔ F) ∧
           ((ZERO = BIT2 n) ⇔ F) ∧ ((BIT2 n = ZERO) ⇔ F) ∧
           ((BIT1 n = BIT2 m) ⇔ F) ∧ ((BIT2 n = BIT1 m) ⇔ F) ∧
           ((BIT1 n = BIT1 m) ⇔ (n = m)) ∧ ((BIT2 n = BIT2 m) ⇔ (n = m))

   [numeral_evenodd]  Theorem

      |- ∀n.
           EVEN ZERO ∧ EVEN (BIT2 n) ∧ ¬EVEN (BIT1 n) ∧ ¬ODD ZERO ∧
           ¬ODD (BIT2 n) ∧ ODD (BIT1 n)

   [numeral_exp]  Theorem

      |- (∀n. n ** ZERO = BIT1 ZERO) ∧
         (∀n m. n ** BIT1 m = n * numeral$iSQR (n ** m)) ∧
         ∀n m. n ** BIT2 m = numeral$iSQR n * numeral$iSQR (n ** m)

   [numeral_fact]  Theorem

      |- (FACT 0 = 1) ∧
         (∀n.
            FACT (NUMERAL (BIT1 n)) =
            NUMERAL (BIT1 n) * FACT (PRE (NUMERAL (BIT1 n)))) ∧
         ∀n.
           FACT (NUMERAL (BIT2 n)) =
           NUMERAL (BIT2 n) * FACT (NUMERAL (BIT1 n))

   [numeral_funpow]  Theorem

      |- (FUNPOW f 0 x = x) ∧
         (FUNPOW f (NUMERAL (BIT1 n)) x =
          FUNPOW f (PRE (NUMERAL (BIT1 n))) (f x)) ∧
         (FUNPOW f (NUMERAL (BIT2 n)) x =
          FUNPOW f (NUMERAL (BIT1 n)) (f x))

   [numeral_iisuc]  Theorem

      |- (numeral$iiSUC ZERO = BIT2 ZERO) ∧
         (numeral$iiSUC (BIT1 n) = BIT1 (SUC n)) ∧
         (numeral$iiSUC (BIT2 n) = BIT2 (SUC n))

   [numeral_lt]  Theorem

      |- ∀n m.
           (ZERO < BIT1 n ⇔ T) ∧ (ZERO < BIT2 n ⇔ T) ∧ (n < ZERO ⇔ F) ∧
           (BIT1 n < BIT1 m ⇔ n < m) ∧ (BIT2 n < BIT2 m ⇔ n < m) ∧
           (BIT1 n < BIT2 m ⇔ ¬(m < n)) ∧ (BIT2 n < BIT1 m ⇔ n < m)

   [numeral_lte]  Theorem

      |- ∀n m.
           (ZERO ≤ n ⇔ T) ∧ (BIT1 n ≤ ZERO ⇔ F) ∧ (BIT2 n ≤ ZERO ⇔ F) ∧
           (BIT1 n ≤ BIT1 m ⇔ n ≤ m) ∧ (BIT1 n ≤ BIT2 m ⇔ n ≤ m) ∧
           (BIT2 n ≤ BIT1 m ⇔ ¬(m ≤ n)) ∧ (BIT2 n ≤ BIT2 m ⇔ n ≤ m)

   [numeral_mult]  Theorem

      |- ∀n m.
           (ZERO * n = ZERO) ∧ (n * ZERO = ZERO) ∧
           (BIT1 n * m = numeral$iZ (numeral$iDUB (n * m) + m)) ∧
           (BIT2 n * m = numeral$iDUB (numeral$iZ (n * m + m)))

   [numeral_pre]  Theorem

      |- (PRE ZERO = ZERO) ∧ (PRE (BIT1 ZERO) = ZERO) ∧
         (∀n. PRE (BIT1 (BIT1 n)) = BIT2 (PRE (BIT1 n))) ∧
         (∀n. PRE (BIT1 (BIT2 n)) = BIT2 (BIT1 n)) ∧
         ∀n. PRE (BIT2 n) = BIT1 n

   [numeral_sub]  Theorem

      |- ∀n m.
           NUMERAL (n − m) =
           if m < n then NUMERAL (numeral$iSUB T n m) else 0

   [numeral_suc]  Theorem

      |- (SUC ZERO = BIT1 ZERO) ∧ (∀n. SUC (BIT1 n) = BIT2 n) ∧
         ∀n. SUC (BIT2 n) = BIT1 (SUC n)

   [numeral_texp_help]  Theorem

      |- (numeral$texp_help ZERO acc = BIT2 acc) ∧
         (numeral$texp_help (BIT1 n) acc =
          numeral$texp_help (PRE (BIT1 n)) (BIT1 acc)) ∧
         (numeral$texp_help (BIT2 n) acc =
          numeral$texp_help (BIT1 n) (BIT1 acc))

   [onecount_characterisation]  Theorem

      |- ∀n a.
           0 < numeral$onecount n a ∧ 0 < n ⇒
           (n = 2 ** (numeral$onecount n a − a) − 1)

   [texp_help0]  Theorem

      |- numeral$texp_help n 0 = 2 ** (n + 1)

   [texp_help_thm]  Theorem

      |- ∀n a. numeral$texp_help n a = (a + 1) * 2 ** (n + 1)


*)
end
