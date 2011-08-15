signature arithmeticTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ABS_DIFF_def : thm
    val ADD : thm
    val ALT_ZERO : thm
    val BIT1 : thm
    val BIT2 : thm
    val DIV2_def : thm
    val DIVISION : thm
    val DIVMOD_DEF : thm
    val DIV_2EXP_def : thm
    val EVEN : thm
    val EXP : thm
    val FACT : thm
    val FUNPOW : thm
    val GREATER_DEF : thm
    val GREATER_OR_EQ : thm
    val LESS_OR_EQ : thm
    val MAX_DEF : thm
    val MIN_DEF : thm
    val MODEQ_DEF : thm
    val MOD_2EXP_def : thm
    val MULT : thm
    val NRC : thm
    val NUMERAL_DEF : thm
    val ODD : thm
    val SUB : thm
    val findq_def : thm
    val nat_elim__magic : thm
    val num_case_def : thm
  
  (*  Theorems  *)
    val ABS_DIFF_ADD_SAME : thm
    val ABS_DIFF_COMM : thm
    val ABS_DIFF_EQS : thm
    val ABS_DIFF_EQ_0 : thm
    val ABS_DIFF_SUMS : thm
    val ABS_DIFF_SYM : thm
    val ABS_DIFF_TRIANGLE : thm
    val ABS_DIFF_ZERO : thm
    val ADD1 : thm
    val ADD_0 : thm
    val ADD_ASSOC : thm
    val ADD_CLAUSES : thm
    val ADD_COMM : thm
    val ADD_DIV_ADD_DIV : thm
    val ADD_DIV_RWT : thm
    val ADD_EQ_0 : thm
    val ADD_EQ_1 : thm
    val ADD_EQ_SUB : thm
    val ADD_INV_0 : thm
    val ADD_INV_0_EQ : thm
    val ADD_MOD : thm
    val ADD_MODULUS : thm
    val ADD_MODULUS_LEFT : thm
    val ADD_MODULUS_RIGHT : thm
    val ADD_MONO_LESS_EQ : thm
    val ADD_SUB : thm
    val ADD_SUC : thm
    val ADD_SYM : thm
    val BOUNDED_EXISTS_THM : thm
    val BOUNDED_FORALL_THM : thm
    val CANCEL_SUB : thm
    val COMPLETE_INDUCTION : thm
    val DA : thm
    val DIVMOD_CALC : thm
    val DIVMOD_CORRECT : thm
    val DIVMOD_ID : thm
    val DIVMOD_THM : thm
    val DIV_1 : thm
    val DIV_DIV_DIV_MULT : thm
    val DIV_EQ_X : thm
    val DIV_LESS : thm
    val DIV_LESS_EQ : thm
    val DIV_LE_MONOTONE : thm
    val DIV_LE_X : thm
    val DIV_LT_X : thm
    val DIV_MOD_MOD_DIV : thm
    val DIV_MULT : thm
    val DIV_ONE : thm
    val DIV_P : thm
    val DIV_P_UNIV : thm
    val DIV_SUB : thm
    val DIV_UNIQUE : thm
    val DOUBLE_LT : thm
    val EQ_ADD_LCANCEL : thm
    val EQ_ADD_RCANCEL : thm
    val EQ_LESS_EQ : thm
    val EQ_MONO_ADD_EQ : thm
    val EQ_MULT_LCANCEL : thm
    val EVEN_ADD : thm
    val EVEN_AND_ODD : thm
    val EVEN_DOUBLE : thm
    val EVEN_EXISTS : thm
    val EVEN_EXP : thm
    val EVEN_MOD2 : thm
    val EVEN_MULT : thm
    val EVEN_ODD : thm
    val EVEN_ODD_EXISTS : thm
    val EVEN_OR_ODD : thm
    val EXISTS_GREATEST : thm
    val EXISTS_NUM : thm
    val EXP2_LT : thm
    val EXP_1 : thm
    val EXP_ADD : thm
    val EXP_ALWAYS_BIG_ENOUGH : thm
    val EXP_BASE_INJECTIVE : thm
    val EXP_BASE_LEQ_MONO_IMP : thm
    val EXP_BASE_LEQ_MONO_SUC_IMP : thm
    val EXP_BASE_LE_IFF : thm
    val EXP_BASE_LE_MONO : thm
    val EXP_BASE_LT_MONO : thm
    val EXP_BASE_MULT : thm
    val EXP_EQ_0 : thm
    val EXP_EQ_1 : thm
    val EXP_EXP_INJECTIVE : thm
    val EXP_EXP_LE_MONO : thm
    val EXP_EXP_LT_MONO : thm
    val EXP_EXP_MULT : thm
    val EXP_SUB : thm
    val EXP_SUB_NUMERAL : thm
    val FACT_LESS : thm
    val FORALL_NUM : thm
    val FORALL_NUM_THM : thm
    val FUNPOW_0 : thm
    val FUNPOW_1 : thm
    val FUNPOW_ADD : thm
    val FUNPOW_SUC : thm
    val FUN_EQ_LEMMA : thm
    val GREATER_EQ : thm
    val INV_PRE_EQ : thm
    val INV_PRE_LESS : thm
    val INV_PRE_LESS_EQ : thm
    val LE : thm
    val LEFT_ADD_DISTRIB : thm
    val LEFT_SUB_DISTRIB : thm
    val LESS_0_CASES : thm
    val LESS_ADD : thm
    val LESS_ADD_1 : thm
    val LESS_ADD_NONZERO : thm
    val LESS_ADD_SUC : thm
    val LESS_ANTISYM : thm
    val LESS_CASES : thm
    val LESS_CASES_IMP : thm
    val LESS_DIV_EQ_ZERO : thm
    val LESS_EQ : thm
    val LESS_EQUAL_ADD : thm
    val LESS_EQUAL_ANTISYM : thm
    val LESS_EQUAL_DIFF : thm
    val LESS_EQ_0 : thm
    val LESS_EQ_ADD : thm
    val LESS_EQ_ADD_EXISTS : thm
    val LESS_EQ_ADD_SUB : thm
    val LESS_EQ_ANTISYM : thm
    val LESS_EQ_CASES : thm
    val LESS_EQ_EXISTS : thm
    val LESS_EQ_IMP_LESS_SUC : thm
    val LESS_EQ_LESS_EQ_MONO : thm
    val LESS_EQ_LESS_TRANS : thm
    val LESS_EQ_MONO : thm
    val LESS_EQ_MONO_ADD_EQ : thm
    val LESS_EQ_REFL : thm
    val LESS_EQ_SUB_LESS : thm
    val LESS_EQ_SUC_REFL : thm
    val LESS_EQ_TRANS : thm
    val LESS_EXP_SUC_MONO : thm
    val LESS_IMP_LESS_ADD : thm
    val LESS_IMP_LESS_OR_EQ : thm
    val LESS_LESS_CASES : thm
    val LESS_LESS_EQ_TRANS : thm
    val LESS_LESS_SUC : thm
    val LESS_MOD : thm
    val LESS_MONO_ADD : thm
    val LESS_MONO_ADD_EQ : thm
    val LESS_MONO_ADD_INV : thm
    val LESS_MONO_EQ : thm
    val LESS_MONO_MULT : thm
    val LESS_MONO_MULT2 : thm
    val LESS_MONO_REV : thm
    val LESS_MULT2 : thm
    val LESS_MULT_MONO : thm
    val LESS_NOT_SUC : thm
    val LESS_OR : thm
    val LESS_OR_EQ_ADD : thm
    val LESS_STRONG_ADD : thm
    val LESS_SUB_ADD_LESS : thm
    val LESS_SUC_EQ_COR : thm
    val LESS_SUC_NOT : thm
    val LESS_TRANS : thm
    val LE_ADD_LCANCEL : thm
    val LE_ADD_RCANCEL : thm
    val LE_LT1 : thm
    val LE_MULT_CANCEL_LBARE : thm
    val LE_MULT_CANCEL_RBARE : thm
    val LE_MULT_LCANCEL : thm
    val LE_MULT_RCANCEL : thm
    val LE_SUB_RCANCEL : thm
    val LT_ADD_LCANCEL : thm
    val LT_ADD_RCANCEL : thm
    val LT_MULT_CANCEL_LBARE : thm
    val LT_MULT_CANCEL_RBARE : thm
    val LT_MULT_LCANCEL : thm
    val LT_MULT_RCANCEL : thm
    val LT_SUB_RCANCEL : thm
    val MAX_0 : thm
    val MAX_ASSOC : thm
    val MAX_COMM : thm
    val MAX_IDEM : thm
    val MAX_LE : thm
    val MAX_LT : thm
    val MIN_0 : thm
    val MIN_ASSOC : thm
    val MIN_COMM : thm
    val MIN_IDEM : thm
    val MIN_LE : thm
    val MIN_LT : thm
    val MIN_MAX_EQ : thm
    val MIN_MAX_LE : thm
    val MIN_MAX_LT : thm
    val MIN_MAX_PRED : thm
    val MODEQ_0 : thm
    val MODEQ_0_CONG : thm
    val MODEQ_INTRO_CONG : thm
    val MODEQ_MOD : thm
    val MODEQ_MULT_CONG : thm
    val MODEQ_NONZERO_MODEQUALITY : thm
    val MODEQ_NUMERAL : thm
    val MODEQ_PLUS_CONG : thm
    val MODEQ_REFL : thm
    val MODEQ_SYM : thm
    val MODEQ_THM : thm
    val MODEQ_TRANS : thm
    val MOD_1 : thm
    val MOD_2 : thm
    val MOD_COMMON_FACTOR : thm
    val MOD_ELIM : thm
    val MOD_EQ_0 : thm
    val MOD_EQ_0_DIVISOR : thm
    val MOD_LESS : thm
    val MOD_LESS_EQ : thm
    val MOD_LIFT_PLUS : thm
    val MOD_LIFT_PLUS_IFF : thm
    val MOD_MOD : thm
    val MOD_MULT : thm
    val MOD_MULT_MOD : thm
    val MOD_ONE : thm
    val MOD_P : thm
    val MOD_PLUS : thm
    val MOD_P_UNIV : thm
    val MOD_SUB : thm
    val MOD_SUC : thm
    val MOD_SUC_IFF : thm
    val MOD_TIMES : thm
    val MOD_TIMES2 : thm
    val MOD_TIMES_SUB : thm
    val MOD_UNIQUE : thm
    val MULT_0 : thm
    val MULT_ASSOC : thm
    val MULT_CLAUSES : thm
    val MULT_COMM : thm
    val MULT_DIV : thm
    val MULT_EQ_0 : thm
    val MULT_EQ_1 : thm
    val MULT_EQ_DIV : thm
    val MULT_EQ_ID : thm
    val MULT_EXP_MONO : thm
    val MULT_INCREASES : thm
    val MULT_LEFT_1 : thm
    val MULT_LESS_EQ_SUC : thm
    val MULT_MONO_EQ : thm
    val MULT_RIGHT_1 : thm
    val MULT_SUC : thm
    val MULT_SUC_EQ : thm
    val MULT_SYM : thm
    val NORM_0 : thm
    val NOT_EXP_0 : thm
    val NOT_GREATER : thm
    val NOT_GREATER_EQ : thm
    val NOT_LEQ : thm
    val NOT_LESS : thm
    val NOT_LESS_EQUAL : thm
    val NOT_NUM_EQ : thm
    val NOT_ODD_EQ_EVEN : thm
    val NOT_STRICTLY_DECREASING : thm
    val NOT_SUC_ADD_LESS_EQ : thm
    val NOT_SUC_LESS_EQ : thm
    val NOT_SUC_LESS_EQ_0 : thm
    val NOT_ZERO_LT_ZERO : thm
    val NRC_0 : thm
    val NRC_1 : thm
    val NRC_ADD_E : thm
    val NRC_ADD_EQN : thm
    val NRC_ADD_I : thm
    val NRC_RTC : thm
    val NRC_SUC_RECURSE_LEFT : thm
    val NUMERAL_MULT_EQ_DIV : thm
    val ODD_ADD : thm
    val ODD_DOUBLE : thm
    val ODD_EVEN : thm
    val ODD_EXISTS : thm
    val ODD_MULT : thm
    val ODD_OR_EVEN : thm
    val ONE : thm
    val ONE_LT_EXP : thm
    val ONE_LT_MULT : thm
    val ONE_LT_MULT_IMP : thm
    val ONE_MOD : thm
    val ONE_MOD_IFF : thm
    val ONE_ONE_UNBOUNDED : thm
    val OR_LESS : thm
    val PRE_ELIM_THM : thm
    val PRE_SUB : thm
    val PRE_SUB1 : thm
    val PRE_SUC_EQ : thm
    val RIGHT_ADD_DISTRIB : thm
    val RIGHT_SUB_DISTRIB : thm
    val RTC_NRC : thm
    val RTC_eq_NRC : thm
    val STRICTLY_INCREASING_ONE_ONE : thm
    val STRICTLY_INCREASING_TC : thm
    val STRICTLY_INCREASING_UNBOUNDED : thm
    val SUB_0 : thm
    val SUB_ADD : thm
    val SUB_CANCEL : thm
    val SUB_ELIM_THM : thm
    val SUB_EQUAL_0 : thm
    val SUB_EQ_0 : thm
    val SUB_EQ_EQ_0 : thm
    val SUB_LEFT_ADD : thm
    val SUB_LEFT_EQ : thm
    val SUB_LEFT_GREATER : thm
    val SUB_LEFT_GREATER_EQ : thm
    val SUB_LEFT_LESS : thm
    val SUB_LEFT_LESS_EQ : thm
    val SUB_LEFT_SUB : thm
    val SUB_LEFT_SUC : thm
    val SUB_LESS : thm
    val SUB_LESS_0 : thm
    val SUB_LESS_EQ : thm
    val SUB_LESS_EQ_ADD : thm
    val SUB_LESS_OR : thm
    val SUB_MOD : thm
    val SUB_MONO_EQ : thm
    val SUB_PLUS : thm
    val SUB_RIGHT_ADD : thm
    val SUB_RIGHT_EQ : thm
    val SUB_RIGHT_GREATER : thm
    val SUB_RIGHT_GREATER_EQ : thm
    val SUB_RIGHT_LESS : thm
    val SUB_RIGHT_LESS_EQ : thm
    val SUB_RIGHT_SUB : thm
    val SUB_SUB : thm
    val SUC_ADD_SYM : thm
    val SUC_ELIM_NUMERALS : thm
    val SUC_ELIM_THM : thm
    val SUC_MOD : thm
    val SUC_NOT : thm
    val SUC_ONE_ADD : thm
    val SUC_PRE : thm
    val SUC_SUB1 : thm
    val TC_eq_NRC : thm
    val TIMES2 : thm
    val TWO : thm
    val WOP : thm
    val X_LE_DIV : thm
    val X_LE_X_EXP : thm
    val X_LT_DIV : thm
    val X_LT_EXP_X : thm
    val X_LT_EXP_X_IFF : thm
    val X_MOD_Y_EQ_X : thm
    val ZERO_DIV : thm
    val ZERO_EXP : thm
    val ZERO_LESS_ADD : thm
    val ZERO_LESS_EQ : thm
    val ZERO_LESS_EXP : thm
    val ZERO_LESS_MULT : thm
    val ZERO_LT_EXP : thm
    val ZERO_MOD : thm
    val findq_divisor : thm
    val findq_eq_0 : thm
    val findq_thm : thm
    val num_CASES : thm
    val num_case_compute : thm
    val num_case_cong : thm
    val transitive_measure : thm
    val transitive_monotone : thm
  
  val arithmetic_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [pair] Parent theory of "arithmetic"
   
   [prim_rec] Parent theory of "arithmetic"
   
   [ABS_DIFF_def]  Definition
      
      |- ∀n m. ABS_DIFF n m = if n < m then m − n else n − m
   
   [ADD]  Definition
      
      |- (∀n. 0 + n = n) ∧ ∀m n. SUC m + n = SUC (m + n)
   
   [ALT_ZERO]  Definition
      
      |- ZERO = 0
   
   [BIT1]  Definition
      
      |- ∀n. BIT1 n = n + (n + SUC 0)
   
   [BIT2]  Definition
      
      |- ∀n. BIT2 n = n + (n + SUC (SUC 0))
   
   [DIV2_def]  Definition
      
      |- ∀n. DIV2 n = n DIV 2
   
   [DIVISION]  Definition
      
      |- ∀n. 0 < n ⇒ ∀k. (k = k DIV n * n + k MOD n) ∧ k MOD n < n
   
   [DIVMOD_DEF]  Definition
      
      |- DIVMOD =
         WFREC (measure (FST o SND))
           (λf (a,m,n).
              if n = 0 then
                (0,0)
              else if m < n then
                (a,m)
              else
                (let q = findq (1,m,n) in f (a + q,m − n * q,n)))
   
   [DIV_2EXP_def]  Definition
      
      |- ∀x n. DIV_2EXP x n = n DIV 2 ** x
   
   [EVEN]  Definition
      
      |- (EVEN 0 ⇔ T) ∧ ∀n. EVEN (SUC n) ⇔ ¬EVEN n
   
   [EXP]  Definition
      
      |- (∀m. m ** 0 = 1) ∧ ∀m n. m ** SUC n = m * m ** n
   
   [FACT]  Definition
      
      |- (FACT 0 = 1) ∧ ∀n. FACT (SUC n) = SUC n * FACT n
   
   [FUNPOW]  Definition
      
      |- (∀f x. FUNPOW f 0 x = x) ∧
         ∀f n x. FUNPOW f (SUC n) x = FUNPOW f n (f x)
   
   [GREATER_DEF]  Definition
      
      |- ∀m n. m > n ⇔ n < m
   
   [GREATER_OR_EQ]  Definition
      
      |- ∀m n. m ≥ n ⇔ m > n ∨ (m = n)
   
   [LESS_OR_EQ]  Definition
      
      |- ∀m n. m ≤ n ⇔ m < n ∨ (m = n)
   
   [MAX_DEF]  Definition
      
      |- ∀m n. MAX m n = if m < n then n else m
   
   [MIN_DEF]  Definition
      
      |- ∀m n. MIN m n = if m < n then m else n
   
   [MODEQ_DEF]  Definition
      
      |- ∀n m1 m2. MODEQ n m1 m2 ⇔ ∃a b. a * n + m1 = b * n + m2
   
   [MOD_2EXP_def]  Definition
      
      |- ∀x n. MOD_2EXP x n = n MOD 2 ** x
   
   [MULT]  Definition
      
      |- (∀n. 0 * n = 0) ∧ ∀m n. SUC m * n = m * n + n
   
   [NRC]  Definition
      
      |- (∀R x y. NRC R 0 x y ⇔ (x = y)) ∧
         ∀R n x y. NRC R (SUC n) x y ⇔ ∃z. R x z ∧ NRC R n z y
   
   [NUMERAL_DEF]  Definition
      
      |- ∀x. NUMERAL x = x
   
   [ODD]  Definition
      
      |- (ODD 0 ⇔ F) ∧ ∀n. ODD (SUC n) ⇔ ¬ODD n
   
   [SUB]  Definition
      
      |- (∀m. 0 − m = 0) ∧
         ∀m n. SUC m − n = if m < n then 0 else SUC (m − n)
   
   [findq_def]  Definition
      
      |- findq =
         WFREC (measure (λ(a,m,n). m − n))
           (λf (a,m,n).
              if n = 0 then
                a
              else
                (let d = 2 * n in if m < d then a else f (2 * a,m,d)))
   
   [nat_elim__magic]  Definition
      
      |- ∀n. &n = n
   
   [num_case_def]  Definition
      
      |- (∀b f. num_case b f 0 = b) ∧ ∀b f n. num_case b f (SUC n) = f n
   
   [ABS_DIFF_ADD_SAME]  Theorem
      
      |- ∀n m p. ABS_DIFF (n + p) (m + p) = ABS_DIFF n m
   
   [ABS_DIFF_COMM]  Theorem
      
      |- ∀n m. ABS_DIFF n m = ABS_DIFF m n
   
   [ABS_DIFF_EQS]  Theorem
      
      |- ∀n. ABS_DIFF n n = 0
   
   [ABS_DIFF_EQ_0]  Theorem
      
      |- ∀n m. (ABS_DIFF n m = 0) ⇔ (n = m)
   
   [ABS_DIFF_SUMS]  Theorem
      
      |- ∀n1 n2 m1 m2.
           ABS_DIFF (n1 + n2) (m1 + m2) ≤ ABS_DIFF n1 m1 + ABS_DIFF n2 m2
   
   [ABS_DIFF_SYM]  Theorem
      
      |- ∀n m. ABS_DIFF n m = ABS_DIFF m n
   
   [ABS_DIFF_TRIANGLE]  Theorem
      
      |- ∀x y z. ABS_DIFF x z ≤ ABS_DIFF x y + ABS_DIFF y z
   
   [ABS_DIFF_ZERO]  Theorem
      
      |- ∀n. (ABS_DIFF n 0 = n) ∧ (ABS_DIFF 0 n = n)
   
   [ADD1]  Theorem
      
      |- ∀m. SUC m = m + 1
   
   [ADD_0]  Theorem
      
      |- ∀m. m + 0 = m
   
   [ADD_ASSOC]  Theorem
      
      |- ∀m n p. m + (n + p) = m + n + p
   
   [ADD_CLAUSES]  Theorem
      
      |- (0 + m = m) ∧ (m + 0 = m) ∧ (SUC m + n = SUC (m + n)) ∧
         (m + SUC n = SUC (m + n))
   
   [ADD_COMM]  Theorem
      
      |- ∀m n. m + n = n + m
   
   [ADD_DIV_ADD_DIV]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀x r. (x * n + r) DIV n = x + r DIV n
   
   [ADD_DIV_RWT]  Theorem
      
      |- ∀n.
           0 < n ⇒
           ∀m p.
             (m MOD n = 0) ∨ (p MOD n = 0) ⇒
             ((m + p) DIV n = m DIV n + p DIV n)
   
   [ADD_EQ_0]  Theorem
      
      |- ∀m n. (m + n = 0) ⇔ (m = 0) ∧ (n = 0)
   
   [ADD_EQ_1]  Theorem
      
      |- ∀m n. (m + n = 1) ⇔ (m = 1) ∧ (n = 0) ∨ (m = 0) ∧ (n = 1)
   
   [ADD_EQ_SUB]  Theorem
      
      |- ∀m n p. n ≤ p ⇒ ((m + n = p) ⇔ (m = p − n))
   
   [ADD_INV_0]  Theorem
      
      |- ∀m n. (m + n = m) ⇒ (n = 0)
   
   [ADD_INV_0_EQ]  Theorem
      
      |- ∀m n. (m + n = m) ⇔ (n = 0)
   
   [ADD_MOD]  Theorem
      
      |- ∀n a b p.
           0 < n ⇒ (((a + p) MOD n = (b + p) MOD n) ⇔ (a MOD n = b MOD n))
   
   [ADD_MODULUS]  Theorem
      
      |- (∀n x. 0 < n ⇒ ((x + n) MOD n = x MOD n)) ∧
         ∀n x. 0 < n ⇒ ((n + x) MOD n = x MOD n)
   
   [ADD_MODULUS_LEFT]  Theorem
      
      |- ∀n x. 0 < n ⇒ ((x + n) MOD n = x MOD n)
   
   [ADD_MODULUS_RIGHT]  Theorem
      
      |- ∀n x. 0 < n ⇒ ((n + x) MOD n = x MOD n)
   
   [ADD_MONO_LESS_EQ]  Theorem
      
      |- ∀m n p. m + n ≤ m + p ⇔ n ≤ p
   
   [ADD_SUB]  Theorem
      
      |- ∀a c. a + c − c = a
   
   [ADD_SUC]  Theorem
      
      |- ∀m n. SUC (m + n) = m + SUC n
   
   [ADD_SYM]  Theorem
      
      |- ∀m n. m + n = n + m
   
   [BOUNDED_EXISTS_THM]  Theorem
      
      |- ∀c. 0 < c ⇒ ((∃n. n < c ∧ P n) ⇔ P (c − 1) ∨ ∃n. n < c − 1 ∧ P n)
   
   [BOUNDED_FORALL_THM]  Theorem
      
      |- ∀c. 0 < c ⇒ ((∀n. n < c ⇒ P n) ⇔ P (c − 1) ∧ ∀n. n < c − 1 ⇒ P n)
   
   [CANCEL_SUB]  Theorem
      
      |- ∀p n m. p ≤ n ∧ p ≤ m ⇒ ((n − p = m − p) ⇔ (n = m))
   
   [COMPLETE_INDUCTION]  Theorem
      
      |- ∀P. (∀n. (∀m. m < n ⇒ P m) ⇒ P n) ⇒ ∀n. P n
   
   [DA]  Theorem
      
      |- ∀k n. 0 < n ⇒ ∃r q. (k = q * n + r) ∧ r < n
   
   [DIVMOD_CALC]  Theorem
      
      |- (∀m n. 0 < n ⇒ (m DIV n = FST (DIVMOD (0,m,n)))) ∧
         ∀m n. 0 < n ⇒ (m MOD n = SND (DIVMOD (0,m,n)))
   
   [DIVMOD_CORRECT]  Theorem
      
      |- ∀m n a. 0 < n ⇒ (DIVMOD (a,m,n) = (a + m DIV n,m MOD n))
   
   [DIVMOD_ID]  Theorem
      
      |- ∀n. 0 < n ⇒ (n DIV n = 1) ∧ (n MOD n = 0)
   
   [DIVMOD_THM]  Theorem
      
      |- DIVMOD (a,m,n) =
         if n = 0 then
           (0,0)
         else if m < n then
           (a,m)
         else
           (let q = findq (1,m,n) in DIVMOD (a + q,m − n * q,n))
   
   [DIV_1]  Theorem
      
      |- ∀q. q DIV 1 = q
   
   [DIV_DIV_DIV_MULT]  Theorem
      
      |- ∀m n. 0 < m ∧ 0 < n ⇒ ∀x. x DIV m DIV n = x DIV (m * n)
   
   [DIV_EQ_X]  Theorem
      
      |- ∀x y z. 0 < z ⇒ ((y DIV z = x) ⇔ x * z ≤ y ∧ y < SUC x * z)
   
   [DIV_LESS]  Theorem
      
      |- ∀n d. 0 < n ∧ 1 < d ⇒ n DIV d < n
   
   [DIV_LESS_EQ]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀k. k DIV n ≤ k
   
   [DIV_LE_MONOTONE]  Theorem
      
      |- ∀n x y. 0 < n ∧ x ≤ y ⇒ x DIV n ≤ y DIV n
   
   [DIV_LE_X]  Theorem
      
      |- ∀x y z. 0 < z ⇒ (y DIV z ≤ x ⇔ y < (x + 1) * z)
   
   [DIV_LT_X]  Theorem
      
      |- ∀x y z. 0 < z ⇒ (y DIV z < x ⇔ y < x * z)
   
   [DIV_MOD_MOD_DIV]  Theorem
      
      |- ∀m n k. 0 < n ∧ 0 < k ⇒ ((m DIV n) MOD k = m MOD (n * k) DIV n)
   
   [DIV_MULT]  Theorem
      
      |- ∀n r. r < n ⇒ ∀q. (q * n + r) DIV n = q
   
   [DIV_ONE]  Theorem
      
      |- ∀q. q DIV SUC 0 = q
   
   [DIV_P]  Theorem
      
      |- ∀P p q.
           0 < q ⇒ (P (p DIV q) ⇔ ∃k r. (p = k * q + r) ∧ r < q ∧ P k)
   
   [DIV_P_UNIV]  Theorem
      
      |- ∀P m n.
           0 < n ⇒ (P (m DIV n) ⇔ ∀q r. (m = q * n + r) ∧ r < n ⇒ P q)
   
   [DIV_SUB]  Theorem
      
      |- 0 < n ∧ n * q ≤ m ⇒ ((m − n * q) DIV n = m DIV n − q)
   
   [DIV_UNIQUE]  Theorem
      
      |- ∀n k q. (∃r. (k = q * n + r) ∧ r < n) ⇒ (k DIV n = q)
   
   [DOUBLE_LT]  Theorem
      
      |- ∀p q. 2 * p + 1 < 2 * q ⇔ 2 * p < 2 * q
   
   [EQ_ADD_LCANCEL]  Theorem
      
      |- ∀m n p. (m + n = m + p) ⇔ (n = p)
   
   [EQ_ADD_RCANCEL]  Theorem
      
      |- ∀m n p. (m + p = n + p) ⇔ (m = n)
   
   [EQ_LESS_EQ]  Theorem
      
      |- ∀m n. (m = n) ⇔ m ≤ n ∧ n ≤ m
   
   [EQ_MONO_ADD_EQ]  Theorem
      
      |- ∀m n p. (m + p = n + p) ⇔ (m = n)
   
   [EQ_MULT_LCANCEL]  Theorem
      
      |- ∀m n p. (m * n = m * p) ⇔ (m = 0) ∨ (n = p)
   
   [EVEN_ADD]  Theorem
      
      |- ∀m n. EVEN (m + n) ⇔ (EVEN m ⇔ EVEN n)
   
   [EVEN_AND_ODD]  Theorem
      
      |- ∀n. ¬(EVEN n ∧ ODD n)
   
   [EVEN_DOUBLE]  Theorem
      
      |- ∀n. EVEN (2 * n)
   
   [EVEN_EXISTS]  Theorem
      
      |- ∀n. EVEN n ⇔ ∃m. n = 2 * m
   
   [EVEN_EXP]  Theorem
      
      |- ∀m n. 0 < n ∧ EVEN m ⇒ EVEN (m ** n)
   
   [EVEN_MOD2]  Theorem
      
      |- ∀x. EVEN x ⇔ (x MOD 2 = 0)
   
   [EVEN_MULT]  Theorem
      
      |- ∀m n. EVEN (m * n) ⇔ EVEN m ∨ EVEN n
   
   [EVEN_ODD]  Theorem
      
      |- ∀n. EVEN n ⇔ ¬ODD n
   
   [EVEN_ODD_EXISTS]  Theorem
      
      |- ∀n. (EVEN n ⇒ ∃m. n = 2 * m) ∧ (ODD n ⇒ ∃m. n = SUC (2 * m))
   
   [EVEN_OR_ODD]  Theorem
      
      |- ∀n. EVEN n ∨ ODD n
   
   [EXISTS_GREATEST]  Theorem
      
      |- ∀P.
           (∃x. P x) ∧ (∃x. ∀y. y > x ⇒ ¬P y) ⇔ ∃x. P x ∧ ∀y. y > x ⇒ ¬P y
   
   [EXISTS_NUM]  Theorem
      
      |- ∀P. (∃n. P n) ⇔ P 0 ∨ ∃m. P (SUC m)
   
   [EXP2_LT]  Theorem
      
      |- ∀m n. n DIV 2 < 2 ** m ⇔ n < 2 ** SUC m
   
   [EXP_1]  Theorem
      
      |- ∀n. (1 ** n = 1) ∧ (n ** 1 = n)
   
   [EXP_ADD]  Theorem
      
      |- ∀p q n. n ** (p + q) = n ** p * n ** q
   
   [EXP_ALWAYS_BIG_ENOUGH]  Theorem
      
      |- ∀b. 1 < b ⇒ ∀n. ∃m. n ≤ b ** m
   
   [EXP_BASE_INJECTIVE]  Theorem
      
      |- ∀b. 1 < b ⇒ ∀n m. (b ** n = b ** m) ⇔ (n = m)
   
   [EXP_BASE_LEQ_MONO_IMP]  Theorem
      
      |- ∀n m b. 0 < b ∧ m ≤ n ⇒ b ** m ≤ b ** n
   
   [EXP_BASE_LEQ_MONO_SUC_IMP]  Theorem
      
      |- m ≤ n ⇒ SUC b ** m ≤ SUC b ** n
   
   [EXP_BASE_LE_IFF]  Theorem
      
      |- b ** m ≤ b ** n ⇔
         (b = 0) ∧ (n = 0) ∨ (b = 0) ∧ 0 < m ∨ (b = 1) ∨ 1 < b ∧ m ≤ n
   
   [EXP_BASE_LE_MONO]  Theorem
      
      |- ∀b. 1 < b ⇒ ∀n m. b ** m ≤ b ** n ⇔ m ≤ n
   
   [EXP_BASE_LT_MONO]  Theorem
      
      |- ∀b. 1 < b ⇒ ∀n m. b ** m < b ** n ⇔ m < n
   
   [EXP_BASE_MULT]  Theorem
      
      |- ∀z x y. (x * y) ** z = x ** z * y ** z
   
   [EXP_EQ_0]  Theorem
      
      |- ∀n m. (n ** m = 0) ⇔ (n = 0) ∧ 0 < m
   
   [EXP_EQ_1]  Theorem
      
      |- ∀n m. (n ** m = 1) ⇔ (n = 1) ∨ (m = 0)
   
   [EXP_EXP_INJECTIVE]  Theorem
      
      |- ∀b1 b2 x. (b1 ** x = b2 ** x) ⇔ (x = 0) ∨ (b1 = b2)
   
   [EXP_EXP_LE_MONO]  Theorem
      
      |- ∀a b. a ** n ≤ b ** n ⇔ a ≤ b ∨ (n = 0)
   
   [EXP_EXP_LT_MONO]  Theorem
      
      |- ∀a b. a ** n < b ** n ⇔ a < b ∧ 0 < n
   
   [EXP_EXP_MULT]  Theorem
      
      |- ∀z x y. x ** (y * z) = (x ** y) ** z
   
   [EXP_SUB]  Theorem
      
      |- ∀p q n. 0 < n ∧ q ≤ p ⇒ (n ** (p − q) = n ** p DIV n ** q)
   
   [EXP_SUB_NUMERAL]  Theorem
      
      |- 0 < n ⇒
         (n ** NUMERAL (BIT1 x) DIV n = n ** (NUMERAL (BIT1 x) − 1)) ∧
         (n ** NUMERAL (BIT2 x) DIV n = n ** NUMERAL (BIT1 x))
   
   [FACT_LESS]  Theorem
      
      |- ∀n. 0 < FACT n
   
   [FORALL_NUM]  Theorem
      
      |- ∀P. (∀n. P n) ⇔ P 0 ∧ ∀n. P (SUC n)
   
   [FORALL_NUM_THM]  Theorem
      
      |- (∀n. P n) ⇔ P 0 ∧ ∀n. P n ⇒ P (SUC n)
   
   [FUNPOW_0]  Theorem
      
      |- FUNPOW f 0 x = x
   
   [FUNPOW_1]  Theorem
      
      |- FUNPOW f 1 x = f x
   
   [FUNPOW_ADD]  Theorem
      
      |- ∀m n. FUNPOW f (m + n) x = FUNPOW f m (FUNPOW f n x)
   
   [FUNPOW_SUC]  Theorem
      
      |- ∀f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
   
   [FUN_EQ_LEMMA]  Theorem
      
      |- ∀f x1 x2. f x1 ∧ ¬f x2 ⇒ x1 ≠ x2
   
   [GREATER_EQ]  Theorem
      
      |- ∀n m. n ≥ m ⇔ m ≤ n
   
   [INV_PRE_EQ]  Theorem
      
      |- ∀m n. 0 < m ∧ 0 < n ⇒ ((PRE m = PRE n) ⇔ (m = n))
   
   [INV_PRE_LESS]  Theorem
      
      |- ∀m. 0 < m ⇒ ∀n. PRE m < PRE n ⇔ m < n
   
   [INV_PRE_LESS_EQ]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀m. PRE m ≤ PRE n ⇔ m ≤ n
   
   [LE]  Theorem
      
      |- (∀n. n ≤ 0 ⇔ (n = 0)) ∧ ∀m n. m ≤ SUC n ⇔ (m = SUC n) ∨ m ≤ n
   
   [LEFT_ADD_DISTRIB]  Theorem
      
      |- ∀m n p. p * (m + n) = p * m + p * n
   
   [LEFT_SUB_DISTRIB]  Theorem
      
      |- ∀m n p. p * (m − n) = p * m − p * n
   
   [LESS_0_CASES]  Theorem
      
      |- ∀m. (0 = m) ∨ 0 < m
   
   [LESS_ADD]  Theorem
      
      |- ∀m n. n < m ⇒ ∃p. p + n = m
   
   [LESS_ADD_1]  Theorem
      
      |- ∀m n. n < m ⇒ ∃p. m = n + (p + 1)
   
   [LESS_ADD_NONZERO]  Theorem
      
      |- ∀m n. n ≠ 0 ⇒ m < m + n
   
   [LESS_ADD_SUC]  Theorem
      
      |- ∀m n. m < m + SUC n
   
   [LESS_ANTISYM]  Theorem
      
      |- ∀m n. ¬(m < n ∧ n < m)
   
   [LESS_CASES]  Theorem
      
      |- ∀m n. m < n ∨ n ≤ m
   
   [LESS_CASES_IMP]  Theorem
      
      |- ∀m n. ¬(m < n) ∧ m ≠ n ⇒ n < m
   
   [LESS_DIV_EQ_ZERO]  Theorem
      
      |- ∀r n. r < n ⇒ (r DIV n = 0)
   
   [LESS_EQ]  Theorem
      
      |- ∀m n. m < n ⇔ SUC m ≤ n
   
   [LESS_EQUAL_ADD]  Theorem
      
      |- ∀m n. m ≤ n ⇒ ∃p. n = m + p
   
   [LESS_EQUAL_ANTISYM]  Theorem
      
      |- ∀n m. n ≤ m ∧ m ≤ n ⇒ (n = m)
   
   [LESS_EQUAL_DIFF]  Theorem
      
      |- ∀m n. m ≤ n ⇒ ∃k. m = n − k
   
   [LESS_EQ_0]  Theorem
      
      |- ∀n. n ≤ 0 ⇔ (n = 0)
   
   [LESS_EQ_ADD]  Theorem
      
      |- ∀m n. m ≤ m + n
   
   [LESS_EQ_ADD_EXISTS]  Theorem
      
      |- ∀m n. n ≤ m ⇒ ∃p. p + n = m
   
   [LESS_EQ_ADD_SUB]  Theorem
      
      |- ∀c b. c ≤ b ⇒ ∀a. a + b − c = a + (b − c)
   
   [LESS_EQ_ANTISYM]  Theorem
      
      |- ∀m n. ¬(m < n ∧ n ≤ m)
   
   [LESS_EQ_CASES]  Theorem
      
      |- ∀m n. m ≤ n ∨ n ≤ m
   
   [LESS_EQ_EXISTS]  Theorem
      
      |- ∀m n. m ≤ n ⇔ ∃p. n = m + p
   
   [LESS_EQ_IMP_LESS_SUC]  Theorem
      
      |- ∀n m. n ≤ m ⇒ n < SUC m
   
   [LESS_EQ_LESS_EQ_MONO]  Theorem
      
      |- ∀m n p q. m ≤ p ∧ n ≤ q ⇒ m + n ≤ p + q
   
   [LESS_EQ_LESS_TRANS]  Theorem
      
      |- ∀m n p. m ≤ n ∧ n < p ⇒ m < p
   
   [LESS_EQ_MONO]  Theorem
      
      |- ∀n m. SUC n ≤ SUC m ⇔ n ≤ m
   
   [LESS_EQ_MONO_ADD_EQ]  Theorem
      
      |- ∀m n p. m + p ≤ n + p ⇔ m ≤ n
   
   [LESS_EQ_REFL]  Theorem
      
      |- ∀m. m ≤ m
   
   [LESS_EQ_SUB_LESS]  Theorem
      
      |- ∀a b. b ≤ a ⇒ ∀c. a − b < c ⇔ a < b + c
   
   [LESS_EQ_SUC_REFL]  Theorem
      
      |- ∀m. m ≤ SUC m
   
   [LESS_EQ_TRANS]  Theorem
      
      |- ∀m n p. m ≤ n ∧ n ≤ p ⇒ m ≤ p
   
   [LESS_EXP_SUC_MONO]  Theorem
      
      |- ∀n m. SUC (SUC m) ** n < SUC (SUC m) ** SUC n
   
   [LESS_IMP_LESS_ADD]  Theorem
      
      |- ∀n m. n < m ⇒ ∀p. n < m + p
   
   [LESS_IMP_LESS_OR_EQ]  Theorem
      
      |- ∀m n. m < n ⇒ m ≤ n
   
   [LESS_LESS_CASES]  Theorem
      
      |- ∀m n. (m = n) ∨ m < n ∨ n < m
   
   [LESS_LESS_EQ_TRANS]  Theorem
      
      |- ∀m n p. m < n ∧ n ≤ p ⇒ m < p
   
   [LESS_LESS_SUC]  Theorem
      
      |- ∀m n. ¬(m < n ∧ n < SUC m)
   
   [LESS_MOD]  Theorem
      
      |- ∀n k. k < n ⇒ (k MOD n = k)
   
   [LESS_MONO_ADD]  Theorem
      
      |- ∀m n p. m < n ⇒ m + p < n + p
   
   [LESS_MONO_ADD_EQ]  Theorem
      
      |- ∀m n p. m + p < n + p ⇔ m < n
   
   [LESS_MONO_ADD_INV]  Theorem
      
      |- ∀m n p. m + p < n + p ⇒ m < n
   
   [LESS_MONO_EQ]  Theorem
      
      |- ∀m n. SUC m < SUC n ⇔ m < n
   
   [LESS_MONO_MULT]  Theorem
      
      |- ∀m n p. m ≤ n ⇒ m * p ≤ n * p
   
   [LESS_MONO_MULT2]  Theorem
      
      |- ∀m n i j. m ≤ i ∧ n ≤ j ⇒ m * n ≤ i * j
   
   [LESS_MONO_REV]  Theorem
      
      |- ∀m n. SUC m < SUC n ⇒ m < n
   
   [LESS_MULT2]  Theorem
      
      |- ∀m n. 0 < m ∧ 0 < n ⇒ 0 < m * n
   
   [LESS_MULT_MONO]  Theorem
      
      |- ∀m i n. SUC n * m < SUC n * i ⇔ m < i
   
   [LESS_NOT_SUC]  Theorem
      
      |- ∀m n. m < n ∧ n ≠ SUC m ⇒ SUC m < n
   
   [LESS_OR]  Theorem
      
      |- ∀m n. m < n ⇒ SUC m ≤ n
   
   [LESS_OR_EQ_ADD]  Theorem
      
      |- ∀n m. n < m ∨ ∃p. n = p + m
   
   [LESS_STRONG_ADD]  Theorem
      
      |- ∀m n. n < m ⇒ ∃p. SUC p + n = m
   
   [LESS_SUB_ADD_LESS]  Theorem
      
      |- ∀n m i. i < n − m ⇒ i + m < n
   
   [LESS_SUC_EQ_COR]  Theorem
      
      |- ∀m n. m < n ∧ SUC m ≠ n ⇒ SUC m < n
   
   [LESS_SUC_NOT]  Theorem
      
      |- ∀m n. m < n ⇒ ¬(n < SUC m)
   
   [LESS_TRANS]  Theorem
      
      |- ∀m n p. m < n ∧ n < p ⇒ m < p
   
   [LE_ADD_LCANCEL]  Theorem
      
      |- ∀m n p. m + n ≤ m + p ⇔ n ≤ p
   
   [LE_ADD_RCANCEL]  Theorem
      
      |- ∀m n p. n + m ≤ p + m ⇔ n ≤ p
   
   [LE_LT1]  Theorem
      
      |- ∀x y. x ≤ y ⇔ x < y + 1
   
   [LE_MULT_CANCEL_LBARE]  Theorem
      
      |- (m ≤ m * n ⇔ (m = 0) ∨ 0 < n) ∧ (m ≤ n * m ⇔ (m = 0) ∨ 0 < n)
   
   [LE_MULT_CANCEL_RBARE]  Theorem
      
      |- (m * n ≤ m ⇔ (m = 0) ∨ n ≤ 1) ∧ (m * n ≤ n ⇔ (n = 0) ∨ m ≤ 1)
   
   [LE_MULT_LCANCEL]  Theorem
      
      |- ∀m n p. m * n ≤ m * p ⇔ (m = 0) ∨ n ≤ p
   
   [LE_MULT_RCANCEL]  Theorem
      
      |- ∀m n p. m * n ≤ p * n ⇔ (n = 0) ∨ m ≤ p
   
   [LE_SUB_RCANCEL]  Theorem
      
      |- ∀m n p. n − m ≤ p − m ⇔ n ≤ m ∨ n ≤ p
   
   [LT_ADD_LCANCEL]  Theorem
      
      |- ∀m n p. p + m < p + n ⇔ m < n
   
   [LT_ADD_RCANCEL]  Theorem
      
      |- ∀m n p. m + p < n + p ⇔ m < n
   
   [LT_MULT_CANCEL_LBARE]  Theorem
      
      |- (m < m * n ⇔ 0 < m ∧ 1 < n) ∧ (m < n * m ⇔ 0 < m ∧ 1 < n)
   
   [LT_MULT_CANCEL_RBARE]  Theorem
      
      |- (m * n < m ⇔ 0 < m ∧ (n = 0)) ∧ (m * n < n ⇔ 0 < n ∧ (m = 0))
   
   [LT_MULT_LCANCEL]  Theorem
      
      |- ∀m n p. m * n < m * p ⇔ 0 < m ∧ n < p
   
   [LT_MULT_RCANCEL]  Theorem
      
      |- ∀m n p. m * n < p * n ⇔ 0 < n ∧ m < p
   
   [LT_SUB_RCANCEL]  Theorem
      
      |- ∀m n p. n − m < p − m ⇔ n < p ∧ m < p
   
   [MAX_0]  Theorem
      
      |- ∀n. (MAX n 0 = n) ∧ (MAX 0 n = n)
   
   [MAX_ASSOC]  Theorem
      
      |- ∀m n p. MAX m (MAX n p) = MAX (MAX m n) p
   
   [MAX_COMM]  Theorem
      
      |- ∀m n. MAX m n = MAX n m
   
   [MAX_IDEM]  Theorem
      
      |- ∀n. MAX n n = n
   
   [MAX_LE]  Theorem
      
      |- ∀n m p.
           (p ≤ MAX m n ⇔ p ≤ m ∨ p ≤ n) ∧ (MAX m n ≤ p ⇔ m ≤ p ∧ n ≤ p)
   
   [MAX_LT]  Theorem
      
      |- ∀n m p.
           (p < MAX m n ⇔ p < m ∨ p < n) ∧ (MAX m n < p ⇔ m < p ∧ n < p)
   
   [MIN_0]  Theorem
      
      |- ∀n. (MIN n 0 = 0) ∧ (MIN 0 n = 0)
   
   [MIN_ASSOC]  Theorem
      
      |- ∀m n p. MIN m (MIN n p) = MIN (MIN m n) p
   
   [MIN_COMM]  Theorem
      
      |- ∀m n. MIN m n = MIN n m
   
   [MIN_IDEM]  Theorem
      
      |- ∀n. MIN n n = n
   
   [MIN_LE]  Theorem
      
      |- ∀n m p.
           (MIN m n ≤ p ⇔ m ≤ p ∨ n ≤ p) ∧ (p ≤ MIN m n ⇔ p ≤ m ∧ p ≤ n)
   
   [MIN_LT]  Theorem
      
      |- ∀n m p.
           (MIN m n < p ⇔ m < p ∨ n < p) ∧ (p < MIN m n ⇔ p < m ∧ p < n)
   
   [MIN_MAX_EQ]  Theorem
      
      |- ∀m n. (MIN m n = MAX m n) ⇔ (m = n)
   
   [MIN_MAX_LE]  Theorem
      
      |- ∀m n. MIN m n ≤ MAX m n
   
   [MIN_MAX_LT]  Theorem
      
      |- ∀m n. MIN m n < MAX m n ⇔ m ≠ n
   
   [MIN_MAX_PRED]  Theorem
      
      |- ∀P m n. P m ∧ P n ⇒ P (MIN m n) ∧ P (MAX m n)
   
   [MODEQ_0]  Theorem
      
      |- 0 < n ⇒ MODEQ n n 0
   
   [MODEQ_0_CONG]  Theorem
      
      |- MODEQ 0 m1 m2 ⇔ (m1 = m2)
   
   [MODEQ_INTRO_CONG]  Theorem
      
      |- 0 < n ⇒ MODEQ n e0 e1 ⇒ (e0 MOD n = e1 MOD n)
   
   [MODEQ_MOD]  Theorem
      
      |- 0 < n ⇒ MODEQ n (x MOD n) x
   
   [MODEQ_MULT_CONG]  Theorem
      
      |- MODEQ n x0 x1 ⇒ MODEQ n y0 y1 ⇒ MODEQ n (x0 * y0) (x1 * y1)
   
   [MODEQ_NONZERO_MODEQUALITY]  Theorem
      
      |- 0 < n ⇒ (MODEQ n m1 m2 ⇔ (m1 MOD n = m2 MOD n))
   
   [MODEQ_NUMERAL]  Theorem
      
      |- (NUMERAL n ≤ NUMERAL m ⇒
          MODEQ (NUMERAL (BIT1 n)) (NUMERAL (BIT1 m))
            (NUMERAL (BIT1 m) MOD NUMERAL (BIT1 n))) ∧
         (NUMERAL n ≤ NUMERAL m ⇒
          MODEQ (NUMERAL (BIT1 n)) (NUMERAL (BIT2 m))
            (NUMERAL (BIT2 m) MOD NUMERAL (BIT1 n))) ∧
         (NUMERAL n ≤ NUMERAL m ⇒
          MODEQ (NUMERAL (BIT2 n)) (NUMERAL (BIT2 m))
            (NUMERAL (BIT2 m) MOD NUMERAL (BIT2 n))) ∧
         (NUMERAL n < NUMERAL m ⇒
          MODEQ (NUMERAL (BIT2 n)) (NUMERAL (BIT1 m))
            (NUMERAL (BIT1 m) MOD NUMERAL (BIT2 n)))
   
   [MODEQ_PLUS_CONG]  Theorem
      
      |- MODEQ n x0 x1 ⇒ MODEQ n y0 y1 ⇒ MODEQ n (x0 + y0) (x1 + y1)
   
   [MODEQ_REFL]  Theorem
      
      |- ∀x. MODEQ n x x
   
   [MODEQ_SYM]  Theorem
      
      |- MODEQ n x y ⇔ MODEQ n y x
   
   [MODEQ_THM]  Theorem
      
      |- MODEQ n m1 m2 ⇔
         (n = 0) ∧ (m1 = m2) ∨ 0 < n ∧ (m1 MOD n = m2 MOD n)
   
   [MODEQ_TRANS]  Theorem
      
      |- ∀x y z. MODEQ n x y ∧ MODEQ n y z ⇒ MODEQ n x z
   
   [MOD_1]  Theorem
      
      |- ∀k. k MOD 1 = 0
   
   [MOD_2]  Theorem
      
      |- ∀n. n MOD 2 = if EVEN n then 0 else 1
   
   [MOD_COMMON_FACTOR]  Theorem
      
      |- ∀n p q. 0 < n ∧ 0 < q ⇒ (n * p MOD q = (n * p) MOD (n * q))
   
   [MOD_ELIM]  Theorem
      
      |- ∀P x n. 0 < n ∧ P x ∧ (∀y. P (y + n) ⇒ P y) ⇒ P (x MOD n)
   
   [MOD_EQ_0]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀k. (k * n) MOD n = 0
   
   [MOD_EQ_0_DIVISOR]  Theorem
      
      |- 0 < n ⇒ ((k MOD n = 0) ⇔ ∃d. k = d * n)
   
   [MOD_LESS]  Theorem
      
      |- ∀m n. 0 < n ⇒ m MOD n < n
   
   [MOD_LESS_EQ]  Theorem
      
      |- 0 < y ⇒ x MOD y ≤ x
   
   [MOD_LIFT_PLUS]  Theorem
      
      |- 0 < n ∧ k < n − x MOD n ⇒ ((x + k) MOD n = x MOD n + k)
   
   [MOD_LIFT_PLUS_IFF]  Theorem
      
      |- 0 < n ⇒ (((x + k) MOD n = x MOD n + k) ⇔ k < n − x MOD n)
   
   [MOD_MOD]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀k. k MOD n MOD n = k MOD n
   
   [MOD_MULT]  Theorem
      
      |- ∀n r. r < n ⇒ ∀q. (q * n + r) MOD n = r
   
   [MOD_MULT_MOD]  Theorem
      
      |- ∀m n. 0 < n ∧ 0 < m ⇒ ∀x. x MOD (n * m) MOD n = x MOD n
   
   [MOD_ONE]  Theorem
      
      |- ∀k. k MOD SUC 0 = 0
   
   [MOD_P]  Theorem
      
      |- ∀P p q.
           0 < q ⇒ (P (p MOD q) ⇔ ∃k r. (p = k * q + r) ∧ r < q ∧ P r)
   
   [MOD_PLUS]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀j k. (j MOD n + k MOD n) MOD n = (j + k) MOD n
   
   [MOD_P_UNIV]  Theorem
      
      |- ∀P m n.
           0 < n ⇒ (P (m MOD n) ⇔ ∀q r. (m = q * n + r) ∧ r < n ⇒ P r)
   
   [MOD_SUB]  Theorem
      
      |- 0 < n ∧ n * q ≤ m ⇒ ((m − n * q) MOD n = m MOD n)
   
   [MOD_SUC]  Theorem
      
      |- 0 < y ∧ SUC x ≠ SUC (x DIV y) * y ⇒ (SUC x MOD y = SUC (x MOD y))
   
   [MOD_SUC_IFF]  Theorem
      
      |- 0 < y ⇒
         ((SUC x MOD y = SUC (x MOD y)) ⇔ SUC x ≠ SUC (x DIV y) * y)
   
   [MOD_TIMES]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀q r. (q * n + r) MOD n = r MOD n
   
   [MOD_TIMES2]  Theorem
      
      |- ∀n. 0 < n ⇒ ∀j k. (j MOD n * k MOD n) MOD n = (j * k) MOD n
   
   [MOD_TIMES_SUB]  Theorem
      
      |- ∀n q r.
           0 < n ∧ 0 < q ∧ r ≤ n ⇒ ((q * n − r) MOD n = (n − r) MOD n)
   
   [MOD_UNIQUE]  Theorem
      
      |- ∀n k r. (∃q. (k = q * n + r) ∧ r < n) ⇒ (k MOD n = r)
   
   [MULT_0]  Theorem
      
      |- ∀m. m * 0 = 0
   
   [MULT_ASSOC]  Theorem
      
      |- ∀m n p. m * (n * p) = m * n * p
   
   [MULT_CLAUSES]  Theorem
      
      |- ∀m n.
           (0 * m = 0) ∧ (m * 0 = 0) ∧ (1 * m = m) ∧ (m * 1 = m) ∧
           (SUC m * n = m * n + n) ∧ (m * SUC n = m + m * n)
   
   [MULT_COMM]  Theorem
      
      |- ∀m n. m * n = n * m
   
   [MULT_DIV]  Theorem
      
      |- ∀n q. 0 < n ⇒ (q * n DIV n = q)
   
   [MULT_EQ_0]  Theorem
      
      |- ∀m n. (m * n = 0) ⇔ (m = 0) ∨ (n = 0)
   
   [MULT_EQ_1]  Theorem
      
      |- ∀x y. (x * y = 1) ⇔ (x = 1) ∧ (y = 1)
   
   [MULT_EQ_DIV]  Theorem
      
      |- 0 < x ⇒ ((x * y = z) ⇔ (y = z DIV x) ∧ (z MOD x = 0))
   
   [MULT_EQ_ID]  Theorem
      
      |- ∀m n. (m * n = n) ⇔ (m = 1) ∨ (n = 0)
   
   [MULT_EXP_MONO]  Theorem
      
      |- ∀p q n m. (n * SUC q ** p = m * SUC q ** p) ⇔ (n = m)
   
   [MULT_INCREASES]  Theorem
      
      |- ∀m n. 1 < m ∧ 0 < n ⇒ SUC n ≤ m * n
   
   [MULT_LEFT_1]  Theorem
      
      |- ∀m. 1 * m = m
   
   [MULT_LESS_EQ_SUC]  Theorem
      
      |- ∀m n p. m ≤ n ⇔ SUC p * m ≤ SUC p * n
   
   [MULT_MONO_EQ]  Theorem
      
      |- ∀m i n. (SUC n * m = SUC n * i) ⇔ (m = i)
   
   [MULT_RIGHT_1]  Theorem
      
      |- ∀m. m * 1 = m
   
   [MULT_SUC]  Theorem
      
      |- ∀m n. m * SUC n = m + m * n
   
   [MULT_SUC_EQ]  Theorem
      
      |- ∀p m n. (n * SUC p = m * SUC p) ⇔ (n = m)
   
   [MULT_SYM]  Theorem
      
      |- ∀m n. m * n = n * m
   
   [NORM_0]  Theorem
      
      |- 0 = 0
   
   [NOT_EXP_0]  Theorem
      
      |- ∀m n. SUC n ** m ≠ 0
   
   [NOT_GREATER]  Theorem
      
      |- ∀m n. ¬(m > n) ⇔ m ≤ n
   
   [NOT_GREATER_EQ]  Theorem
      
      |- ∀m n. ¬(m ≥ n) ⇔ SUC m ≤ n
   
   [NOT_LEQ]  Theorem
      
      |- ∀m n. ¬(m ≤ n) ⇔ SUC n ≤ m
   
   [NOT_LESS]  Theorem
      
      |- ∀m n. ¬(m < n) ⇔ n ≤ m
   
   [NOT_LESS_EQUAL]  Theorem
      
      |- ∀m n. ¬(m ≤ n) ⇔ n < m
   
   [NOT_NUM_EQ]  Theorem
      
      |- ∀m n. m ≠ n ⇔ SUC m ≤ n ∨ SUC n ≤ m
   
   [NOT_ODD_EQ_EVEN]  Theorem
      
      |- ∀n m. SUC (n + n) ≠ m + m
   
   [NOT_STRICTLY_DECREASING]  Theorem
      
      |- ∀f. ¬∀n. f (SUC n) < f n
   
   [NOT_SUC_ADD_LESS_EQ]  Theorem
      
      |- ∀m n. ¬(SUC (m + n) ≤ m)
   
   [NOT_SUC_LESS_EQ]  Theorem
      
      |- ∀n m. ¬(SUC n ≤ m) ⇔ m ≤ n
   
   [NOT_SUC_LESS_EQ_0]  Theorem
      
      |- ∀n. ¬(SUC n ≤ 0)
   
   [NOT_ZERO_LT_ZERO]  Theorem
      
      |- ∀n. n ≠ 0 ⇔ 0 < n
   
   [NRC_0]  Theorem
      
      |- ∀R x y. NRC R 0 x y ⇔ (x = y)
   
   [NRC_1]  Theorem
      
      |- NRC R 1 x y ⇔ R x y
   
   [NRC_ADD_E]  Theorem
      
      |- ∀m n x z. NRC R (m + n) x z ⇒ ∃y. NRC R m x y ∧ NRC R n y z
   
   [NRC_ADD_EQN]  Theorem
      
      |- NRC R (m + n) x z ⇔ ∃y. NRC R m x y ∧ NRC R n y z
   
   [NRC_ADD_I]  Theorem
      
      |- ∀m n x y z. NRC R m x y ∧ NRC R n y z ⇒ NRC R (m + n) x z
   
   [NRC_RTC]  Theorem
      
      |- ∀n x y. NRC R n x y ⇒ R^* x y
   
   [NRC_SUC_RECURSE_LEFT]  Theorem
      
      |- NRC R (SUC n) x y ⇔ ∃z. NRC R n x z ∧ R z y
   
   [NUMERAL_MULT_EQ_DIV]  Theorem
      
      |- ((NUMERAL (BIT1 x) * y = NUMERAL z) ⇔
          (y = NUMERAL z DIV NUMERAL (BIT1 x)) ∧
          (NUMERAL z MOD NUMERAL (BIT1 x) = 0)) ∧
         ((NUMERAL (BIT2 x) * y = NUMERAL z) ⇔
          (y = NUMERAL z DIV NUMERAL (BIT2 x)) ∧
          (NUMERAL z MOD NUMERAL (BIT2 x) = 0))
   
   [ODD_ADD]  Theorem
      
      |- ∀m n. ODD (m + n) ⇔ (ODD m ⇎ ODD n)
   
   [ODD_DOUBLE]  Theorem
      
      |- ∀n. ODD (SUC (2 * n))
   
   [ODD_EVEN]  Theorem
      
      |- ∀n. ODD n ⇔ ¬EVEN n
   
   [ODD_EXISTS]  Theorem
      
      |- ∀n. ODD n ⇔ ∃m. n = SUC (2 * m)
   
   [ODD_MULT]  Theorem
      
      |- ∀m n. ODD (m * n) ⇔ ODD m ∧ ODD n
   
   [ODD_OR_EVEN]  Theorem
      
      |- ∀n. ∃m. (n = SUC (SUC 0) * m) ∨ (n = SUC (SUC 0) * m + 1)
   
   [ONE]  Theorem
      
      |- 1 = SUC 0
   
   [ONE_LT_EXP]  Theorem
      
      |- ∀x y. 1 < x ** y ⇔ 1 < x ∧ 0 < y
   
   [ONE_LT_MULT]  Theorem
      
      |- ∀x y. 1 < x * y ⇔ 0 < x ∧ 1 < y ∨ 0 < y ∧ 1 < x
   
   [ONE_LT_MULT_IMP]  Theorem
      
      |- ∀p q. 1 < p ∧ 0 < q ⇒ 1 < p * q
   
   [ONE_MOD]  Theorem
      
      |- 1 < n ⇒ (1 MOD n = 1)
   
   [ONE_MOD_IFF]  Theorem
      
      |- 1 < n ⇔ 0 < n ∧ (1 MOD n = 1)
   
   [ONE_ONE_UNBOUNDED]  Theorem
      
      |- ∀f. ONE_ONE f ⇒ ∀b. ∃n. b < f n
   
   [OR_LESS]  Theorem
      
      |- ∀m n. SUC m ≤ n ⇒ m < n
   
   [PRE_ELIM_THM]  Theorem
      
      |- P (PRE n) ⇔ ∀m. ((n = 0) ⇒ P 0) ∧ ((n = SUC m) ⇒ P m)
   
   [PRE_SUB]  Theorem
      
      |- ∀m n. PRE (m − n) = PRE m − n
   
   [PRE_SUB1]  Theorem
      
      |- ∀m. PRE m = m − 1
   
   [PRE_SUC_EQ]  Theorem
      
      |- ∀m n. 0 < n ⇒ ((m = PRE n) ⇔ (SUC m = n))
   
   [RIGHT_ADD_DISTRIB]  Theorem
      
      |- ∀m n p. (m + n) * p = m * p + n * p
   
   [RIGHT_SUB_DISTRIB]  Theorem
      
      |- ∀m n p. (m − n) * p = m * p − n * p
   
   [RTC_NRC]  Theorem
      
      |- ∀x y. R^* x y ⇒ ∃n. NRC R n x y
   
   [RTC_eq_NRC]  Theorem
      
      |- ∀R x y. R^* x y ⇔ ∃n. NRC R n x y
   
   [STRICTLY_INCREASING_ONE_ONE]  Theorem
      
      |- ∀f. (∀n. f n < f (SUC n)) ⇒ ONE_ONE f
   
   [STRICTLY_INCREASING_TC]  Theorem
      
      |- ∀f. (∀n. f n < f (SUC n)) ⇒ ∀m n. m < n ⇒ f m < f n
   
   [STRICTLY_INCREASING_UNBOUNDED]  Theorem
      
      |- ∀f. (∀n. f n < f (SUC n)) ⇒ ∀b. ∃n. b < f n
   
   [SUB_0]  Theorem
      
      |- ∀m. (0 − m = 0) ∧ (m − 0 = m)
   
   [SUB_ADD]  Theorem
      
      |- ∀m n. n ≤ m ⇒ (m − n + n = m)
   
   [SUB_CANCEL]  Theorem
      
      |- ∀p n m. n ≤ p ∧ m ≤ p ⇒ ((p − n = p − m) ⇔ (n = m))
   
   [SUB_ELIM_THM]  Theorem
      
      |- P (a − b) ⇔ ∀d. ((b = a + d) ⇒ P 0) ∧ ((a = b + d) ⇒ P d)
   
   [SUB_EQUAL_0]  Theorem
      
      |- ∀c. c − c = 0
   
   [SUB_EQ_0]  Theorem
      
      |- ∀m n. (m − n = 0) ⇔ m ≤ n
   
   [SUB_EQ_EQ_0]  Theorem
      
      |- ∀m n. (m − n = m) ⇔ (m = 0) ∨ (n = 0)
   
   [SUB_LEFT_ADD]  Theorem
      
      |- ∀m n p. m + (n − p) = if n ≤ p then m else m + n − p
   
   [SUB_LEFT_EQ]  Theorem
      
      |- ∀m n p. (m = n − p) ⇔ (m + p = n) ∨ m ≤ 0 ∧ n ≤ p
   
   [SUB_LEFT_GREATER]  Theorem
      
      |- ∀m n p. m > n − p ⇔ m + p > n ∧ m > 0
   
   [SUB_LEFT_GREATER_EQ]  Theorem
      
      |- ∀m n p. m ≥ n − p ⇔ m + p ≥ n
   
   [SUB_LEFT_LESS]  Theorem
      
      |- ∀m n p. m < n − p ⇔ m + p < n
   
   [SUB_LEFT_LESS_EQ]  Theorem
      
      |- ∀m n p. m ≤ n − p ⇔ m + p ≤ n ∨ m ≤ 0
   
   [SUB_LEFT_SUB]  Theorem
      
      |- ∀m n p. m − (n − p) = if n ≤ p then m else m + p − n
   
   [SUB_LEFT_SUC]  Theorem
      
      |- ∀m n. SUC (m − n) = if m ≤ n then SUC 0 else SUC m − n
   
   [SUB_LESS]  Theorem
      
      |- ∀m n. 0 < n ∧ n ≤ m ⇒ m − n < m
   
   [SUB_LESS_0]  Theorem
      
      |- ∀n m. m < n ⇔ 0 < n − m
   
   [SUB_LESS_EQ]  Theorem
      
      |- ∀n m. n − m ≤ n
   
   [SUB_LESS_EQ_ADD]  Theorem
      
      |- ∀m p. m ≤ p ⇒ ∀n. p − m ≤ n ⇔ p ≤ m + n
   
   [SUB_LESS_OR]  Theorem
      
      |- ∀m n. n < m ⇒ n ≤ m − 1
   
   [SUB_MOD]  Theorem
      
      |- ∀m n. 0 < n ∧ n ≤ m ⇒ ((m − n) MOD n = m MOD n)
   
   [SUB_MONO_EQ]  Theorem
      
      |- ∀n m. SUC n − SUC m = n − m
   
   [SUB_PLUS]  Theorem
      
      |- ∀a b c. a − (b + c) = a − b − c
   
   [SUB_RIGHT_ADD]  Theorem
      
      |- ∀m n p. m − n + p = if m ≤ n then p else m + p − n
   
   [SUB_RIGHT_EQ]  Theorem
      
      |- ∀m n p. (m − n = p) ⇔ (m = n + p) ∨ m ≤ n ∧ p ≤ 0
   
   [SUB_RIGHT_GREATER]  Theorem
      
      |- ∀m n p. m − n > p ⇔ m > n + p
   
   [SUB_RIGHT_GREATER_EQ]  Theorem
      
      |- ∀m n p. m − n ≥ p ⇔ m ≥ n + p ∨ 0 ≥ p
   
   [SUB_RIGHT_LESS]  Theorem
      
      |- ∀m n p. m − n < p ⇔ m < n + p ∧ 0 < p
   
   [SUB_RIGHT_LESS_EQ]  Theorem
      
      |- ∀m n p. m − n ≤ p ⇔ m ≤ n + p
   
   [SUB_RIGHT_SUB]  Theorem
      
      |- ∀m n p. m − n − p = m − (n + p)
   
   [SUB_SUB]  Theorem
      
      |- ∀b c. c ≤ b ⇒ ∀a. a − (b − c) = a + c − b
   
   [SUC_ADD_SYM]  Theorem
      
      |- ∀m n. SUC (m + n) = SUC n + m
   
   [SUC_ELIM_NUMERALS]  Theorem
      
      |- ∀f g.
           (∀n. g (SUC n) = f n (SUC n)) ⇔
           (∀n.
              g (NUMERAL (BIT1 n)) =
              f (NUMERAL (BIT1 n) − 1) (NUMERAL (BIT1 n))) ∧
           ∀n.
             g (NUMERAL (BIT2 n)) = f (NUMERAL (BIT1 n)) (NUMERAL (BIT2 n))
   
   [SUC_ELIM_THM]  Theorem
      
      |- ∀P. (∀n. P (SUC n) n) ⇔ ∀n. 0 < n ⇒ P n (n − 1)
   
   [SUC_MOD]  Theorem
      
      |- ∀n a b.
           0 < n ⇒ ((SUC a MOD n = SUC b MOD n) ⇔ (a MOD n = b MOD n))
   
   [SUC_NOT]  Theorem
      
      |- ∀n. 0 ≠ SUC n
   
   [SUC_ONE_ADD]  Theorem
      
      |- ∀n. SUC n = 1 + n
   
   [SUC_PRE]  Theorem
      
      |- 0 < m ⇔ (SUC (PRE m) = m)
   
   [SUC_SUB1]  Theorem
      
      |- ∀m. SUC m − 1 = m
   
   [TC_eq_NRC]  Theorem
      
      |- ∀R x y. R⁺ x y ⇔ ∃n. NRC R (SUC n) x y
   
   [TIMES2]  Theorem
      
      |- ∀n. 2 * n = n + n
   
   [TWO]  Theorem
      
      |- 2 = SUC 1
   
   [WOP]  Theorem
      
      |- ∀P. (∃n. P n) ⇒ ∃n. P n ∧ ∀m. m < n ⇒ ¬P m
   
   [X_LE_DIV]  Theorem
      
      |- ∀x y z. 0 < z ⇒ (x ≤ y DIV z ⇔ x * z ≤ y)
   
   [X_LE_X_EXP]  Theorem
      
      |- 0 < n ⇒ x ≤ x ** n
   
   [X_LT_DIV]  Theorem
      
      |- ∀x y z. 0 < z ⇒ (x < y DIV z ⇔ (x + 1) * z ≤ y)
   
   [X_LT_EXP_X]  Theorem
      
      |- 1 < b ⇒ x < b ** x
   
   [X_LT_EXP_X_IFF]  Theorem
      
      |- x < b ** x ⇔ 1 < b ∨ (x = 0)
   
   [X_MOD_Y_EQ_X]  Theorem
      
      |- ∀x y. 0 < y ⇒ ((x MOD y = x) ⇔ x < y)
   
   [ZERO_DIV]  Theorem
      
      |- ∀n. 0 < n ⇒ (0 DIV n = 0)
   
   [ZERO_EXP]  Theorem
      
      |- 0 ** x = if x = 0 then 1 else 0
   
   [ZERO_LESS_ADD]  Theorem
      
      |- ∀m n. 0 < m + n ⇔ 0 < m ∨ 0 < n
   
   [ZERO_LESS_EQ]  Theorem
      
      |- ∀n. 0 ≤ n
   
   [ZERO_LESS_EXP]  Theorem
      
      |- ∀m n. 0 < SUC n ** m
   
   [ZERO_LESS_MULT]  Theorem
      
      |- ∀m n. 0 < m * n ⇔ 0 < m ∧ 0 < n
   
   [ZERO_LT_EXP]  Theorem
      
      |- 0 < x ** y ⇔ 0 < x ∨ (y = 0)
   
   [ZERO_MOD]  Theorem
      
      |- ∀n. 0 < n ⇒ (0 MOD n = 0)
   
   [findq_divisor]  Theorem
      
      |- n ≤ m ⇒ findq (a,m,n) * n ≤ a * m
   
   [findq_eq_0]  Theorem
      
      |- ∀a m n. (findq (a,m,n) = 0) ⇔ (a = 0)
   
   [findq_thm]  Theorem
      
      |- findq (a,m,n) =
         if n = 0 then
           a
         else
           (let d = 2 * n in if m < d then a else findq (2 * a,m,d))
   
   [num_CASES]  Theorem
      
      |- ∀m. (m = 0) ∨ ∃n. m = SUC n
   
   [num_case_compute]  Theorem
      
      |- ∀n. num_case f g n = if n = 0 then f else g (PRE n)
   
   [num_case_cong]  Theorem
      
      |- ∀M M' b f.
           (M = M') ∧ ((M' = 0) ⇒ (b = b')) ∧
           (∀n. (M' = SUC n) ⇒ (f n = f' n)) ⇒
           (num_case b f M = num_case b' f' M')
   
   [transitive_measure]  Theorem
      
      |- ∀f. transitive (measure f)
   
   [transitive_monotone]  Theorem
      
      |- ∀R f.
           transitive R ∧ (∀n. R (f n) (f (SUC n))) ⇒
           ∀m n. m < n ⇒ R (f m) (f n)
   
   
*)
end
