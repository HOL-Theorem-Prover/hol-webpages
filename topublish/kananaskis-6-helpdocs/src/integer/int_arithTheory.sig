signature int_arithTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val bmarker_def : thm
  
  (*  Theorems  *)
    val CONJ_EQ_ELIM : thm
    val HO_SUB_ELIM : thm
    val INT_DIVIDES_LRMUL : thm
    val INT_DIVIDES_RELPRIME_MUL : thm
    val INT_LINEAR_GCD : thm
    val INT_LT_ADD_NUMERAL : thm
    val INT_NUM_COND : thm
    val INT_NUM_DIVIDES : thm
    val INT_NUM_EVEN : thm
    val INT_NUM_EXISTS : thm
    val INT_NUM_FORALL : thm
    val INT_NUM_ODD : thm
    val INT_NUM_SUB : thm
    val INT_NUM_UEXISTS : thm
    val INT_SUB_SUB3 : thm
    val NOT_INT_DIVIDES : thm
    val NOT_INT_DIVIDES_POS : thm
    val add_to_great : thm
    val bmarker_rewrites : thm
    val bot_and_greaters : thm
    val can_get_big : thm
    val can_get_small : thm
    val cooper_lemma_1 : thm
    val elim_eq : thm
    val elim_eq_coeffs : thm
    val elim_le_coeffs : thm
    val elim_lt_coeffs1 : thm
    val elim_lt_coeffs2 : thm
    val elim_minus_ones : thm
    val elim_neg_ones : thm
    val eq_context_rwt1 : thm
    val eq_context_rwt2 : thm
    val eq_justify_multiplication : thm
    val eq_move_all_left : thm
    val eq_move_all_right : thm
    val eq_move_left_left : thm
    val eq_move_left_right : thm
    val eq_move_right_left : thm
    val gcd1thm : thm
    val gcd21_thm : thm
    val gcdthm2 : thm
    val in_additive_range : thm
    val in_subtractive_range : thm
    val justify_divides : thm
    val justify_divides2 : thm
    val justify_divides3 : thm
    val lcm_eliminate : thm
    val le_context_rwt1 : thm
    val le_context_rwt2 : thm
    val le_context_rwt3 : thm
    val le_context_rwt4 : thm
    val le_context_rwt5 : thm
    val le_move_all_right : thm
    val le_move_right_left : thm
    val less_to_leq_samel : thm
    val less_to_leq_samer : thm
    val lt_justify_multiplication : thm
    val lt_move_all_left : thm
    val lt_move_all_right : thm
    val lt_move_left_left : thm
    val lt_move_left_right : thm
    val move_sub : thm
    val not_less : thm
    val positive_product_implication : thm
    val restricted_quantification_simp : thm
    val subtract_to_small : thm
    val top_and_lessers : thm
  
  val int_arith_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [gcd] Parent theory of "int_arith"
   
   [integer] Parent theory of "int_arith"
   
   [bmarker_def]  Definition
      
      |- ∀b. int_arith$bmarker b ⇔ b
   
   [CONJ_EQ_ELIM]  Theorem
      
      |- ∀P v e. (v = e) ∧ P v ⇔ (v = e) ∧ P e
   
   [HO_SUB_ELIM]  Theorem
      
      |- ∀P a b. P (&(a − b)) ⇔ &b ≤ &a ∧ P (&a + -&b) ∨ &a < &b ∧ P 0
   
   [INT_DIVIDES_LRMUL]  Theorem
      
      |- ∀p q r. q ≠ 0 ⇒ (p * q int_divides r * q ⇔ p int_divides r)
   
   [INT_DIVIDES_RELPRIME_MUL]  Theorem
      
      |- ∀p q r. (gcd p q = 1) ⇒ (&p int_divides &q * r ⇔ &p int_divides r)
   
   [INT_LINEAR_GCD]  Theorem
      
      |- ∀n m. ∃p q. p * &n + q * &m = &gcd n m
   
   [INT_LT_ADD_NUMERAL]  Theorem
      
      |- ∀x y.
           x < x + &NUMERAL (BIT1 y) ∧ x < x + &NUMERAL (BIT2 y) ∧
           ¬(x < x + -&NUMERAL y)
   
   [INT_NUM_COND]  Theorem
      
      |- ∀b n m. &(if b then n else m) = if b then &n else &m
   
   [INT_NUM_DIVIDES]  Theorem
      
      |- ∀n m. &n int_divides &m ⇔ divides n m
   
   [INT_NUM_EVEN]  Theorem
      
      |- ∀n. EVEN n ⇔ 2 int_divides &n
   
   [INT_NUM_EXISTS]  Theorem
      
      |- (∃n. P (&n)) ⇔ ∃x. 0 ≤ x ∧ P x
   
   [INT_NUM_FORALL]  Theorem
      
      |- (∀n. P (&n)) ⇔ ∀x. 0 ≤ x ⇒ P x
   
   [INT_NUM_ODD]  Theorem
      
      |- ∀n. ODD n ⇔ ¬(2 int_divides &n)
   
   [INT_NUM_SUB]  Theorem
      
      |- ∀n m. &(n − m) = if &n < &m then 0 else &n − &m
   
   [INT_NUM_UEXISTS]  Theorem
      
      |- (∃!n. P (&n)) ⇔ ∃!x. 0 ≤ x ∧ P x
   
   [INT_SUB_SUB3]  Theorem
      
      |- ∀x y z. x − (y − z) = x + z − y
   
   [NOT_INT_DIVIDES]  Theorem
      
      |- ∀c d.
           c ≠ 0 ⇒
           (¬(c int_divides d) ⇔ ∃i. 1 ≤ i ∧ i ≤ ABS c − 1 ∧ c int_divides d + i)
   
   [NOT_INT_DIVIDES_POS]  Theorem
      
      |- ∀n d.
           n ≠ 0 ⇒
           (¬(&n int_divides d) ⇔ ∃i. (1 ≤ i ∧ i ≤ &n − 1) ∧ &n int_divides d + i)
   
   [add_to_great]  Theorem
      
      |- ∀x d. 0 < d ⇒ ∃k. 0 < x + k * d ∧ x + k * d ≤ d
   
   [bmarker_rewrites]  Theorem
      
      |- ∀p q r.
           (q ∧ int_arith$bmarker p ⇔ int_arith$bmarker p ∧ q) ∧
           (q ∧ int_arith$bmarker p ∧ r ⇔ int_arith$bmarker p ∧ q ∧ r) ∧
           ((int_arith$bmarker p ∧ q) ∧ r ⇔ int_arith$bmarker p ∧ q ∧ r)
   
   [bot_and_greaters]  Theorem
      
      |- ∀P d x0. (∀x. P x ⇒ P (x + d)) ∧ P x0 ⇒ ∀c. 0 < c ⇒ P (x0 + c * d)
   
   [can_get_big]  Theorem
      
      |- ∀x y d. 0 < d ⇒ ∃c. 0 < c ∧ x < y + c * d
   
   [can_get_small]  Theorem
      
      |- ∀x y d. 0 < d ⇒ ∃c. 0 < c ∧ y − c * d < x
   
   [cooper_lemma_1]  Theorem
      
      |- ∀m n a b u v p q x d.
           (d = gcd (u * m) (a * n)) ∧ (&d = p * &u * &m + q * &a * &n) ∧ m ≠ 0 ∧
           n ≠ 0 ∧ a ≠ 0 ∧ u ≠ 0 ⇒
           (&m int_divides &a * x + b ∧ &n int_divides &u * x + v ⇔
            &m * &n int_divides &d * x + v * &m * p + b * &n * q ∧
            &d int_divides &a * v − &u * b)
   
   [elim_eq]  Theorem
      
      |- (x = y) ⇔ x < y + 1 ∧ y < x + 1
   
   [elim_eq_coeffs]  Theorem
      
      |- ∀m x y. m ≠ 0 ⇒ ((&m * x = y) ⇔ &m int_divides y ∧ (x = y / &m))
   
   [elim_le_coeffs]  Theorem
      
      |- ∀m n x. 0 < m ⇒ (0 ≤ m * x + n ⇔ 0 ≤ x + n / m)
   
   [elim_lt_coeffs1]  Theorem
      
      |- ∀n m x. m ≠ 0 ⇒ (&n < &m * x ⇔ &n / &m < x)
   
   [elim_lt_coeffs2]  Theorem
      
      |- ∀n m x.
           m ≠ 0 ⇒
           (&m * x < &n ⇔ x < if &m int_divides &n then &n / &m else &n / &m + 1)
   
   [elim_minus_ones]  Theorem
      
      |- ∀x. x + 1 − 1 = x
   
   [elim_neg_ones]  Theorem
      
      |- ∀x. x + -1 + 1 = x
   
   [eq_context_rwt1]  Theorem
      
      |- (0 = c + x) ⇒ (0 ≤ c + y ⇔ x ≤ y)
   
   [eq_context_rwt2]  Theorem
      
      |- (0 = c + x) ⇒ (0 ≤ -c + y ⇔ -x ≤ y)
   
   [eq_justify_multiplication]  Theorem
      
      |- ∀n x y. 0 < n ⇒ ((x = y) ⇔ (n * x = n * y))
   
   [eq_move_all_left]  Theorem
      
      |- ∀x y. (x = y) ⇔ (x + -y = 0)
   
   [eq_move_all_right]  Theorem
      
      |- ∀x y. (x = y) ⇔ (0 = y + -x)
   
   [eq_move_left_left]  Theorem
      
      |- ∀x y z. (x = y + z) ⇔ (x + -y = z)
   
   [eq_move_left_right]  Theorem
      
      |- ∀x y z. (x + y = z) ⇔ (y = z + -x)
   
   [eq_move_right_left]  Theorem
      
      |- ∀x y z. (x = y + z) ⇔ (x + -z = y)
   
   [gcd1thm]  Theorem
      
      |- ∀m n p q. (p * &m + q * &n = 1) ⇒ (gcd m n = 1)
   
   [gcd21_thm]  Theorem
      
      |- ∀m a x b p q.
           (p * &a + q * &m = 1) ∧ m ≠ 0 ∧ a ≠ 0 ⇒
           (&m int_divides &a * x + b ⇔ ∃t. x = -p * b + t * &m)
   
   [gcdthm2]  Theorem
      
      |- ∀m a x b d p q.
           (d = gcd a m) ∧ (&d = p * &a + q * &m) ∧ d ≠ 0 ∧ m ≠ 0 ∧ a ≠ 0 ⇒
           (&m int_divides &a * x + b ⇔
            &d int_divides b ∧ ∃t. x = -p * (b / &d) + t * (&m / &d))
   
   [in_additive_range]  Theorem
      
      |- ∀low d x. low < x ∧ x ≤ low + d ⇔ ∃j. (x = low + j) ∧ 0 < j ∧ j ≤ d
   
   [in_subtractive_range]  Theorem
      
      |- ∀high d x. high − d ≤ x ∧ x < high ⇔ ∃j. (x = high − j) ∧ 0 < j ∧ j ≤ d
   
   [justify_divides]  Theorem
      
      |- ∀n x y. 0 < n ⇒ (x int_divides y ⇔ n * x int_divides n * y)
   
   [justify_divides2]  Theorem
      
      |- ∀n c x y.
           n * x int_divides n * y + c ⇔
           n * x int_divides n * y + c ∧ n int_divides c
   
   [justify_divides3]  Theorem
      
      |- ∀n x c. n int_divides n * x + c ⇔ n int_divides c
   
   [lcm_eliminate]  Theorem
      
      |- ∀P c. (∃x. P (c * x)) ⇔ ∃x. P x ∧ c int_divides x
   
   [le_context_rwt1]  Theorem
      
      |- 0 ≤ c + x ⇒ x ≤ y ⇒ (0 ≤ c + y ⇔ T)
   
   [le_context_rwt2]  Theorem
      
      |- 0 ≤ c + x ⇒ y < -x ⇒ (0 ≤ -c + y ⇔ F)
   
   [le_context_rwt3]  Theorem
      
      |- 0 ≤ c + x ⇒ x < y ⇒ ((0 = c + y) ⇔ F)
   
   [le_context_rwt4]  Theorem
      
      |- 0 ≤ c + x ⇒ x < -y ⇒ ((0 = -c + y) ⇔ F)
   
   [le_context_rwt5]  Theorem
      
      |- 0 ≤ c + x ⇒ (0 ≤ -c + -x ⇔ (0 = c + x))
   
   [le_move_all_right]  Theorem
      
      |- ∀x y. x ≤ y ⇔ 0 ≤ y + -x
   
   [le_move_right_left]  Theorem
      
      |- ∀x y z. x ≤ y + z ⇔ x + -z ≤ y
   
   [less_to_leq_samel]  Theorem
      
      |- ∀x y. x < y ⇔ x ≤ y + -1
   
   [less_to_leq_samer]  Theorem
      
      |- ∀x y. x < y ⇔ x + 1 ≤ y
   
   [lt_justify_multiplication]  Theorem
      
      |- ∀n x y. 0 < n ⇒ (x < y ⇔ n * x < n * y)
   
   [lt_move_all_left]  Theorem
      
      |- ∀x y. x < y ⇔ x + -y < 0
   
   [lt_move_all_right]  Theorem
      
      |- ∀x y. x < y ⇔ 0 < y + -x
   
   [lt_move_left_left]  Theorem
      
      |- ∀x y z. x < y + z ⇔ x + -y < z
   
   [lt_move_left_right]  Theorem
      
      |- ∀x y z. x + y < z ⇔ y < z + -x
   
   [move_sub]  Theorem
      
      |- ∀c b a. a − c + b = a + b − c
   
   [not_less]  Theorem
      
      |- ¬(x < y) ⇔ y < x + 1
   
   [positive_product_implication]  Theorem
      
      |- ∀c d. 0 < c ∧ 0 < d ⇒ 0 < c * d
   
   [restricted_quantification_simp]  Theorem
      
      |- ∀low high x.
           low < x ∧ x ≤ high ⇔ low < high ∧ ((x = high) ∨ low < x ∧ x ≤ high − 1)
   
   [subtract_to_small]  Theorem
      
      |- ∀x d. 0 < d ⇒ ∃k. 0 < x − k * d ∧ x − k * d ≤ d
   
   [top_and_lessers]  Theorem
      
      |- ∀P d x0. (∀x. P x ⇒ P (x − d)) ∧ P x0 ⇒ ∀c. 0 < c ⇒ P (x0 − c * d)
   
   
*)
end
