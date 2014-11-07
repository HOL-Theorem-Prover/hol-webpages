signature dividesTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val PRIMES_def : thm
    val divides_def : thm
    val prime_def : thm

  (*  Theorems  *)
    val ALL_DIVIDES_0 : thm
    val DIVIDES_ADD_1 : thm
    val DIVIDES_ADD_2 : thm
    val DIVIDES_ANTISYM : thm
    val DIVIDES_FACT : thm
    val DIVIDES_LE : thm
    val DIVIDES_LEQ_OR_ZERO : thm
    val DIVIDES_MULT : thm
    val DIVIDES_MULT_LEFT : thm
    val DIVIDES_ONE : thm
    val DIVIDES_REFL : thm
    val DIVIDES_SUB : thm
    val DIVIDES_TRANS : thm
    val EUCLID : thm
    val EUCLID_PRIMES : thm
    val INDEX_LESS_PRIMES : thm
    val INFINITE_PRIMES : thm
    val LEQ_DIVIDES_FACT : thm
    val LT_PRIMES : thm
    val NEXT_LARGER_PRIME : thm
    val NOT_LT_DIVIDES : thm
    val NOT_PRIME_0 : thm
    val NOT_PRIME_1 : thm
    val ONE_DIVIDES_ALL : thm
    val ONE_LT_PRIME : thm
    val ONE_LT_PRIMES : thm
    val PRIMES_11 : thm
    val PRIMES_NO_GAP : thm
    val PRIMES_ONTO : thm
    val PRIME_2 : thm
    val PRIME_3 : thm
    val PRIME_FACTOR : thm
    val PRIME_INDEX : thm
    val PRIME_POS : thm
    val ZERO_DIVIDES : thm
    val ZERO_LT_PRIMES : thm
    val compute_divides : thm
    val primePRIMES : thm
    val prime_divides_only_self : thm

  val divides_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [numeral] Parent theory of "divides"

   [while] Parent theory of "divides"

   [PRIMES_def]  Definition

      |- (PRIMES 0 = 2) ∧
         ∀n. PRIMES (SUC n) = LEAST p. prime p ∧ PRIMES n < p

   [divides_def]  Definition

      |- ∀a b. divides a b ⇔ ∃q. b = q * a

   [prime_def]  Definition

      |- ∀a. prime a ⇔ a ≠ 1 ∧ ∀b. divides b a ⇒ (b = a) ∨ (b = 1)

   [ALL_DIVIDES_0]  Theorem

      |- ∀a. divides a 0

   [DIVIDES_ADD_1]  Theorem

      |- ∀a b c. divides a b ∧ divides a c ⇒ divides a (b + c)

   [DIVIDES_ADD_2]  Theorem

      |- ∀a b c. divides a b ∧ divides a (b + c) ⇒ divides a c

   [DIVIDES_ANTISYM]  Theorem

      |- ∀a b. divides a b ∧ divides b a ⇒ (a = b)

   [DIVIDES_FACT]  Theorem

      |- ∀b. 0 < b ⇒ divides b (FACT b)

   [DIVIDES_LE]  Theorem

      |- ∀a b. 0 < b ∧ divides a b ⇒ a ≤ b

   [DIVIDES_LEQ_OR_ZERO]  Theorem

      |- ∀m n. divides m n ⇒ m ≤ n ∨ (n = 0)

   [DIVIDES_MULT]  Theorem

      |- ∀a b c. divides a b ⇒ divides a (b * c)

   [DIVIDES_MULT_LEFT]  Theorem

      |- ∀n m. divides (n * m) m ⇔ (m = 0) ∨ (n = 1)

   [DIVIDES_ONE]  Theorem

      |- ∀x. divides x 1 ⇔ (x = 1)

   [DIVIDES_REFL]  Theorem

      |- ∀a. divides a a

   [DIVIDES_SUB]  Theorem

      |- ∀a b c. divides a b ∧ divides a c ⇒ divides a (b − c)

   [DIVIDES_TRANS]  Theorem

      |- ∀a b c. divides a b ∧ divides b c ⇒ divides a c

   [EUCLID]  Theorem

      |- ∀n. ∃p. n < p ∧ prime p

   [EUCLID_PRIMES]  Theorem

      |- ∀n. ∃i. n < PRIMES i

   [INDEX_LESS_PRIMES]  Theorem

      |- ∀n. n < PRIMES n

   [INFINITE_PRIMES]  Theorem

      |- ∀n. PRIMES n < PRIMES (SUC n)

   [LEQ_DIVIDES_FACT]  Theorem

      |- ∀m n. 0 < m ∧ m ≤ n ⇒ divides m (FACT n)

   [LT_PRIMES]  Theorem

      |- ∀m n. m < n ⇒ PRIMES m < PRIMES n

   [NEXT_LARGER_PRIME]  Theorem

      |- ∀n. ∃i. n < PRIMES i ∧ ∀j. j < i ⇒ PRIMES j ≤ n

   [NOT_LT_DIVIDES]  Theorem

      |- ∀a b. 0 < b ∧ b < a ⇒ ¬divides a b

   [NOT_PRIME_0]  Theorem

      |- ¬prime 0

   [NOT_PRIME_1]  Theorem

      |- ¬prime 1

   [ONE_DIVIDES_ALL]  Theorem

      |- ∀a. divides 1 a

   [ONE_LT_PRIME]  Theorem

      |- ∀p. prime p ⇒ 1 < p

   [ONE_LT_PRIMES]  Theorem

      |- ∀n. 1 < PRIMES n

   [PRIMES_11]  Theorem

      |- ∀m n. (PRIMES m = PRIMES n) ⇒ (m = n)

   [PRIMES_NO_GAP]  Theorem

      |- ∀n p. PRIMES n < p ∧ p < PRIMES (SUC n) ∧ prime p ⇒ F

   [PRIMES_ONTO]  Theorem

      |- ∀p. prime p ⇒ ∃i. PRIMES i = p

   [PRIME_2]  Theorem

      |- prime 2

   [PRIME_3]  Theorem

      |- prime 3

   [PRIME_FACTOR]  Theorem

      |- ∀n. n ≠ 1 ⇒ ∃p. prime p ∧ divides p n

   [PRIME_INDEX]  Theorem

      |- ∀p. prime p ⇔ ∃i. p = PRIMES i

   [PRIME_POS]  Theorem

      |- ∀p. prime p ⇒ 0 < p

   [ZERO_DIVIDES]  Theorem

      |- divides 0 m ⇔ (m = 0)

   [ZERO_LT_PRIMES]  Theorem

      |- ∀n. 0 < PRIMES n

   [compute_divides]  Theorem

      |- ∀a b.
           divides a b ⇔
           if a = 0 then b = 0
           else if a = 1 then T
           else if b = 0 then T
           else b MOD a = 0

   [primePRIMES]  Theorem

      |- ∀n. prime (PRIMES n)

   [prime_divides_only_self]  Theorem

      |- ∀m n. prime m ∧ prime n ∧ divides m n ⇒ (m = n)


*)
end
