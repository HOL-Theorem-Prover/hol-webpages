signature primeFactorTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val PRIME_FACTORS_def : thm

  (*  Theorems  *)
    val DIVISOR_IN_PRIME_FACTORS : thm
    val FACTORS_prime : thm
    val PRIME_FACTORIZATION : thm
    val PRIME_FACTORS_1 : thm
    val PRIME_FACTORS_EXIST : thm
    val PRIME_FACTORS_EXP : thm
    val PRIME_FACTORS_MULT : thm
    val PRIME_FACTOR_DIVIDES : thm
    val UNIQUE_PRIME_FACTORS : thm

  val primeFactor_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bag] Parent theory of "primeFactor"

   [gcd] Parent theory of "primeFactor"

   [PRIME_FACTORS_def]  Definition

      |- ∀n.
           0 < n ⇒
           FINITE_BAG (PRIME_FACTORS n) ∧
           (∀m. m ⋲ PRIME_FACTORS n ⇒ prime m) ∧
           (n = BAG_GEN_PROD (PRIME_FACTORS n) 1)

   [DIVISOR_IN_PRIME_FACTORS]  Theorem

      |- ∀p n. 0 < n ∧ prime p ∧ divides p n ⇒ p ⋲ PRIME_FACTORS n

   [FACTORS_prime]  Theorem

      |- ∀p. prime p ⇒ (PRIME_FACTORS p = {|p|})

   [PRIME_FACTORIZATION]  Theorem

      |- ∀n.
           0 < n ⇒
           ∀b.
             FINITE_BAG b ∧ (∀x. x ⋲ b ⇒ prime x) ∧
             (BAG_GEN_PROD b 1 = n) ⇒
             (b = PRIME_FACTORS n)

   [PRIME_FACTORS_1]  Theorem

      |- PRIME_FACTORS 1 = {||}

   [PRIME_FACTORS_EXIST]  Theorem

      |- ∀n.
           0 < n ⇒
           ∃b.
             FINITE_BAG b ∧ (∀m. m ⋲ b ⇒ prime m) ∧ (n = BAG_GEN_PROD b 1)

   [PRIME_FACTORS_EXP]  Theorem

      |- ∀p e. prime p ⇒ (PRIME_FACTORS (p ** e) p = e)

   [PRIME_FACTORS_MULT]  Theorem

      |- ∀a b.
           0 < a ∧ 0 < b ⇒
           (PRIME_FACTORS (a * b) = PRIME_FACTORS a ⊎ PRIME_FACTORS b)

   [PRIME_FACTOR_DIVIDES]  Theorem

      |- ∀x n. 0 < n ∧ x ⋲ PRIME_FACTORS n ⇒ divides x n

   [UNIQUE_PRIME_FACTORS]  Theorem

      |- ∀n b1 b2.
           (FINITE_BAG b1 ∧ (∀m. m ⋲ b1 ⇒ prime m) ∧
            (n = BAG_GEN_PROD b1 1)) ∧ FINITE_BAG b2 ∧
           (∀m. m ⋲ b2 ⇒ prime m) ∧ (n = BAG_GEN_PROD b2 1) ⇒
           (b1 = b2)


*)
end
