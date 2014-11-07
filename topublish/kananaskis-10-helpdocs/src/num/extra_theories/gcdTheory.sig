signature gcdTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val gcd_curried_def : thm
    val gcd_tupled_primitive_def : thm
    val is_gcd_def : thm
    val lcm_def : thm

  (*  Theorems  *)
    val BINARY_GCD : thm
    val FACTOR_OUT_GCD : thm
    val GCD_0L : thm
    val GCD_0R : thm
    val GCD_1 : thm
    val GCD_ADD_L : thm
    val GCD_ADD_L_THM : thm
    val GCD_ADD_R : thm
    val GCD_ADD_R_THM : thm
    val GCD_CANCEL_MULT : thm
    val GCD_COMMON_FACTOR : thm
    val GCD_EFFICIENTLY : thm
    val GCD_EQ_0 : thm
    val GCD_IS_GCD : thm
    val GCD_REF : thm
    val GCD_SUCfree_ind : thm
    val GCD_SYM : thm
    val IS_GCD_0L : thm
    val IS_GCD_0R : thm
    val IS_GCD_MINUS_L : thm
    val IS_GCD_MINUS_R : thm
    val IS_GCD_REF : thm
    val IS_GCD_SYM : thm
    val IS_GCD_UNIQUE : thm
    val LCM_0 : thm
    val LCM_1 : thm
    val LCM_COMM : thm
    val LCM_IS_LEAST_COMMON_MULTIPLE : thm
    val LCM_LE : thm
    val LCM_LEAST : thm
    val LINEAR_GCD : thm
    val L_EUCLIDES : thm
    val PRIME_GCD : thm
    val PRIME_IS_GCD : thm
    val P_EUCLIDES : thm
    val gcd_def : thm
    val gcd_def_compute : thm
    val gcd_ind : thm

  val gcd_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [basicSize] Parent theory of "gcd"

   [divides] Parent theory of "gcd"

   [gcd_curried_def]  Definition

      |- ∀x x1. gcd x x1 = gcd_tupled (x,x1)

   [gcd_tupled_primitive_def]  Definition

      |- gcd_tupled =
         WFREC
           (@R.
              WF R ∧ (∀x y. ¬(y ≤ x) ⇒ R (SUC x,y − x) (SUC x,SUC y)) ∧
              ∀x y. y ≤ x ⇒ R (x − y,SUC y) (SUC x,SUC y))
           (λgcd_tupled a.
              case a of
                (0,y) => I y
              | (SUC x,0) => I (SUC x)
              | (SUC x,SUC y') =>
                  I
                    (if y' ≤ x then gcd_tupled (x − y',SUC y')
                     else gcd_tupled (SUC x,y' − x)))

   [is_gcd_def]  Definition

      |- ∀a b c.
           is_gcd a b c ⇔
           divides c a ∧ divides c b ∧
           ∀d. divides d a ∧ divides d b ⇒ divides d c

   [lcm_def]  Definition

      |- ∀m n. lcm m n = if (m = 0) ∨ (n = 0) then 0 else m * n DIV gcd m n

   [BINARY_GCD]  Theorem

      |- ∀m n.
           (EVEN m ∧ EVEN n ⇒ (gcd m n = 2 * gcd (m DIV 2) (n DIV 2))) ∧
           (EVEN m ∧ ODD n ⇒ (gcd m n = gcd (m DIV 2) n))

   [FACTOR_OUT_GCD]  Theorem

      |- ∀n m.
           n ≠ 0 ∧ m ≠ 0 ⇒
           ∃p q. (n = p * gcd n m) ∧ (m = q * gcd n m) ∧ (gcd p q = 1)

   [GCD_0L]  Theorem

      |- ∀a. gcd 0 a = a

   [GCD_0R]  Theorem

      |- ∀a. gcd a 0 = a

   [GCD_1]  Theorem

      |- (gcd 1 x = 1) ∧ (gcd x 1 = 1)

   [GCD_ADD_L]  Theorem

      |- ∀a b. gcd (a + b) a = gcd a b

   [GCD_ADD_L_THM]  Theorem

      |- (∀a b. gcd (a + b) a = gcd a b) ∧ ∀a b. gcd (b + a) a = gcd a b

   [GCD_ADD_R]  Theorem

      |- ∀a b. gcd a (a + b) = gcd a b

   [GCD_ADD_R_THM]  Theorem

      |- (∀a b. gcd a (a + b) = gcd a b) ∧ ∀a b. gcd a (b + a) = gcd a b

   [GCD_CANCEL_MULT]  Theorem

      |- ∀m n k. (gcd m k = 1) ⇒ (gcd m (k * n) = gcd m n)

   [GCD_COMMON_FACTOR]  Theorem

      |- ∀m n k. gcd (k * m) (k * n) = k * gcd m n

   [GCD_EFFICIENTLY]  Theorem

      |- ∀a b. gcd a b = if a = 0 then b else gcd (b MOD a) a

   [GCD_EQ_0]  Theorem

      |- ∀n m. (gcd n m = 0) ⇔ (n = 0) ∧ (m = 0)

   [GCD_IS_GCD]  Theorem

      |- ∀a b. is_gcd a b (gcd a b)

   [GCD_REF]  Theorem

      |- ∀a. gcd a a = a

   [GCD_SUCfree_ind]  Theorem

      |- ∀P.
           (∀y. P 0 y) ∧ (∀x y. P x y ⇒ P y x) ∧ (∀x. P x x) ∧
           (∀x y. 0 < x ∧ 0 < y ∧ P x y ⇒ P x (x + y)) ⇒
           ∀m n. P m n

   [GCD_SYM]  Theorem

      |- ∀a b. gcd a b = gcd b a

   [IS_GCD_0L]  Theorem

      |- ∀a. is_gcd 0 a a

   [IS_GCD_0R]  Theorem

      |- ∀a. is_gcd a 0 a

   [IS_GCD_MINUS_L]  Theorem

      |- ∀a b c. b ≤ a ∧ is_gcd (a − b) b c ⇒ is_gcd a b c

   [IS_GCD_MINUS_R]  Theorem

      |- ∀a b c. a ≤ b ∧ is_gcd a (b − a) c ⇒ is_gcd a b c

   [IS_GCD_REF]  Theorem

      |- ∀a. is_gcd a a a

   [IS_GCD_SYM]  Theorem

      |- ∀a b c. is_gcd a b c ⇔ is_gcd b a c

   [IS_GCD_UNIQUE]  Theorem

      |- ∀a b c d. is_gcd a b c ∧ is_gcd a b d ⇒ (c = d)

   [LCM_0]  Theorem

      |- (lcm 0 x = 0) ∧ (lcm x 0 = 0)

   [LCM_1]  Theorem

      |- (lcm 1 x = x) ∧ (lcm x 1 = x)

   [LCM_COMM]  Theorem

      |- lcm a b = lcm b a

   [LCM_IS_LEAST_COMMON_MULTIPLE]  Theorem

      |- divides m (lcm m n) ∧ divides n (lcm m n) ∧
         ∀p. divides m p ∧ divides n p ⇒ divides (lcm m n) p

   [LCM_LE]  Theorem

      |- 0 < m ∧ 0 < n ⇒ m ≤ lcm m n ∧ m ≤ lcm n m

   [LCM_LEAST]  Theorem

      |- 0 < m ∧ 0 < n ⇒
         ∀p. 0 < p ∧ p < lcm m n ⇒ ¬divides m p ∨ ¬divides n p

   [LINEAR_GCD]  Theorem

      |- ∀n m. n ≠ 0 ⇒ ∃p q. p * n = q * m + gcd m n

   [L_EUCLIDES]  Theorem

      |- ∀a b c. (gcd a b = 1) ∧ divides b (a * c) ⇒ divides b c

   [PRIME_GCD]  Theorem

      |- ∀p b. prime p ⇒ divides p b ∨ (gcd p b = 1)

   [PRIME_IS_GCD]  Theorem

      |- ∀p b. prime p ⇒ divides p b ∨ is_gcd p b 1

   [P_EUCLIDES]  Theorem

      |- ∀p a b. prime p ∧ divides p (a * b) ⇒ divides p a ∨ divides p b

   [gcd_def]  Theorem

      |- (∀y. gcd 0 y = y) ∧ (∀x. gcd (SUC x) 0 = SUC x) ∧
         ∀y x.
           gcd (SUC x) (SUC y) =
           if y ≤ x then gcd (x − y) (SUC y) else gcd (SUC x) (y − x)

   [gcd_def_compute]  Theorem

      |- (∀y. gcd 0 y = y) ∧
         (∀x. gcd (NUMERAL (BIT1 x)) 0 = NUMERAL (BIT1 x)) ∧
         (∀x. gcd (NUMERAL (BIT2 x)) 0 = NUMERAL (BIT2 x)) ∧
         (∀y x.
            gcd (NUMERAL (BIT1 x)) (NUMERAL (BIT1 y)) =
            if NUMERAL (BIT1 y) − 1 ≤ NUMERAL (BIT1 x) − 1 then
              gcd (NUMERAL (BIT1 x) − 1 − (NUMERAL (BIT1 y) − 1))
                (NUMERAL (BIT1 y))
            else
              gcd (NUMERAL (BIT1 x))
                (NUMERAL (BIT1 y) − 1 − (NUMERAL (BIT1 x) − 1))) ∧
         (∀y x.
            gcd (NUMERAL (BIT2 x)) (NUMERAL (BIT1 y)) =
            if NUMERAL (BIT1 y) − 1 ≤ NUMERAL (BIT1 x) then
              gcd (NUMERAL (BIT1 x) − (NUMERAL (BIT1 y) − 1))
                (NUMERAL (BIT1 y))
            else
              gcd (NUMERAL (BIT2 x))
                (NUMERAL (BIT1 y) − 1 − NUMERAL (BIT1 x))) ∧
         (∀y x.
            gcd (NUMERAL (BIT1 x)) (NUMERAL (BIT2 y)) =
            if NUMERAL (BIT1 y) ≤ NUMERAL (BIT1 x) − 1 then
              gcd (NUMERAL (BIT1 x) − 1 − NUMERAL (BIT1 y))
                (NUMERAL (BIT2 y))
            else
              gcd (NUMERAL (BIT1 x))
                (NUMERAL (BIT1 y) − (NUMERAL (BIT1 x) − 1))) ∧
         ∀y x.
           gcd (NUMERAL (BIT2 x)) (NUMERAL (BIT2 y)) =
           if NUMERAL (BIT1 y) ≤ NUMERAL (BIT1 x) then
             gcd (NUMERAL (BIT1 x) − NUMERAL (BIT1 y)) (NUMERAL (BIT2 y))
           else
             gcd (NUMERAL (BIT2 x)) (NUMERAL (BIT1 y) − NUMERAL (BIT1 x))

   [gcd_ind]  Theorem

      |- ∀P.
           (∀y. P 0 y) ∧ (∀x. P (SUC x) 0) ∧
           (∀x y.
              (¬(y ≤ x) ⇒ P (SUC x) (y − x)) ∧
              (y ≤ x ⇒ P (x − y) (SUC y)) ⇒
              P (SUC x) (SUC y)) ⇒
           ∀v v1. P v v1


*)
end
