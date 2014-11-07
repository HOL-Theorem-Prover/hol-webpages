signature integralTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val integrable_def : thm
    val integral_def : thm

  (*  Theorems  *)
    val BOLZANO_LEMMA_ALT : thm
    val CONT_UNIFORM : thm
    val DINT_0 : thm
    val DINT_ADD : thm
    val DINT_CMUL : thm
    val DINT_COMBINE : thm
    val DINT_CONST : thm
    val DINT_DELTA : thm
    val DINT_DELTA_LEFT : thm
    val DINT_DELTA_RIGHT : thm
    val DINT_EQ : thm
    val DINT_FINITE_SPIKE : thm
    val DINT_INTEGRAL : thm
    val DINT_LE : thm
    val DINT_LINEAR : thm
    val DINT_NEG : thm
    val DINT_POINT_SPIKE : thm
    val DINT_SUB : thm
    val DINT_TRIANGLE : thm
    val DINT_WRONG : thm
    val DIVISION_APPEND : thm
    val DIVISION_APPEND_EXPLICIT : thm
    val DIVISION_APPEND_STRONG : thm
    val DIVISION_BOUNDS : thm
    val DIVISION_DSIZE_EQ : thm
    val DIVISION_DSIZE_EQ_ALT : thm
    val DIVISION_DSIZE_GE : thm
    val DIVISION_DSIZE_LE : thm
    val DIVISION_INTERMEDIATE : thm
    val DIVISION_LE_SUC : thm
    val DIVISION_MONO_LE : thm
    val DIVISION_MONO_LE_SUC : thm
    val DSIZE_EQ : thm
    val EQ_SUC : thm
    val GAUGE_MIN_FINITE : thm
    val INTEGRABLE_ADD : thm
    val INTEGRABLE_CAUCHY : thm
    val INTEGRABLE_CMUL : thm
    val INTEGRABLE_COMBINE : thm
    val INTEGRABLE_CONST : thm
    val INTEGRABLE_CONTINUOUS : thm
    val INTEGRABLE_DINT : thm
    val INTEGRABLE_LIMIT : thm
    val INTEGRABLE_POINT_SPIKE : thm
    val INTEGRABLE_SPLIT_SIDES : thm
    val INTEGRABLE_SUBINTERVAL : thm
    val INTEGRABLE_SUBINTERVAL_LEFT : thm
    val INTEGRABLE_SUBINTERVAL_RIGHT : thm
    val INTEGRAL_0 : thm
    val INTEGRAL_ADD : thm
    val INTEGRAL_BY_PARTS : thm
    val INTEGRAL_CMUL : thm
    val INTEGRAL_COMBINE : thm
    val INTEGRAL_CONST : thm
    val INTEGRAL_EQ : thm
    val INTEGRAL_LE : thm
    val INTEGRAL_MVT1 : thm
    val INTEGRAL_SUB : thm
    val INTEGRATION_BY_PARTS : thm
    val LE_0 : thm
    val LE_LT : thm
    val LT : thm
    val LT_0 : thm
    val LT_LE : thm
    val REAL_ARCH_POW : thm
    val REAL_ARCH_POW2 : thm
    val REAL_LE_INV2 : thm
    val REAL_LE_LMUL1 : thm
    val REAL_LE_RMUL1 : thm
    val REAL_LT_MIN : thm
    val REAL_POW_LBOUND : thm
    val REAL_POW_LE_1 : thm
    val REAL_POW_MONO : thm
    val RSUM_BOUND : thm
    val RSUM_DIFF_BOUND : thm
    val SUM_DIFFS : thm
    val SUM_EQ_0 : thm
    val SUM_SPLIT : thm
    val SUP_INTERVAL : thm
    val TDIV_BOUNDS : thm
    val TDIV_LE : thm
    val num_MAX : thm

  val integral_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [transc] Parent theory of "integral"

   [integrable_def]  Definition

      |- ∀a b f. integrable (a,b) f ⇔ ∃i. Dint (a,b) f i

   [integral_def]  Definition

      |- ∀a b f. integral (a,b) f = @i. Dint (a,b) f i

   [BOLZANO_LEMMA_ALT]  Theorem

      |- ∀P.
           (∀a b c. a ≤ b ∧ b ≤ c ∧ P a b ∧ P b c ⇒ P a c) ∧
           (∀x. ∃d. 0 < d ∧ ∀a b. a ≤ x ∧ x ≤ b ∧ b − a < d ⇒ P a b) ⇒
           ∀a b. a ≤ b ⇒ P a b

   [CONT_UNIFORM]  Theorem

      |- ∀f a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∀e.
             0 < e ⇒
             ∃d.
               0 < d ∧
               ∀x y.
                 a ≤ x ∧ x ≤ b ∧ a ≤ y ∧ y ≤ b ∧ abs (x − y) < d ⇒
                 abs (f x − f y) < e

   [DINT_0]  Theorem

      |- ∀a b. Dint (a,b) (λx. 0) 0

   [DINT_ADD]  Theorem

      |- ∀f g a b i j.
           Dint (a,b) f i ∧ Dint (a,b) g j ⇒
           Dint (a,b) (λx. f x + g x) (i + j)

   [DINT_CMUL]  Theorem

      |- ∀f a b c i. Dint (a,b) f i ⇒ Dint (a,b) (λx. c * f x) (c * i)

   [DINT_COMBINE]  Theorem

      |- ∀f a b c i j.
           a ≤ b ∧ b ≤ c ∧ Dint (a,b) f i ∧ Dint (b,c) f j ⇒
           Dint (a,c) f (i + j)

   [DINT_CONST]  Theorem

      |- ∀a b c. Dint (a,b) (λx. c) (c * (b − a))

   [DINT_DELTA]  Theorem

      |- ∀a b c. Dint (a,b) (λx. if x = c then 1 else 0) 0

   [DINT_DELTA_LEFT]  Theorem

      |- ∀a b. Dint (a,b) (λx. if x = a then 1 else 0) 0

   [DINT_DELTA_RIGHT]  Theorem

      |- ∀a b. Dint (a,b) (λx. if x = b then 1 else 0) 0

   [DINT_EQ]  Theorem

      |- ∀f g a b i j.
           a ≤ b ∧ Dint (a,b) f i ∧ Dint (a,b) g j ∧
           (∀x. a ≤ x ∧ x ≤ b ⇒ (f x = g x)) ⇒
           (i = j)

   [DINT_FINITE_SPIKE]  Theorem

      |- ∀f g a b s i.
           FINITE s ∧ (∀x. a ≤ x ∧ x ≤ b ∧ x ∉ s ⇒ (f x = g x)) ∧
           Dint (a,b) f i ⇒
           Dint (a,b) g i

   [DINT_INTEGRAL]  Theorem

      |- ∀f a b i. a ≤ b ∧ Dint (a,b) f i ⇒ (integral (a,b) f = i)

   [DINT_LE]  Theorem

      |- ∀f g a b i j.
           a ≤ b ∧ Dint (a,b) f i ∧ Dint (a,b) g j ∧
           (∀x. a ≤ x ∧ x ≤ b ⇒ f x ≤ g x) ⇒
           i ≤ j

   [DINT_LINEAR]  Theorem

      |- ∀f g a b i j.
           Dint (a,b) f i ∧ Dint (a,b) g j ⇒
           Dint (a,b) (λx. m * f x + n * g x) (m * i + n * j)

   [DINT_NEG]  Theorem

      |- ∀f a b i. Dint (a,b) f i ⇒ Dint (a,b) (λx. -f x) (-i)

   [DINT_POINT_SPIKE]  Theorem

      |- ∀f g a b c i.
           (∀x. a ≤ x ∧ x ≤ b ∧ x ≠ c ⇒ (f x = g x)) ∧ Dint (a,b) f i ⇒
           Dint (a,b) g i

   [DINT_SUB]  Theorem

      |- ∀f g a b i j.
           Dint (a,b) f i ∧ Dint (a,b) g j ⇒
           Dint (a,b) (λx. f x − g x) (i − j)

   [DINT_TRIANGLE]  Theorem

      |- ∀f a b i j.
           a ≤ b ∧ Dint (a,b) f i ∧ Dint (a,b) (λx. abs (f x)) j ⇒
           abs i ≤ j

   [DINT_WRONG]  Theorem

      |- ∀a b f i. b < a ⇒ Dint (a,b) f i

   [DIVISION_APPEND]  Theorem

      |- ∀a b c.
           (∃D1 p1. tdiv (a,b) (D1,p1) ∧ fine g (D1,p1)) ∧
           (∃D2 p2. tdiv (b,c) (D2,p2) ∧ fine g (D2,p2)) ⇒
           ∃D p. tdiv (a,c) (D,p) ∧ fine g (D,p)

   [DIVISION_APPEND_EXPLICIT]  Theorem

      |- ∀a b c g d1 p1 d2 p2.
           tdiv (a,b) (d1,p1) ∧ fine g (d1,p1) ∧ tdiv (b,c) (d2,p2) ∧
           fine g (d2,p2) ⇒
           tdiv (a,c)
             ((λn. if n < dsize d1 then d1 n else d2 (n − dsize d1)),
              (λn. if n < dsize d1 then p1 n else p2 (n − dsize d1))) ∧
           fine g
             ((λn. if n < dsize d1 then d1 n else d2 (n − dsize d1)),
              (λn. if n < dsize d1 then p1 n else p2 (n − dsize d1))) ∧
           ∀f.
             rsum
               ((λn. if n < dsize d1 then d1 n else d2 (n − dsize d1)),
                (λn. if n < dsize d1 then p1 n else p2 (n − dsize d1))) f =
             rsum (d1,p1) f + rsum (d2,p2) f

   [DIVISION_APPEND_STRONG]  Theorem

      |- ∀a b c D1 p1 D2 p2.
           tdiv (a,b) (D1,p1) ∧ fine g (D1,p1) ∧ tdiv (b,c) (D2,p2) ∧
           fine g (D2,p2) ⇒
           ∃D p.
             tdiv (a,c) (D,p) ∧ fine g (D,p) ∧
             ∀f. rsum (D,p) f = rsum (D1,p1) f + rsum (D2,p2) f

   [DIVISION_BOUNDS]  Theorem

      |- ∀d a b. division (a,b) d ⇒ ∀n. a ≤ d n ∧ d n ≤ b

   [DIVISION_DSIZE_EQ]  Theorem

      |- ∀a b d n.
           division (a,b) d ∧ d n < d (SUC n) ∧
           (d (SUC (SUC n)) = d (SUC n)) ⇒
           (dsize d = SUC n)

   [DIVISION_DSIZE_EQ_ALT]  Theorem

      |- ∀a b d n.
           division (a,b) d ∧ (d (SUC n) = d n) ∧
           (∀i. i < n ⇒ d i < d (SUC i)) ⇒
           (dsize d = n)

   [DIVISION_DSIZE_GE]  Theorem

      |- ∀a b d n. division (a,b) d ∧ d n < d (SUC n) ⇒ SUC n ≤ dsize d

   [DIVISION_DSIZE_LE]  Theorem

      |- ∀a b d n. division (a,b) d ∧ (d (SUC n) = d n) ⇒ dsize d ≤ n

   [DIVISION_INTERMEDIATE]  Theorem

      |- ∀d a b c.
           division (a,b) d ∧ a ≤ c ∧ c ≤ b ⇒
           ∃n. n ≤ dsize d ∧ d n ≤ c ∧ c ≤ d (SUC n)

   [DIVISION_LE_SUC]  Theorem

      |- ∀d a b. division (a,b) d ⇒ ∀n. d n ≤ d (SUC n)

   [DIVISION_MONO_LE]  Theorem

      |- ∀d a b. division (a,b) d ⇒ ∀m n. m ≤ n ⇒ d m ≤ d n

   [DIVISION_MONO_LE_SUC]  Theorem

      |- ∀d a b. division (a,b) d ⇒ ∀n. d n ≤ d (SUC n)

   [DSIZE_EQ]  Theorem

      |- ∀a b D.
           division (a,b) D ⇒
           (sum (0,dsize D) (λn. D (SUC n) − D n) − (b − a) = 0)

   [EQ_SUC]  Theorem

      |- ∀m n. (SUC m = SUC n) ⇔ (m = n)

   [GAUGE_MIN_FINITE]  Theorem

      |- ∀s gs n.
           (∀m. m ≤ n ⇒ gauge s (gs m)) ⇒
           ∃g.
             gauge s g ∧ ∀d p. fine g (d,p) ⇒ ∀m. m ≤ n ⇒ fine (gs m) (d,p)

   [INTEGRABLE_ADD]  Theorem

      |- ∀f g a b.
           a ≤ b ∧ integrable (a,b) f ∧ integrable (a,b) g ⇒
           integrable (a,b) (λx. f x + g x)

   [INTEGRABLE_CAUCHY]  Theorem

      |- ∀f a b.
           integrable (a,b) f ⇔
           ∀e.
             0 < e ⇒
             ∃g.
               gauge (λx. a ≤ x ∧ x ≤ b) g ∧
               ∀d1 p1 d2 p2.
                 tdiv (a,b) (d1,p1) ∧ fine g (d1,p1) ∧ tdiv (a,b) (d2,p2) ∧
                 fine g (d2,p2) ⇒
                 abs (rsum (d1,p1) f − rsum (d2,p2) f) < e

   [INTEGRABLE_CMUL]  Theorem

      |- ∀f a b c.
           a ≤ b ∧ integrable (a,b) f ⇒ integrable (a,b) (λx. c * f x)

   [INTEGRABLE_COMBINE]  Theorem

      |- ∀f a b c.
           a ≤ b ∧ b ≤ c ∧ integrable (a,b) f ∧ integrable (b,c) f ⇒
           integrable (a,c) f

   [INTEGRABLE_CONST]  Theorem

      |- ∀a b c. integrable (a,b) (λx. c)

   [INTEGRABLE_CONTINUOUS]  Theorem

      |- ∀f a b. (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒ integrable (a,b) f

   [INTEGRABLE_DINT]  Theorem

      |- ∀f a b. integrable (a,b) f ⇒ Dint (a,b) f (integral (a,b) f)

   [INTEGRABLE_LIMIT]  Theorem

      |- ∀f a b.
           (∀e.
              0 < e ⇒
              ∃g.
                (∀x. a ≤ x ∧ x ≤ b ⇒ abs (f x − g x) ≤ e) ∧
                integrable (a,b) g) ⇒
           integrable (a,b) f

   [INTEGRABLE_POINT_SPIKE]  Theorem

      |- ∀f g a b c.
           (∀x. a ≤ x ∧ x ≤ b ∧ x ≠ c ⇒ (f x = g x)) ∧ integrable (a,b) f ⇒
           integrable (a,b) g

   [INTEGRABLE_SPLIT_SIDES]  Theorem

      |- ∀f a b c.
           a ≤ c ∧ c ≤ b ∧ integrable (a,b) f ⇒
           ∃i.
             ∀e.
               0 < e ⇒
               ∃g.
                 gauge (λx. a ≤ x ∧ x ≤ b) g ∧
                 ∀d1 p1 d2 p2.
                   tdiv (a,c) (d1,p1) ∧ fine g (d1,p1) ∧
                   tdiv (c,b) (d2,p2) ∧ fine g (d2,p2) ⇒
                   abs (rsum (d1,p1) f + rsum (d2,p2) f − i) < e

   [INTEGRABLE_SUBINTERVAL]  Theorem

      |- ∀f a b c d.
           a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ integrable (a,b) f ⇒ integrable (c,d) f

   [INTEGRABLE_SUBINTERVAL_LEFT]  Theorem

      |- ∀f a b c. a ≤ c ∧ c ≤ b ∧ integrable (a,b) f ⇒ integrable (a,c) f

   [INTEGRABLE_SUBINTERVAL_RIGHT]  Theorem

      |- ∀f a b c. a ≤ c ∧ c ≤ b ∧ integrable (a,b) f ⇒ integrable (c,b) f

   [INTEGRAL_0]  Theorem

      |- ∀a b. a ≤ b ⇒ (integral (a,b) (λx. 0) = 0)

   [INTEGRAL_ADD]  Theorem

      |- ∀f g a b.
           a ≤ b ∧ integrable (a,b) f ∧ integrable (a,b) g ⇒
           (integral (a,b) (λx. f x + g x) =
            integral (a,b) f + integral (a,b) g)

   [INTEGRAL_BY_PARTS]  Theorem

      |- ∀f g f' g' a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ (f diffl f' x) x) ∧
           (∀x. a ≤ x ∧ x ≤ b ⇒ (g diffl g' x) x) ∧
           integrable (a,b) (λx. f' x * g x) ∧
           integrable (a,b) (λx. f x * g' x) ⇒
           (integral (a,b) (λx. f x * g' x) =
            f b * g b − f a * g a − integral (a,b) (λx. f' x * g x))

   [INTEGRAL_CMUL]  Theorem

      |- ∀f c a b.
           a ≤ b ∧ integrable (a,b) f ⇒
           (integral (a,b) (λx. c * f x) = c * integral (a,b) f)

   [INTEGRAL_COMBINE]  Theorem

      |- ∀f a b c.
           a ≤ b ∧ b ≤ c ∧ integrable (a,c) f ⇒
           (integral (a,c) f = integral (a,b) f + integral (b,c) f)

   [INTEGRAL_CONST]  Theorem

      |- ∀a b c. a ≤ b ⇒ (integral (a,b) (λx. c) = c * (b − a))

   [INTEGRAL_EQ]  Theorem

      |- ∀f g a b i.
           Dint (a,b) f i ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ (f x = g x)) ⇒
           Dint (a,b) g i

   [INTEGRAL_LE]  Theorem

      |- ∀f g a b i j.
           a ≤ b ∧ integrable (a,b) f ∧ integrable (a,b) g ∧
           (∀x. a ≤ x ∧ x ≤ b ⇒ f x ≤ g x) ⇒
           integral (a,b) f ≤ integral (a,b) g

   [INTEGRAL_MVT1]  Theorem

      |- ∀f a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∃x. a ≤ x ∧ x ≤ b ∧ (integral (a,b) f = f x * (b − a))

   [INTEGRAL_SUB]  Theorem

      |- ∀f g a b.
           a ≤ b ∧ integrable (a,b) f ∧ integrable (a,b) g ⇒
           (integral (a,b) (λx. f x − g x) =
            integral (a,b) f − integral (a,b) g)

   [INTEGRATION_BY_PARTS]  Theorem

      |- ∀f g f' g' a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ (f diffl f' x) x) ∧
           (∀x. a ≤ x ∧ x ≤ b ⇒ (g diffl g' x) x) ⇒
           Dint (a,b) (λx. f' x * g x + f x * g' x) (f b * g b − f a * g a)

   [LE_0]  Theorem

      |- ∀n. 0 ≤ n

   [LE_LT]  Theorem

      |- ∀m n. m ≤ n ⇔ m < n ∨ (m = n)

   [LT]  Theorem

      |- (∀m. m < 0 ⇔ F) ∧ ∀m n. m < SUC n ⇔ (m = n) ∨ m < n

   [LT_0]  Theorem

      |- ∀n. 0 < SUC n

   [LT_LE]  Theorem

      |- ∀m n. m < n ⇔ m ≤ n ∧ m ≠ n

   [REAL_ARCH_POW]  Theorem

      |- ∀x y. 1 < x ⇒ ∃n. y < x pow n

   [REAL_ARCH_POW2]  Theorem

      |- ∀x. ∃n. x < 2 pow n

   [REAL_LE_INV2]  Theorem

      |- ∀x y. 0 < x ∧ x ≤ y ⇒ inv y ≤ inv x

   [REAL_LE_LMUL1]  Theorem

      |- ∀x y z. 0 ≤ x ∧ y ≤ z ⇒ x * y ≤ x * z

   [REAL_LE_RMUL1]  Theorem

      |- ∀x y z. x ≤ y ∧ 0 ≤ z ⇒ x * z ≤ y * z

   [REAL_LT_MIN]  Theorem

      |- ∀x y z. z < min x y ⇔ z < x ∧ z < y

   [REAL_POW_LBOUND]  Theorem

      |- ∀x n. 0 ≤ x ⇒ 1 + &n * x ≤ (1 + x) pow n

   [REAL_POW_LE_1]  Theorem

      |- ∀n x. 1 ≤ x ⇒ 1 ≤ x pow n

   [REAL_POW_MONO]  Theorem

      |- ∀m n x. 1 ≤ x ∧ m ≤ n ⇒ x pow m ≤ x pow n

   [RSUM_BOUND]  Theorem

      |- ∀a b d p e f.
           tdiv (a,b) (d,p) ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ abs (f x) ≤ e) ⇒
           abs (rsum (d,p) f) ≤ e * (b − a)

   [RSUM_DIFF_BOUND]  Theorem

      |- ∀a b d p e f g.
           tdiv (a,b) (d,p) ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ abs (f x − g x) ≤ e) ⇒
           abs (rsum (d,p) f − rsum (d,p) g) ≤ e * (b − a)

   [SUM_DIFFS]  Theorem

      |- ∀m n. sum (m,n) (λi. d (SUC i) − d i) = d (m + n) − d m

   [SUM_EQ_0]  Theorem

      |- (∀r. m ≤ r ∧ r < m + n ⇒ (f r = 0)) ⇒ (sum (m,n) f = 0)

   [SUM_SPLIT]  Theorem

      |- ∀f n p. sum (m,n) f + sum (m + n,p) f = sum (m,n + p) f

   [SUP_INTERVAL]  Theorem

      |- ∀P a b.
           (∃x. a ≤ x ∧ x ≤ b ∧ P x) ⇒
           ∃s. a ≤ s ∧ s ≤ b ∧ ∀y. y < s ⇔ ∃x. a ≤ x ∧ x ≤ b ∧ P x ∧ y < x

   [TDIV_BOUNDS]  Theorem

      |- ∀d p a b.
           tdiv (a,b) (d,p) ⇒ ∀n. a ≤ d n ∧ d n ≤ b ∧ a ≤ p n ∧ p n ≤ b

   [TDIV_LE]  Theorem

      |- ∀d p a b. tdiv (a,b) (d,p) ⇒ a ≤ b

   [num_MAX]  Theorem

      |- ∀P. (∃x. P x) ∧ (∃M. ∀x. P x ⇒ x ≤ M) ⇔ ∃m. P m ∧ ∀x. P x ⇒ x ≤ m


*)
end
