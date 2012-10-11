signature transcTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val Dint : thm
    val acs : thm
    val asn : thm
    val atn : thm
    val cos : thm
    val division : thm
    val dsize : thm
    val exp : thm
    val fine : thm
    val gauge : thm
    val ln : thm
    val pi : thm
    val root : thm
    val rpow_def : thm
    val rsum : thm
    val sin : thm
    val sqrt : thm
    val tan : thm
    val tdiv : thm

  (*  Theorems  *)
    val ACS : thm
    val ACS_BOUNDS : thm
    val ACS_BOUNDS_LT : thm
    val ACS_COS : thm
    val ASN : thm
    val ASN_BOUNDS : thm
    val ASN_BOUNDS_LT : thm
    val ASN_SIN : thm
    val ATN : thm
    val ATN_BOUNDS : thm
    val ATN_TAN : thm
    val BASE_RPOW_LE : thm
    val BASE_RPOW_LT : thm
    val COS_0 : thm
    val COS_2 : thm
    val COS_ACS : thm
    val COS_ADD : thm
    val COS_ASN_NZ : thm
    val COS_ATN_NZ : thm
    val COS_BOUND : thm
    val COS_BOUNDS : thm
    val COS_CONVERGES : thm
    val COS_DOUBLE : thm
    val COS_FDIFF : thm
    val COS_ISZERO : thm
    val COS_NEG : thm
    val COS_NPI : thm
    val COS_PAIRED : thm
    val COS_PERIODIC : thm
    val COS_PERIODIC_PI : thm
    val COS_PI : thm
    val COS_PI2 : thm
    val COS_POS_PI : thm
    val COS_POS_PI2 : thm
    val COS_POS_PI2_LE : thm
    val COS_POS_PI_LE : thm
    val COS_SIN : thm
    val COS_SIN_SQ : thm
    val COS_SIN_SQRT : thm
    val COS_TOTAL : thm
    val COS_ZERO : thm
    val COS_ZERO_LEMMA : thm
    val DIFF_ACS : thm
    val DIFF_ACS_LEMMA : thm
    val DIFF_ASN : thm
    val DIFF_ASN_LEMMA : thm
    val DIFF_ATN : thm
    val DIFF_COMPOSITE : thm
    val DIFF_COMPOSITE_EXP : thm
    val DIFF_COS : thm
    val DIFF_EXP : thm
    val DIFF_LN : thm
    val DIFF_LN_COMPOSITE : thm
    val DIFF_RPOW : thm
    val DIFF_SIN : thm
    val DIFF_TAN : thm
    val DINT_UNIQ : thm
    val DIVISION_0 : thm
    val DIVISION_1 : thm
    val DIVISION_APPEND : thm
    val DIVISION_EQ : thm
    val DIVISION_EXISTS : thm
    val DIVISION_GT : thm
    val DIVISION_LBOUND : thm
    val DIVISION_LBOUND_LT : thm
    val DIVISION_LE : thm
    val DIVISION_LHS : thm
    val DIVISION_LT : thm
    val DIVISION_LT_GEN : thm
    val DIVISION_RHS : thm
    val DIVISION_SINGLE : thm
    val DIVISION_THM : thm
    val DIVISION_UBOUND : thm
    val DIVISION_UBOUND_LT : thm
    val EXP_0 : thm
    val EXP_ADD : thm
    val EXP_ADD_MUL : thm
    val EXP_CONVERGES : thm
    val EXP_FDIFF : thm
    val EXP_INJ : thm
    val EXP_LE_X : thm
    val EXP_LN : thm
    val EXP_LT_1 : thm
    val EXP_MONO_IMP : thm
    val EXP_MONO_LE : thm
    val EXP_MONO_LT : thm
    val EXP_N : thm
    val EXP_NEG : thm
    val EXP_NEG_MUL : thm
    val EXP_NEG_MUL2 : thm
    val EXP_NZ : thm
    val EXP_POS_LE : thm
    val EXP_POS_LT : thm
    val EXP_SUB : thm
    val EXP_TOTAL : thm
    val EXP_TOTAL_LEMMA : thm
    val FINE_MIN : thm
    val FTC1 : thm
    val GAUGE_MIN : thm
    val GEN_RPOW : thm
    val INTEGRAL_NULL : thm
    val LN_1 : thm
    val LN_DIV : thm
    val LN_EXP : thm
    val LN_INJ : thm
    val LN_INV : thm
    val LN_LE : thm
    val LN_LT_X : thm
    val LN_MONO_LE : thm
    val LN_MONO_LT : thm
    val LN_MUL : thm
    val LN_POS : thm
    val LN_POW : thm
    val LN_RPOW : thm
    val MCLAURIN : thm
    val MCLAURIN_ALL_LE : thm
    val MCLAURIN_ALL_LT : thm
    val MCLAURIN_EXP_LE : thm
    val MCLAURIN_EXP_LT : thm
    val MCLAURIN_NEG : thm
    val MCLAURIN_ZERO : thm
    val ONE_RPOW : thm
    val PI2 : thm
    val PI2_BOUNDS : thm
    val PI_POS : thm
    val POW_2_SQRT : thm
    val POW_ROOT_POS : thm
    val REAL_DIV_SQRT : thm
    val ROOT_0 : thm
    val ROOT_1 : thm
    val ROOT_DIV : thm
    val ROOT_INV : thm
    val ROOT_LN : thm
    val ROOT_LT_LEMMA : thm
    val ROOT_MONO_LE : thm
    val ROOT_MUL : thm
    val ROOT_POS : thm
    val ROOT_POS_LT : thm
    val ROOT_POS_UNIQ : thm
    val ROOT_POW_POS : thm
    val RPOW_0 : thm
    val RPOW_1 : thm
    val RPOW_ADD : thm
    val RPOW_ADD_MUL : thm
    val RPOW_DIV : thm
    val RPOW_DIV_BASE : thm
    val RPOW_INV : thm
    val RPOW_LE : thm
    val RPOW_LT : thm
    val RPOW_MUL : thm
    val RPOW_NZ : thm
    val RPOW_POS_LT : thm
    val RPOW_RPOW : thm
    val RPOW_SUB : thm
    val RPOW_SUC_N : thm
    val RPOW_UNIQ_BASE : thm
    val RPOW_UNIQ_EXP : thm
    val SIN_0 : thm
    val SIN_ACS_NZ : thm
    val SIN_ADD : thm
    val SIN_ASN : thm
    val SIN_BOUND : thm
    val SIN_BOUNDS : thm
    val SIN_CIRCLE : thm
    val SIN_CONVERGES : thm
    val SIN_COS : thm
    val SIN_COS_ADD : thm
    val SIN_COS_NEG : thm
    val SIN_COS_SQ : thm
    val SIN_COS_SQRT : thm
    val SIN_DOUBLE : thm
    val SIN_FDIFF : thm
    val SIN_NEG : thm
    val SIN_NEGLEMMA : thm
    val SIN_NPI : thm
    val SIN_PAIRED : thm
    val SIN_PERIODIC : thm
    val SIN_PERIODIC_PI : thm
    val SIN_PI : thm
    val SIN_PI2 : thm
    val SIN_POS : thm
    val SIN_POS_PI : thm
    val SIN_POS_PI2 : thm
    val SIN_POS_PI2_LE : thm
    val SIN_POS_PI_LE : thm
    val SIN_TOTAL : thm
    val SIN_ZERO : thm
    val SIN_ZERO_LEMMA : thm
    val SQRT_0 : thm
    val SQRT_1 : thm
    val SQRT_DIV : thm
    val SQRT_EQ : thm
    val SQRT_EVEN_POW2 : thm
    val SQRT_INV : thm
    val SQRT_MONO_LE : thm
    val SQRT_MUL : thm
    val SQRT_POS_LE : thm
    val SQRT_POS_LT : thm
    val SQRT_POS_UNIQ : thm
    val SQRT_POW2 : thm
    val SQRT_POW_2 : thm
    val TAN_0 : thm
    val TAN_ADD : thm
    val TAN_ATN : thm
    val TAN_DOUBLE : thm
    val TAN_NEG : thm
    val TAN_NPI : thm
    val TAN_PERIODIC : thm
    val TAN_PI : thm
    val TAN_POS_PI2 : thm
    val TAN_SEC : thm
    val TAN_TOTAL : thm
    val TAN_TOTAL_LEMMA : thm
    val TAN_TOTAL_POS : thm

  val transc_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [powser] Parent theory of "transc"

   [Dint]  Definition

      |- ∀a b f k.
           Dint (a,b) f k ⇔
           ∀e.
             0 < e ⇒
             ∃g.
               gauge (λx. a ≤ x ∧ x ≤ b) g ∧
               ∀D p.
                 tdiv (a,b) (D,p) ∧ fine g (D,p) ⇒
                 abs (rsum (D,p) f − k) < e

   [acs]  Definition

      |- ∀y. acs y = @x. 0 ≤ x ∧ x ≤ pi ∧ (cos x = y)

   [asn]  Definition

      |- ∀y. asn y = @x. -(pi / 2) ≤ x ∧ x ≤ pi / 2 ∧ (sin x = y)

   [atn]  Definition

      |- ∀y. atn y = @x. -(pi / 2) < x ∧ x < pi / 2 ∧ (tan x = y)

   [cos]  Definition

      |- ∀x.
           cos x =
           suminf
             (λn.
                (λn. if EVEN n then -1 pow (n DIV 2) / &FACT n else 0) n *
                x pow n)

   [division]  Definition

      |- ∀a b D.
           division (a,b) D ⇔
           (D 0 = a) ∧
           ∃N. (∀n. n < N ⇒ D n < D (SUC n)) ∧ ∀n. n ≥ N ⇒ (D n = b)

   [dsize]  Definition

      |- ∀D.
           dsize D =
           @N. (∀n. n < N ⇒ D n < D (SUC n)) ∧ ∀n. n ≥ N ⇒ (D n = D N)

   [exp]  Definition

      |- ∀x. exp x = suminf (λn. (λn. inv (&FACT n)) n * x pow n)

   [fine]  Definition

      |- ∀g D p. fine g (D,p) ⇔ ∀n. n < dsize D ⇒ D (SUC n) − D n < g (p n)

   [gauge]  Definition

      |- ∀E g. gauge E g ⇔ ∀x. E x ⇒ 0 < g x

   [ln]  Definition

      |- ∀x. ln x = @u. exp u = x

   [pi]  Definition

      |- pi = 2 * @x. 0 ≤ x ∧ x ≤ 2 ∧ (cos x = 0)

   [root]  Definition

      |- ∀n x. root n x = @u. (0 < x ⇒ 0 < u) ∧ (u pow n = x)

   [rpow_def]  Definition

      |- ∀a b. a rpow b = exp (b * ln a)

   [rsum]  Definition

      |- ∀D p f.
           rsum (D,p) f = sum (0,dsize D) (λn. f (p n) * (D (SUC n) − D n))

   [sin]  Definition

      |- ∀x.
           sin x =
           suminf
             (λn.
                (λn.
                   if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &FACT n)
                  n * x pow n)

   [sqrt]  Definition

      |- ∀x. sqrt x = root 2 x

   [tan]  Definition

      |- ∀x. tan x = sin x / cos x

   [tdiv]  Definition

      |- ∀a b D p.
           tdiv (a,b) (D,p) ⇔
           division (a,b) D ∧ ∀n. D n ≤ p n ∧ p n ≤ D (SUC n)

   [ACS]  Theorem

      |- ∀y. -1 ≤ y ∧ y ≤ 1 ⇒ 0 ≤ acs y ∧ acs y ≤ pi ∧ (cos (acs y) = y)

   [ACS_BOUNDS]  Theorem

      |- ∀y. -1 ≤ y ∧ y ≤ 1 ⇒ 0 ≤ acs y ∧ acs y ≤ pi

   [ACS_BOUNDS_LT]  Theorem

      |- ∀y. -1 < y ∧ y < 1 ⇒ 0 < acs y ∧ acs y < pi

   [ACS_COS]  Theorem

      |- ∀y. -1 ≤ y ∧ y ≤ 1 ⇒ (cos (acs y) = y)

   [ASN]  Theorem

      |- ∀y.
           -1 ≤ y ∧ y ≤ 1 ⇒
           -(pi / 2) ≤ asn y ∧ asn y ≤ pi / 2 ∧ (sin (asn y) = y)

   [ASN_BOUNDS]  Theorem

      |- ∀y. -1 ≤ y ∧ y ≤ 1 ⇒ -(pi / 2) ≤ asn y ∧ asn y ≤ pi / 2

   [ASN_BOUNDS_LT]  Theorem

      |- ∀y. -1 < y ∧ y < 1 ⇒ -(pi / 2) < asn y ∧ asn y < pi / 2

   [ASN_SIN]  Theorem

      |- ∀y. -1 ≤ y ∧ y ≤ 1 ⇒ (sin (asn y) = y)

   [ATN]  Theorem

      |- ∀y. -(pi / 2) < atn y ∧ atn y < pi / 2 ∧ (tan (atn y) = y)

   [ATN_BOUNDS]  Theorem

      |- ∀y. -(pi / 2) < atn y ∧ atn y < pi / 2

   [ATN_TAN]  Theorem

      |- ∀y. tan (atn y) = y

   [BASE_RPOW_LE]  Theorem

      |- ∀a b c. 0 < a ∧ 0 < c ∧ 0 < b ⇒ (a rpow b ≤ c rpow b ⇔ a ≤ c)

   [BASE_RPOW_LT]  Theorem

      |- ∀a b c. 0 < a ∧ 0 < c ∧ 0 < b ⇒ (a rpow b < c rpow b ⇔ a < c)

   [COS_0]  Theorem

      |- cos 0 = 1

   [COS_2]  Theorem

      |- cos 2 < 0

   [COS_ACS]  Theorem

      |- ∀x. 0 ≤ x ∧ x ≤ pi ⇒ (acs (cos x) = x)

   [COS_ADD]  Theorem

      |- ∀x y. cos (x + y) = cos x * cos y − sin x * sin y

   [COS_ASN_NZ]  Theorem

      |- ∀x. -1 < x ∧ x < 1 ⇒ cos (asn x) ≠ 0

   [COS_ATN_NZ]  Theorem

      |- ∀x. cos (atn x) ≠ 0

   [COS_BOUND]  Theorem

      |- ∀x. abs (cos x) ≤ 1

   [COS_BOUNDS]  Theorem

      |- ∀x. -1 ≤ cos x ∧ cos x ≤ 1

   [COS_CONVERGES]  Theorem

      |- ∀x.
           (λn.
              (λn. if EVEN n then -1 pow (n DIV 2) / &FACT n else 0) n *
              x pow n) sums cos x

   [COS_DOUBLE]  Theorem

      |- ∀x. cos (2 * x) = cos x pow 2 − sin x pow 2

   [COS_FDIFF]  Theorem

      |- diffs (λn. if EVEN n then -1 pow (n DIV 2) / &FACT n else 0) =
         (λn.
            -(λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &FACT n)
               n)

   [COS_ISZERO]  Theorem

      |- ∃!x. 0 ≤ x ∧ x ≤ 2 ∧ (cos x = 0)

   [COS_NEG]  Theorem

      |- ∀x. cos (-x) = cos x

   [COS_NPI]  Theorem

      |- ∀n. cos (&n * pi) = -1 pow n

   [COS_PAIRED]  Theorem

      |- ∀x. (λn. -1 pow n / &FACT (2 * n) * x pow (2 * n)) sums cos x

   [COS_PERIODIC]  Theorem

      |- ∀x. cos (x + 2 * pi) = cos x

   [COS_PERIODIC_PI]  Theorem

      |- ∀x. cos (x + pi) = -cos x

   [COS_PI]  Theorem

      |- cos pi = -1

   [COS_PI2]  Theorem

      |- cos (pi / 2) = 0

   [COS_POS_PI]  Theorem

      |- ∀x. -(pi / 2) < x ∧ x < pi / 2 ⇒ 0 < cos x

   [COS_POS_PI2]  Theorem

      |- ∀x. 0 < x ∧ x < pi / 2 ⇒ 0 < cos x

   [COS_POS_PI2_LE]  Theorem

      |- ∀x. 0 ≤ x ∧ x ≤ pi / 2 ⇒ 0 ≤ cos x

   [COS_POS_PI_LE]  Theorem

      |- ∀x. -(pi / 2) ≤ x ∧ x ≤ pi / 2 ⇒ 0 ≤ cos x

   [COS_SIN]  Theorem

      |- ∀x. cos x = sin (pi / 2 − x)

   [COS_SIN_SQ]  Theorem

      |- ∀x. -(pi / 2) ≤ x ∧ x ≤ pi / 2 ⇒ (cos x = sqrt (1 − sin x pow 2))

   [COS_SIN_SQRT]  Theorem

      |- ∀x. 0 ≤ cos x ⇒ (cos x = sqrt (1 − sin x pow 2))

   [COS_TOTAL]  Theorem

      |- ∀y. -1 ≤ y ∧ y ≤ 1 ⇒ ∃!x. 0 ≤ x ∧ x ≤ pi ∧ (cos x = y)

   [COS_ZERO]  Theorem

      |- ∀x.
           (cos x = 0) ⇔
           (∃n. ¬EVEN n ∧ (x = &n * (pi / 2))) ∨
           ∃n. ¬EVEN n ∧ (x = -(&n * (pi / 2)))

   [COS_ZERO_LEMMA]  Theorem

      |- ∀x. 0 ≤ x ∧ (cos x = 0) ⇒ ∃n. ¬EVEN n ∧ (x = &n * (pi / 2))

   [DIFF_ACS]  Theorem

      |- ∀x. -1 < x ∧ x < 1 ⇒ (acs diffl -inv (sqrt (1 − x pow 2))) x

   [DIFF_ACS_LEMMA]  Theorem

      |- ∀x. -1 < x ∧ x < 1 ⇒ (acs diffl inv (-sin (acs x))) x

   [DIFF_ASN]  Theorem

      |- ∀x. -1 < x ∧ x < 1 ⇒ (asn diffl inv (sqrt (1 − x pow 2))) x

   [DIFF_ASN_LEMMA]  Theorem

      |- ∀x. -1 < x ∧ x < 1 ⇒ (asn diffl inv (cos (asn x))) x

   [DIFF_ATN]  Theorem

      |- ∀x. (atn diffl inv (1 + x pow 2)) x

   [DIFF_COMPOSITE]  Theorem

      |- ((f diffl l) x ∧ f x ≠ 0 ⇒
          ((λx. inv (f x)) diffl -(l / f x pow 2)) x) ∧
         ((f diffl l) x ∧ (g diffl m) x ∧ g x ≠ 0 ⇒
          ((λx. f x / g x) diffl ((l * g x − m * f x) / g x pow 2)) x) ∧
         ((f diffl l) x ∧ (g diffl m) x ⇒
          ((λx. f x + g x) diffl (l + m)) x) ∧
         ((f diffl l) x ∧ (g diffl m) x ⇒
          ((λx. f x * g x) diffl (l * g x + m * f x)) x) ∧
         ((f diffl l) x ∧ (g diffl m) x ⇒
          ((λx. f x − g x) diffl (l − m)) x) ∧
         ((f diffl l) x ⇒ ((λx. -f x) diffl -l) x) ∧
         ((g diffl m) x ⇒
          ((λx. g x pow n) diffl (&n * g x pow (n − 1) * m)) x) ∧
         ((g diffl m) x ⇒ ((λx. exp (g x)) diffl (exp (g x) * m)) x) ∧
         ((g diffl m) x ⇒ ((λx. sin (g x)) diffl (cos (g x) * m)) x) ∧
         ((g diffl m) x ⇒ ((λx. cos (g x)) diffl (-sin (g x) * m)) x)

   [DIFF_COMPOSITE_EXP]  Theorem

      |- ∀g m x. (g diffl m) x ⇒ ((λx. exp (g x)) diffl (exp (g x) * m)) x

   [DIFF_COS]  Theorem

      |- ∀x. (cos diffl -sin x) x

   [DIFF_EXP]  Theorem

      |- ∀x. (exp diffl exp x) x

   [DIFF_LN]  Theorem

      |- ∀x. 0 < x ⇒ (ln diffl inv x) x

   [DIFF_LN_COMPOSITE]  Theorem

      |- ∀g m x.
           (g diffl m) x ∧ 0 < g x ⇒
           ((λx. ln (g x)) diffl (inv (g x) * m)) x

   [DIFF_RPOW]  Theorem

      |- ∀x y. 0 < x ⇒ ((λx. x rpow y) diffl (y * x rpow (y − 1))) x

   [DIFF_SIN]  Theorem

      |- ∀x. (sin diffl cos x) x

   [DIFF_TAN]  Theorem

      |- ∀x. cos x ≠ 0 ⇒ (tan diffl inv (cos x pow 2)) x

   [DINT_UNIQ]  Theorem

      |- ∀a b f k1 k2.
           a ≤ b ∧ Dint (a,b) f k1 ∧ Dint (a,b) f k2 ⇒ (k1 = k2)

   [DIVISION_0]  Theorem

      |- ∀a b. (a = b) ⇒ (dsize (λn. if n = 0 then a else b) = 0)

   [DIVISION_1]  Theorem

      |- ∀a b. a < b ⇒ (dsize (λn. if n = 0 then a else b) = 1)

   [DIVISION_APPEND]  Theorem

      |- ∀a b c.
           (∃D1 p1. tdiv (a,b) (D1,p1) ∧ fine g (D1,p1)) ∧
           (∃D2 p2. tdiv (b,c) (D2,p2) ∧ fine g (D2,p2)) ⇒
           ∃D p. tdiv (a,c) (D,p) ∧ fine g (D,p)

   [DIVISION_EQ]  Theorem

      |- ∀D a b. division (a,b) D ⇒ ((a = b) ⇔ (dsize D = 0))

   [DIVISION_EXISTS]  Theorem

      |- ∀a b g.
           a ≤ b ∧ gauge (λx. a ≤ x ∧ x ≤ b) g ⇒
           ∃D p. tdiv (a,b) (D,p) ∧ fine g (D,p)

   [DIVISION_GT]  Theorem

      |- ∀D a b. division (a,b) D ⇒ ∀n. n < dsize D ⇒ D n < D (dsize D)

   [DIVISION_LBOUND]  Theorem

      |- ∀D a b. division (a,b) D ⇒ ∀r. a ≤ D r

   [DIVISION_LBOUND_LT]  Theorem

      |- ∀D a b. division (a,b) D ∧ dsize D ≠ 0 ⇒ ∀n. a < D (SUC n)

   [DIVISION_LE]  Theorem

      |- ∀D a b. division (a,b) D ⇒ a ≤ b

   [DIVISION_LHS]  Theorem

      |- ∀D a b. division (a,b) D ⇒ (D 0 = a)

   [DIVISION_LT]  Theorem

      |- ∀D a b. division (a,b) D ⇒ ∀n. n < dsize D ⇒ D 0 < D (SUC n)

   [DIVISION_LT_GEN]  Theorem

      |- ∀D a b m n. division (a,b) D ∧ m < n ∧ n ≤ dsize D ⇒ D m < D n

   [DIVISION_RHS]  Theorem

      |- ∀D a b. division (a,b) D ⇒ (D (dsize D) = b)

   [DIVISION_SINGLE]  Theorem

      |- ∀a b. a ≤ b ⇒ division (a,b) (λn. if n = 0 then a else b)

   [DIVISION_THM]  Theorem

      |- ∀D a b.
           division (a,b) D ⇔
           (D 0 = a) ∧ (∀n. n < dsize D ⇒ D n < D (SUC n)) ∧
           ∀n. n ≥ dsize D ⇒ (D n = b)

   [DIVISION_UBOUND]  Theorem

      |- ∀D a b. division (a,b) D ⇒ ∀r. D r ≤ b

   [DIVISION_UBOUND_LT]  Theorem

      |- ∀D a b n. division (a,b) D ∧ n < dsize D ⇒ D n < b

   [EXP_0]  Theorem

      |- exp 0 = 1

   [EXP_ADD]  Theorem

      |- ∀x y. exp (x + y) = exp x * exp y

   [EXP_ADD_MUL]  Theorem

      |- ∀x y. exp (x + y) * exp (-x) = exp y

   [EXP_CONVERGES]  Theorem

      |- ∀x. (λn. (λn. inv (&FACT n)) n * x pow n) sums exp x

   [EXP_FDIFF]  Theorem

      |- diffs (λn. inv (&FACT n)) = (λn. inv (&FACT n))

   [EXP_INJ]  Theorem

      |- ∀x y. (exp x = exp y) ⇔ (x = y)

   [EXP_LE_X]  Theorem

      |- ∀x. 0 ≤ x ⇒ 1 + x ≤ exp x

   [EXP_LN]  Theorem

      |- ∀x. (exp (ln x) = x) ⇔ 0 < x

   [EXP_LT_1]  Theorem

      |- ∀x. 0 < x ⇒ 1 < exp x

   [EXP_MONO_IMP]  Theorem

      |- ∀x y. x < y ⇒ exp x < exp y

   [EXP_MONO_LE]  Theorem

      |- ∀x y. exp x ≤ exp y ⇔ x ≤ y

   [EXP_MONO_LT]  Theorem

      |- ∀x y. exp x < exp y ⇔ x < y

   [EXP_N]  Theorem

      |- ∀n x. exp (&n * x) = exp x pow n

   [EXP_NEG]  Theorem

      |- ∀x. exp (-x) = inv (exp x)

   [EXP_NEG_MUL]  Theorem

      |- ∀x. exp x * exp (-x) = 1

   [EXP_NEG_MUL2]  Theorem

      |- ∀x. exp (-x) * exp x = 1

   [EXP_NZ]  Theorem

      |- ∀x. exp x ≠ 0

   [EXP_POS_LE]  Theorem

      |- ∀x. 0 ≤ exp x

   [EXP_POS_LT]  Theorem

      |- ∀x. 0 < exp x

   [EXP_SUB]  Theorem

      |- ∀x y. exp (x − y) = exp x / exp y

   [EXP_TOTAL]  Theorem

      |- ∀y. 0 < y ⇒ ∃x. exp x = y

   [EXP_TOTAL_LEMMA]  Theorem

      |- ∀y. 1 ≤ y ⇒ ∃x. 0 ≤ x ∧ x ≤ y − 1 ∧ (exp x = y)

   [FINE_MIN]  Theorem

      |- ∀g1 g2 D p.
           fine (λx. if g1 x < g2 x then g1 x else g2 x) (D,p) ⇒
           fine g1 (D,p) ∧ fine g2 (D,p)

   [FTC1]  Theorem

      |- ∀f f' a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ (f diffl f' x) x) ⇒
           Dint (a,b) f' (f b − f a)

   [GAUGE_MIN]  Theorem

      |- ∀E g1 g2.
           gauge E g1 ∧ gauge E g2 ⇒
           gauge E (λx. if g1 x < g2 x then g1 x else g2 x)

   [GEN_RPOW]  Theorem

      |- ∀a n. 0 < a ⇒ (a pow n = a rpow &n)

   [INTEGRAL_NULL]  Theorem

      |- ∀f a. Dint (a,a) f 0

   [LN_1]  Theorem

      |- ln 1 = 0

   [LN_DIV]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ (ln (x / y) = ln x − ln y)

   [LN_EXP]  Theorem

      |- ∀x. ln (exp x) = x

   [LN_INJ]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ ((ln x = ln y) ⇔ (x = y))

   [LN_INV]  Theorem

      |- ∀x. 0 < x ⇒ (ln (inv x) = -ln x)

   [LN_LE]  Theorem

      |- ∀x. 0 ≤ x ⇒ ln (1 + x) ≤ x

   [LN_LT_X]  Theorem

      |- ∀x. 0 < x ⇒ ln x < x

   [LN_MONO_LE]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ (ln x ≤ ln y ⇔ x ≤ y)

   [LN_MONO_LT]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ (ln x < ln y ⇔ x < y)

   [LN_MUL]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ (ln (x * y) = ln x + ln y)

   [LN_POS]  Theorem

      |- ∀x. 1 ≤ x ⇒ 0 ≤ ln x

   [LN_POW]  Theorem

      |- ∀n x. 0 < x ⇒ (ln (x pow n) = &n * ln x)

   [LN_RPOW]  Theorem

      |- ∀a b. 0 < a ⇒ (ln (a rpow b) = b * ln a)

   [MCLAURIN]  Theorem

      |- ∀f diff h n.
           0 < h ∧ 0 < n ∧ (diff 0 = f) ∧
           (∀m t.
              m < n ∧ 0 ≤ t ∧ t ≤ h ⇒ (diff m diffl diff (SUC m) t) t) ⇒
           ∃t.
             0 < t ∧ t < h ∧
             (f h =
              sum (0,n) (λm. diff m 0 / &FACT m * h pow m) +
              diff n t / &FACT n * h pow n)

   [MCLAURIN_ALL_LE]  Theorem

      |- ∀f diff.
           (diff 0 = f) ∧ (∀m x. (diff m diffl diff (SUC m) x) x) ⇒
           ∀x n.
             ∃t.
               abs t ≤ abs x ∧
               (f x =
                sum (0,n) (λm. diff m 0 / &FACT m * x pow m) +
                diff n t / &FACT n * x pow n)

   [MCLAURIN_ALL_LT]  Theorem

      |- ∀f diff.
           (diff 0 = f) ∧ (∀m x. (diff m diffl diff (SUC m) x) x) ⇒
           ∀x n.
             x ≠ 0 ∧ 0 < n ⇒
             ∃t.
               0 < abs t ∧ abs t < abs x ∧
               (f x =
                sum (0,n) (λm. diff m 0 / &FACT m * x pow m) +
                diff n t / &FACT n * x pow n)

   [MCLAURIN_EXP_LE]  Theorem

      |- ∀x n.
           ∃t.
             abs t ≤ abs x ∧
             (exp x =
              sum (0,n) (λm. x pow m / &FACT m) +
              exp t / &FACT n * x pow n)

   [MCLAURIN_EXP_LT]  Theorem

      |- ∀x n.
           x ≠ 0 ∧ 0 < n ⇒
           ∃t.
             0 < abs t ∧ abs t < abs x ∧
             (exp x =
              sum (0,n) (λm. x pow m / &FACT m) +
              exp t / &FACT n * x pow n)

   [MCLAURIN_NEG]  Theorem

      |- ∀f diff h n.
           h < 0 ∧ 0 < n ∧ (diff 0 = f) ∧
           (∀m t.
              m < n ∧ h ≤ t ∧ t ≤ 0 ⇒ (diff m diffl diff (SUC m) t) t) ⇒
           ∃t.
             h < t ∧ t < 0 ∧
             (f h =
              sum (0,n) (λm. diff m 0 / &FACT m * h pow m) +
              diff n t / &FACT n * h pow n)

   [MCLAURIN_ZERO]  Theorem

      |- ∀diff n x.
           (x = 0) ∧ 0 < n ⇒
           (sum (0,n) (λm. diff m 0 / &FACT m * x pow m) = diff 0 0)

   [ONE_RPOW]  Theorem

      |- ∀a. 0 < a ⇒ (1 rpow a = 1)

   [PI2]  Theorem

      |- pi / 2 = @x. 0 ≤ x ∧ x ≤ 2 ∧ (cos x = 0)

   [PI2_BOUNDS]  Theorem

      |- 0 < pi / 2 ∧ pi / 2 < 2

   [PI_POS]  Theorem

      |- 0 < pi

   [POW_2_SQRT]  Theorem

      |- 0 ≤ x ⇒ (sqrt (x pow 2) = x)

   [POW_ROOT_POS]  Theorem

      |- ∀n x. 0 ≤ x ⇒ (root (SUC n) (x pow SUC n) = x)

   [REAL_DIV_SQRT]  Theorem

      |- ∀x. 0 ≤ x ⇒ (x / sqrt x = sqrt x)

   [ROOT_0]  Theorem

      |- ∀n. root (SUC n) 0 = 0

   [ROOT_1]  Theorem

      |- ∀n. root (SUC n) 1 = 1

   [ROOT_DIV]  Theorem

      |- ∀n x y.
           0 ≤ x ∧ 0 ≤ y ⇒
           (root (SUC n) (x / y) = root (SUC n) x / root (SUC n) y)

   [ROOT_INV]  Theorem

      |- ∀n x. 0 ≤ x ⇒ (root (SUC n) (inv x) = inv (root (SUC n) x))

   [ROOT_LN]  Theorem

      |- ∀n x. 0 < x ⇒ (root (SUC n) x = exp (ln x / &SUC n))

   [ROOT_LT_LEMMA]  Theorem

      |- ∀n x. 0 < x ⇒ (exp (ln x / &SUC n) pow SUC n = x)

   [ROOT_MONO_LE]  Theorem

      |- ∀x y. 0 ≤ x ∧ x ≤ y ⇒ root (SUC n) x ≤ root (SUC n) y

   [ROOT_MUL]  Theorem

      |- ∀n x y.
           0 ≤ x ∧ 0 ≤ y ⇒
           (root (SUC n) (x * y) = root (SUC n) x * root (SUC n) y)

   [ROOT_POS]  Theorem

      |- ∀n x. 0 ≤ x ⇒ 0 ≤ root (SUC n) x

   [ROOT_POS_LT]  Theorem

      |- ∀n x. 0 < x ⇒ 0 < root (SUC n) x

   [ROOT_POS_UNIQ]  Theorem

      |- ∀n x y. 0 ≤ x ∧ 0 ≤ y ∧ (y pow SUC n = x) ⇒ (root (SUC n) x = y)

   [ROOT_POW_POS]  Theorem

      |- ∀n x. 0 ≤ x ⇒ (root (SUC n) x pow SUC n = x)

   [RPOW_0]  Theorem

      |- ∀a. 0 < a ⇒ (a rpow 0 = 1)

   [RPOW_1]  Theorem

      |- ∀a. 0 < a ⇒ (a rpow 1 = a)

   [RPOW_ADD]  Theorem

      |- ∀a b c. a rpow (b + c) = a rpow b * a rpow c

   [RPOW_ADD_MUL]  Theorem

      |- ∀a b c. a rpow (b + c) * a rpow -b = a rpow c

   [RPOW_DIV]  Theorem

      |- ∀a b c. 0 < a ∧ 0 < b ⇒ ((a / b) rpow c = a rpow c / b rpow c)

   [RPOW_DIV_BASE]  Theorem

      |- ∀x t. 0 < x ⇒ (x rpow t / x = x rpow (t − 1))

   [RPOW_INV]  Theorem

      |- ∀a b. 0 < a ⇒ (inv a rpow b = inv (a rpow b))

   [RPOW_LE]  Theorem

      |- ∀a b c. 1 < a ⇒ (a rpow b ≤ a rpow c ⇔ b ≤ c)

   [RPOW_LT]  Theorem

      |- ∀a b c. 1 < a ⇒ (a rpow b < a rpow c ⇔ b < c)

   [RPOW_MUL]  Theorem

      |- ∀a b c. 0 < a ∧ 0 < b ⇒ ((a * b) rpow c = a rpow c * b rpow c)

   [RPOW_NZ]  Theorem

      |- ∀a b. 0 ≠ a ⇒ a rpow b ≠ 0

   [RPOW_POS_LT]  Theorem

      |- ∀a b. 0 < a ⇒ 0 < a rpow b

   [RPOW_RPOW]  Theorem

      |- ∀a b c. 0 < a ⇒ ((a rpow b) rpow c = a rpow (b * c))

   [RPOW_SUB]  Theorem

      |- ∀a b c. a rpow (b − c) = a rpow b / a rpow c

   [RPOW_SUC_N]  Theorem

      |- ∀a n. 0 < a ⇒ (a rpow (&n + 1) = a pow SUC n)

   [RPOW_UNIQ_BASE]  Theorem

      |- ∀a b c. 0 < a ∧ 0 < c ∧ 0 ≠ b ∧ (a rpow b = c rpow b) ⇒ (a = c)

   [RPOW_UNIQ_EXP]  Theorem

      |- ∀a b c. 1 < a ∧ 0 < c ∧ 0 < b ∧ (a rpow b = a rpow c) ⇒ (b = c)

   [SIN_0]  Theorem

      |- sin 0 = 0

   [SIN_ACS_NZ]  Theorem

      |- ∀x. -1 < x ∧ x < 1 ⇒ sin (acs x) ≠ 0

   [SIN_ADD]  Theorem

      |- ∀x y. sin (x + y) = sin x * cos y + cos x * sin y

   [SIN_ASN]  Theorem

      |- ∀x. -(pi / 2) ≤ x ∧ x ≤ pi / 2 ⇒ (asn (sin x) = x)

   [SIN_BOUND]  Theorem

      |- ∀x. abs (sin x) ≤ 1

   [SIN_BOUNDS]  Theorem

      |- ∀x. -1 ≤ sin x ∧ sin x ≤ 1

   [SIN_CIRCLE]  Theorem

      |- ∀x. sin x pow 2 + cos x pow 2 = 1

   [SIN_CONVERGES]  Theorem

      |- ∀x.
           (λn.
              (λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &FACT n)
                n * x pow n) sums sin x

   [SIN_COS]  Theorem

      |- ∀x. sin x = cos (pi / 2 − x)

   [SIN_COS_ADD]  Theorem

      |- ∀x y.
           (sin (x + y) − (sin x * cos y + cos x * sin y)) pow 2 +
           (cos (x + y) − (cos x * cos y − sin x * sin y)) pow 2 =
           0

   [SIN_COS_NEG]  Theorem

      |- ∀x. (sin (-x) + sin x) pow 2 + (cos (-x) − cos x) pow 2 = 0

   [SIN_COS_SQ]  Theorem

      |- ∀x. 0 ≤ x ∧ x ≤ pi ⇒ (sin x = sqrt (1 − cos x pow 2))

   [SIN_COS_SQRT]  Theorem

      |- ∀x. 0 ≤ sin x ⇒ (sin x = sqrt (1 − cos x pow 2))

   [SIN_DOUBLE]  Theorem

      |- ∀x. sin (2 * x) = 2 * (sin x * cos x)

   [SIN_FDIFF]  Theorem

      |- diffs
           (λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &FACT n) =
         (λn. if EVEN n then -1 pow (n DIV 2) / &FACT n else 0)

   [SIN_NEG]  Theorem

      |- ∀x. sin (-x) = -sin x

   [SIN_NEGLEMMA]  Theorem

      |- ∀x.
           -sin x =
           suminf
             (λn.
                -((λn.
                     if EVEN n then
                       0
                     else
                       -1 pow ((n − 1) DIV 2) / &FACT n) n * x pow n))

   [SIN_NPI]  Theorem

      |- ∀n. sin (&n * pi) = 0

   [SIN_PAIRED]  Theorem

      |- ∀x.
           (λn. -1 pow n / &FACT (2 * n + 1) * x pow (2 * n + 1)) sums
           sin x

   [SIN_PERIODIC]  Theorem

      |- ∀x. sin (x + 2 * pi) = sin x

   [SIN_PERIODIC_PI]  Theorem

      |- ∀x. sin (x + pi) = -sin x

   [SIN_PI]  Theorem

      |- sin pi = 0

   [SIN_PI2]  Theorem

      |- sin (pi / 2) = 1

   [SIN_POS]  Theorem

      |- ∀x. 0 < x ∧ x < 2 ⇒ 0 < sin x

   [SIN_POS_PI]  Theorem

      |- ∀x. 0 < x ∧ x < pi ⇒ 0 < sin x

   [SIN_POS_PI2]  Theorem

      |- ∀x. 0 < x ∧ x < pi / 2 ⇒ 0 < sin x

   [SIN_POS_PI2_LE]  Theorem

      |- ∀x. 0 ≤ x ∧ x ≤ pi / 2 ⇒ 0 ≤ sin x

   [SIN_POS_PI_LE]  Theorem

      |- ∀x. 0 ≤ x ∧ x ≤ pi ⇒ 0 ≤ sin x

   [SIN_TOTAL]  Theorem

      |- ∀y. -1 ≤ y ∧ y ≤ 1 ⇒ ∃!x. -(pi / 2) ≤ x ∧ x ≤ pi / 2 ∧ (sin x = y)

   [SIN_ZERO]  Theorem

      |- ∀x.
           (sin x = 0) ⇔
           (∃n. EVEN n ∧ (x = &n * (pi / 2))) ∨
           ∃n. EVEN n ∧ (x = -(&n * (pi / 2)))

   [SIN_ZERO_LEMMA]  Theorem

      |- ∀x. 0 ≤ x ∧ (sin x = 0) ⇒ ∃n. EVEN n ∧ (x = &n * (pi / 2))

   [SQRT_0]  Theorem

      |- sqrt 0 = 0

   [SQRT_1]  Theorem

      |- sqrt 1 = 1

   [SQRT_DIV]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 ≤ y ⇒ (sqrt (x / y) = sqrt x / sqrt y)

   [SQRT_EQ]  Theorem

      |- ∀x y. (x pow 2 = y) ∧ 0 ≤ x ⇒ (x = sqrt y)

   [SQRT_EVEN_POW2]  Theorem

      |- ∀n. EVEN n ⇒ (sqrt (2 pow n) = 2 pow (n DIV 2))

   [SQRT_INV]  Theorem

      |- ∀x. 0 ≤ x ⇒ (sqrt (inv x) = inv (sqrt x))

   [SQRT_MONO_LE]  Theorem

      |- ∀x y. 0 ≤ x ∧ x ≤ y ⇒ sqrt x ≤ sqrt y

   [SQRT_MUL]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 ≤ y ⇒ (sqrt (x * y) = sqrt x * sqrt y)

   [SQRT_POS_LE]  Theorem

      |- ∀x. 0 ≤ x ⇒ 0 ≤ sqrt x

   [SQRT_POS_LT]  Theorem

      |- ∀x. 0 < x ⇒ 0 < sqrt x

   [SQRT_POS_UNIQ]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 ≤ y ∧ (y pow 2 = x) ⇒ (sqrt x = y)

   [SQRT_POW2]  Theorem

      |- ∀x. (sqrt x pow 2 = x) ⇔ 0 ≤ x

   [SQRT_POW_2]  Theorem

      |- ∀x. 0 ≤ x ⇒ (sqrt x pow 2 = x)

   [TAN_0]  Theorem

      |- tan 0 = 0

   [TAN_ADD]  Theorem

      |- ∀x y.
           cos x ≠ 0 ∧ cos y ≠ 0 ∧ cos (x + y) ≠ 0 ⇒
           (tan (x + y) = (tan x + tan y) / (1 − tan x * tan y))

   [TAN_ATN]  Theorem

      |- ∀x. -(pi / 2) < x ∧ x < pi / 2 ⇒ (atn (tan x) = x)

   [TAN_DOUBLE]  Theorem

      |- ∀x.
           cos x ≠ 0 ∧ cos (2 * x) ≠ 0 ⇒
           (tan (2 * x) = 2 * tan x / (1 − tan x pow 2))

   [TAN_NEG]  Theorem

      |- ∀x. tan (-x) = -tan x

   [TAN_NPI]  Theorem

      |- ∀n. tan (&n * pi) = 0

   [TAN_PERIODIC]  Theorem

      |- ∀x. tan (x + 2 * pi) = tan x

   [TAN_PI]  Theorem

      |- tan pi = 0

   [TAN_POS_PI2]  Theorem

      |- ∀x. 0 < x ∧ x < pi / 2 ⇒ 0 < tan x

   [TAN_SEC]  Theorem

      |- ∀x. cos x ≠ 0 ⇒ (1 + tan x pow 2 = inv (cos x) pow 2)

   [TAN_TOTAL]  Theorem

      |- ∀y. ∃!x. -(pi / 2) < x ∧ x < pi / 2 ∧ (tan x = y)

   [TAN_TOTAL_LEMMA]  Theorem

      |- ∀y. 0 < y ⇒ ∃x. 0 < x ∧ x < pi / 2 ∧ y < tan x

   [TAN_TOTAL_POS]  Theorem

      |- ∀y. 0 ≤ y ⇒ ∃x. 0 ≤ x ∧ x < pi / 2 ∧ (tan x = y)


*)
end
