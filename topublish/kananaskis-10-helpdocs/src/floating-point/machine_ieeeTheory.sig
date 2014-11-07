signature machine_ieeeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val float_to_fp16_def : thm
    val float_to_fp32_def : thm
    val float_to_fp64_def : thm
    val fp16_abs_def : thm
    val fp16_add_def : thm
    val fp16_bottom_def : thm
    val fp16_div_def : thm
    val fp16_equal_def : thm
    val fp16_greaterEqual_def : thm
    val fp16_greaterThan_def : thm
    val fp16_isFinite_def : thm
    val fp16_isInfinite_def : thm
    val fp16_isIntegral_def : thm
    val fp16_isNan_def : thm
    val fp16_isNormal_def : thm
    val fp16_isSubnormal_def : thm
    val fp16_isZero_def : thm
    val fp16_lessEqual_def : thm
    val fp16_lessThan_def : thm
    val fp16_mul_add_def : thm
    val fp16_mul_def : thm
    val fp16_negInf_def : thm
    val fp16_negMin_def : thm
    val fp16_negZero_def : thm
    val fp16_negate_def : thm
    val fp16_posInf_def : thm
    val fp16_posMin_def : thm
    val fp16_posZero_def : thm
    val fp16_roundToIntegral_def : thm
    val fp16_sqrt_def : thm
    val fp16_sub_def : thm
    val fp16_to_float_def : thm
    val fp16_to_real_def : thm
    val fp16_top_def : thm
    val fp32_abs_def : thm
    val fp32_add_def : thm
    val fp32_bottom_def : thm
    val fp32_div_def : thm
    val fp32_equal_def : thm
    val fp32_greaterEqual_def : thm
    val fp32_greaterThan_def : thm
    val fp32_isFinite_def : thm
    val fp32_isInfinite_def : thm
    val fp32_isIntegral_def : thm
    val fp32_isNan_def : thm
    val fp32_isNormal_def : thm
    val fp32_isSubnormal_def : thm
    val fp32_isZero_def : thm
    val fp32_lessEqual_def : thm
    val fp32_lessThan_def : thm
    val fp32_mul_add_def : thm
    val fp32_mul_def : thm
    val fp32_negInf_def : thm
    val fp32_negMin_def : thm
    val fp32_negZero_def : thm
    val fp32_negate_def : thm
    val fp32_posInf_def : thm
    val fp32_posMin_def : thm
    val fp32_posZero_def : thm
    val fp32_roundToIntegral_def : thm
    val fp32_sqrt_def : thm
    val fp32_sub_def : thm
    val fp32_to_float_def : thm
    val fp32_to_real_def : thm
    val fp32_top_def : thm
    val fp64_abs_def : thm
    val fp64_add_def : thm
    val fp64_bottom_def : thm
    val fp64_div_def : thm
    val fp64_equal_def : thm
    val fp64_greaterEqual_def : thm
    val fp64_greaterThan_def : thm
    val fp64_isFinite_def : thm
    val fp64_isInfinite_def : thm
    val fp64_isIntegral_def : thm
    val fp64_isNan_def : thm
    val fp64_isNormal_def : thm
    val fp64_isSubnormal_def : thm
    val fp64_isZero_def : thm
    val fp64_lessEqual_def : thm
    val fp64_lessThan_def : thm
    val fp64_mul_add_def : thm
    val fp64_mul_def : thm
    val fp64_negInf_def : thm
    val fp64_negMin_def : thm
    val fp64_negZero_def : thm
    val fp64_negate_def : thm
    val fp64_posInf_def : thm
    val fp64_posMin_def : thm
    val fp64_posZero_def : thm
    val fp64_roundToIntegral_def : thm
    val fp64_sqrt_def : thm
    val fp64_sub_def : thm
    val fp64_to_float_def : thm
    val fp64_to_real_def : thm
    val fp64_top_def : thm
    val real_to_fp16_def : thm
    val real_to_fp32_def : thm
    val real_to_fp64_def : thm

  (*  Theorems  *)
    val float_fp16_nchotomy : thm
    val float_fp32_nchotomy : thm
    val float_fp64_nchotomy : thm
    val float_to_fp16_11 : thm
    val float_to_fp16_fp16_to_float : thm
    val float_to_fp32_11 : thm
    val float_to_fp32_fp32_to_float : thm
    val float_to_fp64_11 : thm
    val float_to_fp64_fp64_to_float : thm
    val fp16_abs_float_to_fp : thm
    val fp16_abs_n2w : thm
    val fp16_add_float_to_fp : thm
    val fp16_add_n2w : thm
    val fp16_div_float_to_fp : thm
    val fp16_div_n2w : thm
    val fp16_equal_float_to_fp : thm
    val fp16_equal_n2w : thm
    val fp16_greaterEqual_float_to_fp : thm
    val fp16_greaterEqual_n2w : thm
    val fp16_greaterThan_float_to_fp : thm
    val fp16_greaterThan_n2w : thm
    val fp16_isFinite_float_to_fp : thm
    val fp16_isFinite_n2w : thm
    val fp16_isInfinite_float_to_fp : thm
    val fp16_isInfinite_n2w : thm
    val fp16_isIntegral_float_to_fp : thm
    val fp16_isIntegral_n2w : thm
    val fp16_isNan_float_to_fp : thm
    val fp16_isNan_n2w : thm
    val fp16_isNormal_float_to_fp : thm
    val fp16_isNormal_n2w : thm
    val fp16_isSubnormal_float_to_fp : thm
    val fp16_isSubnormal_n2w : thm
    val fp16_isZero_float_to_fp : thm
    val fp16_isZero_n2w : thm
    val fp16_lessEqual_float_to_fp : thm
    val fp16_lessEqual_n2w : thm
    val fp16_lessThan_float_to_fp : thm
    val fp16_lessThan_n2w : thm
    val fp16_mul_add_float_to_fp : thm
    val fp16_mul_add_n2w : thm
    val fp16_mul_float_to_fp : thm
    val fp16_mul_n2w : thm
    val fp16_nchotomy : thm
    val fp16_negate_float_to_fp : thm
    val fp16_negate_n2w : thm
    val fp16_roundToIntegral_float_to_fp : thm
    val fp16_roundToIntegral_n2w : thm
    val fp16_sqrt_float_to_fp : thm
    val fp16_sqrt_n2w : thm
    val fp16_sub_float_to_fp : thm
    val fp16_sub_n2w : thm
    val fp16_to_float_11 : thm
    val fp16_to_float_float_to_fp16 : thm
    val fp16_to_float_n2w : thm
    val fp16_to_real_float_to_fp : thm
    val fp16_to_real_n2w : thm
    val fp32_abs_float_to_fp : thm
    val fp32_abs_n2w : thm
    val fp32_add_float_to_fp : thm
    val fp32_add_n2w : thm
    val fp32_div_float_to_fp : thm
    val fp32_div_n2w : thm
    val fp32_equal_float_to_fp : thm
    val fp32_equal_n2w : thm
    val fp32_greaterEqual_float_to_fp : thm
    val fp32_greaterEqual_n2w : thm
    val fp32_greaterThan_float_to_fp : thm
    val fp32_greaterThan_n2w : thm
    val fp32_isFinite_float_to_fp : thm
    val fp32_isFinite_n2w : thm
    val fp32_isInfinite_float_to_fp : thm
    val fp32_isInfinite_n2w : thm
    val fp32_isIntegral_float_to_fp : thm
    val fp32_isIntegral_n2w : thm
    val fp32_isNan_float_to_fp : thm
    val fp32_isNan_n2w : thm
    val fp32_isNormal_float_to_fp : thm
    val fp32_isNormal_n2w : thm
    val fp32_isSubnormal_float_to_fp : thm
    val fp32_isSubnormal_n2w : thm
    val fp32_isZero_float_to_fp : thm
    val fp32_isZero_n2w : thm
    val fp32_lessEqual_float_to_fp : thm
    val fp32_lessEqual_n2w : thm
    val fp32_lessThan_float_to_fp : thm
    val fp32_lessThan_n2w : thm
    val fp32_mul_add_float_to_fp : thm
    val fp32_mul_add_n2w : thm
    val fp32_mul_float_to_fp : thm
    val fp32_mul_n2w : thm
    val fp32_nchotomy : thm
    val fp32_negate_float_to_fp : thm
    val fp32_negate_n2w : thm
    val fp32_roundToIntegral_float_to_fp : thm
    val fp32_roundToIntegral_n2w : thm
    val fp32_sqrt_float_to_fp : thm
    val fp32_sqrt_n2w : thm
    val fp32_sub_float_to_fp : thm
    val fp32_sub_n2w : thm
    val fp32_to_float_11 : thm
    val fp32_to_float_float_to_fp32 : thm
    val fp32_to_float_n2w : thm
    val fp32_to_real_float_to_fp : thm
    val fp32_to_real_n2w : thm
    val fp64_abs_float_to_fp : thm
    val fp64_abs_n2w : thm
    val fp64_add_float_to_fp : thm
    val fp64_add_n2w : thm
    val fp64_div_float_to_fp : thm
    val fp64_div_n2w : thm
    val fp64_equal_float_to_fp : thm
    val fp64_equal_n2w : thm
    val fp64_greaterEqual_float_to_fp : thm
    val fp64_greaterEqual_n2w : thm
    val fp64_greaterThan_float_to_fp : thm
    val fp64_greaterThan_n2w : thm
    val fp64_isFinite_float_to_fp : thm
    val fp64_isFinite_n2w : thm
    val fp64_isInfinite_float_to_fp : thm
    val fp64_isInfinite_n2w : thm
    val fp64_isIntegral_float_to_fp : thm
    val fp64_isIntegral_n2w : thm
    val fp64_isNan_float_to_fp : thm
    val fp64_isNan_n2w : thm
    val fp64_isNormal_float_to_fp : thm
    val fp64_isNormal_n2w : thm
    val fp64_isSubnormal_float_to_fp : thm
    val fp64_isSubnormal_n2w : thm
    val fp64_isZero_float_to_fp : thm
    val fp64_isZero_n2w : thm
    val fp64_lessEqual_float_to_fp : thm
    val fp64_lessEqual_n2w : thm
    val fp64_lessThan_float_to_fp : thm
    val fp64_lessThan_n2w : thm
    val fp64_mul_add_float_to_fp : thm
    val fp64_mul_add_n2w : thm
    val fp64_mul_float_to_fp : thm
    val fp64_mul_n2w : thm
    val fp64_nchotomy : thm
    val fp64_negate_float_to_fp : thm
    val fp64_negate_n2w : thm
    val fp64_roundToIntegral_float_to_fp : thm
    val fp64_roundToIntegral_n2w : thm
    val fp64_sqrt_float_to_fp : thm
    val fp64_sqrt_n2w : thm
    val fp64_sub_float_to_fp : thm
    val fp64_sub_n2w : thm
    val fp64_to_float_11 : thm
    val fp64_to_float_float_to_fp64 : thm
    val fp64_to_float_n2w : thm
    val fp64_to_real_float_to_fp : thm
    val fp64_to_real_n2w : thm

  val machine_ieee_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [binary_ieee] Parent theory of "machine_ieee"

   [float_to_fp16_def]  Definition

      |- ∀x. float_to_fp16 x = x.Sign @@ x.Exponent @@ x.Significand

   [float_to_fp32_def]  Definition

      |- ∀x. float_to_fp32 x = x.Sign @@ x.Exponent @@ x.Significand

   [float_to_fp64_def]  Definition

      |- ∀x. float_to_fp64 x = x.Sign @@ x.Exponent @@ x.Significand

   [fp16_abs_def]  Definition

      |- fp16_abs = float_to_fp16 o float_abs o fp16_to_float

   [fp16_add_def]  Definition

      |- ∀mode a b.
           fp16_add mode a b =
           float_to_fp16
             (float_add mode (fp16_to_float a) (fp16_to_float b))

   [fp16_bottom_def]  Definition

      |- fp16_bottom = float_to_fp16 (float_bottom (:10 # 5))

   [fp16_div_def]  Definition

      |- ∀mode a b.
           fp16_div mode a b =
           float_to_fp16
             (float_div mode (fp16_to_float a) (fp16_to_float b))

   [fp16_equal_def]  Definition

      |- ∀a b.
           fp16_equal a b ⇔ float_equal (fp16_to_float a) (fp16_to_float b)

   [fp16_greaterEqual_def]  Definition

      |- ∀a b.
           fp16_greaterEqual a b ⇔
           float_greater_equal (fp16_to_float a) (fp16_to_float b)

   [fp16_greaterThan_def]  Definition

      |- ∀a b.
           fp16_greaterThan a b ⇔
           float_greater_than (fp16_to_float a) (fp16_to_float b)

   [fp16_isFinite_def]  Definition

      |- fp16_isFinite = float_is_finite o fp16_to_float

   [fp16_isInfinite_def]  Definition

      |- fp16_isInfinite = float_is_infinite o fp16_to_float

   [fp16_isIntegral_def]  Definition

      |- fp16_isIntegral = float_is_integral o fp16_to_float

   [fp16_isNan_def]  Definition

      |- fp16_isNan = float_is_nan o fp16_to_float

   [fp16_isNormal_def]  Definition

      |- fp16_isNormal = float_is_normal o fp16_to_float

   [fp16_isSubnormal_def]  Definition

      |- fp16_isSubnormal = float_is_subnormal o fp16_to_float

   [fp16_isZero_def]  Definition

      |- fp16_isZero = float_is_zero o fp16_to_float

   [fp16_lessEqual_def]  Definition

      |- ∀a b.
           fp16_lessEqual a b ⇔
           float_less_equal (fp16_to_float a) (fp16_to_float b)

   [fp16_lessThan_def]  Definition

      |- ∀a b.
           fp16_lessThan a b ⇔
           float_less_than (fp16_to_float a) (fp16_to_float b)

   [fp16_mul_add_def]  Definition

      |- ∀mode a b c.
           fp16_mul_add mode a b c =
           float_to_fp16
             (float_mul_add mode (fp16_to_float a) (fp16_to_float b)
                (fp16_to_float c))

   [fp16_mul_def]  Definition

      |- ∀mode a b.
           fp16_mul mode a b =
           float_to_fp16
             (float_mul mode (fp16_to_float a) (fp16_to_float b))

   [fp16_negInf_def]  Definition

      |- fp16_negInf = float_to_fp16 (float_minus_infinity (:10 # 5))

   [fp16_negMin_def]  Definition

      |- fp16_negMin = float_to_fp16 (float_minus_min (:10 # 5))

   [fp16_negZero_def]  Definition

      |- fp16_negZero = float_to_fp16 (float_minus_zero (:10 # 5))

   [fp16_negate_def]  Definition

      |- fp16_negate = float_to_fp16 o float_negate o fp16_to_float

   [fp16_posInf_def]  Definition

      |- fp16_posInf = float_to_fp16 (float_plus_infinity (:10 # 5))

   [fp16_posMin_def]  Definition

      |- fp16_posMin = float_to_fp16 (float_plus_min (:10 # 5))

   [fp16_posZero_def]  Definition

      |- fp16_posZero = float_to_fp16 (float_plus_zero (:10 # 5))

   [fp16_roundToIntegral_def]  Definition

      |- ∀mode.
           fp16_roundToIntegral mode =
           float_to_fp16 o float_round_to_integral mode o fp16_to_float

   [fp16_sqrt_def]  Definition

      |- ∀mode.
           fp16_sqrt mode = float_to_fp16 o float_sqrt mode o fp16_to_float

   [fp16_sub_def]  Definition

      |- ∀mode a b.
           fp16_sub mode a b =
           float_to_fp16
             (float_sub mode (fp16_to_float a) (fp16_to_float b))

   [fp16_to_float_def]  Definition

      |- ∀w.
           fp16_to_float w =
           <|Sign := (15 >< 15) w; Exponent := (14 >< 10) w;
             Significand := (9 >< 0) w|>

   [fp16_to_real_def]  Definition

      |- fp16_to_real = float_to_real o fp16_to_float

   [fp16_top_def]  Definition

      |- fp16_top = float_to_fp16 (float_top (:10 # 5))

   [fp32_abs_def]  Definition

      |- fp32_abs = float_to_fp32 o float_abs o fp32_to_float

   [fp32_add_def]  Definition

      |- ∀mode a b.
           fp32_add mode a b =
           float_to_fp32
             (float_add mode (fp32_to_float a) (fp32_to_float b))

   [fp32_bottom_def]  Definition

      |- fp32_bottom = float_to_fp32 (float_bottom (:23 # 8))

   [fp32_div_def]  Definition

      |- ∀mode a b.
           fp32_div mode a b =
           float_to_fp32
             (float_div mode (fp32_to_float a) (fp32_to_float b))

   [fp32_equal_def]  Definition

      |- ∀a b.
           fp32_equal a b ⇔ float_equal (fp32_to_float a) (fp32_to_float b)

   [fp32_greaterEqual_def]  Definition

      |- ∀a b.
           fp32_greaterEqual a b ⇔
           float_greater_equal (fp32_to_float a) (fp32_to_float b)

   [fp32_greaterThan_def]  Definition

      |- ∀a b.
           fp32_greaterThan a b ⇔
           float_greater_than (fp32_to_float a) (fp32_to_float b)

   [fp32_isFinite_def]  Definition

      |- fp32_isFinite = float_is_finite o fp32_to_float

   [fp32_isInfinite_def]  Definition

      |- fp32_isInfinite = float_is_infinite o fp32_to_float

   [fp32_isIntegral_def]  Definition

      |- fp32_isIntegral = float_is_integral o fp32_to_float

   [fp32_isNan_def]  Definition

      |- fp32_isNan = float_is_nan o fp32_to_float

   [fp32_isNormal_def]  Definition

      |- fp32_isNormal = float_is_normal o fp32_to_float

   [fp32_isSubnormal_def]  Definition

      |- fp32_isSubnormal = float_is_subnormal o fp32_to_float

   [fp32_isZero_def]  Definition

      |- fp32_isZero = float_is_zero o fp32_to_float

   [fp32_lessEqual_def]  Definition

      |- ∀a b.
           fp32_lessEqual a b ⇔
           float_less_equal (fp32_to_float a) (fp32_to_float b)

   [fp32_lessThan_def]  Definition

      |- ∀a b.
           fp32_lessThan a b ⇔
           float_less_than (fp32_to_float a) (fp32_to_float b)

   [fp32_mul_add_def]  Definition

      |- ∀mode a b c.
           fp32_mul_add mode a b c =
           float_to_fp32
             (float_mul_add mode (fp32_to_float a) (fp32_to_float b)
                (fp32_to_float c))

   [fp32_mul_def]  Definition

      |- ∀mode a b.
           fp32_mul mode a b =
           float_to_fp32
             (float_mul mode (fp32_to_float a) (fp32_to_float b))

   [fp32_negInf_def]  Definition

      |- fp32_negInf = float_to_fp32 (float_minus_infinity (:23 # 8))

   [fp32_negMin_def]  Definition

      |- fp32_negMin = float_to_fp32 (float_minus_min (:23 # 8))

   [fp32_negZero_def]  Definition

      |- fp32_negZero = float_to_fp32 (float_minus_zero (:23 # 8))

   [fp32_negate_def]  Definition

      |- fp32_negate = float_to_fp32 o float_negate o fp32_to_float

   [fp32_posInf_def]  Definition

      |- fp32_posInf = float_to_fp32 (float_plus_infinity (:23 # 8))

   [fp32_posMin_def]  Definition

      |- fp32_posMin = float_to_fp32 (float_plus_min (:23 # 8))

   [fp32_posZero_def]  Definition

      |- fp32_posZero = float_to_fp32 (float_plus_zero (:23 # 8))

   [fp32_roundToIntegral_def]  Definition

      |- ∀mode.
           fp32_roundToIntegral mode =
           float_to_fp32 o float_round_to_integral mode o fp32_to_float

   [fp32_sqrt_def]  Definition

      |- ∀mode.
           fp32_sqrt mode = float_to_fp32 o float_sqrt mode o fp32_to_float

   [fp32_sub_def]  Definition

      |- ∀mode a b.
           fp32_sub mode a b =
           float_to_fp32
             (float_sub mode (fp32_to_float a) (fp32_to_float b))

   [fp32_to_float_def]  Definition

      |- ∀w.
           fp32_to_float w =
           <|Sign := (31 >< 31) w; Exponent := (30 >< 23) w;
             Significand := (22 >< 0) w|>

   [fp32_to_real_def]  Definition

      |- fp32_to_real = float_to_real o fp32_to_float

   [fp32_top_def]  Definition

      |- fp32_top = float_to_fp32 (float_top (:23 # 8))

   [fp64_abs_def]  Definition

      |- fp64_abs = float_to_fp64 o float_abs o fp64_to_float

   [fp64_add_def]  Definition

      |- ∀mode a b.
           fp64_add mode a b =
           float_to_fp64
             (float_add mode (fp64_to_float a) (fp64_to_float b))

   [fp64_bottom_def]  Definition

      |- fp64_bottom = float_to_fp64 (float_bottom (:52 # 11))

   [fp64_div_def]  Definition

      |- ∀mode a b.
           fp64_div mode a b =
           float_to_fp64
             (float_div mode (fp64_to_float a) (fp64_to_float b))

   [fp64_equal_def]  Definition

      |- ∀a b.
           fp64_equal a b ⇔ float_equal (fp64_to_float a) (fp64_to_float b)

   [fp64_greaterEqual_def]  Definition

      |- ∀a b.
           fp64_greaterEqual a b ⇔
           float_greater_equal (fp64_to_float a) (fp64_to_float b)

   [fp64_greaterThan_def]  Definition

      |- ∀a b.
           fp64_greaterThan a b ⇔
           float_greater_than (fp64_to_float a) (fp64_to_float b)

   [fp64_isFinite_def]  Definition

      |- fp64_isFinite = float_is_finite o fp64_to_float

   [fp64_isInfinite_def]  Definition

      |- fp64_isInfinite = float_is_infinite o fp64_to_float

   [fp64_isIntegral_def]  Definition

      |- fp64_isIntegral = float_is_integral o fp64_to_float

   [fp64_isNan_def]  Definition

      |- fp64_isNan = float_is_nan o fp64_to_float

   [fp64_isNormal_def]  Definition

      |- fp64_isNormal = float_is_normal o fp64_to_float

   [fp64_isSubnormal_def]  Definition

      |- fp64_isSubnormal = float_is_subnormal o fp64_to_float

   [fp64_isZero_def]  Definition

      |- fp64_isZero = float_is_zero o fp64_to_float

   [fp64_lessEqual_def]  Definition

      |- ∀a b.
           fp64_lessEqual a b ⇔
           float_less_equal (fp64_to_float a) (fp64_to_float b)

   [fp64_lessThan_def]  Definition

      |- ∀a b.
           fp64_lessThan a b ⇔
           float_less_than (fp64_to_float a) (fp64_to_float b)

   [fp64_mul_add_def]  Definition

      |- ∀mode a b c.
           fp64_mul_add mode a b c =
           float_to_fp64
             (float_mul_add mode (fp64_to_float a) (fp64_to_float b)
                (fp64_to_float c))

   [fp64_mul_def]  Definition

      |- ∀mode a b.
           fp64_mul mode a b =
           float_to_fp64
             (float_mul mode (fp64_to_float a) (fp64_to_float b))

   [fp64_negInf_def]  Definition

      |- fp64_negInf = float_to_fp64 (float_minus_infinity (:52 # 11))

   [fp64_negMin_def]  Definition

      |- fp64_negMin = float_to_fp64 (float_minus_min (:52 # 11))

   [fp64_negZero_def]  Definition

      |- fp64_negZero = float_to_fp64 (float_minus_zero (:52 # 11))

   [fp64_negate_def]  Definition

      |- fp64_negate = float_to_fp64 o float_negate o fp64_to_float

   [fp64_posInf_def]  Definition

      |- fp64_posInf = float_to_fp64 (float_plus_infinity (:52 # 11))

   [fp64_posMin_def]  Definition

      |- fp64_posMin = float_to_fp64 (float_plus_min (:52 # 11))

   [fp64_posZero_def]  Definition

      |- fp64_posZero = float_to_fp64 (float_plus_zero (:52 # 11))

   [fp64_roundToIntegral_def]  Definition

      |- ∀mode.
           fp64_roundToIntegral mode =
           float_to_fp64 o float_round_to_integral mode o fp64_to_float

   [fp64_sqrt_def]  Definition

      |- ∀mode.
           fp64_sqrt mode = float_to_fp64 o float_sqrt mode o fp64_to_float

   [fp64_sub_def]  Definition

      |- ∀mode a b.
           fp64_sub mode a b =
           float_to_fp64
             (float_sub mode (fp64_to_float a) (fp64_to_float b))

   [fp64_to_float_def]  Definition

      |- ∀w.
           fp64_to_float w =
           <|Sign := (63 >< 63) w; Exponent := (62 >< 52) w;
             Significand := (51 >< 0) w|>

   [fp64_to_real_def]  Definition

      |- fp64_to_real = float_to_real o fp64_to_float

   [fp64_top_def]  Definition

      |- fp64_top = float_to_fp64 (float_top (:52 # 11))

   [real_to_fp16_def]  Definition

      |- ∀mode. real_to_fp16 mode = float_to_fp16 o round mode

   [real_to_fp32_def]  Definition

      |- ∀mode. real_to_fp32 mode = float_to_fp32 o round mode

   [real_to_fp64_def]  Definition

      |- ∀mode. real_to_fp64 mode = float_to_fp64 o round mode

   [float_fp16_nchotomy]  Theorem

      |- ∀x. ∃y. x = fp16_to_float y

   [float_fp32_nchotomy]  Theorem

      |- ∀x. ∃y. x = fp32_to_float y

   [float_fp64_nchotomy]  Theorem

      |- ∀x. ∃y. x = fp64_to_float y

   [float_to_fp16_11]  Theorem

      |- ∀x y. (float_to_fp16 x = float_to_fp16 y) ⇔ (x = y)

   [float_to_fp16_fp16_to_float]  Theorem

      |- ∀x. float_to_fp16 (fp16_to_float x) = x

   [float_to_fp32_11]  Theorem

      |- ∀x y. (float_to_fp32 x = float_to_fp32 y) ⇔ (x = y)

   [float_to_fp32_fp32_to_float]  Theorem

      |- ∀x. float_to_fp32 (fp32_to_float x) = x

   [float_to_fp64_11]  Theorem

      |- ∀x y. (float_to_fp64 x = float_to_fp64 y) ⇔ (x = y)

   [float_to_fp64_fp64_to_float]  Theorem

      |- ∀x. float_to_fp64 (fp64_to_float x) = x

   [fp16_abs_float_to_fp]  Theorem

      |- ∀a. fp16_abs (float_to_fp16 a) = float_to_fp16 (float_abs a)

   [fp16_abs_n2w]  Theorem

      |- ∀a.
           fp16_abs (n2w a) =
           float_to_fp16 (float_abs (fp16_to_float (n2w a)))

   [fp16_add_float_to_fp]  Theorem

      |- ∀mode b a.
           fp16_add mode (float_to_fp16 a) (float_to_fp16 b) =
           float_to_fp16 (float_add mode a b)

   [fp16_add_n2w]  Theorem

      |- ∀mode b a.
           fp16_add mode (n2w a) (n2w b) =
           float_to_fp16
             (float_add mode (fp16_to_float (n2w a))
                (fp16_to_float (n2w b)))

   [fp16_div_float_to_fp]  Theorem

      |- ∀mode b a.
           fp16_div mode (float_to_fp16 a) (float_to_fp16 b) =
           float_to_fp16 (float_div mode a b)

   [fp16_div_n2w]  Theorem

      |- ∀mode b a.
           fp16_div mode (n2w a) (n2w b) =
           float_to_fp16
             (float_div mode (fp16_to_float (n2w a))
                (fp16_to_float (n2w b)))

   [fp16_equal_float_to_fp]  Theorem

      |- ∀b a.
           fp16_equal (float_to_fp16 a) (float_to_fp16 b) ⇔ float_equal a b

   [fp16_equal_n2w]  Theorem

      |- ∀b a.
           fp16_equal (n2w a) (n2w b) ⇔
           float_equal (fp16_to_float (n2w a)) (fp16_to_float (n2w b))

   [fp16_greaterEqual_float_to_fp]  Theorem

      |- ∀b a.
           fp16_greaterEqual (float_to_fp16 a) (float_to_fp16 b) ⇔
           float_greater_equal a b

   [fp16_greaterEqual_n2w]  Theorem

      |- ∀b a.
           fp16_greaterEqual (n2w a) (n2w b) ⇔
           float_greater_equal (fp16_to_float (n2w a))
             (fp16_to_float (n2w b))

   [fp16_greaterThan_float_to_fp]  Theorem

      |- ∀b a.
           fp16_greaterThan (float_to_fp16 a) (float_to_fp16 b) ⇔
           float_greater_than a b

   [fp16_greaterThan_n2w]  Theorem

      |- ∀b a.
           fp16_greaterThan (n2w a) (n2w b) ⇔
           float_greater_than (fp16_to_float (n2w a))
             (fp16_to_float (n2w b))

   [fp16_isFinite_float_to_fp]  Theorem

      |- ∀a. fp16_isFinite (float_to_fp16 a) ⇔ float_is_finite a

   [fp16_isFinite_n2w]  Theorem

      |- ∀a.
           fp16_isFinite (n2w a) ⇔ float_is_finite (fp16_to_float (n2w a))

   [fp16_isInfinite_float_to_fp]  Theorem

      |- ∀a. fp16_isInfinite (float_to_fp16 a) ⇔ float_is_infinite a

   [fp16_isInfinite_n2w]  Theorem

      |- ∀a.
           fp16_isInfinite (n2w a) ⇔
           float_is_infinite (fp16_to_float (n2w a))

   [fp16_isIntegral_float_to_fp]  Theorem

      |- ∀a. fp16_isIntegral (float_to_fp16 a) ⇔ float_is_integral a

   [fp16_isIntegral_n2w]  Theorem

      |- ∀a.
           fp16_isIntegral (n2w a) ⇔
           float_is_integral (fp16_to_float (n2w a))

   [fp16_isNan_float_to_fp]  Theorem

      |- ∀a. fp16_isNan (float_to_fp16 a) ⇔ float_is_nan a

   [fp16_isNan_n2w]  Theorem

      |- ∀a. fp16_isNan (n2w a) ⇔ float_is_nan (fp16_to_float (n2w a))

   [fp16_isNormal_float_to_fp]  Theorem

      |- ∀a. fp16_isNormal (float_to_fp16 a) ⇔ float_is_normal a

   [fp16_isNormal_n2w]  Theorem

      |- ∀a.
           fp16_isNormal (n2w a) ⇔ float_is_normal (fp16_to_float (n2w a))

   [fp16_isSubnormal_float_to_fp]  Theorem

      |- ∀a. fp16_isSubnormal (float_to_fp16 a) ⇔ float_is_subnormal a

   [fp16_isSubnormal_n2w]  Theorem

      |- ∀a.
           fp16_isSubnormal (n2w a) ⇔
           float_is_subnormal (fp16_to_float (n2w a))

   [fp16_isZero_float_to_fp]  Theorem

      |- ∀a. fp16_isZero (float_to_fp16 a) ⇔ float_is_zero a

   [fp16_isZero_n2w]  Theorem

      |- ∀a. fp16_isZero (n2w a) ⇔ float_is_zero (fp16_to_float (n2w a))

   [fp16_lessEqual_float_to_fp]  Theorem

      |- ∀b a.
           fp16_lessEqual (float_to_fp16 a) (float_to_fp16 b) ⇔
           float_less_equal a b

   [fp16_lessEqual_n2w]  Theorem

      |- ∀b a.
           fp16_lessEqual (n2w a) (n2w b) ⇔
           float_less_equal (fp16_to_float (n2w a)) (fp16_to_float (n2w b))

   [fp16_lessThan_float_to_fp]  Theorem

      |- ∀b a.
           fp16_lessThan (float_to_fp16 a) (float_to_fp16 b) ⇔
           float_less_than a b

   [fp16_lessThan_n2w]  Theorem

      |- ∀b a.
           fp16_lessThan (n2w a) (n2w b) ⇔
           float_less_than (fp16_to_float (n2w a)) (fp16_to_float (n2w b))

   [fp16_mul_add_float_to_fp]  Theorem

      |- ∀mode c b a.
           fp16_mul_add mode (float_to_fp16 a) (float_to_fp16 b)
             (float_to_fp16 c) =
           float_to_fp16 (float_mul_add mode a b c)

   [fp16_mul_add_n2w]  Theorem

      |- ∀mode c b a.
           fp16_mul_add mode (n2w a) (n2w b) (n2w c) =
           float_to_fp16
             (float_mul_add mode (fp16_to_float (n2w a))
                (fp16_to_float (n2w b)) (fp16_to_float (n2w c)))

   [fp16_mul_float_to_fp]  Theorem

      |- ∀mode b a.
           fp16_mul mode (float_to_fp16 a) (float_to_fp16 b) =
           float_to_fp16 (float_mul mode a b)

   [fp16_mul_n2w]  Theorem

      |- ∀mode b a.
           fp16_mul mode (n2w a) (n2w b) =
           float_to_fp16
             (float_mul mode (fp16_to_float (n2w a))
                (fp16_to_float (n2w b)))

   [fp16_nchotomy]  Theorem

      |- ∀x. ∃y. x = float_to_fp16 y

   [fp16_negate_float_to_fp]  Theorem

      |- ∀a. fp16_negate (float_to_fp16 a) = float_to_fp16 (float_negate a)

   [fp16_negate_n2w]  Theorem

      |- ∀a.
           fp16_negate (n2w a) =
           float_to_fp16 (float_negate (fp16_to_float (n2w a)))

   [fp16_roundToIntegral_float_to_fp]  Theorem

      |- ∀mode a.
           fp16_roundToIntegral mode (float_to_fp16 a) =
           float_to_fp16 (float_round_to_integral mode a)

   [fp16_roundToIntegral_n2w]  Theorem

      |- ∀mode a.
           fp16_roundToIntegral mode (n2w a) =
           float_to_fp16
             (float_round_to_integral mode (fp16_to_float (n2w a)))

   [fp16_sqrt_float_to_fp]  Theorem

      |- ∀mode a.
           fp16_sqrt mode (float_to_fp16 a) =
           float_to_fp16 (float_sqrt mode a)

   [fp16_sqrt_n2w]  Theorem

      |- ∀mode a.
           fp16_sqrt mode (n2w a) =
           float_to_fp16 (float_sqrt mode (fp16_to_float (n2w a)))

   [fp16_sub_float_to_fp]  Theorem

      |- ∀mode b a.
           fp16_sub mode (float_to_fp16 a) (float_to_fp16 b) =
           float_to_fp16 (float_sub mode a b)

   [fp16_sub_n2w]  Theorem

      |- ∀mode b a.
           fp16_sub mode (n2w a) (n2w b) =
           float_to_fp16
             (float_sub mode (fp16_to_float (n2w a))
                (fp16_to_float (n2w b)))

   [fp16_to_float_11]  Theorem

      |- ∀x y. (fp16_to_float x = fp16_to_float y) ⇔ (x = y)

   [fp16_to_float_float_to_fp16]  Theorem

      |- ∀x. fp16_to_float (float_to_fp16 x) = x

   [fp16_to_float_n2w]  Theorem

      |- ∀n.
           fp16_to_float (n2w n) =
           (let (q,f) = DIVMOD_2EXP 10 n in
            let (s,e) = DIVMOD_2EXP 5 q
            in
              <|Sign := n2w (s MOD 2); Exponent := n2w e;
                Significand := n2w f|>)

   [fp16_to_real_float_to_fp]  Theorem

      |- ∀a. fp16_to_real (float_to_fp16 a) = float_to_real a

   [fp16_to_real_n2w]  Theorem

      |- ∀a. fp16_to_real (n2w a) = float_to_real (fp16_to_float (n2w a))

   [fp32_abs_float_to_fp]  Theorem

      |- ∀a. fp32_abs (float_to_fp32 a) = float_to_fp32 (float_abs a)

   [fp32_abs_n2w]  Theorem

      |- ∀a.
           fp32_abs (n2w a) =
           float_to_fp32 (float_abs (fp32_to_float (n2w a)))

   [fp32_add_float_to_fp]  Theorem

      |- ∀mode b a.
           fp32_add mode (float_to_fp32 a) (float_to_fp32 b) =
           float_to_fp32 (float_add mode a b)

   [fp32_add_n2w]  Theorem

      |- ∀mode b a.
           fp32_add mode (n2w a) (n2w b) =
           float_to_fp32
             (float_add mode (fp32_to_float (n2w a))
                (fp32_to_float (n2w b)))

   [fp32_div_float_to_fp]  Theorem

      |- ∀mode b a.
           fp32_div mode (float_to_fp32 a) (float_to_fp32 b) =
           float_to_fp32 (float_div mode a b)

   [fp32_div_n2w]  Theorem

      |- ∀mode b a.
           fp32_div mode (n2w a) (n2w b) =
           float_to_fp32
             (float_div mode (fp32_to_float (n2w a))
                (fp32_to_float (n2w b)))

   [fp32_equal_float_to_fp]  Theorem

      |- ∀b a.
           fp32_equal (float_to_fp32 a) (float_to_fp32 b) ⇔ float_equal a b

   [fp32_equal_n2w]  Theorem

      |- ∀b a.
           fp32_equal (n2w a) (n2w b) ⇔
           float_equal (fp32_to_float (n2w a)) (fp32_to_float (n2w b))

   [fp32_greaterEqual_float_to_fp]  Theorem

      |- ∀b a.
           fp32_greaterEqual (float_to_fp32 a) (float_to_fp32 b) ⇔
           float_greater_equal a b

   [fp32_greaterEqual_n2w]  Theorem

      |- ∀b a.
           fp32_greaterEqual (n2w a) (n2w b) ⇔
           float_greater_equal (fp32_to_float (n2w a))
             (fp32_to_float (n2w b))

   [fp32_greaterThan_float_to_fp]  Theorem

      |- ∀b a.
           fp32_greaterThan (float_to_fp32 a) (float_to_fp32 b) ⇔
           float_greater_than a b

   [fp32_greaterThan_n2w]  Theorem

      |- ∀b a.
           fp32_greaterThan (n2w a) (n2w b) ⇔
           float_greater_than (fp32_to_float (n2w a))
             (fp32_to_float (n2w b))

   [fp32_isFinite_float_to_fp]  Theorem

      |- ∀a. fp32_isFinite (float_to_fp32 a) ⇔ float_is_finite a

   [fp32_isFinite_n2w]  Theorem

      |- ∀a.
           fp32_isFinite (n2w a) ⇔ float_is_finite (fp32_to_float (n2w a))

   [fp32_isInfinite_float_to_fp]  Theorem

      |- ∀a. fp32_isInfinite (float_to_fp32 a) ⇔ float_is_infinite a

   [fp32_isInfinite_n2w]  Theorem

      |- ∀a.
           fp32_isInfinite (n2w a) ⇔
           float_is_infinite (fp32_to_float (n2w a))

   [fp32_isIntegral_float_to_fp]  Theorem

      |- ∀a. fp32_isIntegral (float_to_fp32 a) ⇔ float_is_integral a

   [fp32_isIntegral_n2w]  Theorem

      |- ∀a.
           fp32_isIntegral (n2w a) ⇔
           float_is_integral (fp32_to_float (n2w a))

   [fp32_isNan_float_to_fp]  Theorem

      |- ∀a. fp32_isNan (float_to_fp32 a) ⇔ float_is_nan a

   [fp32_isNan_n2w]  Theorem

      |- ∀a. fp32_isNan (n2w a) ⇔ float_is_nan (fp32_to_float (n2w a))

   [fp32_isNormal_float_to_fp]  Theorem

      |- ∀a. fp32_isNormal (float_to_fp32 a) ⇔ float_is_normal a

   [fp32_isNormal_n2w]  Theorem

      |- ∀a.
           fp32_isNormal (n2w a) ⇔ float_is_normal (fp32_to_float (n2w a))

   [fp32_isSubnormal_float_to_fp]  Theorem

      |- ∀a. fp32_isSubnormal (float_to_fp32 a) ⇔ float_is_subnormal a

   [fp32_isSubnormal_n2w]  Theorem

      |- ∀a.
           fp32_isSubnormal (n2w a) ⇔
           float_is_subnormal (fp32_to_float (n2w a))

   [fp32_isZero_float_to_fp]  Theorem

      |- ∀a. fp32_isZero (float_to_fp32 a) ⇔ float_is_zero a

   [fp32_isZero_n2w]  Theorem

      |- ∀a. fp32_isZero (n2w a) ⇔ float_is_zero (fp32_to_float (n2w a))

   [fp32_lessEqual_float_to_fp]  Theorem

      |- ∀b a.
           fp32_lessEqual (float_to_fp32 a) (float_to_fp32 b) ⇔
           float_less_equal a b

   [fp32_lessEqual_n2w]  Theorem

      |- ∀b a.
           fp32_lessEqual (n2w a) (n2w b) ⇔
           float_less_equal (fp32_to_float (n2w a)) (fp32_to_float (n2w b))

   [fp32_lessThan_float_to_fp]  Theorem

      |- ∀b a.
           fp32_lessThan (float_to_fp32 a) (float_to_fp32 b) ⇔
           float_less_than a b

   [fp32_lessThan_n2w]  Theorem

      |- ∀b a.
           fp32_lessThan (n2w a) (n2w b) ⇔
           float_less_than (fp32_to_float (n2w a)) (fp32_to_float (n2w b))

   [fp32_mul_add_float_to_fp]  Theorem

      |- ∀mode c b a.
           fp32_mul_add mode (float_to_fp32 a) (float_to_fp32 b)
             (float_to_fp32 c) =
           float_to_fp32 (float_mul_add mode a b c)

   [fp32_mul_add_n2w]  Theorem

      |- ∀mode c b a.
           fp32_mul_add mode (n2w a) (n2w b) (n2w c) =
           float_to_fp32
             (float_mul_add mode (fp32_to_float (n2w a))
                (fp32_to_float (n2w b)) (fp32_to_float (n2w c)))

   [fp32_mul_float_to_fp]  Theorem

      |- ∀mode b a.
           fp32_mul mode (float_to_fp32 a) (float_to_fp32 b) =
           float_to_fp32 (float_mul mode a b)

   [fp32_mul_n2w]  Theorem

      |- ∀mode b a.
           fp32_mul mode (n2w a) (n2w b) =
           float_to_fp32
             (float_mul mode (fp32_to_float (n2w a))
                (fp32_to_float (n2w b)))

   [fp32_nchotomy]  Theorem

      |- ∀x. ∃y. x = float_to_fp32 y

   [fp32_negate_float_to_fp]  Theorem

      |- ∀a. fp32_negate (float_to_fp32 a) = float_to_fp32 (float_negate a)

   [fp32_negate_n2w]  Theorem

      |- ∀a.
           fp32_negate (n2w a) =
           float_to_fp32 (float_negate (fp32_to_float (n2w a)))

   [fp32_roundToIntegral_float_to_fp]  Theorem

      |- ∀mode a.
           fp32_roundToIntegral mode (float_to_fp32 a) =
           float_to_fp32 (float_round_to_integral mode a)

   [fp32_roundToIntegral_n2w]  Theorem

      |- ∀mode a.
           fp32_roundToIntegral mode (n2w a) =
           float_to_fp32
             (float_round_to_integral mode (fp32_to_float (n2w a)))

   [fp32_sqrt_float_to_fp]  Theorem

      |- ∀mode a.
           fp32_sqrt mode (float_to_fp32 a) =
           float_to_fp32 (float_sqrt mode a)

   [fp32_sqrt_n2w]  Theorem

      |- ∀mode a.
           fp32_sqrt mode (n2w a) =
           float_to_fp32 (float_sqrt mode (fp32_to_float (n2w a)))

   [fp32_sub_float_to_fp]  Theorem

      |- ∀mode b a.
           fp32_sub mode (float_to_fp32 a) (float_to_fp32 b) =
           float_to_fp32 (float_sub mode a b)

   [fp32_sub_n2w]  Theorem

      |- ∀mode b a.
           fp32_sub mode (n2w a) (n2w b) =
           float_to_fp32
             (float_sub mode (fp32_to_float (n2w a))
                (fp32_to_float (n2w b)))

   [fp32_to_float_11]  Theorem

      |- ∀x y. (fp32_to_float x = fp32_to_float y) ⇔ (x = y)

   [fp32_to_float_float_to_fp32]  Theorem

      |- ∀x. fp32_to_float (float_to_fp32 x) = x

   [fp32_to_float_n2w]  Theorem

      |- ∀n.
           fp32_to_float (n2w n) =
           (let (q,f) = DIVMOD_2EXP 23 n in
            let (s,e) = DIVMOD_2EXP 8 q
            in
              <|Sign := n2w (s MOD 2); Exponent := n2w e;
                Significand := n2w f|>)

   [fp32_to_real_float_to_fp]  Theorem

      |- ∀a. fp32_to_real (float_to_fp32 a) = float_to_real a

   [fp32_to_real_n2w]  Theorem

      |- ∀a. fp32_to_real (n2w a) = float_to_real (fp32_to_float (n2w a))

   [fp64_abs_float_to_fp]  Theorem

      |- ∀a. fp64_abs (float_to_fp64 a) = float_to_fp64 (float_abs a)

   [fp64_abs_n2w]  Theorem

      |- ∀a.
           fp64_abs (n2w a) =
           float_to_fp64 (float_abs (fp64_to_float (n2w a)))

   [fp64_add_float_to_fp]  Theorem

      |- ∀mode b a.
           fp64_add mode (float_to_fp64 a) (float_to_fp64 b) =
           float_to_fp64 (float_add mode a b)

   [fp64_add_n2w]  Theorem

      |- ∀mode b a.
           fp64_add mode (n2w a) (n2w b) =
           float_to_fp64
             (float_add mode (fp64_to_float (n2w a))
                (fp64_to_float (n2w b)))

   [fp64_div_float_to_fp]  Theorem

      |- ∀mode b a.
           fp64_div mode (float_to_fp64 a) (float_to_fp64 b) =
           float_to_fp64 (float_div mode a b)

   [fp64_div_n2w]  Theorem

      |- ∀mode b a.
           fp64_div mode (n2w a) (n2w b) =
           float_to_fp64
             (float_div mode (fp64_to_float (n2w a))
                (fp64_to_float (n2w b)))

   [fp64_equal_float_to_fp]  Theorem

      |- ∀b a.
           fp64_equal (float_to_fp64 a) (float_to_fp64 b) ⇔ float_equal a b

   [fp64_equal_n2w]  Theorem

      |- ∀b a.
           fp64_equal (n2w a) (n2w b) ⇔
           float_equal (fp64_to_float (n2w a)) (fp64_to_float (n2w b))

   [fp64_greaterEqual_float_to_fp]  Theorem

      |- ∀b a.
           fp64_greaterEqual (float_to_fp64 a) (float_to_fp64 b) ⇔
           float_greater_equal a b

   [fp64_greaterEqual_n2w]  Theorem

      |- ∀b a.
           fp64_greaterEqual (n2w a) (n2w b) ⇔
           float_greater_equal (fp64_to_float (n2w a))
             (fp64_to_float (n2w b))

   [fp64_greaterThan_float_to_fp]  Theorem

      |- ∀b a.
           fp64_greaterThan (float_to_fp64 a) (float_to_fp64 b) ⇔
           float_greater_than a b

   [fp64_greaterThan_n2w]  Theorem

      |- ∀b a.
           fp64_greaterThan (n2w a) (n2w b) ⇔
           float_greater_than (fp64_to_float (n2w a))
             (fp64_to_float (n2w b))

   [fp64_isFinite_float_to_fp]  Theorem

      |- ∀a. fp64_isFinite (float_to_fp64 a) ⇔ float_is_finite a

   [fp64_isFinite_n2w]  Theorem

      |- ∀a.
           fp64_isFinite (n2w a) ⇔ float_is_finite (fp64_to_float (n2w a))

   [fp64_isInfinite_float_to_fp]  Theorem

      |- ∀a. fp64_isInfinite (float_to_fp64 a) ⇔ float_is_infinite a

   [fp64_isInfinite_n2w]  Theorem

      |- ∀a.
           fp64_isInfinite (n2w a) ⇔
           float_is_infinite (fp64_to_float (n2w a))

   [fp64_isIntegral_float_to_fp]  Theorem

      |- ∀a. fp64_isIntegral (float_to_fp64 a) ⇔ float_is_integral a

   [fp64_isIntegral_n2w]  Theorem

      |- ∀a.
           fp64_isIntegral (n2w a) ⇔
           float_is_integral (fp64_to_float (n2w a))

   [fp64_isNan_float_to_fp]  Theorem

      |- ∀a. fp64_isNan (float_to_fp64 a) ⇔ float_is_nan a

   [fp64_isNan_n2w]  Theorem

      |- ∀a. fp64_isNan (n2w a) ⇔ float_is_nan (fp64_to_float (n2w a))

   [fp64_isNormal_float_to_fp]  Theorem

      |- ∀a. fp64_isNormal (float_to_fp64 a) ⇔ float_is_normal a

   [fp64_isNormal_n2w]  Theorem

      |- ∀a.
           fp64_isNormal (n2w a) ⇔ float_is_normal (fp64_to_float (n2w a))

   [fp64_isSubnormal_float_to_fp]  Theorem

      |- ∀a. fp64_isSubnormal (float_to_fp64 a) ⇔ float_is_subnormal a

   [fp64_isSubnormal_n2w]  Theorem

      |- ∀a.
           fp64_isSubnormal (n2w a) ⇔
           float_is_subnormal (fp64_to_float (n2w a))

   [fp64_isZero_float_to_fp]  Theorem

      |- ∀a. fp64_isZero (float_to_fp64 a) ⇔ float_is_zero a

   [fp64_isZero_n2w]  Theorem

      |- ∀a. fp64_isZero (n2w a) ⇔ float_is_zero (fp64_to_float (n2w a))

   [fp64_lessEqual_float_to_fp]  Theorem

      |- ∀b a.
           fp64_lessEqual (float_to_fp64 a) (float_to_fp64 b) ⇔
           float_less_equal a b

   [fp64_lessEqual_n2w]  Theorem

      |- ∀b a.
           fp64_lessEqual (n2w a) (n2w b) ⇔
           float_less_equal (fp64_to_float (n2w a)) (fp64_to_float (n2w b))

   [fp64_lessThan_float_to_fp]  Theorem

      |- ∀b a.
           fp64_lessThan (float_to_fp64 a) (float_to_fp64 b) ⇔
           float_less_than a b

   [fp64_lessThan_n2w]  Theorem

      |- ∀b a.
           fp64_lessThan (n2w a) (n2w b) ⇔
           float_less_than (fp64_to_float (n2w a)) (fp64_to_float (n2w b))

   [fp64_mul_add_float_to_fp]  Theorem

      |- ∀mode c b a.
           fp64_mul_add mode (float_to_fp64 a) (float_to_fp64 b)
             (float_to_fp64 c) =
           float_to_fp64 (float_mul_add mode a b c)

   [fp64_mul_add_n2w]  Theorem

      |- ∀mode c b a.
           fp64_mul_add mode (n2w a) (n2w b) (n2w c) =
           float_to_fp64
             (float_mul_add mode (fp64_to_float (n2w a))
                (fp64_to_float (n2w b)) (fp64_to_float (n2w c)))

   [fp64_mul_float_to_fp]  Theorem

      |- ∀mode b a.
           fp64_mul mode (float_to_fp64 a) (float_to_fp64 b) =
           float_to_fp64 (float_mul mode a b)

   [fp64_mul_n2w]  Theorem

      |- ∀mode b a.
           fp64_mul mode (n2w a) (n2w b) =
           float_to_fp64
             (float_mul mode (fp64_to_float (n2w a))
                (fp64_to_float (n2w b)))

   [fp64_nchotomy]  Theorem

      |- ∀x. ∃y. x = float_to_fp64 y

   [fp64_negate_float_to_fp]  Theorem

      |- ∀a. fp64_negate (float_to_fp64 a) = float_to_fp64 (float_negate a)

   [fp64_negate_n2w]  Theorem

      |- ∀a.
           fp64_negate (n2w a) =
           float_to_fp64 (float_negate (fp64_to_float (n2w a)))

   [fp64_roundToIntegral_float_to_fp]  Theorem

      |- ∀mode a.
           fp64_roundToIntegral mode (float_to_fp64 a) =
           float_to_fp64 (float_round_to_integral mode a)

   [fp64_roundToIntegral_n2w]  Theorem

      |- ∀mode a.
           fp64_roundToIntegral mode (n2w a) =
           float_to_fp64
             (float_round_to_integral mode (fp64_to_float (n2w a)))

   [fp64_sqrt_float_to_fp]  Theorem

      |- ∀mode a.
           fp64_sqrt mode (float_to_fp64 a) =
           float_to_fp64 (float_sqrt mode a)

   [fp64_sqrt_n2w]  Theorem

      |- ∀mode a.
           fp64_sqrt mode (n2w a) =
           float_to_fp64 (float_sqrt mode (fp64_to_float (n2w a)))

   [fp64_sub_float_to_fp]  Theorem

      |- ∀mode b a.
           fp64_sub mode (float_to_fp64 a) (float_to_fp64 b) =
           float_to_fp64 (float_sub mode a b)

   [fp64_sub_n2w]  Theorem

      |- ∀mode b a.
           fp64_sub mode (n2w a) (n2w b) =
           float_to_fp64
             (float_sub mode (fp64_to_float (n2w a))
                (fp64_to_float (n2w b)))

   [fp64_to_float_11]  Theorem

      |- ∀x y. (fp64_to_float x = fp64_to_float y) ⇔ (x = y)

   [fp64_to_float_float_to_fp64]  Theorem

      |- ∀x. fp64_to_float (float_to_fp64 x) = x

   [fp64_to_float_n2w]  Theorem

      |- ∀n.
           fp64_to_float (n2w n) =
           (let (q,f) = DIVMOD_2EXP 52 n in
            let (s,e) = DIVMOD_2EXP 11 q
            in
              <|Sign := n2w (s MOD 2); Exponent := n2w e;
                Significand := n2w f|>)

   [fp64_to_real_float_to_fp]  Theorem

      |- ∀a. fp64_to_real (float_to_fp64 a) = float_to_real a

   [fp64_to_real_n2w]  Theorem

      |- ∀a. fp64_to_real (n2w a) = float_to_real (fp64_to_float (n2w a))


*)
end
