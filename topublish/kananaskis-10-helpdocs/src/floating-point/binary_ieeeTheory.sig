signature binary_ieeeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ULP_primitive_def : thm
    val closest_def : thm
    val closest_such_def : thm
    val exponent_boundary_def : thm
    val float_Exponent : thm
    val float_Exponent_fupd : thm
    val float_Sign : thm
    val float_Sign_fupd : thm
    val float_Significand : thm
    val float_Significand_fupd : thm
    val float_TY_DEF : thm
    val float_abs_def : thm
    val float_add_def : thm
    val float_bottom_def : thm
    val float_case_def : thm
    val float_compare_BIJ : thm
    val float_compare_CASE : thm
    val float_compare_TY_DEF : thm
    val float_compare_def : thm
    val float_compare_size_def : thm
    val float_div_def : thm
    val float_equal_def : thm
    val float_greater_equal_def : thm
    val float_greater_than_def : thm
    val float_is_finite_def : thm
    val float_is_infinite_def : thm
    val float_is_integral_def : thm
    val float_is_nan_def : thm
    val float_is_normal_def : thm
    val float_is_subnormal_def : thm
    val float_is_zero_def : thm
    val float_less_equal_def : thm
    val float_less_than_def : thm
    val float_minus_infinity_def : thm
    val float_minus_min_def : thm
    val float_minus_zero_def : thm
    val float_mul_add_def : thm
    val float_mul_def : thm
    val float_negate_def : thm
    val float_plus_infinity_def : thm
    val float_plus_min_def : thm
    val float_plus_zero_def : thm
    val float_round_def : thm
    val float_round_to_integral_def : thm
    val float_size_def : thm
    val float_some_nan_def : thm
    val float_sqrt_def : thm
    val float_sub_def : thm
    val float_to_real_def : thm
    val float_top_def : thm
    val float_value_TY_DEF : thm
    val float_value_case_def : thm
    val float_value_def : thm
    val float_value_size_def : thm
    val integral_round_def : thm
    val is_closest_def : thm
    val largest_def : thm
    val round_def : thm
    val rounding_BIJ : thm
    val rounding_CASE : thm
    val rounding_TY_DEF : thm
    val rounding_size_def : thm
    val threshold_def : thm
    val ulp_def : thm

  (*  Theorems  *)
    val EXISTS_float : thm
    val FORALL_float : thm
    val ULP_def : thm
    val ULP_ind : thm
    val ULP_le_mono : thm
    val abs_float_value : thm
    val bottom_properties : thm
    val datatype_float : thm
    val datatype_float_compare : thm
    val datatype_float_value : thm
    val datatype_rounding : thm
    val diff_float_ULP : thm
    val diff_lt_ulp_eq0 : thm
    val diff_lt_ulp_even : thm
    val diff_lt_ulp_even4 : thm
    val div_eq0 : thm
    val exp_ge2 : thm
    val exp_gt2 : thm
    val float_11 : thm
    val float_Axiom : thm
    val float_accessors : thm
    val float_accfupds : thm
    val float_add_compute : thm
    val float_add_finite : thm
    val float_add_finite_minus_infinity : thm
    val float_add_finite_plus_infinity : thm
    val float_add_minus_infinity_finite : thm
    val float_add_nan : thm
    val float_add_plus_infinity_finite : thm
    val float_case_cong : thm
    val float_compare2num_11 : thm
    val float_compare2num_ONTO : thm
    val float_compare2num_num2float_compare : thm
    val float_compare2num_thm : thm
    val float_compare_Axiom : thm
    val float_compare_EQ_float_compare : thm
    val float_compare_case_cong : thm
    val float_compare_case_def : thm
    val float_compare_distinct : thm
    val float_compare_induction : thm
    val float_compare_nchotomy : thm
    val float_component_equality : thm
    val float_components : thm
    val float_distinct : thm
    val float_div_compute : thm
    val float_div_finite : thm
    val float_div_finite_minus_infinity : thm
    val float_div_finite_plus_infinity : thm
    val float_div_minus_infinity_finite : thm
    val float_div_nan : thm
    val float_div_plus_infinity_finite : thm
    val float_fn_updates : thm
    val float_fupdcanon : thm
    val float_fupdcanon_comp : thm
    val float_fupdfupds : thm
    val float_fupdfupds_comp : thm
    val float_induction : thm
    val float_infinity_negate_abs : thm
    val float_is_zero : thm
    val float_is_zero_to_real : thm
    val float_literal_11 : thm
    val float_literal_nchotomy : thm
    val float_minus_infinity : thm
    val float_minus_zero : thm
    val float_mul_compute : thm
    val float_mul_finite : thm
    val float_mul_finite_minus_infinity : thm
    val float_mul_finite_plus_infinity : thm
    val float_mul_minus_infinity_finite : thm
    val float_mul_nan : thm
    val float_mul_plus_infinity_finite : thm
    val float_nchotomy : thm
    val float_negate_negate : thm
    val float_round_bottom : thm
    val float_round_minus_infinity : thm
    val float_round_non_zero : thm
    val float_round_plus_infinity : thm
    val float_round_roundTowardNegative_minus_infinity : thm
    val float_round_roundTowardNegative_top : thm
    val float_round_roundTowardPositive_bottom : thm
    val float_round_roundTowardPositive_plus_infinity : thm
    val float_round_roundTowardZero_bottom : thm
    val float_round_roundTowardZero_top : thm
    val float_round_top : thm
    val float_sets : thm
    val float_sub_compute : thm
    val float_sub_finite : thm
    val float_sub_finite_minus_infinity : thm
    val float_sub_finite_plus_infinity : thm
    val float_sub_minus_infinity_finite : thm
    val float_sub_nan : thm
    val float_sub_plus_infinity_finite : thm
    val float_tests : thm
    val float_to_real : thm
    val float_to_real_eq : thm
    val float_to_real_negate : thm
    val float_updates_eq_literal : thm
    val float_value_11 : thm
    val float_value_Axiom : thm
    val float_value_case_cong : thm
    val float_value_distinct : thm
    val float_value_induction : thm
    val float_value_nchotomy : thm
    val float_values : thm
    val infinity_properties : thm
    val largest : thm
    val largest_is_positive : thm
    val le2 : thm
    val less_than_ulp : thm
    val min_properties : thm
    val neg_ulp : thm
    val num2float_compare_11 : thm
    val num2float_compare_ONTO : thm
    val num2float_compare_float_compare2num : thm
    val num2float_compare_thm : thm
    val num2rounding_11 : thm
    val num2rounding_ONTO : thm
    val num2rounding_rounding2num : thm
    val num2rounding_thm : thm
    val round_roundTiesToEven : thm
    val round_roundTiesToEven0 : thm
    val round_roundTiesToEven_is_minus_zero : thm
    val round_roundTiesToEven_is_plus_zero : thm
    val round_roundTiesToEven_is_zero : thm
    val round_roundTiesToEven_minus_infinity : thm
    val round_roundTiesToEven_plus_infinity : thm
    val round_roundTowardNegative_minus_infinity : thm
    val round_roundTowardNegative_top : thm
    val round_roundTowardPositive_bottom : thm
    val round_roundTowardPositive_plus_infinity : thm
    val round_roundTowardZero : thm
    val round_roundTowardZero_bottom : thm
    val round_roundTowardZero_is_minus_zero : thm
    val round_roundTowardZero_is_plus_zero : thm
    val round_roundTowardZero_is_zero : thm
    val round_roundTowardZero_top : thm
    val rounding2num_11 : thm
    val rounding2num_ONTO : thm
    val rounding2num_num2rounding : thm
    val rounding2num_thm : thm
    val rounding_Axiom : thm
    val rounding_EQ_rounding : thm
    val rounding_case_cong : thm
    val rounding_case_def : thm
    val rounding_distinct : thm
    val rounding_induction : thm
    val rounding_nchotomy : thm
    val sign_not_zero : thm
    val some_nan_properties : thm
    val threshold : thm
    val threshold_is_positive : thm
    val top_properties : thm
    val ulp : thm
    val ulp_lt_ULP : thm
    val ulp_lt_largest : thm
    val ulp_lt_threshold : thm
    val zero_le_pos_div_twopow : thm
    val zero_le_twopow : thm
    val zero_lt_twopow : thm
    val zero_neq_twopow : thm
    val zero_properties : thm
    val zero_to_real : thm

  val binary_ieee_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [transc] Parent theory of "binary_ieee"

   [words] Parent theory of "binary_ieee"

   [ULP_primitive_def]  Definition

      |- ULP =
         WFREC (@R. WF R)
           (λULP a.
              case a of
                (e,v1) =>
                  I
                    (2 pow (if e = 0w then 1 else w2n e) /
                     2 pow (bias (:χ) + precision (:τ))))

   [closest_def]  Definition

      |- closest = closest_such (K T)

   [closest_such_def]  Definition

      |- ∀p s x.
           closest_such p s x =
           @a. is_closest s x a ∧ ∀b. is_closest s x b ∧ p b ⇒ p a

   [exponent_boundary_def]  Definition

      |- ∀y x.
           exponent_boundary y x ⇔
           (x.Sign = y.Sign) ∧ (w2n x.Exponent = w2n y.Exponent + 1) ∧
           x.Exponent ≠ 1w ∧ (y.Significand = -1w) ∧ (x.Significand = 0w)

   [float_Exponent]  Definition

      |- ∀c c0 c1. (float c c0 c1).Exponent = c0

   [float_Exponent_fupd]  Definition

      |- ∀f c c0 c1.
           float c c0 c1 with Exponent updated_by f = float c (f c0) c1

   [float_Sign]  Definition

      |- ∀c c0 c1. (float c c0 c1).Sign = c

   [float_Sign_fupd]  Definition

      |- ∀f c c0 c1.
           float c c0 c1 with Sign updated_by f = float (f c) c0 c1

   [float_Significand]  Definition

      |- ∀c c0 c1. (float c c0 c1).Significand = c1

   [float_Significand_fupd]  Definition

      |- ∀f c c0 c1.
           float c c0 c1 with Significand updated_by f = float c c0 (f c1)

   [float_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'float' .
                  (∀a0'.
                     (∃a0 a1 a2.
                        a0' =
                        (λa0 a1 a2.
                           ind_type$CONSTR 0 (a0,a1,a2)
                             (λn. ind_type$BOTTOM)) a0 a1 a2) ⇒
                     'float' a0') ⇒
                  'float' a0') rep

   [float_abs_def]  Definition

      |- ∀x. float_abs x = x with Sign := 0w

   [float_add_def]  Definition

      |- ∀mode x y.
           float_add mode x y =
           case (float_value x,float_value y) of
             (Float r1,Float r2) =>
               float_round mode
                 (if (r1 = 0) ∧ (r2 = 0) ∧ (x.Sign = y.Sign) then
                    x.Sign = 1w
                  else (mode = roundTowardNegative)) (r1 + r2)
           | (Float r1,Infinity) => y
           | (Float r1,NaN) => float_some_nan (:τ # χ)
           | (Infinity,Float v7) => x
           | (Infinity,Infinity) =>
               if x.Sign = y.Sign then x else float_some_nan (:τ # χ)
           | (Infinity,NaN) => float_some_nan (:τ # χ)
           | (NaN,v1) => float_some_nan (:τ # χ)

   [float_bottom_def]  Definition

      |- float_bottom (:τ # χ) = float_negate (float_top (:τ # χ))

   [float_case_def]  Definition

      |- ∀a0 a1 a2 f. float_CASE (float a0 a1 a2) f = f a0 a1 a2

   [float_compare_BIJ]  Definition

      |- (∀a. num2float_compare (float_compare2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (float_compare2num (num2float_compare r) = r)

   [float_compare_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of LT => v0 | GT => v1 | EQ => v2 | UN => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (float_compare2num x)

   [float_compare_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [float_compare_def]  Definition

      |- ∀x y.
           float_compare x y =
           case (float_value x,float_value y) of
             (Float r1,Float r2) =>
               if r1 < r2 then LT else if r1 = r2 then EQ else GT
           | (Float r1,Infinity) => if y.Sign = 1w then GT else LT
           | (Float r1,NaN) => UN
           | (Infinity,Float v7) => if x.Sign = 1w then LT else GT
           | (Infinity,Infinity) =>
               if x.Sign = y.Sign then EQ
               else if x.Sign = 1w then LT
               else GT
           | (Infinity,NaN) => UN
           | (NaN,v1) => UN

   [float_compare_size_def]  Definition

      |- ∀x. float_compare_size x = 0

   [float_div_def]  Definition

      |- ∀mode x y.
           float_div mode x y =
           case (float_value x,float_value y) of
             (Float 0,Float 0) => float_some_nan (:τ # χ)
           | (Float r1,Float 0) =>
               if x.Sign = y.Sign then float_plus_infinity (:τ # χ)
               else float_minus_infinity (:τ # χ)
           | (Float r1,Float r2) =>
               float_round mode (x.Sign ≠ y.Sign) (r1 / r2)
           | (Float r1,Infinity) =>
               if x.Sign = y.Sign then float_plus_zero (:τ # χ)
               else float_minus_zero (:τ # χ)
           | (Float r1,NaN) => float_some_nan (:τ # χ)
           | (Infinity,Float v7) =>
               if x.Sign = y.Sign then float_plus_infinity (:τ # χ)
               else float_minus_infinity (:τ # χ)
           | (Infinity,Infinity) => float_some_nan (:τ # χ)
           | (Infinity,NaN) => float_some_nan (:τ # χ)
           | (NaN,v1) => float_some_nan (:τ # χ)

   [float_equal_def]  Definition

      |- ∀x y. float_equal x y ⇔ (float_compare x y = EQ)

   [float_greater_equal_def]  Definition

      |- ∀x y.
           float_greater_equal x y ⇔
           case float_compare x y of LT => F | GT => T | EQ => T | UN => F

   [float_greater_than_def]  Definition

      |- ∀x y. float_greater_than x y ⇔ (float_compare x y = GT)

   [float_is_finite_def]  Definition

      |- ∀x.
           float_is_finite x ⇔ case float_value x of Float v1 => T | _ => F

   [float_is_infinite_def]  Definition

      |- ∀x.
           float_is_infinite x ⇔
           case float_value x of Infinity => T | _ => F

   [float_is_integral_def]  Definition

      |- ∀x.
           float_is_integral x ⇔
           case float_value x of Float r => ∃n. abs r = &n | _ => F

   [float_is_nan_def]  Definition

      |- ∀x. float_is_nan x ⇔ case float_value x of NaN => T | _ => F

   [float_is_normal_def]  Definition

      |- ∀x. float_is_normal x ⇔ x.Exponent ≠ 0w ∧ x.Exponent ≠ UINT_MAXw

   [float_is_subnormal_def]  Definition

      |- ∀x. float_is_subnormal x ⇔ (x.Exponent = 0w) ∧ x.Significand ≠ 0w

   [float_is_zero_def]  Definition

      |- ∀x.
           float_is_zero x ⇔
           case float_value x of Float r => r = 0 | _ => F

   [float_less_equal_def]  Definition

      |- ∀x y.
           float_less_equal x y ⇔
           case float_compare x y of LT => T | GT => F | EQ => T | UN => F

   [float_less_than_def]  Definition

      |- ∀x y. float_less_than x y ⇔ (float_compare x y = LT)

   [float_minus_infinity_def]  Definition

      |- float_minus_infinity (:τ # χ) =
         float_negate (float_plus_infinity (:τ # χ))

   [float_minus_min_def]  Definition

      |- float_minus_min (:τ # χ) = float_negate (float_plus_min (:τ # χ))

   [float_minus_zero_def]  Definition

      |- float_minus_zero (:τ # χ) =
         float_negate (float_plus_zero (:τ # χ))

   [float_mul_add_def]  Definition

      |- ∀mode x y z.
           float_mul_add mode x y z =
           (let signP = x.Sign ⊕ y.Sign in
            let infP = float_is_infinite x ∨ float_is_infinite y
            in
              if
                float_is_nan x ∨ float_is_nan y ∨ float_is_nan z ∨
                float_is_infinite x ∧ float_is_zero y ∨
                float_is_zero x ∧ float_is_infinite y ∨
                float_is_infinite z ∧ infP ∧ z.Sign ≠ signP
              then
                float_some_nan (:τ # χ)
              else if
                float_is_infinite z ∧ (z.Sign = 0w) ∨ infP ∧ (signP = 0w)
              then
                float_plus_infinity (:τ # χ)
              else if
                float_is_infinite z ∧ (z.Sign = 1w) ∨ infP ∧ (signP = 1w)
              then
                float_minus_infinity (:τ # χ)
              else if
                float_is_zero z ∧ (float_is_zero x ∨ float_is_zero y) ∧
                (x.Sign = signP)
              then
                if x.Sign = 1w then float_minus_zero (:τ # χ)
                else float_plus_zero (:τ # χ)
              else
                float_round mode (mode = roundTowardNegative)
                  (float_to_real z + float_to_real x * float_to_real y))

   [float_mul_def]  Definition

      |- ∀mode x y.
           float_mul mode x y =
           case (float_value x,float_value y) of
             (Float r',Float r2) =>
               float_round mode (x.Sign ≠ y.Sign) (r' * r2)
           | (Float 0,Infinity) => float_some_nan (:τ # χ)
           | (Float r',Infinity) =>
               if x.Sign = y.Sign then float_plus_infinity (:τ # χ)
               else float_minus_infinity (:τ # χ)
           | (Float r',NaN) => float_some_nan (:τ # χ)
           | (Infinity,Float 0) => float_some_nan (:τ # χ)
           | (Infinity,Float r) =>
               if x.Sign = y.Sign then float_plus_infinity (:τ # χ)
               else float_minus_infinity (:τ # χ)
           | (Infinity,Infinity) =>
               if x.Sign = y.Sign then float_plus_infinity (:τ # χ)
               else float_minus_infinity (:τ # χ)
           | (Infinity,NaN) => float_some_nan (:τ # χ)
           | (NaN,v1) => float_some_nan (:τ # χ)

   [float_negate_def]  Definition

      |- ∀x. float_negate x = x with Sign := ¬x.Sign

   [float_plus_infinity_def]  Definition

      |- float_plus_infinity (:τ # χ) =
         <|Sign := 0w; Exponent := UINT_MAXw; Significand := 0w|>

   [float_plus_min_def]  Definition

      |- float_plus_min (:τ # χ) =
         <|Sign := 0w; Exponent := 0w; Significand := 1w|>

   [float_plus_zero_def]  Definition

      |- float_plus_zero (:τ # χ) =
         <|Sign := 0w; Exponent := 0w; Significand := 0w|>

   [float_round_def]  Definition

      |- ∀mode toneg r.
           float_round mode toneg r =
           (let x = round mode r
            in
              if float_is_zero x then
                if toneg then float_minus_zero (:τ # χ)
                else float_plus_zero (:τ # χ)
              else x)

   [float_round_to_integral_def]  Definition

      |- ∀mode x.
           float_round_to_integral mode x =
           case float_value x of Float r => integral_round mode r | _ => x

   [float_size_def]  Definition

      |- ∀f f1 a0 a1 a2. float_size f f1 (float a0 a1 a2) = 1

   [float_some_nan_def]  Definition

      |- float_some_nan (:τ # χ) = @a. float_is_nan a

   [float_sqrt_def]  Definition

      |- ∀mode x.
           float_sqrt mode x =
           if x.Sign = 0w then
             case float_value x of
               Float r => float_round mode (x.Sign = 1w) (sqrt r)
             | Infinity => float_plus_infinity (:τ # χ)
             | NaN => float_some_nan (:τ # χ)
           else float_some_nan (:τ # χ)

   [float_sub_def]  Definition

      |- ∀mode x y.
           float_sub mode x y =
           case (float_value x,float_value y) of
             (Float r1,Float r2) =>
               float_round mode
                 (if (r1 = 0) ∧ (r2 = 0) ∧ x.Sign ≠ y.Sign then x.Sign = 1w
                  else (mode = roundTowardNegative)) (r1 − r2)
           | (Float r1,Infinity) => float_negate y
           | (Float r1,NaN) => float_some_nan (:τ # χ)
           | (Infinity,Float v7) => x
           | (Infinity,Infinity) =>
               if x.Sign = y.Sign then float_some_nan (:τ # χ) else x
           | (Infinity,NaN) => float_some_nan (:τ # χ)
           | (NaN,v1) => float_some_nan (:τ # χ)

   [float_to_real_def]  Definition

      |- ∀x.
           float_to_real x =
           if x.Exponent = 0w then
             -1 pow w2n x.Sign * (2 / 2 pow bias (:χ)) *
             (&w2n x.Significand / 2 pow precision (:τ))
           else
             -1 pow w2n x.Sign * (2 pow w2n x.Exponent / 2 pow bias (:χ)) *
             (1 + &w2n x.Significand / 2 pow precision (:τ))

   [float_top_def]  Definition

      |- float_top (:τ # χ) =
         <|Sign := 0w; Exponent := UINT_MAXw − 1w;
           Significand := UINT_MAXw|>

   [float_value_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'float_value' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM)) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC 0)) ARB
                        (λn. ind_type$BOTTOM)) ⇒
                     'float_value' a0) ⇒
                  'float_value' a0) rep

   [float_value_case_def]  Definition

      |- (∀a f v v1. float_value_CASE (Float a) f v v1 = f a) ∧
         (∀f v v1. float_value_CASE Infinity f v v1 = v) ∧
         ∀f v v1. float_value_CASE NaN f v v1 = v1

   [float_value_def]  Definition

      |- ∀x.
           float_value x =
           if x.Exponent = UINT_MAXw then
             if x.Significand = 0w then Infinity else NaN
           else Float (float_to_real x)

   [float_value_size_def]  Definition

      |- (∀a. float_value_size (Float a) = 1) ∧
         (float_value_size Infinity = 0) ∧ (float_value_size NaN = 0)

   [integral_round_def]  Definition

      |- ∀mode x.
           integral_round mode x =
           case mode of
             roundTiesToEven =>
               (let t = threshold (:τ # χ)
                in
                  if x ≤ -t then float_minus_infinity (:τ # χ)
                  else if x ≥ t then float_plus_infinity (:τ # χ)
                  else
                    closest_such
                      (λa. ∃n. EVEN n ∧ (abs (float_to_real a) = &n))
                      float_is_integral x)
           | roundTowardPositive =>
               (let t = largest (:τ # χ)
                in
                  if x < -t then float_bottom (:τ # χ)
                  else if x > t then float_plus_infinity (:τ # χ)
                  else
                    closest {a | float_is_integral a ∧ float_to_real a ≥ x}
                      x)
           | roundTowardNegative =>
               (let t = largest (:τ # χ)
                in
                  if x < -t then float_minus_infinity (:τ # χ)
                  else if x > t then float_top (:τ # χ)
                  else
                    closest {a | float_is_integral a ∧ float_to_real a ≤ x}
                      x)
           | roundTowardZero =>
               (let t = largest (:τ # χ)
                in
                  if x < -t then float_bottom (:τ # χ)
                  else if x > t then float_top (:τ # χ)
                  else
                    closest
                      {a |
                       float_is_integral a ∧ abs (float_to_real a) ≤ abs x}
                      x)

   [is_closest_def]  Definition

      |- ∀s x a.
           is_closest s x a ⇔
           a ∈ s ∧
           ∀b.
             b ∈ s ⇒ abs (float_to_real a − x) ≤ abs (float_to_real b − x)

   [largest_def]  Definition

      |- largest (:τ # χ) =
         2 pow (UINT_MAX (:χ) − 1) / 2 pow bias (:χ) *
         (2 − inv (2 pow precision (:τ)))

   [round_def]  Definition

      |- ∀mode x.
           round mode x =
           case mode of
             roundTiesToEven =>
               (let t = threshold (:τ # χ)
                in
                  if x ≤ -t then float_minus_infinity (:τ # χ)
                  else if x ≥ t then float_plus_infinity (:τ # χ)
                  else
                    closest_such (λa. ¬word_lsb a.Significand)
                      float_is_finite x)
           | roundTowardPositive =>
               (let t = largest (:τ # χ)
                in
                  if x < -t then float_bottom (:τ # χ)
                  else if x > t then float_plus_infinity (:τ # χ)
                  else
                    closest {a | float_is_finite a ∧ float_to_real a ≥ x}
                      x)
           | roundTowardNegative =>
               (let t = largest (:τ # χ)
                in
                  if x < -t then float_minus_infinity (:τ # χ)
                  else if x > t then float_top (:τ # χ)
                  else
                    closest {a | float_is_finite a ∧ float_to_real a ≤ x}
                      x)
           | roundTowardZero =>
               (let t = largest (:τ # χ)
                in
                  if x < -t then float_bottom (:τ # χ)
                  else if x > t then float_top (:τ # χ)
                  else
                    closest
                      {a |
                       float_is_finite a ∧ abs (float_to_real a) ≤ abs x}
                      x)

   [rounding_BIJ]  Definition

      |- (∀a. num2rounding (rounding2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (rounding2num (num2rounding r) = r)

   [rounding_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              roundTiesToEven => v0
            | roundTowardPositive => v1
            | roundTowardNegative => v2
            | roundTowardZero => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (rounding2num x)

   [rounding_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [rounding_size_def]  Definition

      |- ∀x. rounding_size x = 0

   [threshold_def]  Definition

      |- threshold (:τ # χ) =
         2 pow (UINT_MAX (:χ) − 1) / 2 pow bias (:χ) *
         (2 − inv (2 pow SUC (precision (:τ))))

   [ulp_def]  Definition

      |- ulp (:τ # χ) = ULP (0w,(:τ))

   [EXISTS_float]  Theorem

      |- ∀P.
           (∃f. P f) ⇔
           ∃c1 c0 c. P <|Sign := c1; Exponent := c0; Significand := c|>

   [FORALL_float]  Theorem

      |- ∀P.
           (∀f. P f) ⇔
           ∀c1 c0 c. P <|Sign := c1; Exponent := c0; Significand := c|>

   [ULP_def]  Theorem

      |- ULP (e,(:τ)) =
         2 pow (if e = 0w then 1 else w2n e) /
         2 pow (bias (:χ) + precision (:τ))

   [ULP_ind]  Theorem

      |- ∀P. (∀e. P (e,(:τ))) ⇒ ∀v v1. P (v,v1)

   [ULP_le_mono]  Theorem

      |- ∀e1 e2. e2 ≠ 0w ⇒ (ULP (e1,(:τ)) ≤ ULP (e2,(:τ)) ⇔ e1 ≤₊ e2)

   [abs_float_value]  Theorem

      |- (∀b c d. abs (-1 pow w2n b * c * d) = abs (c * d)) ∧
         ∀b c. abs (-1 pow w2n b * c) = abs c

   [bottom_properties]  Theorem

      |- ¬float_is_zero (float_bottom (:τ # χ)) ∧
         float_is_finite (float_bottom (:τ # χ)) ∧
         ¬float_is_nan (float_bottom (:τ # χ)) ∧
         (float_is_normal (float_bottom (:τ # χ)) ⇔ precision (:χ) ≠ 1) ∧
         (float_is_subnormal (float_bottom (:τ # χ)) ⇔
          (precision (:χ) = 1)) ∧
         ¬float_is_infinite (float_bottom (:τ # χ))

   [datatype_float]  Theorem

      |- DATATYPE (record float Sign Exponent Significand)

   [datatype_float_compare]  Theorem

      |- DATATYPE (float_compare LT GT EQ UN)

   [datatype_float_value]  Theorem

      |- DATATYPE (float_value Float Infinity NaN)

   [datatype_rounding]  Theorem

      |- DATATYPE
           (rounding roundTiesToEven roundTowardPositive
              roundTowardNegative roundTowardZero)

   [diff_float_ULP]  Theorem

      |- ∀x y.
           float_to_real x ≠ float_to_real y ∧ ¬exponent_boundary y x ⇒
           ULP (x.Exponent,(:τ)) ≤ abs (float_to_real x − float_to_real y)

   [diff_lt_ulp_eq0]  Theorem

      |- ∀a b x.
           ¬exponent_boundary b a ∧
           abs (x − float_to_real a) < ULP (a.Exponent,(:τ)) ∧
           abs (x − float_to_real b) < ULP (a.Exponent,(:τ)) ∧
           abs (float_to_real a) ≤ abs x ∧ abs (float_to_real b) ≤ abs x ∧
           ¬float_is_zero a ⇒
           (b = a)

   [diff_lt_ulp_even]  Theorem

      |- ∀a b x.
           ¬exponent_boundary b a ∧
           2 * abs (float_to_real a − x) < ULP (a.Exponent,(:τ)) ∧
           2 * abs (float_to_real b − x) < ULP (a.Exponent,(:τ)) ∧
           ¬float_is_zero a ⇒
           (b = a)

   [diff_lt_ulp_even4]  Theorem

      |- ∀a b x.
           ¬exponent_boundary b a ∧
           4 * abs (float_to_real a − x) ≤ ULP (a.Exponent,(:τ)) ∧
           4 * abs (float_to_real b − x) ≤ ULP (a.Exponent,(:τ)) ∧
           ¬float_is_zero a ⇒
           (b = a)

   [div_eq0]  Theorem

      |- ∀a b. 0 < b ⇒ ((a / b = 0) ⇔ (a = 0))

   [exp_ge2]  Theorem

      |- ∀b. 2 ≤ 2 ** b ⇔ 1 ≤ b

   [exp_gt2]  Theorem

      |- ∀b. 2 < 2 ** b ⇔ 1 < b

   [float_11]  Theorem

      |- ∀a0 a1 a2 a0' a1' a2'.
           (float a0 a1 a2 = float a0' a1' a2') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2')

   [float_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1 a2. fn (float a0 a1 a2) = f a0 a1 a2

   [float_accessors]  Theorem

      |- (∀c c0 c1. (float c c0 c1).Sign = c) ∧
         (∀c c0 c1. (float c c0 c1).Exponent = c0) ∧
         ∀c c0 c1. (float c c0 c1).Significand = c1

   [float_accfupds]  Theorem

      |- (∀f0 f. (f with Exponent updated_by f0).Sign = f.Sign) ∧
         (∀f0 f. (f with Significand updated_by f0).Sign = f.Sign) ∧
         (∀f0 f. (f with Sign updated_by f0).Exponent = f.Exponent) ∧
         (∀f0 f.
            (f with Significand updated_by f0).Exponent = f.Exponent) ∧
         (∀f0 f. (f with Sign updated_by f0).Significand = f.Significand) ∧
         (∀f0 f.
            (f with Exponent updated_by f0).Significand = f.Significand) ∧
         (∀f0 f. (f with Sign updated_by f0).Sign = f0 f.Sign) ∧
         (∀f0 f.
            (f with Exponent updated_by f0).Exponent = f0 f.Exponent) ∧
         ∀f0 f.
           (f with Significand updated_by f0).Significand =
           f0 f.Significand

   [float_add_compute]  Theorem

      |- (∀mode x.
            float_add mode (float_some_nan (:τ # χ)) x =
            float_some_nan (:τ # χ)) ∧
         (∀mode x.
            float_add mode x (float_some_nan (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_add mode (float_minus_infinity (:τ # χ))
              (float_minus_infinity (:τ # χ)) =
            float_minus_infinity (:τ # χ)) ∧
         (∀mode.
            float_add mode (float_minus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_add mode (float_plus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_plus_infinity (:τ # χ)) ∧
         ∀mode.
           float_add mode (float_plus_infinity (:τ # χ))
             (float_minus_infinity (:τ # χ)) =
           float_some_nan (:τ # χ)

   [float_add_finite]  Theorem

      |- ∀mode x y r1 r2.
           (float_value x = Float r1) ∧ (float_value y = Float r2) ⇒
           (float_add mode x y =
            float_round mode
              (if (r1 = 0) ∧ (r2 = 0) ∧ (x.Sign = y.Sign) then x.Sign = 1w
               else (mode = roundTowardNegative)) (r1 + r2))

   [float_add_finite_minus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_add mode x (float_minus_infinity (:τ # χ)) =
            float_minus_infinity (:τ # χ))

   [float_add_finite_plus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_add mode x (float_plus_infinity (:τ # χ)) =
            float_plus_infinity (:τ # χ))

   [float_add_minus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_add mode (float_minus_infinity (:τ # χ)) x =
            float_minus_infinity (:τ # χ))

   [float_add_nan]  Theorem

      |- ∀mode x y.
           (float_value x = NaN) ∨ (float_value y = NaN) ⇒
           (float_add mode x y = float_some_nan (:τ # χ))

   [float_add_plus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_add mode (float_plus_infinity (:τ # χ)) x =
            float_plus_infinity (:τ # χ))

   [float_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2.
              (M' = float a0 a1 a2) ⇒ (f a0 a1 a2 = f' a0 a1 a2)) ⇒
           (float_CASE M f = float_CASE M' f')

   [float_compare2num_11]  Theorem

      |- ∀a a'. (float_compare2num a = float_compare2num a') ⇔ (a = a')

   [float_compare2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = float_compare2num a

   [float_compare2num_num2float_compare]  Theorem

      |- ∀r. r < 4 ⇔ (float_compare2num (num2float_compare r) = r)

   [float_compare2num_thm]  Theorem

      |- (float_compare2num LT = 0) ∧ (float_compare2num GT = 1) ∧
         (float_compare2num EQ = 2) ∧ (float_compare2num UN = 3)

   [float_compare_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f. (f LT = x0) ∧ (f GT = x1) ∧ (f EQ = x2) ∧ (f UN = x3)

   [float_compare_EQ_float_compare]  Theorem

      |- ∀a a'. (a = a') ⇔ (float_compare2num a = float_compare2num a')

   [float_compare_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = LT) ⇒ (v0 = v0')) ∧ ((M' = GT) ⇒ (v1 = v1')) ∧
           ((M' = EQ) ⇒ (v2 = v2')) ∧ ((M' = UN) ⇒ (v3 = v3')) ⇒
           ((case M of LT => v0 | GT => v1 | EQ => v2 | UN => v3) =
            case M' of LT => v0' | GT => v1' | EQ => v2' | UN => v3')

   [float_compare_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case LT of LT => v0 | GT => v1 | EQ => v2 | UN => v3) = v0) ∧
         (∀v0 v1 v2 v3.
            (case GT of LT => v0 | GT => v1 | EQ => v2 | UN => v3) = v1) ∧
         (∀v0 v1 v2 v3.
            (case EQ of LT => v0 | GT => v1 | EQ => v2 | UN => v3) = v2) ∧
         ∀v0 v1 v2 v3.
           (case UN of LT => v0 | GT => v1 | EQ => v2 | UN => v3) = v3

   [float_compare_distinct]  Theorem

      |- LT ≠ GT ∧ LT ≠ EQ ∧ LT ≠ UN ∧ GT ≠ EQ ∧ GT ≠ UN ∧ EQ ≠ UN

   [float_compare_induction]  Theorem

      |- ∀P. P EQ ∧ P GT ∧ P LT ∧ P UN ⇒ ∀a. P a

   [float_compare_nchotomy]  Theorem

      |- ∀a. (a = LT) ∨ (a = GT) ∨ (a = EQ) ∨ (a = UN)

   [float_component_equality]  Theorem

      |- ∀f1 f2.
           (f1 = f2) ⇔
           (f1.Sign = f2.Sign) ∧ (f1.Exponent = f2.Exponent) ∧
           (f1.Significand = f2.Significand)

   [float_components]  Theorem

      |- ((float_plus_infinity (:τ # χ)).Sign = 0w) ∧
         ((float_plus_infinity (:τ # χ)).Exponent = UINT_MAXw) ∧
         ((float_plus_infinity (:τ # χ)).Significand = 0w) ∧
         ((float_minus_infinity (:τ # χ)).Sign = 1w) ∧
         ((float_minus_infinity (:τ # χ)).Exponent = UINT_MAXw) ∧
         ((float_minus_infinity (:τ # χ)).Significand = 0w) ∧
         ((float_plus_zero (:τ # χ)).Sign = 0w) ∧
         ((float_plus_zero (:τ # χ)).Exponent = 0w) ∧
         ((float_plus_zero (:τ # χ)).Significand = 0w) ∧
         ((float_minus_zero (:τ # χ)).Sign = 1w) ∧
         ((float_minus_zero (:τ # χ)).Exponent = 0w) ∧
         ((float_minus_zero (:τ # χ)).Significand = 0w) ∧
         ((float_plus_min (:τ # χ)).Sign = 0w) ∧
         ((float_plus_min (:τ # χ)).Exponent = 0w) ∧
         ((float_plus_min (:τ # χ)).Significand = 1w) ∧
         ((float_minus_min (:τ # χ)).Sign = 1w) ∧
         ((float_minus_min (:τ # χ)).Exponent = 0w) ∧
         ((float_minus_min (:τ # χ)).Significand = 1w) ∧
         ((float_top (:τ # χ)).Sign = 0w) ∧
         ((float_top (:τ # χ)).Exponent = UINT_MAXw − 1w) ∧
         ((float_top (:τ # χ)).Significand = UINT_MAXw) ∧
         ((float_bottom (:τ # χ)).Sign = 1w) ∧
         ((float_bottom (:τ # χ)).Exponent = UINT_MAXw − 1w) ∧
         ((float_bottom (:τ # χ)).Significand = UINT_MAXw) ∧
         ((float_some_nan (:τ # χ)).Exponent = UINT_MAXw) ∧
         (float_some_nan (:τ # χ)).Significand ≠ 0w ∧
         (∀x. (float_negate x).Sign = ¬x.Sign) ∧
         (∀x. (float_negate x).Exponent = x.Exponent) ∧
         ∀x. (float_negate x).Significand = x.Significand

   [float_distinct]  Theorem

      |- float_plus_infinity (:τ # χ) ≠ float_minus_infinity (:τ # χ) ∧
         float_plus_infinity (:τ # χ) ≠ float_plus_zero (:τ # χ) ∧
         float_plus_infinity (:τ # χ) ≠ float_minus_zero (:τ # χ) ∧
         float_plus_infinity (:τ # χ) ≠ float_top (:τ # χ) ∧
         float_plus_infinity (:τ # χ) ≠ float_bottom (:τ # χ) ∧
         float_plus_infinity (:τ # χ) ≠ float_plus_min (:τ # χ) ∧
         float_plus_infinity (:τ # χ) ≠ float_minus_min (:τ # χ) ∧
         float_plus_infinity (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         float_minus_infinity (:τ # χ) ≠ float_plus_zero (:τ # χ) ∧
         float_minus_infinity (:τ # χ) ≠ float_minus_zero (:τ # χ) ∧
         float_minus_infinity (:τ # χ) ≠ float_top (:τ # χ) ∧
         float_minus_infinity (:τ # χ) ≠ float_bottom (:τ # χ) ∧
         float_minus_infinity (:τ # χ) ≠ float_plus_min (:τ # χ) ∧
         float_minus_infinity (:τ # χ) ≠ float_minus_min (:τ # χ) ∧
         float_minus_infinity (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         float_plus_zero (:τ # χ) ≠ float_minus_zero (:τ # χ) ∧
         float_plus_zero (:τ # χ) ≠ float_top (:τ # χ) ∧
         float_plus_zero (:τ # χ) ≠ float_bottom (:τ # χ) ∧
         float_plus_zero (:τ # χ) ≠ float_plus_min (:τ # χ) ∧
         float_plus_zero (:τ # χ) ≠ float_minus_min (:τ # χ) ∧
         float_plus_zero (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         float_minus_zero (:τ # χ) ≠ float_top (:τ # χ) ∧
         float_minus_zero (:τ # χ) ≠ float_bottom (:τ # χ) ∧
         float_minus_zero (:τ # χ) ≠ float_plus_min (:τ # χ) ∧
         float_minus_zero (:τ # χ) ≠ float_minus_min (:τ # χ) ∧
         float_minus_zero (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         float_top (:τ # χ) ≠ float_minus_min (:τ # χ) ∧
         float_top (:τ # χ) ≠ float_bottom (:τ # χ) ∧
         float_top (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         float_bottom (:τ # χ) ≠ float_plus_min (:τ # χ) ∧
         float_bottom (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         float_plus_min (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         float_plus_min (:τ # χ) ≠ float_minus_min (:τ # χ) ∧
         float_minus_min (:τ # χ) ≠ float_some_nan (:τ # χ) ∧
         ∀x. float_negate x ≠ x

   [float_div_compute]  Theorem

      |- (∀mode x.
            float_div mode (float_some_nan (:τ # χ)) x =
            float_some_nan (:τ # χ)) ∧
         (∀mode x.
            float_div mode x (float_some_nan (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_div mode (float_minus_infinity (:τ # χ))
              (float_minus_infinity (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_div mode (float_minus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_div mode (float_plus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         ∀mode.
           float_div mode (float_plus_infinity (:τ # χ))
             (float_minus_infinity (:τ # χ)) =
           float_some_nan (:τ # χ)

   [float_div_finite]  Theorem

      |- ∀mode x y r1 r2.
           (float_value x = Float r1) ∧ (float_value y = Float r2) ⇒
           (float_div mode x y =
            if r2 = 0 then
              if r1 = 0 then float_some_nan (:τ # χ)
              else if x.Sign = y.Sign then float_plus_infinity (:τ # χ)
              else float_minus_infinity (:τ # χ)
            else float_round mode (x.Sign ≠ y.Sign) (r1 / r2))

   [float_div_finite_minus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_div mode x (float_minus_infinity (:τ # χ)) =
            if x.Sign = 0w then float_minus_zero (:τ # χ)
            else float_plus_zero (:τ # χ))

   [float_div_finite_plus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_div mode x (float_plus_infinity (:τ # χ)) =
            if x.Sign = 0w then float_plus_zero (:τ # χ)
            else float_minus_zero (:τ # χ))

   [float_div_minus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_div mode (float_minus_infinity (:τ # χ)) x =
            if x.Sign = 0w then float_minus_infinity (:τ # χ)
            else float_plus_infinity (:τ # χ))

   [float_div_nan]  Theorem

      |- ∀mode x y.
           (float_value x = NaN) ∨ (float_value y = NaN) ⇒
           (float_div mode x y = float_some_nan (:τ # χ))

   [float_div_plus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_div mode (float_plus_infinity (:τ # χ)) x =
            if x.Sign = 0w then float_plus_infinity (:τ # χ)
            else float_minus_infinity (:τ # χ))

   [float_fn_updates]  Theorem

      |- (∀f c c0 c1.
            float c c0 c1 with Sign updated_by f = float (f c) c0 c1) ∧
         (∀f c c0 c1.
            float c c0 c1 with Exponent updated_by f = float c (f c0) c1) ∧
         ∀f c c0 c1.
           float c c0 c1 with Significand updated_by f = float c c0 (f c1)

   [float_fupdcanon]  Theorem

      |- (∀g f0 f.
            f with <|Exponent updated_by f0; Sign updated_by g|> =
            f with <|Sign updated_by g; Exponent updated_by f0|>) ∧
         (∀g f0 f.
            f with <|Significand updated_by f0; Sign updated_by g|> =
            f with <|Sign updated_by g; Significand updated_by f0|>) ∧
         ∀g f0 f.
           f with <|Significand updated_by f0; Exponent updated_by g|> =
           f with <|Exponent updated_by g; Significand updated_by f0|>

   [float_fupdcanon_comp]  Theorem

      |- ((∀g f0.
              _ record fupdateExponent f0 o  _ record fupdateSign g =
              _ record fupdateSign g o  _ record fupdateExponent f0) ∧
          ∀h g f0.
             _ record fupdateExponent f0 o  _ record fupdateSign g o h =
             _ record fupdateSign g o  _ record fupdateExponent f0 o h) ∧
         ((∀g f0.
              _ record fupdateSignificand f0 o  _ record fupdateSign g =
              _ record fupdateSign g o  _ record fupdateSignificand f0) ∧
          ∀h g f0.
             _ record fupdateSignificand f0 o  _ record fupdateSign g o h =
             _ record fupdateSign g o  _ record fupdateSignificand f0 o
            h) ∧
         (∀g f0.
             _ record fupdateSignificand f0 o  _ record fupdateExponent g =
             _ record fupdateExponent g o
             _ record fupdateSignificand f0) ∧
         ∀h g f0.
            _ record fupdateSignificand f0 o  _ record fupdateExponent g o
           h =
            _ record fupdateExponent g o  _ record fupdateSignificand f0 o
           h

   [float_fupdfupds]  Theorem

      |- (∀g f0 f.
            f with <|Sign updated_by f0; Sign updated_by g|> =
            f with Sign updated_by f0 o g) ∧
         (∀g f0 f.
            f with <|Exponent updated_by f0; Exponent updated_by g|> =
            f with Exponent updated_by f0 o g) ∧
         ∀g f0 f.
           f with <|Significand updated_by f0; Significand updated_by g|> =
           f with Significand updated_by f0 o g

   [float_fupdfupds_comp]  Theorem

      |- ((∀g f0.
              _ record fupdateSign f0 o  _ record fupdateSign g =
              _ record fupdateSign (f0 o g)) ∧
          ∀h g f0.
             _ record fupdateSign f0 o  _ record fupdateSign g o h =
             _ record fupdateSign (f0 o g) o h) ∧
         ((∀g f0.
              _ record fupdateExponent f0 o  _ record fupdateExponent g =
              _ record fupdateExponent (f0 o g)) ∧
          ∀h g f0.
             _ record fupdateExponent f0 o  _ record fupdateExponent g o
            h =
             _ record fupdateExponent (f0 o g) o h) ∧
         (∀g f0.
             _ record fupdateSignificand f0 o
             _ record fupdateSignificand g =
             _ record fupdateSignificand (f0 o g)) ∧
         ∀h g f0.
            _ record fupdateSignificand f0 o
            _ record fupdateSignificand g o h =
            _ record fupdateSignificand (f0 o g) o h

   [float_induction]  Theorem

      |- ∀P. (∀c c0 c1. P (float c c0 c1)) ⇒ ∀f. P f

   [float_infinity_negate_abs]  Theorem

      |- (float_negate (float_plus_infinity (:τ # χ)) =
          float_minus_infinity (:τ # χ)) ∧
         (float_negate (float_minus_infinity (:τ # χ)) =
          float_plus_infinity (:τ # χ)) ∧
         (float_abs (float_plus_infinity (:τ # χ)) =
          float_plus_infinity (:τ # χ)) ∧
         (float_abs (float_minus_infinity (:τ # χ)) =
          float_plus_infinity (:τ # χ))

   [float_is_zero]  Theorem

      |- ∀x. float_is_zero x ⇔ (x.Exponent = 0w) ∧ (x.Significand = 0w)

   [float_is_zero_to_real]  Theorem

      |- ∀x. float_is_zero x ⇔ (float_to_real x = 0)

   [float_literal_11]  Theorem

      |- ∀c11 c01 c1 c12 c02 c2.
           (<|Sign := c11; Exponent := c01; Significand := c1|> =
            <|Sign := c12; Exponent := c02; Significand := c2|>) ⇔
           (c11 = c12) ∧ (c01 = c02) ∧ (c1 = c2)

   [float_literal_nchotomy]  Theorem

      |- ∀f. ∃c1 c0 c. f = <|Sign := c1; Exponent := c0; Significand := c|>

   [float_minus_infinity]  Theorem

      |- float_minus_infinity (:τ # χ) =
         <|Sign := 1w; Exponent := UINT_MAXw; Significand := 0w|>

   [float_minus_zero]  Theorem

      |- float_minus_zero (:τ # χ) =
         <|Sign := 1w; Exponent := 0w; Significand := 0w|>

   [float_mul_compute]  Theorem

      |- (∀mode x.
            float_mul mode (float_some_nan (:τ # χ)) x =
            float_some_nan (:τ # χ)) ∧
         (∀mode x.
            float_mul mode x (float_some_nan (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_mul mode (float_minus_infinity (:τ # χ))
              (float_minus_infinity (:τ # χ)) =
            float_plus_infinity (:τ # χ)) ∧
         (∀mode.
            float_mul mode (float_minus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_minus_infinity (:τ # χ)) ∧
         (∀mode.
            float_mul mode (float_plus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_plus_infinity (:τ # χ)) ∧
         ∀mode.
           float_mul mode (float_plus_infinity (:τ # χ))
             (float_minus_infinity (:τ # χ)) =
           float_minus_infinity (:τ # χ)

   [float_mul_finite]  Theorem

      |- ∀mode x y r1 r2.
           (float_value x = Float r1) ∧ (float_value y = Float r2) ⇒
           (float_mul mode x y =
            float_round mode (x.Sign ≠ y.Sign) (r1 * r2))

   [float_mul_finite_minus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_mul mode x (float_minus_infinity (:τ # χ)) =
            if r = 0 then float_some_nan (:τ # χ)
            else if x.Sign = 0w then float_minus_infinity (:τ # χ)
            else float_plus_infinity (:τ # χ))

   [float_mul_finite_plus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_mul mode x (float_plus_infinity (:τ # χ)) =
            if r = 0 then float_some_nan (:τ # χ)
            else if x.Sign = 0w then float_plus_infinity (:τ # χ)
            else float_minus_infinity (:τ # χ))

   [float_mul_minus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_mul mode (float_minus_infinity (:τ # χ)) x =
            if r = 0 then float_some_nan (:τ # χ)
            else if x.Sign = 0w then float_minus_infinity (:τ # χ)
            else float_plus_infinity (:τ # χ))

   [float_mul_nan]  Theorem

      |- ∀mode x y.
           (float_value x = NaN) ∨ (float_value y = NaN) ⇒
           (float_mul mode x y = float_some_nan (:τ # χ))

   [float_mul_plus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_mul mode (float_plus_infinity (:τ # χ)) x =
            if r = 0 then float_some_nan (:τ # χ)
            else if x.Sign = 0w then float_plus_infinity (:τ # χ)
            else float_minus_infinity (:τ # χ))

   [float_nchotomy]  Theorem

      |- ∀ff. ∃c c0 c1. ff = float c c0 c1

   [float_negate_negate]  Theorem

      |- ∀x. float_negate (float_negate x) = x

   [float_round_bottom]  Theorem

      |- ∀mode toneg r.
           (round mode r = float_bottom (:τ # χ)) ⇒
           (float_round mode toneg r = float_bottom (:τ # χ))

   [float_round_minus_infinity]  Theorem

      |- ∀mode toneg r.
           (round mode r = float_minus_infinity (:τ # χ)) ⇒
           (float_round mode toneg r = float_minus_infinity (:τ # χ))

   [float_round_non_zero]  Theorem

      |- ∀mode toneg r s e f.
           (round mode r =
            <|Sign := s; Exponent := e; Significand := f|>) ∧
           (e ≠ 0w ∨ f ≠ 0w) ⇒
           (float_round mode toneg r =
            <|Sign := s; Exponent := e; Significand := f|>)

   [float_round_plus_infinity]  Theorem

      |- ∀mode toneg r.
           (round mode r = float_plus_infinity (:τ # χ)) ⇒
           (float_round mode toneg r = float_plus_infinity (:τ # χ))

   [float_round_roundTowardNegative_minus_infinity]  Theorem

      |- ∀b y x.
           x < -largest (:τ # χ) ⇒
           (float_round roundTowardNegative b x =
            float_minus_infinity (:τ # χ))

   [float_round_roundTowardNegative_top]  Theorem

      |- ∀b y x.
           largest (:τ # χ) < x ⇒
           (float_round roundTowardNegative b x = float_top (:τ # χ))

   [float_round_roundTowardPositive_bottom]  Theorem

      |- ∀b y x.
           x < -largest (:τ # χ) ⇒
           (float_round roundTowardPositive b x = float_bottom (:τ # χ))

   [float_round_roundTowardPositive_plus_infinity]  Theorem

      |- ∀b y x.
           largest (:τ # χ) < x ⇒
           (float_round roundTowardPositive b x =
            float_plus_infinity (:τ # χ))

   [float_round_roundTowardZero_bottom]  Theorem

      |- ∀b y x.
           x < -largest (:τ # χ) ⇒
           (float_round roundTowardZero b x = float_bottom (:τ # χ))

   [float_round_roundTowardZero_top]  Theorem

      |- ∀b y x.
           largest (:τ # χ) < x ⇒
           (float_round roundTowardZero b x = float_top (:τ # χ))

   [float_round_top]  Theorem

      |- ∀mode toneg r.
           (round mode r = float_top (:τ # χ)) ⇒
           (float_round mode toneg r = float_top (:τ # χ))

   [float_sets]  Theorem

      |- (float_is_zero =
          {float_minus_zero (:τ # χ); float_plus_zero (:τ # χ)}) ∧
         (float_is_infinite =
          {float_minus_infinity (:τ # χ); float_plus_infinity (:τ # χ)})

   [float_sub_compute]  Theorem

      |- (∀mode x.
            float_sub mode (float_some_nan (:τ # χ)) x =
            float_some_nan (:τ # χ)) ∧
         (∀mode x.
            float_sub mode x (float_some_nan (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_sub mode (float_minus_infinity (:τ # χ))
              (float_minus_infinity (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         (∀mode.
            float_sub mode (float_minus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_minus_infinity (:τ # χ)) ∧
         (∀mode.
            float_sub mode (float_plus_infinity (:τ # χ))
              (float_plus_infinity (:τ # χ)) =
            float_some_nan (:τ # χ)) ∧
         ∀mode.
           float_sub mode (float_plus_infinity (:τ # χ))
             (float_minus_infinity (:τ # χ)) =
           float_plus_infinity (:τ # χ)

   [float_sub_finite]  Theorem

      |- ∀mode x y r1 r2.
           (float_value x = Float r1) ∧ (float_value y = Float r2) ⇒
           (float_sub mode x y =
            float_round mode
              (if (r1 = 0) ∧ (r2 = 0) ∧ x.Sign ≠ y.Sign then x.Sign = 1w
               else (mode = roundTowardNegative)) (r1 − r2))

   [float_sub_finite_minus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_sub mode x (float_minus_infinity (:τ # χ)) =
            float_plus_infinity (:τ # χ))

   [float_sub_finite_plus_infinity]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_sub mode x (float_plus_infinity (:τ # χ)) =
            float_minus_infinity (:τ # χ))

   [float_sub_minus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_sub mode (float_minus_infinity (:τ # χ)) x =
            float_minus_infinity (:τ # χ))

   [float_sub_nan]  Theorem

      |- ∀mode x y.
           (float_value x = NaN) ∨ (float_value y = NaN) ⇒
           (float_sub mode x y = float_some_nan (:τ # χ))

   [float_sub_plus_infinity_finite]  Theorem

      |- ∀mode x r.
           (float_value x = Float r) ⇒
           (float_sub mode (float_plus_infinity (:τ # χ)) x =
            float_plus_infinity (:τ # χ))

   [float_tests]  Theorem

      |- (∀s e f.
            float_is_nan <|Sign := s; Exponent := e; Significand := f|> ⇔
            (e = -1w) ∧ f ≠ 0w) ∧
         (∀s e f.
            float_is_infinite
              <|Sign := s; Exponent := e; Significand := f|> ⇔
            (e = -1w) ∧ (f = 0w)) ∧
         (∀s e f.
            float_is_normal
              <|Sign := s; Exponent := e; Significand := f|> ⇔
            e ≠ 0w ∧ e ≠ -1w) ∧
         (∀s e f.
            float_is_subnormal
              <|Sign := s; Exponent := e; Significand := f|> ⇔
            (e = 0w) ∧ f ≠ 0w) ∧
         (∀s e f.
            float_is_zero <|Sign := s; Exponent := e; Significand := f|> ⇔
            (e = 0w) ∧ (f = 0w)) ∧
         ∀s e f.
           float_is_finite <|Sign := s; Exponent := e; Significand := f|> ⇔
           e ≠ -1w

   [float_to_real]  Theorem

      |- ∀s e f.
           float_to_real <|Sign := s; Exponent := e; Significand := f|> =
           (let r =
                  if e = 0w then
                    2 / &(2 ** bias (:χ)) * (&w2n f / &dimword (:τ))
                  else
                    &(2 ** w2n e) / &(2 ** bias (:χ)) *
                    (1 + &w2n f / &dimword (:τ))
            in
              if s = 1w then -r else r)

   [float_to_real_eq]  Theorem

      |- ∀x y.
           (float_to_real x = float_to_real y) ⇔
           (x = y) ∨ float_is_zero x ∧ float_is_zero y

   [float_to_real_negate]  Theorem

      |- ∀x. float_to_real (float_negate x) = -float_to_real x

   [float_updates_eq_literal]  Theorem

      |- ∀f c1 c0 c.
           f with <|Sign := c1; Exponent := c0; Significand := c|> =
           <|Sign := c1; Exponent := c0; Significand := c|>

   [float_value_11]  Theorem

      |- ∀a a'. (Float a = Float a') ⇔ (a = a')

   [float_value_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (∀a. fn (Float a) = f0 a) ∧ (fn Infinity = f1) ∧ (fn NaN = f2)

   [float_value_case_cong]  Theorem

      |- ∀M M' f v v1.
           (M = M') ∧ (∀a. (M' = Float a) ⇒ (f a = f' a)) ∧
           ((M' = Infinity) ⇒ (v = v')) ∧ ((M' = NaN) ⇒ (v1 = v1')) ⇒
           (float_value_CASE M f v v1 = float_value_CASE M' f' v' v1')

   [float_value_distinct]  Theorem

      |- (∀a. Float a ≠ Infinity) ∧ (∀a. Float a ≠ NaN) ∧ Infinity ≠ NaN

   [float_value_induction]  Theorem

      |- ∀P. (∀r. P (Float r)) ∧ P Infinity ∧ P NaN ⇒ ∀f. P f

   [float_value_nchotomy]  Theorem

      |- ∀ff. (∃r. ff = Float r) ∨ (ff = Infinity) ∨ (ff = NaN)

   [float_values]  Theorem

      |- (float_value (float_plus_infinity (:τ # χ)) = Infinity) ∧
         (float_value (float_minus_infinity (:τ # χ)) = Infinity) ∧
         (float_value (float_some_nan (:τ # χ)) = NaN) ∧
         (float_value (float_plus_zero (:τ # χ)) = Float 0) ∧
         (float_value (float_minus_zero (:τ # χ)) = Float 0) ∧
         (float_value (float_plus_min (:τ # χ)) =
          Float (2 / 2 pow (bias (:χ) + precision (:τ)))) ∧
         (float_value (float_minus_min (:τ # χ)) =
          Float (-2 / 2 pow (bias (:χ) + precision (:τ))))

   [infinity_properties]  Theorem

      |- ¬float_is_zero (float_plus_infinity (:τ # χ)) ∧
         ¬float_is_zero (float_minus_infinity (:τ # χ)) ∧
         ¬float_is_finite (float_plus_infinity (:τ # χ)) ∧
         ¬float_is_finite (float_minus_infinity (:τ # χ)) ∧
         ¬float_is_integral (float_plus_infinity (:τ # χ)) ∧
         ¬float_is_integral (float_minus_infinity (:τ # χ)) ∧
         ¬float_is_nan (float_plus_infinity (:τ # χ)) ∧
         ¬float_is_nan (float_minus_infinity (:τ # χ)) ∧
         ¬float_is_normal (float_plus_infinity (:τ # χ)) ∧
         ¬float_is_normal (float_minus_infinity (:τ # χ)) ∧
         ¬float_is_subnormal (float_plus_infinity (:τ # χ)) ∧
         ¬float_is_subnormal (float_minus_infinity (:τ # χ)) ∧
         float_is_infinite (float_plus_infinity (:τ # χ)) ∧
         float_is_infinite (float_minus_infinity (:τ # χ))

   [largest]  Theorem

      |- largest (:τ # χ) =
         &(2 ** (UINT_MAX (:χ) − 1)) * (2 − 1 / &dimword (:τ)) /
         &(2 ** bias (:χ))

   [largest_is_positive]  Theorem

      |- 0 ≤ largest (:τ # χ)

   [le2]  Theorem

      |- ∀n m. 2 ≤ n ∧ 2 ≤ m ⇒ 2 ≤ n * m

   [less_than_ulp]  Theorem

      |- ∀a.
           abs (float_to_real a) < ulp (:τ # χ) ⇔
           (a.Exponent = 0w) ∧ (a.Significand = 0w)

   [min_properties]  Theorem

      |- ¬float_is_zero (float_plus_min (:τ # χ)) ∧
         float_is_finite (float_plus_min (:τ # χ)) ∧
         (float_is_integral (float_plus_min (:τ # χ)) ⇔
          (precision (:χ) = 1) ∧ (precision (:τ) = 1)) ∧
         ¬float_is_nan (float_plus_min (:τ # χ)) ∧
         ¬float_is_normal (float_plus_min (:τ # χ)) ∧
         float_is_subnormal (float_plus_min (:τ # χ)) ∧
         ¬float_is_infinite (float_plus_min (:τ # χ)) ∧
         ¬float_is_zero (float_minus_min (:τ # χ)) ∧
         float_is_finite (float_minus_min (:τ # χ)) ∧
         (float_is_integral (float_minus_min (:τ # χ)) ⇔
          (precision (:χ) = 1) ∧ (precision (:τ) = 1)) ∧
         ¬float_is_nan (float_minus_min (:τ # χ)) ∧
         ¬float_is_normal (float_minus_min (:τ # χ)) ∧
         float_is_subnormal (float_minus_min (:τ # χ)) ∧
         ¬float_is_infinite (float_minus_min (:τ # χ))

   [neg_ulp]  Theorem

      |- -ulp (:τ # χ) =
         float_to_real (float_negate (float_plus_min (:τ # χ)))

   [num2float_compare_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒
           r' < 4 ⇒
           ((num2float_compare r = num2float_compare r') ⇔ (r = r'))

   [num2float_compare_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2float_compare r) ∧ r < 4

   [num2float_compare_float_compare2num]  Theorem

      |- ∀a. num2float_compare (float_compare2num a) = a

   [num2float_compare_thm]  Theorem

      |- (num2float_compare 0 = LT) ∧ (num2float_compare 1 = GT) ∧
         (num2float_compare 2 = EQ) ∧ (num2float_compare 3 = UN)

   [num2rounding_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒ r' < 4 ⇒ ((num2rounding r = num2rounding r') ⇔ (r = r'))

   [num2rounding_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2rounding r) ∧ r < 4

   [num2rounding_rounding2num]  Theorem

      |- ∀a. num2rounding (rounding2num a) = a

   [num2rounding_thm]  Theorem

      |- (num2rounding 0 = roundTiesToEven) ∧
         (num2rounding 1 = roundTowardPositive) ∧
         (num2rounding 2 = roundTowardNegative) ∧
         (num2rounding 3 = roundTowardZero)

   [round_roundTiesToEven]  Theorem

      |- ∀y x r.
           (float_value y = Float r) ∧
           ((y.Significand = 0w) ∧ y.Exponent ≠ 1w ⇒ abs r ≤ abs x) ∧
           2 * abs (r − x) ≤ ULP (y.Exponent,(:τ)) ∧
           ((2 * abs (r − x) = ULP (y.Exponent,(:τ))) ⇒
            ¬word_lsb y.Significand) ∧ ulp (:τ # χ) < 2 * abs x ∧
           abs x < threshold (:τ # χ) ⇒
           (round roundTiesToEven x = y)

   [round_roundTiesToEven0]  Theorem

      |- ∀y x r.
           (float_value y = Float r) ∧
           ((y.Significand = 0w) ∧ y.Exponent ≠ 1w ∧ ¬(abs r ≤ abs x)) ∧
           4 * abs (r − x) ≤ ULP (y.Exponent,(:τ)) ∧
           ulp (:τ # χ) < 2 * abs x ∧ abs x < threshold (:τ # χ) ⇒
           (round roundTiesToEven x = y)

   [round_roundTiesToEven_is_minus_zero]  Theorem

      |- ∀x.
           2 * abs x ≤ ulp (:τ # χ) ⇒
           (float_round roundTiesToEven T x = float_minus_zero (:τ # χ))

   [round_roundTiesToEven_is_plus_zero]  Theorem

      |- ∀x.
           2 * abs x ≤ ulp (:τ # χ) ⇒
           (float_round roundTiesToEven F x = float_plus_zero (:τ # χ))

   [round_roundTiesToEven_is_zero]  Theorem

      |- ∀x.
           2 * abs x ≤ ulp (:τ # χ) ⇒
           (round roundTiesToEven x = float_plus_zero (:τ # χ)) ∨
           (round roundTiesToEven x = float_minus_zero (:τ # χ))

   [round_roundTiesToEven_minus_infinity]  Theorem

      |- ∀y x.
           x ≤ -threshold (:τ # χ) ⇒
           (round roundTiesToEven x = float_minus_infinity (:τ # χ))

   [round_roundTiesToEven_plus_infinity]  Theorem

      |- ∀y x.
           threshold (:τ # χ) ≤ x ⇒
           (round roundTiesToEven x = float_plus_infinity (:τ # χ))

   [round_roundTowardNegative_minus_infinity]  Theorem

      |- ∀y x.
           x < -largest (:τ # χ) ⇒
           (round roundTowardNegative x = float_minus_infinity (:τ # χ))

   [round_roundTowardNegative_top]  Theorem

      |- ∀y x.
           largest (:τ # χ) < x ⇒
           (round roundTowardNegative x = float_top (:τ # χ))

   [round_roundTowardPositive_bottom]  Theorem

      |- ∀y x.
           x < -largest (:τ # χ) ⇒
           (round roundTowardPositive x = float_bottom (:τ # χ))

   [round_roundTowardPositive_plus_infinity]  Theorem

      |- ∀y x.
           largest (:τ # χ) < x ⇒
           (round roundTowardPositive x = float_plus_infinity (:τ # χ))

   [round_roundTowardZero]  Theorem

      |- ∀y x r.
           (float_value y = Float r) ∧
           abs (r − x) < ULP (y.Exponent,(:τ)) ∧ abs r ≤ abs x ∧
           ulp (:τ # χ) ≤ abs x ∧ abs x ≤ largest (:τ # χ) ⇒
           (round roundTowardZero x = y)

   [round_roundTowardZero_bottom]  Theorem

      |- ∀y x.
           x < -largest (:τ # χ) ⇒
           (round roundTowardZero x = float_bottom (:τ # χ))

   [round_roundTowardZero_is_minus_zero]  Theorem

      |- ∀x.
           abs x < ulp (:τ # χ) ⇒
           (float_round roundTowardZero T x = float_minus_zero (:τ # χ))

   [round_roundTowardZero_is_plus_zero]  Theorem

      |- ∀x.
           abs x < ulp (:τ # χ) ⇒
           (float_round roundTowardZero F x = float_plus_zero (:τ # χ))

   [round_roundTowardZero_is_zero]  Theorem

      |- ∀x.
           abs x < ulp (:τ # χ) ⇒
           (round roundTowardZero x = float_plus_zero (:τ # χ)) ∨
           (round roundTowardZero x = float_minus_zero (:τ # χ))

   [round_roundTowardZero_top]  Theorem

      |- ∀y x.
           largest (:τ # χ) < x ⇒
           (round roundTowardZero x = float_top (:τ # χ))

   [rounding2num_11]  Theorem

      |- ∀a a'. (rounding2num a = rounding2num a') ⇔ (a = a')

   [rounding2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = rounding2num a

   [rounding2num_num2rounding]  Theorem

      |- ∀r. r < 4 ⇔ (rounding2num (num2rounding r) = r)

   [rounding2num_thm]  Theorem

      |- (rounding2num roundTiesToEven = 0) ∧
         (rounding2num roundTowardPositive = 1) ∧
         (rounding2num roundTowardNegative = 2) ∧
         (rounding2num roundTowardZero = 3)

   [rounding_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f roundTiesToEven = x0) ∧ (f roundTowardPositive = x1) ∧
             (f roundTowardNegative = x2) ∧ (f roundTowardZero = x3)

   [rounding_EQ_rounding]  Theorem

      |- ∀a a'. (a = a') ⇔ (rounding2num a = rounding2num a')

   [rounding_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = roundTiesToEven) ⇒ (v0 = v0')) ∧
           ((M' = roundTowardPositive) ⇒ (v1 = v1')) ∧
           ((M' = roundTowardNegative) ⇒ (v2 = v2')) ∧
           ((M' = roundTowardZero) ⇒ (v3 = v3')) ⇒
           ((case M of
               roundTiesToEven => v0
             | roundTowardPositive => v1
             | roundTowardNegative => v2
             | roundTowardZero => v3) =
            case M' of
              roundTiesToEven => v0'
            | roundTowardPositive => v1'
            | roundTowardNegative => v2'
            | roundTowardZero => v3')

   [rounding_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case roundTiesToEven of
               roundTiesToEven => v0
             | roundTowardPositive => v1
             | roundTowardNegative => v2
             | roundTowardZero => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case roundTowardPositive of
               roundTiesToEven => v0
             | roundTowardPositive => v1
             | roundTowardNegative => v2
             | roundTowardZero => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case roundTowardNegative of
               roundTiesToEven => v0
             | roundTowardPositive => v1
             | roundTowardNegative => v2
             | roundTowardZero => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case roundTowardZero of
              roundTiesToEven => v0
            | roundTowardPositive => v1
            | roundTowardNegative => v2
            | roundTowardZero => v3) =
           v3

   [rounding_distinct]  Theorem

      |- roundTiesToEven ≠ roundTowardPositive ∧
         roundTiesToEven ≠ roundTowardNegative ∧
         roundTiesToEven ≠ roundTowardZero ∧
         roundTowardPositive ≠ roundTowardNegative ∧
         roundTowardPositive ≠ roundTowardZero ∧
         roundTowardNegative ≠ roundTowardZero

   [rounding_induction]  Theorem

      |- ∀P.
           P roundTiesToEven ∧ P roundTowardNegative ∧
           P roundTowardPositive ∧ P roundTowardZero ⇒
           ∀a. P a

   [rounding_nchotomy]  Theorem

      |- ∀a.
           (a = roundTiesToEven) ∨ (a = roundTowardPositive) ∨
           (a = roundTowardNegative) ∨ (a = roundTowardZero)

   [sign_not_zero]  Theorem

      |- ∀s. -1 pow w2n s ≠ 0

   [some_nan_properties]  Theorem

      |- ¬float_is_zero (float_some_nan (:τ # χ)) ∧
         ¬float_is_finite (float_some_nan (:τ # χ)) ∧
         ¬float_is_integral (float_some_nan (:τ # χ)) ∧
         float_is_nan (float_some_nan (:τ # χ)) ∧
         ¬float_is_normal (float_some_nan (:τ # χ)) ∧
         ¬float_is_subnormal (float_some_nan (:τ # χ)) ∧
         ¬float_is_infinite (float_some_nan (:τ # χ))

   [threshold]  Theorem

      |- threshold (:τ # χ) =
         &(2 ** (UINT_MAX (:χ) − 1)) * (2 − 1 / &(2 * dimword (:τ))) /
         &(2 ** bias (:χ))

   [threshold_is_positive]  Theorem

      |- 0 < threshold (:τ # χ)

   [top_properties]  Theorem

      |- ¬float_is_zero (float_top (:τ # χ)) ∧
         float_is_finite (float_top (:τ # χ)) ∧
         ¬float_is_nan (float_top (:τ # χ)) ∧
         (float_is_normal (float_top (:τ # χ)) ⇔ precision (:χ) ≠ 1) ∧
         (float_is_subnormal (float_top (:τ # χ)) ⇔ (precision (:χ) = 1)) ∧
         ¬float_is_infinite (float_top (:τ # χ))

   [ulp]  Theorem

      |- ulp (:τ # χ) = float_to_real (float_plus_min (:τ # χ))

   [ulp_lt_ULP]  Theorem

      |- ∀e. ulp (:τ # χ) ≤ ULP (e,(:τ))

   [ulp_lt_largest]  Theorem

      |- ulp (:τ # χ) < largest (:τ # χ)

   [ulp_lt_threshold]  Theorem

      |- ulp (:τ # χ) < threshold (:τ # χ)

   [zero_le_pos_div_twopow]  Theorem

      |- ∀m n. 0 ≤ &m / 2 pow n

   [zero_le_twopow]  Theorem

      |- ∀n. 0 ≤ 2 pow n

   [zero_lt_twopow]  Theorem

      |- ∀n. 0 < 2 pow n

   [zero_neq_twopow]  Theorem

      |- ∀n. 2 pow n ≠ 0

   [zero_properties]  Theorem

      |- float_is_zero (float_plus_zero (:τ # χ)) ∧
         float_is_zero (float_minus_zero (:τ # χ)) ∧
         float_is_finite (float_plus_zero (:τ # χ)) ∧
         float_is_finite (float_minus_zero (:τ # χ)) ∧
         float_is_integral (float_plus_zero (:τ # χ)) ∧
         float_is_integral (float_minus_zero (:τ # χ)) ∧
         ¬float_is_nan (float_plus_zero (:τ # χ)) ∧
         ¬float_is_nan (float_minus_zero (:τ # χ)) ∧
         ¬float_is_normal (float_plus_zero (:τ # χ)) ∧
         ¬float_is_normal (float_minus_zero (:τ # χ)) ∧
         ¬float_is_subnormal (float_plus_zero (:τ # χ)) ∧
         ¬float_is_subnormal (float_minus_zero (:τ # χ)) ∧
         ¬float_is_infinite (float_plus_zero (:τ # χ)) ∧
         ¬float_is_infinite (float_minus_zero (:τ # χ))

   [zero_to_real]  Theorem

      |- (float_to_real (float_plus_zero (:τ # χ)) = 0) ∧
         (float_to_real (float_minus_zero (:τ # χ)) = 0)


*)
end
