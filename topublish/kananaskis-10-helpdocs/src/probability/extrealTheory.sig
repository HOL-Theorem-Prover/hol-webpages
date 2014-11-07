signature extrealTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val EXTREAL_SUM_IMAGE_DEF : thm
    val Q_set_def : thm
    val ceiling_def : thm
    val ext_mono_decreasing_def : thm
    val ext_mono_increasing_def : thm
    val ext_suminf_def : thm
    val extreal_TY_DEF : thm
    val extreal_abs_primitive_def : thm
    val extreal_add_curried_def : thm
    val extreal_add_tupled_primitive_def : thm
    val extreal_ainv_def : thm
    val extreal_case_def : thm
    val extreal_div_def : thm
    val extreal_exp_def : thm
    val extreal_inf_def : thm
    val extreal_inv_def : thm
    val extreal_le_curried_def : thm
    val extreal_le_tupled_primitive_def : thm
    val extreal_lg_def : thm
    val extreal_logr_def : thm
    val extreal_lt_def : thm
    val extreal_max_def : thm
    val extreal_min_def : thm
    val extreal_mul_curried_def : thm
    val extreal_mul_tupled_primitive_def : thm
    val extreal_of_num_def : thm
    val extreal_pow_def : thm
    val extreal_size_def : thm
    val extreal_sqrt_def : thm
    val extreal_sub_curried_def : thm
    val extreal_sub_tupled_primitive_def : thm
    val extreal_sup_def : thm
    val mono_decreasing_def : thm
    val mono_increasing_def : thm
    val open_interval_def : thm
    val open_intervals_set_def : thm
    val rational_intervals_def : thm
    val real_def : thm

  (*  Theorems  *)
    val ADD_IN_Q : thm
    val CEILING_LBOUND : thm
    val CEILING_UBOUND : thm
    val CMUL_IN_Q : thm
    val COUNTABLE_ENUM_Q : thm
    val COUNTABLE_RATIONAL_INTERVALS : thm
    val CROSS_COUNTABLE : thm
    val CROSS_COUNTABLE_LEMMA1 : thm
    val CROSS_COUNTABLE_LEMMA2 : thm
    val CROSS_COUNTABLE_UNIV : thm
    val DIV_IN_Q : thm
    val EXTREAL_ARCH : thm
    val EXTREAL_ARCH_POW : thm
    val EXTREAL_ARCH_POW_INV : thm
    val EXTREAL_EQ_LADD : thm
    val EXTREAL_SUM_IMAGE_0 : thm
    val EXTREAL_SUM_IMAGE_ADD : thm
    val EXTREAL_SUM_IMAGE_CMUL : thm
    val EXTREAL_SUM_IMAGE_CMUL2 : thm
    val EXTREAL_SUM_IMAGE_COUNT : thm
    val EXTREAL_SUM_IMAGE_CROSS_SYM : thm
    val EXTREAL_SUM_IMAGE_DISJOINT_UNION : thm
    val EXTREAL_SUM_IMAGE_EQ : thm
    val EXTREAL_SUM_IMAGE_EQ_CARD : thm
    val EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE : thm
    val EXTREAL_SUM_IMAGE_FINITE_CONST : thm
    val EXTREAL_SUM_IMAGE_FINITE_SAME : thm
    val EXTREAL_SUM_IMAGE_IF_ELIM : thm
    val EXTREAL_SUM_IMAGE_IMAGE : thm
    val EXTREAL_SUM_IMAGE_INTER_ELIM : thm
    val EXTREAL_SUM_IMAGE_INTER_NONZERO : thm
    val EXTREAL_SUM_IMAGE_INV_CARD_EQ_1 : thm
    val EXTREAL_SUM_IMAGE_IN_IF : thm
    val EXTREAL_SUM_IMAGE_IN_IF_ALT : thm
    val EXTREAL_SUM_IMAGE_MONO : thm
    val EXTREAL_SUM_IMAGE_MONO_SET : thm
    val EXTREAL_SUM_IMAGE_NORMAL : thm
    val EXTREAL_SUM_IMAGE_NOT_INFTY : thm
    val EXTREAL_SUM_IMAGE_NOT_NEG_INF : thm
    val EXTREAL_SUM_IMAGE_NOT_POS_INF : thm
    val EXTREAL_SUM_IMAGE_POS : thm
    val EXTREAL_SUM_IMAGE_POS_MEM_LE : thm
    val EXTREAL_SUM_IMAGE_SING : thm
    val EXTREAL_SUM_IMAGE_SPOS : thm
    val EXTREAL_SUM_IMAGE_SUB : thm
    val EXTREAL_SUM_IMAGE_THM : thm
    val EXTREAL_SUM_IMAGE_ZERO : thm
    val EXTREAL_SUM_IMAGE_ZERO_DIFF : thm
    val INV_IN_Q : thm
    val LOGR_MONO_LE : thm
    val LOGR_MONO_LE_IMP : thm
    val MUL_IN_Q : thm
    val NUM_IN_Q : thm
    val OPP_IN_Q : thm
    val POW_NEG_ODD : thm
    val POW_POS_EVEN : thm
    val Q_COUNTABLE : thm
    val Q_DENSE_IN_R : thm
    val Q_DENSE_IN_R_LEMMA : thm
    val Q_INFINITE : thm
    val Q_not_infty : thm
    val REAL_ARCH_POW : thm
    val REAL_LE_MUL_EPSILON : thm
    val REAL_LE_RDIV_EQ_NEG : thm
    val REAL_LT_LMUL_0_NEG : thm
    val REAL_LT_LMUL_NEG_0 : thm
    val REAL_LT_LMUL_NEG_0_NEG : thm
    val REAL_LT_RDIV_EQ_NEG : thm
    val REAL_LT_RMUL_0_NEG : thm
    val REAL_LT_RMUL_NEG_0 : thm
    val REAL_LT_RMUL_NEG_0_NEG : thm
    val SIMP_EXTREAL_ARCH : thm
    val SIMP_REAL_ARCH : thm
    val SIMP_REAL_ARCH_NEG : thm
    val SUB_IN_Q : thm
    val abs_bounds : thm
    val abs_bounds_lt : thm
    val abs_pos : thm
    val abs_refl : thm
    val add2_sub2 : thm
    val add_assoc : thm
    val add_comm : thm
    val add_infty : thm
    val add_ldistrib : thm
    val add_ldistrib_neg : thm
    val add_ldistrib_normal : thm
    val add_ldistrib_normal2 : thm
    val add_ldistrib_pos : thm
    val add_lzero : thm
    val add_not_infty : thm
    val add_pow2 : thm
    val add_rdistrib : thm
    val add_rdistrib_normal : thm
    val add_rdistrib_normal2 : thm
    val add_rzero : thm
    val add_sub : thm
    val add_sub2 : thm
    val datatype_extreal : thm
    val div_add : thm
    val div_one : thm
    val entire : thm
    val eq_add_sub_switch : thm
    val eq_neg : thm
    val eq_sub_ladd : thm
    val eq_sub_ladd_normal : thm
    val eq_sub_radd : thm
    val eq_sub_switch : thm
    val ext_mono_decreasing_suc : thm
    val ext_mono_increasing_suc : thm
    val ext_suminf_add : thm
    val ext_suminf_cmul : thm
    val ext_suminf_cmul_alt : thm
    val ext_suminf_lt_infty : thm
    val ext_suminf_mono : thm
    val ext_suminf_sub : thm
    val ext_suminf_sum : thm
    val ext_suminf_suminf : thm
    val extreal_11 : thm
    val extreal_Axiom : thm
    val extreal_abs_def : thm
    val extreal_abs_ind : thm
    val extreal_add_def : thm
    val extreal_add_ind : thm
    val extreal_case_cong : thm
    val extreal_cases : thm
    val extreal_distinct : thm
    val extreal_div_eq : thm
    val extreal_eq_zero : thm
    val extreal_induction : thm
    val extreal_le_def : thm
    val extreal_le_ind : thm
    val extreal_lt_eq : thm
    val extreal_mul_def : thm
    val extreal_mul_ind : thm
    val extreal_nchotomy : thm
    val extreal_not_infty : thm
    val extreal_sub_add : thm
    val extreal_sub_def : thm
    val extreal_sub_ind : thm
    val fourth_cancel : thm
    val half_between : thm
    val half_cancel : thm
    val inf_cminus : thm
    val inf_const : thm
    val inf_const_alt : thm
    val inf_const_over_set : thm
    val inf_eq : thm
    val inf_le : thm
    val inf_le_imp : thm
    val inf_lt_infty : thm
    val inf_min : thm
    val inf_seq : thm
    val inf_suc : thm
    val inv_1over : thm
    val inv_one : thm
    val inv_pos : thm
    val le_01 : thm
    val le_02 : thm
    val le_add : thm
    val le_add2 : thm
    val le_addr : thm
    val le_addr_imp : thm
    val le_antisym : thm
    val le_epsilon : thm
    val le_inf : thm
    val le_infty : thm
    val le_inv : thm
    val le_ladd : thm
    val le_ladd_imp : thm
    val le_ldiv : thm
    val le_lmul_imp : thm
    val le_lneg : thm
    val le_lsub_imp : thm
    val le_lt : thm
    val le_max : thm
    val le_max1 : thm
    val le_max2 : thm
    val le_min : thm
    val le_mul : thm
    val le_mul_epsilon : thm
    val le_mul_neg : thm
    val le_neg : thm
    val le_num : thm
    val le_pow2 : thm
    val le_radd : thm
    val le_radd_imp : thm
    val le_rdiv : thm
    val le_refl : thm
    val le_rmul_imp : thm
    val le_sub_eq : thm
    val le_sub_eq2 : thm
    val le_sub_imp : thm
    val le_sup : thm
    val le_sup_imp : thm
    val le_total : thm
    val le_trans : thm
    val let_add : thm
    val let_add2 : thm
    val let_add2_alt : thm
    val let_mul : thm
    val let_trans : thm
    val linv_uniq : thm
    val logr_not_infty : thm
    val lt_01 : thm
    val lt_02 : thm
    val lt_add : thm
    val lt_add2 : thm
    val lt_addl : thm
    val lt_antisym : thm
    val lt_imp_le : thm
    val lt_imp_ne : thm
    val lt_infty : thm
    val lt_ladd : thm
    val lt_ldiv : thm
    val lt_le : thm
    val lt_lmul : thm
    val lt_mul : thm
    val lt_mul2 : thm
    val lt_mul_neg : thm
    val lt_neg : thm
    val lt_radd : thm
    val lt_rdiv : thm
    val lt_rdiv_neg : thm
    val lt_refl : thm
    val lt_rmul : thm
    val lt_sub : thm
    val lt_sub_imp : thm
    val lt_total : thm
    val lt_trans : thm
    val lte_add : thm
    val lte_mul : thm
    val lte_trans : thm
    val max_comm : thm
    val max_infty : thm
    val max_le : thm
    val max_le2_imp : thm
    val max_refl : thm
    val min_comm : thm
    val min_infty : thm
    val min_le : thm
    val min_le1 : thm
    val min_le2 : thm
    val min_le2_imp : thm
    val min_refl : thm
    val mono_decreasing_suc : thm
    val mono_increasing_converges_to_sup : thm
    val mono_increasing_suc : thm
    val mul_assoc : thm
    val mul_comm : thm
    val mul_le : thm
    val mul_let : thm
    val mul_lneg : thm
    val mul_lone : thm
    val mul_lt : thm
    val mul_lte : thm
    val mul_lzero : thm
    val mul_not_infty : thm
    val mul_not_infty2 : thm
    val mul_rneg : thm
    val mul_rone : thm
    val mul_rzero : thm
    val ne_01 : thm
    val ne_02 : thm
    val neg_0 : thm
    val neg_eq0 : thm
    val neg_minus1 : thm
    val neg_mul2 : thm
    val neg_neg : thm
    val neg_sub : thm
    val normal_real : thm
    val num_not_infty : thm
    val pow2_sqrt : thm
    val pow_0 : thm
    val pow_1 : thm
    val pow_2 : thm
    val pow_add : thm
    val pow_le : thm
    val pow_le_mono : thm
    val pow_lt : thm
    val pow_lt2 : thm
    val pow_minus1 : thm
    val pow_mul : thm
    val pow_neg_odd : thm
    val pow_not_infty : thm
    val pow_pos_even : thm
    val pow_pos_le : thm
    val pow_pos_lt : thm
    val pow_zero : thm
    val pow_zero_imp : thm
    val quotient_normal : thm
    val rat_not_infty : thm
    val real_normal : thm
    val rinv_uniq : thm
    val sqrt_mono_le : thm
    val sqrt_pos_le : thm
    val sqrt_pos_lt : thm
    val sqrt_pow2 : thm
    val sub_0 : thm
    val sub_add : thm
    val sub_add2 : thm
    val sub_ldistrib : thm
    val sub_le_eq : thm
    val sub_le_eq2 : thm
    val sub_le_imp : thm
    val sub_le_imp2 : thm
    val sub_le_switch : thm
    val sub_le_switch2 : thm
    val sub_le_zero : thm
    val sub_lneg : thm
    val sub_lt_imp : thm
    val sub_lt_imp2 : thm
    val sub_lt_zero : thm
    val sub_lt_zero2 : thm
    val sub_lzero : thm
    val sub_not_infty : thm
    val sub_rdistrib : thm
    val sub_refl : thm
    val sub_rneg : thm
    val sub_rzero : thm
    val sub_zero_le : thm
    val sub_zero_lt : thm
    val sub_zero_lt2 : thm
    val sup_add_mono : thm
    val sup_cmul : thm
    val sup_const : thm
    val sup_const_alt : thm
    val sup_const_over_set : thm
    val sup_eq : thm
    val sup_le : thm
    val sup_le_mono : thm
    val sup_le_sup_imp : thm
    val sup_lt : thm
    val sup_lt_epsilon : thm
    val sup_lt_infty : thm
    val sup_max : thm
    val sup_mono : thm
    val sup_num : thm
    val sup_seq : thm
    val sup_suc : thm
    val sup_sum_mono : thm
    val third_cancel : thm
    val thirds_between : thm

  val extreal_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [util_prob] Parent theory of "extreal"

   [EXTREAL_SUM_IMAGE_DEF]  Definition

      |- ∀f s. SIGMA f s = ITSET (λe acc. f e + acc) s 0

   [Q_set_def]  Definition

      |- Q_set =
         {x | ∃a b. (x = &a / &b) ∧ 0 < &b} ∪
         {x | ∃a b. (x = -(&a / &b)) ∧ 0 < &b}

   [ceiling_def]  Definition

      |- ∀x. ceiling (Normal x) = LEAST n. x ≤ &n

   [ext_mono_decreasing_def]  Definition

      |- ∀f. mono_decreasing f ⇔ ∀m n. m ≤ n ⇒ f n ≤ f m

   [ext_mono_increasing_def]  Definition

      |- ∀f. mono_increasing f ⇔ ∀m n. m ≤ n ⇒ f m ≤ f n

   [ext_suminf_def]  Definition

      |- ∀f. suminf f = sup (IMAGE (λn. SIGMA f (count n)) 𝕌(:num))

   [extreal_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'extreal' .
                  (∀a0.
                     (a0 = ind_type$CONSTR 0 ARB (λn. ind_type$BOTTOM)) ∨
                     (a0 =
                      ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM)) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC 0)) a
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'extreal' a0) ⇒
                  'extreal' a0) rep

   [extreal_abs_primitive_def]  Definition

      |- abs =
         WFREC (@R. WF R)
           (λextreal_abs a.
              case a of Normal x => I (Normal (abs x)) | _ => I PosInf)

   [extreal_add_curried_def]  Definition

      |- ∀x x1. x + x1 = extreal_add_tupled (x,x1)

   [extreal_add_tupled_primitive_def]  Definition

      |- extreal_add_tupled =
         WFREC (@R. WF R)
           (λextreal_add_tupled a'.
              case a' of
                (NegInf,NegInf) => I NegInf
              | (NegInf,PosInf) => I PosInf
              | (NegInf,Normal v6) => I NegInf
              | (PosInf,a) => I PosInf
              | (Normal x,NegInf) => I NegInf
              | (Normal x,PosInf) => I PosInf
              | (Normal x,Normal y) => I (Normal (x + y)))

   [extreal_ainv_def]  Definition

      |- (-NegInf = PosInf) ∧ (-PosInf = NegInf) ∧
         ∀x. -Normal x = Normal (-x)

   [extreal_case_def]  Definition

      |- (∀v v1 f. extreal_CASE NegInf v v1 f = v) ∧
         (∀v v1 f. extreal_CASE PosInf v v1 f = v1) ∧
         ∀a v v1 f. extreal_CASE (Normal a) v v1 f = f a

   [extreal_div_def]  Definition

      |- ∀x y. x / y = x * inv y

   [extreal_exp_def]  Definition

      |- (∀x. exp (Normal x) = Normal (exp x)) ∧ (exp PosInf = PosInf) ∧
         (exp NegInf = Normal 0)

   [extreal_inf_def]  Definition

      |- ∀p. inf p = -sup (IMAGE numeric_negate p)

   [extreal_inv_def]  Definition

      |- (inv NegInf = Normal 0) ∧ (inv PosInf = Normal 0) ∧
         ∀x. inv (Normal x) = Normal (inv x)

   [extreal_le_curried_def]  Definition

      |- ∀x x1. x ≤ x1 ⇔ extreal_le_tupled (x,x1)

   [extreal_le_tupled_primitive_def]  Definition

      |- extreal_le_tupled =
         WFREC (@R. WF R)
           (λextreal_le_tupled a'.
              case a' of
                (NegInf,a) => I T
              | (PosInf,NegInf) => I F
              | (PosInf,PosInf) => I T
              | (PosInf,Normal v6) => I F
              | (Normal x,NegInf) => I F
              | (Normal x,PosInf) => I T
              | (Normal x,Normal y) => I (x ≤ y))

   [extreal_lg_def]  Definition

      |- ∀x. lg x = logr 2 x

   [extreal_logr_def]  Definition

      |- (∀b x. logr b (Normal x) = Normal (logr b x)) ∧
         (∀b. logr b PosInf = PosInf) ∧ ∀b. logr b NegInf = NegInf

   [extreal_lt_def]  Definition

      |- ∀x y. x < y ⇔ ¬(y ≤ x)

   [extreal_max_def]  Definition

      |- ∀x y. max x y = if x ≤ y then y else x

   [extreal_min_def]  Definition

      |- ∀x y. min x y = if x ≤ y then x else y

   [extreal_mul_curried_def]  Definition

      |- ∀x x1. x * x1 = extreal_mul_tupled (x,x1)

   [extreal_mul_tupled_primitive_def]  Definition

      |- extreal_mul_tupled =
         WFREC (@R. WF R)
           (λextreal_mul_tupled a.
              case a of
                (NegInf,NegInf) => I PosInf
              | (NegInf,PosInf) => I NegInf
              | (NegInf,Normal y) =>
                  I
                    (if y = 0 then Normal 0
                     else if 0 < y then NegInf
                     else PosInf)
              | (PosInf,NegInf) => I NegInf
              | (PosInf,PosInf) => I PosInf
              | (PosInf,Normal y') =>
                  I
                    (if y' = 0 then Normal 0
                     else if 0 < y' then PosInf
                     else NegInf)
              | (Normal x,NegInf) =>
                  I
                    (if x = 0 then Normal 0
                     else if 0 < x then NegInf
                     else PosInf)
              | (Normal x,PosInf) =>
                  I
                    (if x = 0 then Normal 0
                     else if 0 < x then PosInf
                     else NegInf)
              | (Normal x,Normal y'') => I (Normal (x * y'')))

   [extreal_of_num_def]  Definition

      |- ∀n. &n = Normal (&n)

   [extreal_pow_def]  Definition

      |- (∀a n. Normal a pow n = Normal (a pow n)) ∧
         (∀n. PosInf pow n = if n = 0 then Normal 1 else PosInf) ∧
         ∀n.
           NegInf pow n =
           if n = 0 then Normal 1 else if EVEN n then PosInf else NegInf

   [extreal_size_def]  Definition

      |- (extreal_size NegInf = 0) ∧ (extreal_size PosInf = 0) ∧
         ∀a. extreal_size (Normal a) = 1

   [extreal_sqrt_def]  Definition

      |- (∀x. sqrt (Normal x) = Normal (sqrt x)) ∧ (sqrt PosInf = PosInf)

   [extreal_sub_curried_def]  Definition

      |- ∀x x1. x − x1 = extreal_sub_tupled (x,x1)

   [extreal_sub_tupled_primitive_def]  Definition

      |- extreal_sub_tupled =
         WFREC (@R. WF R)
           (λextreal_sub_tupled a'.
              case a' of
                (NegInf,NegInf) => I PosInf
              | (NegInf,PosInf) => I NegInf
              | (NegInf,Normal v6) => I NegInf
              | (PosInf,a) => I PosInf
              | (Normal x,NegInf) => I PosInf
              | (Normal x,PosInf) => I NegInf
              | (Normal x,Normal y) => I (Normal (x − y)))

   [extreal_sup_def]  Definition

      |- ∀p.
           sup p =
           if ∀x. (∀y. p y ⇒ y ≤ x) ⇒ (x = PosInf) then PosInf
           else if ∀x. p x ⇒ (x = NegInf) then NegInf
           else Normal (sup (λr. p (Normal r)))

   [mono_decreasing_def]  Definition

      |- ∀f. mono_decreasing f ⇔ ∀m n. m ≤ n ⇒ f n ≤ f m

   [mono_increasing_def]  Definition

      |- ∀f. mono_increasing f ⇔ ∀m n. m ≤ n ⇒ f m ≤ f n

   [open_interval_def]  Definition

      |- ∀a b. open_interval a b = {x | a < x ∧ x < b}

   [open_intervals_set_def]  Definition

      |- open_intervals_set =
         {open_interval a b | a ∈ 𝕌(:extreal) ∧ b ∈ 𝕌(:extreal)}

   [rational_intervals_def]  Definition

      |- rational_intervals = {open_interval a b | a ∈ Q_set ∧ b ∈ Q_set}

   [real_def]  Definition

      |- ∀x.
           real x =
           if (x = NegInf) ∨ (x = PosInf) then 0 else @r. x = Normal r

   [ADD_IN_Q]  Theorem

      |- ∀x y. x ∈ Q_set ∧ y ∈ Q_set ⇒ x + y ∈ Q_set

   [CEILING_LBOUND]  Theorem

      |- ∀x. Normal x ≤ &ceiling (Normal x)

   [CEILING_UBOUND]  Theorem

      |- ∀x. 0 ≤ x ⇒ &ceiling (Normal x) < Normal x + 1

   [CMUL_IN_Q]  Theorem

      |- ∀z x. x ∈ Q_set ⇒ &z * x ∈ Q_set ∧ -&z * x ∈ Q_set

   [COUNTABLE_ENUM_Q]  Theorem

      |- ∀c. countable c ⇔ (c = ∅) ∨ ∃f. c = IMAGE f Q_set

   [COUNTABLE_RATIONAL_INTERVALS]  Theorem

      |- countable rational_intervals

   [CROSS_COUNTABLE]  Theorem

      |- ∀s. countable s ∧ countable t ⇒ countable (s × t)

   [CROSS_COUNTABLE_LEMMA1]  Theorem

      |- ∀s. countable s ∧ FINITE s ∧ countable t ⇒ countable (s × t)

   [CROSS_COUNTABLE_LEMMA2]  Theorem

      |- ∀s. countable s ∧ countable t ∧ FINITE t ⇒ countable (s × t)

   [CROSS_COUNTABLE_UNIV]  Theorem

      |- countable (𝕌(:num) × 𝕌(:num))

   [DIV_IN_Q]  Theorem

      |- ∀x y. x ∈ Q_set ∧ y ∈ Q_set ∧ y ≠ 0 ⇒ x / y ∈ Q_set

   [EXTREAL_ARCH]  Theorem

      |- ∀x. 0 < x ⇒ ∀y. y ≠ PosInf ⇒ ∃n. y < &n * x

   [EXTREAL_ARCH_POW]  Theorem

      |- ∀x. x ≠ PosInf ⇒ ∃n. x < 2 pow n

   [EXTREAL_ARCH_POW_INV]  Theorem

      |- ∀e. 0 < e ⇒ ∃n. Normal ((1 / 2) pow n) < e

   [EXTREAL_EQ_LADD]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ⇒ ((x + y = x + z) ⇔ (y = z))

   [EXTREAL_SUM_IMAGE_0]  Theorem

      |- ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ (f x = 0)) ⇒ (SIGMA f s = 0)

   [EXTREAL_SUM_IMAGE_ADD]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f f'. SIGMA (λx. f x + f' x) s = SIGMA f s + SIGMA f' s

   [EXTREAL_SUM_IMAGE_CMUL]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f c.
             0 ≤ c ∨ (∀x. x ∈ s ⇒ 0 ≤ f x) ⇒
             (SIGMA (λx. Normal c * f x) s = Normal c * SIGMA f s)

   [EXTREAL_SUM_IMAGE_CMUL2]  Theorem

      |- ∀s f c.
           FINITE s ∧ (∀x. x ∈ s ⇒ f x ≠ NegInf) ⇒
           (SIGMA (λx. Normal c * f x) s = Normal c * SIGMA f s)

   [EXTREAL_SUM_IMAGE_COUNT]  Theorem

      |- ∀f.
           (SIGMA f (count 2) = f 0 + f 1) ∧
           (SIGMA f (count 3) = f 0 + f 1 + f 2) ∧
           (SIGMA f (count 4) = f 0 + f 1 + f 2 + f 3) ∧
           (SIGMA f (count 5) = f 0 + f 1 + f 2 + f 3 + f 4)

   [EXTREAL_SUM_IMAGE_CROSS_SYM]  Theorem

      |- ∀f s1 s2.
           FINITE s1 ∧ FINITE s2 ⇒
           (SIGMA (λ(x,y). f (x,y)) (s1 × s2) =
            SIGMA (λ(y,x). f (x,y)) (s2 × s1))

   [EXTREAL_SUM_IMAGE_DISJOINT_UNION]  Theorem

      |- ∀s s'.
           FINITE s ∧ FINITE s' ∧ DISJOINT s s' ⇒
           ∀f. SIGMA f (s ∪ s') = SIGMA f s + SIGMA f s'

   [EXTREAL_SUM_IMAGE_EQ]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f f'. (∀x. x ∈ s ⇒ (f x = f' x)) ⇒ (SIGMA f s = SIGMA f' s)

   [EXTREAL_SUM_IMAGE_EQ_CARD]  Theorem

      |- ∀s. FINITE s ⇒ (SIGMA (λx. if x ∈ s then 1 else 0) s = &CARD s)

   [EXTREAL_SUM_IMAGE_EXTREAL_SUM_IMAGE]  Theorem

      |- ∀s s' f.
           FINITE s ∧ FINITE s' ⇒
           (SIGMA (λx. SIGMA (f x) s') s =
            SIGMA (λx. f (FST x) (SND x)) (s × s'))

   [EXTREAL_SUM_IMAGE_FINITE_CONST]  Theorem

      |- ∀P. FINITE P ⇒ ∀f x. (∀y. f y = x) ⇒ (SIGMA f P = &CARD P * x)

   [EXTREAL_SUM_IMAGE_FINITE_SAME]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f p.
             p ∈ s ∧ (∀q. q ∈ s ⇒ (f p = f q)) ⇒
             (SIGMA f s = &CARD s * f p)

   [EXTREAL_SUM_IMAGE_IF_ELIM]  Theorem

      |- ∀s P f.
           FINITE s ∧ (∀x. x ∈ s ⇒ P x) ⇒
           (SIGMA (λx. if P x then f x else 0) s = SIGMA f s)

   [EXTREAL_SUM_IMAGE_IMAGE]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f'.
             INJ f' s (IMAGE f' s) ⇒
             ∀f. SIGMA f (IMAGE f' s) = SIGMA (f o f') s

   [EXTREAL_SUM_IMAGE_INTER_ELIM]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f s'. (∀x. x ∉ s' ⇒ (f x = 0)) ⇒ (SIGMA f (s ∩ s') = SIGMA f s)

   [EXTREAL_SUM_IMAGE_INTER_NONZERO]  Theorem

      |- ∀s. FINITE s ⇒ ∀f. SIGMA f (s ∩ (λp. f p ≠ 0)) = SIGMA f s

   [EXTREAL_SUM_IMAGE_INV_CARD_EQ_1]  Theorem

      |- ∀s.
           s ≠ ∅ ∧ FINITE s ⇒
           (SIGMA (λx. if x ∈ s then inv (&CARD s) else 0) s = 1)

   [EXTREAL_SUM_IMAGE_IN_IF]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f. SIGMA f s = SIGMA (λx. if x ∈ s then f x else 0) s

   [EXTREAL_SUM_IMAGE_IN_IF_ALT]  Theorem

      |- ∀s f z.
           FINITE s ⇒ (SIGMA f s = SIGMA (λx. if x ∈ s then f x else z) s)

   [EXTREAL_SUM_IMAGE_MONO]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f f'. (∀x. x ∈ s ⇒ f x ≤ f' x) ⇒ SIGMA f s ≤ SIGMA f' s

   [EXTREAL_SUM_IMAGE_MONO_SET]  Theorem

      |- ∀f s t.
           FINITE s ∧ FINITE t ∧ s ⊆ t ∧ (∀x. x ∈ t ⇒ 0 ≤ f x) ⇒
           SIGMA f s ≤ SIGMA f t

   [EXTREAL_SUM_IMAGE_NORMAL]  Theorem

      |- ∀f s. FINITE s ⇒ (SIGMA (λx. Normal (f x)) s = Normal (SIGMA f s))

   [EXTREAL_SUM_IMAGE_NOT_INFTY]  Theorem

      |- ∀f s.
           (FINITE s ∧ (∀x. x ∈ s ⇒ f x ≠ NegInf) ⇒ SIGMA f s ≠ NegInf) ∧
           (FINITE s ∧ (∀x. x ∈ s ⇒ f x ≠ PosInf) ⇒ SIGMA f s ≠ PosInf)

   [EXTREAL_SUM_IMAGE_NOT_NEG_INF]  Theorem

      |- ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ f x ≠ NegInf) ⇒ SIGMA f s ≠ NegInf

   [EXTREAL_SUM_IMAGE_NOT_POS_INF]  Theorem

      |- ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ f x ≠ PosInf) ⇒ SIGMA f s ≠ PosInf

   [EXTREAL_SUM_IMAGE_POS]  Theorem

      |- ∀f s. FINITE s ∧ (∀x. x ∈ s ⇒ 0 ≤ f x) ⇒ 0 ≤ SIGMA f s

   [EXTREAL_SUM_IMAGE_POS_MEM_LE]  Theorem

      |- ∀f s.
           FINITE s ∧ (∀x. x ∈ s ⇒ 0 ≤ f x) ⇒ ∀x. x ∈ s ⇒ f x ≤ SIGMA f s

   [EXTREAL_SUM_IMAGE_SING]  Theorem

      |- ∀f e. SIGMA f {e} = f e

   [EXTREAL_SUM_IMAGE_SPOS]  Theorem

      |- ∀f s. FINITE s ∧ s ≠ ∅ ∧ (∀x. x ∈ s ⇒ 0 < f x) ⇒ 0 < SIGMA f s

   [EXTREAL_SUM_IMAGE_SUB]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f f'.
             (∀x. x ∈ s ⇒ f' x ≠ NegInf) ∨ (∀x. x ∈ s ⇒ f' x ≠ PosInf) ⇒
             (SIGMA (λx. f x − f' x) s = SIGMA f s − SIGMA f' s)

   [EXTREAL_SUM_IMAGE_THM]  Theorem

      |- ∀f.
           (SIGMA f ∅ = 0) ∧
           ∀e s.
             FINITE s ⇒ (SIGMA f (e INSERT s) = f e + SIGMA f (s DELETE e))

   [EXTREAL_SUM_IMAGE_ZERO]  Theorem

      |- ∀s. FINITE s ⇒ (SIGMA (λx. 0) s = 0)

   [EXTREAL_SUM_IMAGE_ZERO_DIFF]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f t. (∀x. x ∈ t ⇒ (f x = 0)) ⇒ (SIGMA f s = SIGMA f (s DIFF t))

   [INV_IN_Q]  Theorem

      |- ∀x. x ∈ Q_set ∧ x ≠ 0 ⇒ 1 / x ∈ Q_set

   [LOGR_MONO_LE]  Theorem

      |- ∀x y b. 0 < x ∧ 0 < y ∧ 1 < b ⇒ (logr b x ≤ logr b y ⇔ x ≤ y)

   [LOGR_MONO_LE_IMP]  Theorem

      |- ∀x y b. 0 < x ∧ x ≤ y ∧ 1 ≤ b ⇒ logr b x ≤ logr b y

   [MUL_IN_Q]  Theorem

      |- ∀x y. x ∈ Q_set ∧ y ∈ Q_set ⇒ x * y ∈ Q_set

   [NUM_IN_Q]  Theorem

      |- ∀n. &n ∈ Q_set ∧ -&n ∈ Q_set

   [OPP_IN_Q]  Theorem

      |- ∀x. x ∈ Q_set ⇒ -x ∈ Q_set

   [POW_NEG_ODD]  Theorem

      |- ∀x. x < 0 ⇒ (x pow n < 0 ⇔ ODD n)

   [POW_POS_EVEN]  Theorem

      |- ∀x. x < 0 ⇒ (0 < x pow n ⇔ EVEN n)

   [Q_COUNTABLE]  Theorem

      |- countable Q_set

   [Q_DENSE_IN_R]  Theorem

      |- ∀x y. x < y ⇒ ∃r. r ∈ Q_set ∧ x < r ∧ r < y

   [Q_DENSE_IN_R_LEMMA]  Theorem

      |- ∀x y. 0 ≤ x ∧ x < y ⇒ ∃r. r ∈ Q_set ∧ x < r ∧ r < y

   [Q_INFINITE]  Theorem

      |- INFINITE Q_set

   [Q_not_infty]  Theorem

      |- ∀x. x ∈ Q_set ⇒ ∃y. x = Normal y

   [REAL_ARCH_POW]  Theorem

      |- ∀x. ∃n. x < 2 pow n

   [REAL_LE_MUL_EPSILON]  Theorem

      |- ∀x y. (∀z. 0 < z ∧ z < 1 ⇒ z * x ≤ y) ⇒ x ≤ y

   [REAL_LE_RDIV_EQ_NEG]  Theorem

      |- ∀x y z. z < 0 ⇒ (y / z ≤ x ⇔ x * z ≤ y)

   [REAL_LT_LMUL_0_NEG]  Theorem

      |- ∀x y. 0 < x * y ∧ x < 0 ⇒ y < 0

   [REAL_LT_LMUL_NEG_0]  Theorem

      |- ∀x y. x * y < 0 ∧ 0 < x ⇒ y < 0

   [REAL_LT_LMUL_NEG_0_NEG]  Theorem

      |- ∀x y. x * y < 0 ∧ x < 0 ⇒ 0 < y

   [REAL_LT_RDIV_EQ_NEG]  Theorem

      |- ∀x y z. z < 0 ⇒ (y / z < x ⇔ x * z < y)

   [REAL_LT_RMUL_0_NEG]  Theorem

      |- ∀x y. 0 < x * y ∧ y < 0 ⇒ x < 0

   [REAL_LT_RMUL_NEG_0]  Theorem

      |- ∀x y. x * y < 0 ∧ 0 < y ⇒ x < 0

   [REAL_LT_RMUL_NEG_0_NEG]  Theorem

      |- ∀x y. x * y < 0 ∧ y < 0 ⇒ 0 < x

   [SIMP_EXTREAL_ARCH]  Theorem

      |- ∀x. x ≠ PosInf ⇒ ∃n. x ≤ &n

   [SIMP_REAL_ARCH]  Theorem

      |- ∀x. ∃n. x ≤ &n

   [SIMP_REAL_ARCH_NEG]  Theorem

      |- ∀x. ∃n. -&n ≤ x

   [SUB_IN_Q]  Theorem

      |- ∀x y. x ∈ Q_set ∧ y ∈ Q_set ⇒ x − y ∈ Q_set

   [abs_bounds]  Theorem

      |- ∀x k. abs x ≤ k ⇔ -k ≤ x ∧ x ≤ k

   [abs_bounds_lt]  Theorem

      |- ∀x k. abs x < k ⇔ -k < x ∧ x < k

   [abs_pos]  Theorem

      |- ∀x. 0 ≤ abs x

   [abs_refl]  Theorem

      |- ∀x. (abs x = x) ⇔ 0 ≤ x

   [add2_sub2]  Theorem

      |- ∀a b c d.
           b ≠ PosInf ∧ d ≠ PosInf ∨ b ≠ NegInf ∧ d ≠ NegInf ⇒
           (a − b + (c − d) = a + c − (b + d))

   [add_assoc]  Theorem

      |- ∀x y z. x + (y + z) = x + y + z

   [add_comm]  Theorem

      |- ∀x y. x + y = y + x

   [add_infty]  Theorem

      |- (∀x. (x + PosInf = PosInf) ∧ (PosInf + x = PosInf)) ∧
         ∀x. x ≠ PosInf ⇒ (x + NegInf = NegInf) ∧ (NegInf + x = NegInf)

   [add_ldistrib]  Theorem

      |- ∀x y z.
           0 ≤ y ∧ 0 ≤ z ∨ y ≤ 0 ∧ z ≤ 0 ⇒ (x * (y + z) = x * y + x * z)

   [add_ldistrib_neg]  Theorem

      |- ∀x y z. y ≤ 0 ∧ z ≤ 0 ⇒ (x * (y + z) = x * y + x * z)

   [add_ldistrib_normal]  Theorem

      |- ∀x y z.
           y ≠ PosInf ∧ z ≠ PosInf ∨ y ≠ NegInf ∧ z ≠ NegInf ⇒
           (Normal x * (y + z) = Normal x * y + Normal x * z)

   [add_ldistrib_normal2]  Theorem

      |- ∀x y z. 0 ≤ x ⇒ (Normal x * (y + z) = Normal x * y + Normal x * z)

   [add_ldistrib_pos]  Theorem

      |- ∀x y z. 0 ≤ y ∧ 0 ≤ z ⇒ (x * (y + z) = x * y + x * z)

   [add_lzero]  Theorem

      |- ∀x. 0 + x = x

   [add_not_infty]  Theorem

      |- ∀x y.
           (x ≠ NegInf ∧ y ≠ NegInf ⇒ x + y ≠ NegInf) ∧
           (x ≠ PosInf ∧ y ≠ PosInf ⇒ x + y ≠ PosInf)

   [add_pow2]  Theorem

      |- ∀x y. (x + y) pow 2 = x pow 2 + y pow 2 + 2 * x * y

   [add_rdistrib]  Theorem

      |- ∀x y z.
           0 ≤ y ∧ 0 ≤ z ∨ y ≤ 0 ∧ z ≤ 0 ⇒ ((y + z) * x = y * x + z * x)

   [add_rdistrib_normal]  Theorem

      |- ∀x y z.
           y ≠ PosInf ∧ z ≠ PosInf ∨ y ≠ NegInf ∧ z ≠ NegInf ⇒
           ((y + z) * Normal x = y * Normal x + z * Normal x)

   [add_rdistrib_normal2]  Theorem

      |- ∀x y z. 0 ≤ x ⇒ ((y + z) * Normal x = y * Normal x + z * Normal x)

   [add_rzero]  Theorem

      |- ∀x. x + 0 = x

   [add_sub]  Theorem

      |- ∀x y. y ≠ NegInf ∧ y ≠ PosInf ⇒ (x + y − y = x)

   [add_sub2]  Theorem

      |- ∀x y. y ≠ NegInf ∧ y ≠ PosInf ⇒ (y + x − y = x)

   [datatype_extreal]  Theorem

      |- DATATYPE (extreal NegInf PosInf Normal)

   [div_add]  Theorem

      |- ∀x y z.
           x ≠ NegInf ∧ y ≠ NegInf ∧ z ≠ 0 ⇒ (x / z + y / z = (x + y) / z)

   [div_one]  Theorem

      |- ∀x. x / 1 = x

   [entire]  Theorem

      |- ∀x y. (x * y = 0) ⇔ (x = 0) ∨ (y = 0)

   [eq_add_sub_switch]  Theorem

      |- ∀a b c d.
           b ≠ NegInf ∧ b ≠ PosInf ∧ c ≠ NegInf ∧ c ≠ PosInf ⇒
           ((a + b = c + d) ⇔ (a − c = d − b))

   [eq_neg]  Theorem

      |- ∀x y. (-x = -y) ⇔ (x = y)

   [eq_sub_ladd]  Theorem

      |- ∀x y z. z ≠ NegInf ∧ z ≠ PosInf ⇒ ((x = y − z) ⇔ (x + z = y))

   [eq_sub_ladd_normal]  Theorem

      |- ∀x y z. (x = y − Normal z) ⇔ (x + Normal z = y)

   [eq_sub_radd]  Theorem

      |- ∀x y z. y ≠ NegInf ∧ y ≠ PosInf ⇒ ((x − y = z) ⇔ (x = z + y))

   [eq_sub_switch]  Theorem

      |- ∀x y z. (x = Normal z − y) ⇔ (y = Normal z − x)

   [ext_mono_decreasing_suc]  Theorem

      |- ∀f. mono_decreasing f ⇔ ∀n. f (SUC n) ≤ f n

   [ext_mono_increasing_suc]  Theorem

      |- ∀f. mono_increasing f ⇔ ∀n. f n ≤ f (SUC n)

   [ext_suminf_add]  Theorem

      |- ∀f g.
           (∀n. 0 ≤ f n ∧ 0 ≤ g n) ⇒
           (suminf (λn. f n + g n) = suminf f + suminf g)

   [ext_suminf_cmul]  Theorem

      |- ∀f c.
           0 ≤ c ∧ (∀n. 0 ≤ f n) ⇒ (suminf (λn. c * f n) = c * suminf f)

   [ext_suminf_cmul_alt]  Theorem

      |- ∀f c.
           0 ≤ c ∧ ((∀n. f n ≠ NegInf) ∨ ∀n. f n ≠ PosInf) ⇒
           (suminf (λn. Normal c * f n) = Normal c * suminf f)

   [ext_suminf_lt_infty]  Theorem

      |- ∀f. (∀n. 0 ≤ f n) ∧ suminf f ≠ PosInf ⇒ ∀n. f n < PosInf

   [ext_suminf_mono]  Theorem

      |- ∀f g. (∀n. g n ≠ NegInf ∧ g n ≤ f n) ⇒ suminf g ≤ suminf f

   [ext_suminf_sub]  Theorem

      |- ∀f g.
           (∀n. 0 ≤ g n ∧ g n ≤ f n) ∧ suminf f ≠ PosInf ⇒
           (suminf (λi. f i − g i) = suminf f − suminf g)

   [ext_suminf_sum]  Theorem

      |- ∀f n.
           (∀n. 0 ≤ f n) ∧ (∀m. n ≤ m ⇒ (f m = 0)) ⇒
           (suminf f = SIGMA f (count n))

   [ext_suminf_suminf]  Theorem

      |- ∀r.
           (∀n. 0 ≤ r n) ∧ suminf (λn. Normal (r n)) ≠ PosInf ⇒
           (suminf (λn. Normal (r n)) = Normal (suminf r))

   [extreal_11]  Theorem

      |- ∀a a'. (Normal a = Normal a') ⇔ (a = a')

   [extreal_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (fn NegInf = f0) ∧ (fn PosInf = f1) ∧ ∀a. fn (Normal a) = f2 a

   [extreal_abs_def]  Theorem

      |- (abs (Normal x) = Normal (abs x)) ∧ (abs NegInf = PosInf) ∧
         (abs PosInf = PosInf)

   [extreal_abs_ind]  Theorem

      |- ∀P. (∀x. P (Normal x)) ∧ P NegInf ∧ P PosInf ⇒ ∀v. P v

   [extreal_add_def]  Theorem

      |- (Normal x + Normal y = Normal (x + y)) ∧ (PosInf + a = PosInf) ∧
         (NegInf + PosInf = PosInf) ∧ (Normal v2 + PosInf = PosInf) ∧
         (NegInf + NegInf = NegInf) ∧ (NegInf + Normal v5 = NegInf) ∧
         (Normal v3 + NegInf = NegInf)

   [extreal_add_ind]  Theorem

      |- ∀P.
           (∀x y. P (Normal x) (Normal y)) ∧ (∀a. P PosInf a) ∧
           P NegInf PosInf ∧ (∀v2. P (Normal v2) PosInf) ∧
           P NegInf NegInf ∧ (∀v5. P NegInf (Normal v5)) ∧
           (∀v3. P (Normal v3) NegInf) ⇒
           ∀v v1. P v v1

   [extreal_case_cong]  Theorem

      |- ∀M M' v v1 f.
           (M = M') ∧ ((M' = NegInf) ⇒ (v = v')) ∧
           ((M' = PosInf) ⇒ (v1 = v1')) ∧
           (∀a. (M' = Normal a) ⇒ (f a = f' a)) ⇒
           (extreal_CASE M v v1 f = extreal_CASE M' v' v1' f')

   [extreal_cases]  Theorem

      |- ∀x. (x = NegInf) ∨ (x = PosInf) ∨ ∃r. x = Normal r

   [extreal_distinct]  Theorem

      |- NegInf ≠ PosInf ∧ (∀a. NegInf ≠ Normal a) ∧ ∀a. PosInf ≠ Normal a

   [extreal_div_eq]  Theorem

      |- ∀x y. Normal x / Normal y = Normal (x / y)

   [extreal_eq_zero]  Theorem

      |- ∀x. (Normal x = 0) ⇔ (x = 0)

   [extreal_induction]  Theorem

      |- ∀P. P NegInf ∧ P PosInf ∧ (∀r. P (Normal r)) ⇒ ∀e. P e

   [extreal_le_def]  Theorem

      |- (Normal x ≤ Normal y ⇔ x ≤ y) ∧ (NegInf ≤ a ⇔ T) ∧
         (PosInf ≤ PosInf ⇔ T) ∧ (Normal v2 ≤ PosInf ⇔ T) ∧
         (PosInf ≤ NegInf ⇔ F) ∧ (Normal v3 ≤ NegInf ⇔ F) ∧
         (PosInf ≤ Normal v5 ⇔ F)

   [extreal_le_ind]  Theorem

      |- ∀P.
           (∀x y. P (Normal x) (Normal y)) ∧ (∀a. P NegInf a) ∧
           P PosInf PosInf ∧ (∀v2. P (Normal v2) PosInf) ∧
           P PosInf NegInf ∧ (∀v3. P (Normal v3) NegInf) ∧
           (∀v5. P PosInf (Normal v5)) ⇒
           ∀v v1. P v v1

   [extreal_lt_eq]  Theorem

      |- ∀x y. Normal x < Normal y ⇔ x < y

   [extreal_mul_def]  Theorem

      |- (NegInf * NegInf = PosInf) ∧ (NegInf * PosInf = NegInf) ∧
         (PosInf * NegInf = NegInf) ∧ (PosInf * PosInf = PosInf) ∧
         (Normal x * NegInf =
          if x = 0 then Normal 0 else if 0 < x then NegInf else PosInf) ∧
         (NegInf * Normal y =
          if y = 0 then Normal 0 else if 0 < y then NegInf else PosInf) ∧
         (Normal x * PosInf =
          if x = 0 then Normal 0 else if 0 < x then PosInf else NegInf) ∧
         (PosInf * Normal y =
          if y = 0 then Normal 0 else if 0 < y then PosInf else NegInf) ∧
         (Normal x * Normal y = Normal (x * y))

   [extreal_mul_ind]  Theorem

      |- ∀P.
           P NegInf NegInf ∧ P NegInf PosInf ∧ P PosInf NegInf ∧
           P PosInf PosInf ∧ (∀x. P (Normal x) NegInf) ∧
           (∀y. P NegInf (Normal y)) ∧ (∀x. P (Normal x) PosInf) ∧
           (∀y. P PosInf (Normal y)) ∧ (∀x y. P (Normal x) (Normal y)) ⇒
           ∀v v1. P v v1

   [extreal_nchotomy]  Theorem

      |- ∀ee. (ee = NegInf) ∨ (ee = PosInf) ∨ ∃r. ee = Normal r

   [extreal_not_infty]  Theorem

      |- ∀x. Normal x ≠ NegInf ∧ Normal x ≠ PosInf

   [extreal_sub_add]  Theorem

      |- ∀x y. x − y = x + -y

   [extreal_sub_def]  Theorem

      |- (Normal x − Normal y = Normal (x − y)) ∧ (PosInf − a = PosInf) ∧
         (NegInf − PosInf = NegInf) ∧ (Normal v2 − PosInf = NegInf) ∧
         (NegInf − NegInf = PosInf) ∧ (NegInf − Normal v5 = NegInf) ∧
         (Normal v3 − NegInf = PosInf)

   [extreal_sub_ind]  Theorem

      |- ∀P.
           (∀x y. P (Normal x) (Normal y)) ∧ (∀a. P PosInf a) ∧
           P NegInf PosInf ∧ (∀v2. P (Normal v2) PosInf) ∧
           P NegInf NegInf ∧ (∀v5. P NegInf (Normal v5)) ∧
           (∀v3. P (Normal v3) NegInf) ⇒
           ∀v v1. P v v1

   [fourth_cancel]  Theorem

      |- 4 * (1 / 4) = 1

   [half_between]  Theorem

      |- (0 < 1 / 2 ∧ 1 / 2 < 1) ∧ 0 ≤ 1 / 2 ∧ 1 / 2 ≤ 1

   [half_cancel]  Theorem

      |- 2 * (1 / 2) = 1

   [inf_cminus]  Theorem

      |- ∀f c.
           Normal c − inf (IMAGE f 𝕌(:α)) =
           sup (IMAGE (λn. Normal c − f n) 𝕌(:α))

   [inf_const]  Theorem

      |- ∀x. inf (λy. y = x) = x

   [inf_const_alt]  Theorem

      |- ∀p z. (∃x. p x) ∧ (∀x. p x ⇒ (x = z)) ⇒ (inf p = z)

   [inf_const_over_set]  Theorem

      |- ∀s k. s ≠ ∅ ⇒ (inf (IMAGE (λx. k) s) = k)

   [inf_eq]  Theorem

      |- ∀p x.
           (inf p = x) ⇔ (∀y. p y ⇒ x ≤ y) ∧ ∀y. (∀z. p z ⇒ y ≤ z) ⇒ y ≤ x

   [inf_le]  Theorem

      |- ∀p x. inf p ≤ x ⇔ ∀y. (∀z. p z ⇒ y ≤ z) ⇒ y ≤ x

   [inf_le_imp]  Theorem

      |- ∀p x. p x ⇒ inf p ≤ x

   [inf_lt_infty]  Theorem

      |- ∀p. NegInf < inf p ⇒ ∀x. p x ⇒ NegInf < x

   [inf_min]  Theorem

      |- ∀p z. p z ∧ (∀x. p x ⇒ z ≤ x) ⇒ (inf p = z)

   [inf_seq]  Theorem

      |- ∀f l.
           mono_decreasing f ⇒
           (f --> l ⇔ (inf (IMAGE (λn. Normal (f n)) 𝕌(:num)) = Normal l))

   [inf_suc]  Theorem

      |- ∀f.
           (∀m n. m ≤ n ⇒ f n ≤ f m) ⇒
           (inf (IMAGE (λn. f (SUC n)) 𝕌(:num)) = inf (IMAGE f 𝕌(:num)))

   [inv_1over]  Theorem

      |- ∀x. inv x = 1 / x

   [inv_one]  Theorem

      |- inv 1 = 1

   [inv_pos]  Theorem

      |- ∀x. 0 < x ∧ x ≠ PosInf ⇒ 0 < 1 / x

   [le_01]  Theorem

      |- 0 ≤ 1

   [le_02]  Theorem

      |- 0 ≤ 2

   [le_add]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 ≤ y ⇒ 0 ≤ x + y

   [le_add2]  Theorem

      |- ∀w x y z. w ≤ x ∧ y ≤ z ⇒ w + y ≤ x + z

   [le_addr]  Theorem

      |- ∀x y. x ≠ NegInf ∧ x ≠ PosInf ⇒ (x ≤ x + y ⇔ 0 ≤ y)

   [le_addr_imp]  Theorem

      |- ∀x y. 0 ≤ y ⇒ x ≤ x + y

   [le_antisym]  Theorem

      |- ∀x y. x ≤ y ∧ y ≤ x ⇔ (x = y)

   [le_epsilon]  Theorem

      |- ∀x y. (∀e. 0 < e ∧ e ≠ PosInf ⇒ x ≤ y + e) ⇒ x ≤ y

   [le_inf]  Theorem

      |- ∀p x. x ≤ inf p ⇔ ∀y. p y ⇒ x ≤ y

   [le_infty]  Theorem

      |- (∀x. NegInf ≤ x ∧ x ≤ PosInf) ∧ (∀x. x ≤ NegInf ⇔ (x = NegInf)) ∧
         ∀x. PosInf ≤ x ⇔ (x = PosInf)

   [le_inv]  Theorem

      |- ∀x. 0 ≤ x ⇒ 0 ≤ inv x

   [le_ladd]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ⇒ (x + y ≤ x + z ⇔ y ≤ z)

   [le_ladd_imp]  Theorem

      |- ∀x y z. y ≤ z ⇒ x + y ≤ x + z

   [le_ldiv]  Theorem

      |- ∀x y z. 0 < x ⇒ (y ≤ z * Normal x ⇔ y / Normal x ≤ z)

   [le_lmul_imp]  Theorem

      |- ∀x y z. 0 ≤ z ∧ x ≤ y ⇒ z * x ≤ z * y

   [le_lneg]  Theorem

      |- ∀x y. -x ≤ y ⇔ 0 ≤ x + y

   [le_lsub_imp]  Theorem

      |- ∀x y z. y ≤ z ⇒ x − z ≤ x − y

   [le_lt]  Theorem

      |- ∀x y. x ≤ y ⇔ x < y ∨ (x = y)

   [le_max]  Theorem

      |- ∀z x y. z ≤ max x y ⇔ z ≤ x ∨ z ≤ y

   [le_max1]  Theorem

      |- ∀x y. x ≤ max x y

   [le_max2]  Theorem

      |- ∀x y. y ≤ max x y

   [le_min]  Theorem

      |- ∀z x y. z ≤ min x y ⇔ z ≤ x ∧ z ≤ y

   [le_mul]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 ≤ y ⇒ 0 ≤ x * y

   [le_mul_epsilon]  Theorem

      |- ∀x y. (∀z. 0 ≤ z ∧ z < 1 ⇒ z * x ≤ y) ⇒ x ≤ y

   [le_mul_neg]  Theorem

      |- ∀x y. x ≤ 0 ∧ y ≤ 0 ⇒ 0 ≤ x * y

   [le_neg]  Theorem

      |- ∀x y. -x ≤ -y ⇔ y ≤ x

   [le_num]  Theorem

      |- ∀n. 0 ≤ &n

   [le_pow2]  Theorem

      |- ∀x. 0 ≤ x pow 2

   [le_radd]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ⇒ (y + x ≤ z + x ⇔ y ≤ z)

   [le_radd_imp]  Theorem

      |- ∀x y z. y ≤ z ⇒ y + x ≤ z + x

   [le_rdiv]  Theorem

      |- ∀x y z. 0 < x ⇒ (y * Normal x ≤ z ⇔ y ≤ z / Normal x)

   [le_refl]  Theorem

      |- ∀x. x ≤ x

   [le_rmul_imp]  Theorem

      |- ∀x y z. 0 < z ∧ x ≤ y ⇒ x * z ≤ y * z

   [le_sub_eq]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ⇒ (y ≤ z − x ⇔ y + x ≤ z)

   [le_sub_eq2]  Theorem

      |- ∀x y z.
           z ≠ NegInf ∧ z ≠ PosInf ∧ x ≠ NegInf ∧ y ≠ NegInf ⇒
           (y ≤ z − x ⇔ y + x ≤ z)

   [le_sub_imp]  Theorem

      |- ∀x y z. y + x ≤ z ⇒ y ≤ z − x

   [le_sup]  Theorem

      |- ∀p x. x ≤ sup p ⇔ ∀y. (∀z. p z ⇒ z ≤ y) ⇒ x ≤ y

   [le_sup_imp]  Theorem

      |- ∀p x. p x ⇒ x ≤ sup p

   [le_total]  Theorem

      |- ∀x y. x ≤ y ∨ y ≤ x

   [le_trans]  Theorem

      |- ∀x y z. x ≤ y ∧ y ≤ z ⇒ x ≤ z

   [let_add]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 < y ⇒ 0 < x + y

   [let_add2]  Theorem

      |- ∀w x y z. w ≠ NegInf ∧ w ≠ PosInf ∧ w ≤ x ∧ y < z ⇒ w + y < x + z

   [let_add2_alt]  Theorem

      |- ∀w x y z. x ≠ NegInf ∧ x ≠ PosInf ∧ w ≤ x ∧ y < z ⇒ w + y < x + z

   [let_mul]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 < y ⇒ 0 ≤ x * y

   [let_trans]  Theorem

      |- ∀x y z. x ≤ y ∧ y < z ⇒ x < z

   [linv_uniq]  Theorem

      |- ∀x y. (x * y = 1) ⇒ (x = inv y)

   [logr_not_infty]  Theorem

      |- ∀x b.
           x ≠ NegInf ∧ x ≠ PosInf ⇒ logr b x ≠ NegInf ∧ logr b x ≠ PosInf

   [lt_01]  Theorem

      |- 0 < 1

   [lt_02]  Theorem

      |- 0 < 2

   [lt_add]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ 0 < x + y

   [lt_add2]  Theorem

      |- ∀w x y z. w < x ∧ y < z ⇒ w + y < x + z

   [lt_addl]  Theorem

      |- ∀x y. y ≠ NegInf ∧ y ≠ PosInf ⇒ (y < x + y ⇔ 0 < x)

   [lt_antisym]  Theorem

      |- ∀x y. ¬(x < y ∧ y < x)

   [lt_imp_le]  Theorem

      |- ∀x y. x < y ⇒ x ≤ y

   [lt_imp_ne]  Theorem

      |- ∀x y. x < y ⇒ x ≠ y

   [lt_infty]  Theorem

      |- ∀x y.
           NegInf < Normal y ∧ Normal y < PosInf ∧ NegInf < PosInf ∧
           ¬(x < NegInf) ∧ ¬(PosInf < x) ∧ (x ≠ PosInf ⇔ x < PosInf) ∧
           (x ≠ NegInf ⇔ NegInf < x)

   [lt_ladd]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ⇒ (x + y < x + z ⇔ y < z)

   [lt_ldiv]  Theorem

      |- ∀x y z. 0 < z ⇒ (x / Normal z < y ⇔ x < y * Normal z)

   [lt_le]  Theorem

      |- ∀x y. x < y ⇔ x ≤ y ∧ x ≠ y

   [lt_lmul]  Theorem

      |- ∀x y z. 0 < x ∧ x ≠ PosInf ⇒ (x * y < x * z ⇔ y < z)

   [lt_mul]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ 0 < x * y

   [lt_mul2]  Theorem

      |- ∀x1 x2 y1 y2.
           0 ≤ x1 ∧ 0 ≤ y1 ∧ x1 ≠ PosInf ∧ y1 ≠ PosInf ∧ x1 < x2 ∧
           y1 < y2 ⇒
           x1 * y1 < x2 * y2

   [lt_mul_neg]  Theorem

      |- ∀x y. x < 0 ∧ y < 0 ⇒ 0 < x * y

   [lt_neg]  Theorem

      |- ∀x y. -x < -y ⇔ y < x

   [lt_radd]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ⇒ (y + x < z + x ⇔ y < z)

   [lt_rdiv]  Theorem

      |- ∀x y z. 0 < z ⇒ (x < y / Normal z ⇔ x * Normal z < y)

   [lt_rdiv_neg]  Theorem

      |- ∀x y z. z < 0 ⇒ (y / Normal z < x ⇔ x * Normal z < y)

   [lt_refl]  Theorem

      |- ∀x. ¬(x < x)

   [lt_rmul]  Theorem

      |- ∀x y z. 0 < z ∧ z ≠ PosInf ⇒ (x * z < y * z ⇔ x < y)

   [lt_sub]  Theorem

      |- ∀x y z. z ≠ NegInf ∧ z ≠ PosInf ⇒ (y + x < z ⇔ y < z − x)

   [lt_sub_imp]  Theorem

      |- ∀x y z. y + x < z ⇒ y < z − x

   [lt_total]  Theorem

      |- ∀x y. (x = y) ∨ x < y ∨ y < x

   [lt_trans]  Theorem

      |- ∀x y z. x < y ∧ y < z ⇒ x < z

   [lte_add]  Theorem

      |- ∀x y. 0 < x ∧ 0 ≤ y ⇒ 0 < x + y

   [lte_mul]  Theorem

      |- ∀x y. 0 < x ∧ 0 ≤ y ⇒ 0 ≤ x * y

   [lte_trans]  Theorem

      |- ∀x y z. x < y ∧ y ≤ z ⇒ x < z

   [max_comm]  Theorem

      |- ∀x y. max x y = max y x

   [max_infty]  Theorem

      |- ∀x.
           (max x PosInf = PosInf) ∧ (max PosInf x = PosInf) ∧
           (max NegInf x = x) ∧ (max x NegInf = x)

   [max_le]  Theorem

      |- ∀z x y. max x y ≤ z ⇔ x ≤ z ∧ y ≤ z

   [max_le2_imp]  Theorem

      |- ∀x1 x2 y1 y2. x1 ≤ y1 ∧ x2 ≤ y2 ⇒ max x1 x2 ≤ max y1 y2

   [max_refl]  Theorem

      |- ∀x. max x x = x

   [min_comm]  Theorem

      |- ∀x y. min x y = min y x

   [min_infty]  Theorem

      |- ∀x.
           (min x PosInf = x) ∧ (min PosInf x = x) ∧
           (min NegInf x = NegInf) ∧ (min x NegInf = NegInf)

   [min_le]  Theorem

      |- ∀z x y. min x y ≤ z ⇔ x ≤ z ∨ y ≤ z

   [min_le1]  Theorem

      |- ∀x y. min x y ≤ x

   [min_le2]  Theorem

      |- ∀x y. min x y ≤ y

   [min_le2_imp]  Theorem

      |- ∀x1 x2 y1 y2. x1 ≤ y1 ∧ x2 ≤ y2 ⇒ min x1 x2 ≤ min y1 y2

   [min_refl]  Theorem

      |- ∀x. min x x = x

   [mono_decreasing_suc]  Theorem

      |- ∀f. mono_decreasing f ⇔ ∀n. f (SUC n) ≤ f n

   [mono_increasing_converges_to_sup]  Theorem

      |- ∀f r. mono_increasing f ∧ f --> r ⇒ (r = sup (IMAGE f 𝕌(:num)))

   [mono_increasing_suc]  Theorem

      |- ∀f. mono_increasing f ⇔ ∀n. f n ≤ f (SUC n)

   [mul_assoc]  Theorem

      |- ∀x y z. x * (y * z) = x * y * z

   [mul_comm]  Theorem

      |- ∀x y. x * y = y * x

   [mul_le]  Theorem

      |- ∀x y. 0 ≤ x ∧ y ≤ 0 ⇒ x * y ≤ 0

   [mul_let]  Theorem

      |- ∀x y. 0 ≤ x ∧ y < 0 ⇒ x * y ≤ 0

   [mul_lneg]  Theorem

      |- ∀x y. -x * y = -(x * y)

   [mul_lone]  Theorem

      |- ∀x. 1 * x = x

   [mul_lt]  Theorem

      |- ∀x y. 0 < x ∧ y < 0 ⇒ x * y < 0

   [mul_lte]  Theorem

      |- ∀x y. 0 < x ∧ y ≤ 0 ⇒ x * y ≤ 0

   [mul_lzero]  Theorem

      |- ∀x. 0 * x = 0

   [mul_not_infty]  Theorem

      |- (∀c y. 0 ≤ c ∧ y ≠ NegInf ⇒ Normal c * y ≠ NegInf) ∧
         (∀c y. 0 ≤ c ∧ y ≠ PosInf ⇒ Normal c * y ≠ PosInf) ∧
         (∀c y. c ≤ 0 ∧ y ≠ NegInf ⇒ Normal c * y ≠ PosInf) ∧
         ∀c y. c ≤ 0 ∧ y ≠ PosInf ⇒ Normal c * y ≠ NegInf

   [mul_not_infty2]  Theorem

      |- ∀x y.
           x ≠ NegInf ∧ x ≠ PosInf ∧ y ≠ NegInf ∧ y ≠ PosInf ⇒
           x * y ≠ NegInf ∧ x * y ≠ PosInf

   [mul_rneg]  Theorem

      |- ∀x y. x * -y = -(x * y)

   [mul_rone]  Theorem

      |- ∀x. x * 1 = x

   [mul_rzero]  Theorem

      |- ∀x. x * 0 = 0

   [ne_01]  Theorem

      |- 0 ≠ 1

   [ne_02]  Theorem

      |- 0 ≠ 2

   [neg_0]  Theorem

      |- -0 = 0

   [neg_eq0]  Theorem

      |- ∀x. (-x = 0) ⇔ (x = 0)

   [neg_minus1]  Theorem

      |- ∀x. -x = -1 * x

   [neg_mul2]  Theorem

      |- ∀x y. -x * -y = x * y

   [neg_neg]  Theorem

      |- ∀x. --x = x

   [neg_sub]  Theorem

      |- ∀x y.
           x ≠ NegInf ∧ x ≠ PosInf ∨ y ≠ NegInf ∧ y ≠ PosInf ⇒
           (-(x − y) = y − x)

   [normal_real]  Theorem

      |- ∀x. x ≠ NegInf ∧ x ≠ PosInf ⇒ (Normal (real x) = x)

   [num_not_infty]  Theorem

      |- ∀n. &n ≠ NegInf ∧ &n ≠ PosInf

   [pow2_sqrt]  Theorem

      |- ∀x. 0 ≤ x ⇒ (sqrt (x pow 2) = x)

   [pow_0]  Theorem

      |- ∀x. x pow 0 = 1

   [pow_1]  Theorem

      |- ∀x. x pow 1 = x

   [pow_2]  Theorem

      |- ∀x. x pow 2 = x * x

   [pow_add]  Theorem

      |- ∀x n m. x pow (n + m) = x pow n * x pow m

   [pow_le]  Theorem

      |- ∀n x y. 0 ≤ x ∧ x ≤ y ⇒ x pow n ≤ y pow n

   [pow_le_mono]  Theorem

      |- ∀x n m. 1 ≤ x ∧ n ≤ m ⇒ x pow n ≤ x pow m

   [pow_lt]  Theorem

      |- ∀n x y. 0 ≤ x ∧ x < y ⇒ x pow SUC n < y pow SUC n

   [pow_lt2]  Theorem

      |- ∀n x y. n ≠ 0 ∧ 0 ≤ x ∧ x < y ⇒ x pow n < y pow n

   [pow_minus1]  Theorem

      |- ∀n. -1 pow (2 * n) = 1

   [pow_mul]  Theorem

      |- ∀n x y. (x * y) pow n = x pow n * y pow n

   [pow_neg_odd]  Theorem

      |- ∀x. x < 0 ⇒ (x pow n < 0 ⇔ ODD n)

   [pow_not_infty]  Theorem

      |- ∀n x.
           x ≠ NegInf ∧ x ≠ PosInf ⇒ x pow n ≠ NegInf ∧ x pow n ≠ PosInf

   [pow_pos_even]  Theorem

      |- ∀x. x < 0 ⇒ (0 < x pow n ⇔ EVEN n)

   [pow_pos_le]  Theorem

      |- ∀x. 0 ≤ x ⇒ ∀n. 0 ≤ x pow n

   [pow_pos_lt]  Theorem

      |- ∀x n. 0 < x ⇒ 0 < x pow n

   [pow_zero]  Theorem

      |- ∀n x. (x pow SUC n = 0) ⇔ (x = 0)

   [pow_zero_imp]  Theorem

      |- ∀n x. (x pow n = 0) ⇒ (x = 0)

   [quotient_normal]  Theorem

      |- ∀n m. &n / &m = Normal (&n / &m)

   [rat_not_infty]  Theorem

      |- ∀r. r ∈ Q_set ⇒ r ≠ NegInf ∧ r ≠ PosInf

   [real_normal]  Theorem

      |- ∀x. real (Normal x) = x

   [rinv_uniq]  Theorem

      |- ∀x y. (x * y = 1) ⇒ (y = inv x)

   [sqrt_mono_le]  Theorem

      |- ∀x y. 0 ≤ x ∧ x ≤ y ⇒ sqrt x ≤ sqrt y

   [sqrt_pos_le]  Theorem

      |- ∀x. 0 ≤ x ⇒ 0 ≤ sqrt x

   [sqrt_pos_lt]  Theorem

      |- ∀x. 0 < x ⇒ 0 < sqrt x

   [sqrt_pow2]  Theorem

      |- ∀x. (sqrt x pow 2 = x) ⇔ 0 ≤ x

   [sub_0]  Theorem

      |- ∀x y. (x − y = 0) ⇒ (x = y)

   [sub_add]  Theorem

      |- ∀x y. y ≠ NegInf ∧ y ≠ PosInf ⇒ (x − y + y = x)

   [sub_add2]  Theorem

      |- ∀x y. x ≠ NegInf ∧ x ≠ PosInf ⇒ (x + (y − x) = y)

   [sub_ldistrib]  Theorem

      |- ∀x y z.
           x ≠ NegInf ∧ x ≠ PosInf ∧ y ≠ NegInf ∧ y ≠ PosInf ∧ z ≠ NegInf ∧
           z ≠ PosInf ⇒
           (x * (y − z) = x * y − x * z)

   [sub_le_eq]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ⇒ (y − x ≤ z ⇔ y ≤ z + x)

   [sub_le_eq2]  Theorem

      |- ∀x y z.
           y ≠ NegInf ∧ y ≠ PosInf ∧ x ≠ NegInf ∧ z ≠ NegInf ⇒
           (y − x ≤ z ⇔ y ≤ z + x)

   [sub_le_imp]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ∧ y ≤ z + x ⇒ y − x ≤ z

   [sub_le_imp2]  Theorem

      |- ∀x y z. y ≠ NegInf ∧ y ≠ PosInf ∧ y ≤ z + x ⇒ y − x ≤ z

   [sub_le_switch]  Theorem

      |- ∀x y z.
           x ≠ NegInf ∧ x ≠ PosInf ∧ z ≠ NegInf ∧ z ≠ PosInf ⇒
           (y − x ≤ z ⇔ y − z ≤ x)

   [sub_le_switch2]  Theorem

      |- ∀x y z.
           x ≠ NegInf ∧ x ≠ PosInf ∧ y ≠ NegInf ∧ y ≠ PosInf ⇒
           (y − x ≤ z ⇔ y − z ≤ x)

   [sub_le_zero]  Theorem

      |- ∀x y. y ≠ NegInf ∧ y ≠ PosInf ⇒ (x ≤ y ⇔ x − y ≤ 0)

   [sub_lneg]  Theorem

      |- ∀x y.
           x ≠ NegInf ∧ y ≠ NegInf ∨ x ≠ PosInf ∧ y ≠ PosInf ⇒
           (-x − y = -(x + y))

   [sub_lt_imp]  Theorem

      |- ∀x y z. x ≠ NegInf ∧ x ≠ PosInf ∧ y < z + x ⇒ y − x < z

   [sub_lt_imp2]  Theorem

      |- ∀x y z. z ≠ NegInf ∧ z ≠ PosInf ∧ y < z + x ⇒ y − x < z

   [sub_lt_zero]  Theorem

      |- ∀x y. x < y ⇒ x − y < 0

   [sub_lt_zero2]  Theorem

      |- ∀x y. y ≠ NegInf ∧ y ≠ PosInf ∧ x − y < 0 ⇒ x < y

   [sub_lzero]  Theorem

      |- ∀x. 0 − x = -x

   [sub_not_infty]  Theorem

      |- ∀x y.
           (x ≠ NegInf ∧ y ≠ PosInf ⇒ x − y ≠ NegInf) ∧
           (x ≠ PosInf ∧ y ≠ NegInf ⇒ x − y ≠ PosInf)

   [sub_rdistrib]  Theorem

      |- ∀x y z.
           x ≠ NegInf ∧ x ≠ PosInf ∧ y ≠ NegInf ∧ y ≠ PosInf ∧ z ≠ NegInf ∧
           z ≠ PosInf ⇒
           ((x − y) * z = x * z − y * z)

   [sub_refl]  Theorem

      |- ∀x. x ≠ NegInf ∧ x ≠ PosInf ⇒ (x − x = 0)

   [sub_rneg]  Theorem

      |- ∀x y. x − -y = x + y

   [sub_rzero]  Theorem

      |- ∀x. x − 0 = x

   [sub_zero_le]  Theorem

      |- ∀x y. x ≤ y ⇔ 0 ≤ y − x

   [sub_zero_lt]  Theorem

      |- ∀x y. x < y ⇒ 0 < y − x

   [sub_zero_lt2]  Theorem

      |- ∀x y. x ≠ NegInf ∧ x ≠ PosInf ∧ 0 < y − x ⇒ x < y

   [sup_add_mono]  Theorem

      |- ∀f g.
           (∀n. 0 ≤ f n) ∧ (∀n. f n ≤ f (SUC n)) ∧ (∀n. 0 ≤ g n) ∧
           (∀n. g n ≤ g (SUC n)) ⇒
           (sup (IMAGE (λn. f n + g n) 𝕌(:num)) =
            sup (IMAGE f 𝕌(:num)) + sup (IMAGE g 𝕌(:num)))

   [sup_cmul]  Theorem

      |- ∀f c.
           0 ≤ c ⇒
           (sup (IMAGE (λn. Normal c * f n) 𝕌(:α)) =
            Normal c * sup (IMAGE f 𝕌(:α)))

   [sup_const]  Theorem

      |- ∀x. sup (λy. y = x) = x

   [sup_const_alt]  Theorem

      |- ∀p z. (∃x. p x) ∧ (∀x. p x ⇒ (x = z)) ⇒ (sup p = z)

   [sup_const_over_set]  Theorem

      |- ∀s k. s ≠ ∅ ⇒ (sup (IMAGE (λx. k) s) = k)

   [sup_eq]  Theorem

      |- ∀p x.
           (sup p = x) ⇔ (∀y. p y ⇒ y ≤ x) ∧ ∀y. (∀z. p z ⇒ z ≤ y) ⇒ x ≤ y

   [sup_le]  Theorem

      |- ∀p x. sup p ≤ x ⇔ ∀y. p y ⇒ y ≤ x

   [sup_le_mono]  Theorem

      |- ∀f z.
           (∀n. f n ≤ f (SUC n)) ∧ z < sup (IMAGE f 𝕌(:num)) ⇒ ∃n. z ≤ f n

   [sup_le_sup_imp]  Theorem

      |- ∀p q. (∀x. p x ⇒ ∃y. q y ∧ x ≤ y) ⇒ sup p ≤ sup q

   [sup_lt]  Theorem

      |- ∀P y. (∃x. P x ∧ y < x) ⇔ y < sup P

   [sup_lt_epsilon]  Theorem

      |- ∀P e.
           0 < e ∧ (∃x. P x ∧ x ≠ NegInf) ∧ sup P ≠ PosInf ⇒
           ∃x. P x ∧ sup P < x + e

   [sup_lt_infty]  Theorem

      |- ∀p. sup p < PosInf ⇒ ∀x. p x ⇒ x < PosInf

   [sup_max]  Theorem

      |- ∀p z. p z ∧ (∀x. p x ⇒ x ≤ z) ⇒ (sup p = z)

   [sup_mono]  Theorem

      |- ∀p q.
           (∀n. p n ≤ q n) ⇒ sup (IMAGE p 𝕌(:num)) ≤ sup (IMAGE q 𝕌(:num))

   [sup_num]  Theorem

      |- sup (λx. ∃n. x = &n) = PosInf

   [sup_seq]  Theorem

      |- ∀f l.
           mono_increasing f ⇒
           (f --> l ⇔ (sup (IMAGE (λn. Normal (f n)) 𝕌(:num)) = Normal l))

   [sup_suc]  Theorem

      |- ∀f.
           (∀m n. m ≤ n ⇒ f m ≤ f n) ⇒
           (sup (IMAGE (λn. f (SUC n)) 𝕌(:num)) = sup (IMAGE f 𝕌(:num)))

   [sup_sum_mono]  Theorem

      |- ∀f s.
           FINITE s ∧ (∀i. i ∈ s ⇒ ∀n. 0 ≤ f i n) ∧
           (∀i. i ∈ s ⇒ ∀n. f i n ≤ f i (SUC n)) ⇒
           (sup (IMAGE (λn. SIGMA (λi. f i n) s) 𝕌(:num)) =
            SIGMA (λi. sup (IMAGE (f i) 𝕌(:num))) s)

   [third_cancel]  Theorem

      |- 3 * (1 / 3) = 1

   [thirds_between]  Theorem

      |- ((0 < 1 / 3 ∧ 1 / 3 < 1) ∧ 0 < 2 / 3 ∧ 2 / 3 < 1) ∧
         (0 ≤ 1 / 3 ∧ 1 / 3 ≤ 1) ∧ 0 ≤ 2 / 3 ∧ 2 / 3 ≤ 1


*)
end
