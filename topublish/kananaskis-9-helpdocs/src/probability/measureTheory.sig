signature measureTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val Borel_def : thm
    val additive_def : thm
    val algebra_def : thm
    val closed_cdi_def : thm
    val countably_additive_def : thm
    val countably_subadditive_def : thm
    val fn_abs_def : thm
    val fn_minus_def : thm
    val fn_plus_def : thm
    val increasing_def : thm
    val indicator_fn_def : thm
    val inf_measure_def : thm
    val lambda_system_def : thm
    val m_space_def : thm
    val measurable_def : thm
    val measurable_sets_def : thm
    val measure_def : thm
    val measure_preserving_def : thm
    val measure_space_def : thm
    val null_set_def : thm
    val outer_measure_space_def : thm
    val pos_simple_fn_def : thm
    val positive_def : thm
    val sigma_algebra_def : thm
    val sigma_def : thm
    val smallest_closed_cdi_def : thm
    val space_def : thm
    val subadditive_def : thm
    val subset_class_def : thm
    val subsets_def : thm

  (*  Theorems  *)
    val ADDITIVE : thm
    val ADDITIVE_INCREASING : thm
    val ADDITIVE_SUM : thm
    val ALGEBRA_ALT_INTER : thm
    val ALGEBRA_COMPL : thm
    val ALGEBRA_DIFF : thm
    val ALGEBRA_EMPTY : thm
    val ALGEBRA_FINITE_UNION : thm
    val ALGEBRA_INTER : thm
    val ALGEBRA_INTER_SPACE : thm
    val ALGEBRA_SPACE : thm
    val ALGEBRA_SUBSET_LAMBDA_SYSTEM : thm
    val ALGEBRA_UNION : thm
    val BIGUNION_IMAGE_Q : thm
    val BOREL_MEASURABLE_SETS : thm
    val BOREL_MEASURABLE_SETS1 : thm
    val BOREL_MEASURABLE_SETS10 : thm
    val BOREL_MEASURABLE_SETS2 : thm
    val BOREL_MEASURABLE_SETS3 : thm
    val BOREL_MEASURABLE_SETS4 : thm
    val BOREL_MEASURABLE_SETS5 : thm
    val BOREL_MEASURABLE_SETS6 : thm
    val BOREL_MEASURABLE_SETS7 : thm
    val BOREL_MEASURABLE_SETS8 : thm
    val BOREL_MEASURABLE_SETS9 : thm
    val CARATHEODORY : thm
    val CARATHEODORY_LEMMA : thm
    val CLOSED_CDI_COMPL : thm
    val CLOSED_CDI_DISJOINT : thm
    val CLOSED_CDI_DUNION : thm
    val CLOSED_CDI_INCREASING : thm
    val COUNTABLY_ADDITIVE : thm
    val COUNTABLY_ADDITIVE_ADDITIVE : thm
    val COUNTABLY_SUBADDITIVE : thm
    val COUNTABLY_SUBADDITIVE_SUBADDITIVE : thm
    val FN_MINUS_ADD_LE : thm
    val FN_MINUS_CMUL : thm
    val FN_MINUS_POS : thm
    val FN_MINUS_POS_ZERO : thm
    val FN_PLUS_ADD_LE : thm
    val FN_PLUS_CMUL : thm
    val FN_PLUS_POS : thm
    val FN_PLUS_POS_ID : thm
    val IMAGE_SING : thm
    val INCREASING : thm
    val INCREASING_ADDITIVE_SUMMABLE : thm
    val INDICATOR_FN_MUL_INTER : thm
    val INF_MEASURE_AGREES : thm
    val INF_MEASURE_CLOSE : thm
    val INF_MEASURE_COUNTABLY_SUBADDITIVE : thm
    val INF_MEASURE_EMPTY : thm
    val INF_MEASURE_INCREASING : thm
    val INF_MEASURE_LE : thm
    val INF_MEASURE_NONEMPTY : thm
    val INF_MEASURE_OUTER : thm
    val INF_MEASURE_POS : thm
    val INF_MEASURE_POS0 : thm
    val INF_MEASURE_POSITIVE : thm
    val IN_MEASURABLE : thm
    val IN_MEASURABLE_BOREL : thm
    val IN_MEASURABLE_BOREL_ABS : thm
    val IN_MEASURABLE_BOREL_ADD : thm
    val IN_MEASURABLE_BOREL_ALL : thm
    val IN_MEASURABLE_BOREL_ALL_MEASURE : thm
    val IN_MEASURABLE_BOREL_ALT1 : thm
    val IN_MEASURABLE_BOREL_ALT2 : thm
    val IN_MEASURABLE_BOREL_ALT3 : thm
    val IN_MEASURABLE_BOREL_ALT4 : thm
    val IN_MEASURABLE_BOREL_ALT5 : thm
    val IN_MEASURABLE_BOREL_ALT6 : thm
    val IN_MEASURABLE_BOREL_ALT7 : thm
    val IN_MEASURABLE_BOREL_ALT8 : thm
    val IN_MEASURABLE_BOREL_ALT9 : thm
    val IN_MEASURABLE_BOREL_CMUL : thm
    val IN_MEASURABLE_BOREL_CMUL_INDICATOR : thm
    val IN_MEASURABLE_BOREL_CONST : thm
    val IN_MEASURABLE_BOREL_FN_MINUS : thm
    val IN_MEASURABLE_BOREL_FN_PLUS : thm
    val IN_MEASURABLE_BOREL_INDICATOR : thm
    val IN_MEASURABLE_BOREL_LE : thm
    val IN_MEASURABLE_BOREL_LT : thm
    val IN_MEASURABLE_BOREL_MAX : thm
    val IN_MEASURABLE_BOREL_MONO_SUP : thm
    val IN_MEASURABLE_BOREL_MUL : thm
    val IN_MEASURABLE_BOREL_MUL_INDICATOR : thm
    val IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ : thm
    val IN_MEASURABLE_BOREL_NEGINF : thm
    val IN_MEASURABLE_BOREL_PLUS_MINUS : thm
    val IN_MEASURABLE_BOREL_POS_SIMPLE_FN : thm
    val IN_MEASURABLE_BOREL_POW : thm
    val IN_MEASURABLE_BOREL_SQR : thm
    val IN_MEASURABLE_BOREL_SUB : thm
    val IN_MEASURABLE_BOREL_SUM : thm
    val IN_MEASURE_PRESERVING : thm
    val IN_SIGMA : thm
    val LAMBDA_SYSTEM_ADDITIVE : thm
    val LAMBDA_SYSTEM_ALGEBRA : thm
    val LAMBDA_SYSTEM_CARATHEODORY : thm
    val LAMBDA_SYSTEM_COMPL : thm
    val LAMBDA_SYSTEM_EMPTY : thm
    val LAMBDA_SYSTEM_INCREASING : thm
    val LAMBDA_SYSTEM_INTER : thm
    val LAMBDA_SYSTEM_POSITIVE : thm
    val LAMBDA_SYSTEM_STRONG_ADDITIVE : thm
    val LAMBDA_SYSTEM_STRONG_SUM : thm
    val MEASUBABLE_BIGUNION_LEMMA : thm
    val MEASURABLE_BIGUNION_PROPERTY : thm
    val MEASURABLE_BOREL : thm
    val MEASURABLE_COMP : thm
    val MEASURABLE_COMP_STRONG : thm
    val MEASURABLE_COMP_STRONGER : thm
    val MEASURABLE_DIFF_PROPERTY : thm
    val MEASURABLE_I : thm
    val MEASURABLE_LIFT : thm
    val MEASURABLE_POW_TO_POW : thm
    val MEASURABLE_POW_TO_POW_IMAGE : thm
    val MEASURABLE_PROD_SIGMA : thm
    val MEASURABLE_RANGE_REDUCE : thm
    val MEASURABLE_SETS_SUBSET_SPACE : thm
    val MEASURABLE_SIGMA : thm
    val MEASURABLE_SIGMA_PREIMAGES : thm
    val MEASURABLE_SUBSET : thm
    val MEASURABLE_UP_LIFT : thm
    val MEASURABLE_UP_SIGMA : thm
    val MEASURABLE_UP_SUBSET : thm
    val MEASURE_ADDITIVE : thm
    val MEASURE_COMPL : thm
    val MEASURE_COMPL_SUBSET : thm
    val MEASURE_COUNTABLE_INCREASING : thm
    val MEASURE_COUNTABLY_ADDITIVE : thm
    val MEASURE_DOWN : thm
    val MEASURE_EMPTY : thm
    val MEASURE_PRESERVING_LIFT : thm
    val MEASURE_PRESERVING_SUBSET : thm
    val MEASURE_PRESERVING_UP_LIFT : thm
    val MEASURE_PRESERVING_UP_SIGMA : thm
    val MEASURE_PRESERVING_UP_SUBSET : thm
    val MEASURE_REAL_SUM_IMAGE : thm
    val MEASURE_SPACE_ADDITIVE : thm
    val MEASURE_SPACE_BIGINTER : thm
    val MEASURE_SPACE_BIGUNION : thm
    val MEASURE_SPACE_CMUL : thm
    val MEASURE_SPACE_DIFF : thm
    val MEASURE_SPACE_EMPTY_MEASURABLE : thm
    val MEASURE_SPACE_INCREASING : thm
    val MEASURE_SPACE_INTER : thm
    val MEASURE_SPACE_IN_MSPACE : thm
    val MEASURE_SPACE_MSPACE_MEASURABLE : thm
    val MEASURE_SPACE_POSITIVE : thm
    val MEASURE_SPACE_REDUCE : thm
    val MEASURE_SPACE_RESTRICTED : thm
    val MEASURE_SPACE_SUBSET : thm
    val MEASURE_SPACE_SUBSET_MSPACE : thm
    val MEASURE_SPACE_UNION : thm
    val MONOTONE_CONVERGENCE : thm
    val MONOTONE_CONVERGENCE2 : thm
    val MONOTONE_CONVERGENCE_BIGINTER : thm
    val MONOTONE_CONVERGENCE_BIGINTER2 : thm
    val OUTER_MEASURE_SPACE_POSITIVE : thm
    val POW_ALGEBRA : thm
    val POW_SIGMA_ALGEBRA : thm
    val SIGMA_ALGEBRA : thm
    val SIGMA_ALGEBRA_ALGEBRA : thm
    val SIGMA_ALGEBRA_ALT : thm
    val SIGMA_ALGEBRA_ALT_DISJOINT : thm
    val SIGMA_ALGEBRA_ALT_MONO : thm
    val SIGMA_ALGEBRA_BOREL : thm
    val SIGMA_ALGEBRA_COUNTABLE_UNION : thm
    val SIGMA_ALGEBRA_ENUM : thm
    val SIGMA_ALGEBRA_FN : thm
    val SIGMA_ALGEBRA_FN_BIGINTER : thm
    val SIGMA_ALGEBRA_FN_DISJOINT : thm
    val SIGMA_ALGEBRA_SIGMA : thm
    val SIGMA_POW : thm
    val SIGMA_PROPERTY : thm
    val SIGMA_PROPERTY_ALT : thm
    val SIGMA_PROPERTY_DISJOINT : thm
    val SIGMA_PROPERTY_DISJOINT_LEMMA : thm
    val SIGMA_PROPERTY_DISJOINT_LEMMA1 : thm
    val SIGMA_PROPERTY_DISJOINT_LEMMA2 : thm
    val SIGMA_PROPERTY_DISJOINT_WEAK : thm
    val SIGMA_REDUCE : thm
    val SIGMA_SUBSET : thm
    val SIGMA_SUBSET_MEASURABLE_SETS : thm
    val SIGMA_SUBSET_SUBSETS : thm
    val SMALLEST_CLOSED_CDI : thm
    val SPACE : thm
    val SPACE_BOREL : thm
    val SPACE_SIGMA : thm
    val SPACE_SMALLEST_CLOSED_CDI : thm
    val STRONG_MEASURE_SPACE_SUBSET : thm
    val SUBADDITIVE : thm
    val SUBSET_BIGINTER : thm
    val UNIV_SIGMA_ALGEBRA : thm
    val finite_additivity_sufficient_for_finite_spaces : thm
    val finite_additivity_sufficient_for_finite_spaces2 : thm
    val indicator_fn_split : thm
    val indicator_fn_suminf : thm
    val measure_split : thm

  val measure_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [extreal] Parent theory of "measure"

   [Borel_def]  Definition

      |- Borel = sigma 𝕌(:extreal) (IMAGE (λa. {x | x < a}) 𝕌(:extreal))

   [additive_def]  Definition

      |- ∀m.
           additive m ⇔
           ∀s t.
             s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧ DISJOINT s t ⇒
             (measure m (s ∪ t) = measure m s + measure m t)

   [algebra_def]  Definition

      |- ∀a.
           algebra a ⇔
           subset_class (space a) (subsets a) ∧ ∅ ∈ subsets a ∧
           (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ subsets a) ∧
           ∀s t. s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∪ t ∈ subsets a

   [closed_cdi_def]  Definition

      |- ∀p.
           closed_cdi p ⇔
           subset_class (space p) (subsets p) ∧
           (∀s. s ∈ subsets p ⇒ space p DIFF s ∈ subsets p) ∧
           (∀f.
              f ∈ (𝕌(:num) -> subsets p) ∧ (f 0 = ∅) ∧
              (∀n. f n ⊆ f (SUC n)) ⇒
              BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets p) ∧
           ∀f.
             f ∈ (𝕌(:num) -> subsets p) ∧
             (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
             BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets p

   [countably_additive_def]  Definition

      |- ∀m.
           countably_additive m ⇔
           ∀f.
             f ∈ (𝕌(:num) -> measurable_sets m) ∧
             (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
             BIGUNION (IMAGE f 𝕌(:num)) ∈ measurable_sets m ⇒
             measure m o f sums measure m (BIGUNION (IMAGE f 𝕌(:num)))

   [countably_subadditive_def]  Definition

      |- ∀m.
           countably_subadditive m ⇔
           ∀f.
             f ∈ (𝕌(:num) -> measurable_sets m) ∧
             BIGUNION (IMAGE f 𝕌(:num)) ∈ measurable_sets m ∧
             summable (measure m o f) ⇒
             measure m (BIGUNION (IMAGE f 𝕌(:num))) ≤
             suminf (measure m o f)

   [fn_abs_def]  Definition

      |- ∀f. fn_abs f = (λx. abs (f x))

   [fn_minus_def]  Definition

      |- ∀f. fn_minus f = (λx. if f x < 0 then -f x else 0)

   [fn_plus_def]  Definition

      |- ∀f. fn_plus f = (λx. if 0 < f x then f x else 0)

   [increasing_def]  Definition

      |- ∀m.
           increasing m ⇔
           ∀s t.
             s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧ s ⊆ t ⇒
             measure m s ≤ measure m t

   [indicator_fn_def]  Definition

      |- ∀s. indicator_fn s = (λx. if x ∈ s then 1 else 0)

   [inf_measure_def]  Definition

      |- ∀m s.
           inf_measure m s =
           inf
             {r |
              ∃f.
                f ∈ (𝕌(:num) -> measurable_sets m) ∧
                (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
                s ⊆ BIGUNION (IMAGE f 𝕌(:num)) ∧ measure m o f sums r}

   [lambda_system_def]  Definition

      |- ∀gen lam.
           lambda_system gen lam =
           {l |
            l ∈ subsets gen ∧
            ∀s.
              s ∈ subsets gen ⇒
              (lam (l ∩ s) + lam ((space gen DIFF l) ∩ s) = lam s)}

   [m_space_def]  Definition

      |- ∀sp sts mu. m_space (sp,sts,mu) = sp

   [measurable_def]  Definition

      |- ∀a b.
           measurable a b =
           {f |
            sigma_algebra a ∧ sigma_algebra b ∧ f ∈ (space a -> space b) ∧
            ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}

   [measurable_sets_def]  Definition

      |- ∀sp sts mu. measurable_sets (sp,sts,mu) = sts

   [measure_def]  Definition

      |- ∀sp sts mu. measure (sp,sts,mu) = mu

   [measure_preserving_def]  Definition

      |- ∀m1 m2.
           measure_preserving m1 m2 =
           {f |
            f ∈
            measurable (m_space m1,measurable_sets m1)
              (m_space m2,measurable_sets m2) ∧ measure_space m1 ∧
            measure_space m2 ∧
            ∀s.
              s ∈ measurable_sets m2 ⇒
              (measure m1 (PREIMAGE f s ∩ m_space m1) = measure m2 s)}

   [measure_space_def]  Definition

      |- ∀m.
           measure_space m ⇔
           sigma_algebra (m_space m,measurable_sets m) ∧ positive m ∧
           countably_additive m

   [null_set_def]  Definition

      |- ∀m s. null_set m s ⇔ s ∈ measurable_sets m ∧ (measure m s = 0)

   [outer_measure_space_def]  Definition

      |- ∀m.
           outer_measure_space m ⇔
           positive m ∧ increasing m ∧ countably_subadditive m

   [pos_simple_fn_def]  Definition

      |- ∀m f s a x.
           pos_simple_fn m f s a x ⇔
           (∀t. 0 ≤ f t) ∧
           (∀t.
              t ∈ m_space m ⇒
              (f t = SIGMA (λi. Normal (x i) * indicator_fn (a i) t) s)) ∧
           (∀i. i ∈ s ⇒ a i ∈ measurable_sets m) ∧ FINITE s ∧
           (∀i. i ∈ s ⇒ 0 ≤ x i) ∧
           (∀i j. i ∈ s ∧ j ∈ s ∧ i ≠ j ⇒ DISJOINT (a i) (a j)) ∧
           (BIGUNION (IMAGE a s) = m_space m)

   [positive_def]  Definition

      |- ∀m.
           positive m ⇔
           (measure m ∅ = 0) ∧ ∀s. s ∈ measurable_sets m ⇒ 0 ≤ measure m s

   [sigma_algebra_def]  Definition

      |- ∀a.
           sigma_algebra a ⇔
           algebra a ∧
           ∀c. countable c ∧ c ⊆ subsets a ⇒ BIGUNION c ∈ subsets a

   [sigma_def]  Definition

      |- ∀sp st.
           sigma sp st = (sp,BIGINTER {s | st ⊆ s ∧ sigma_algebra (sp,s)})

   [smallest_closed_cdi_def]  Definition

      |- ∀a.
           smallest_closed_cdi a =
           (space a,BIGINTER {b | subsets a ⊆ b ∧ closed_cdi (space a,b)})

   [space_def]  Definition

      |- ∀x y. space (x,y) = x

   [subadditive_def]  Definition

      |- ∀m.
           subadditive m ⇔
           ∀s t.
             s ∈ measurable_sets m ∧ t ∈ measurable_sets m ⇒
             measure m (s ∪ t) ≤ measure m s + measure m t

   [subset_class_def]  Definition

      |- ∀sp sts. subset_class sp sts ⇔ ∀x. x ∈ sts ⇒ x ⊆ sp

   [subsets_def]  Definition

      |- ∀x y. subsets (x,y) = y

   [ADDITIVE]  Theorem

      |- ∀m s t u.
           additive m ∧ s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧
           DISJOINT s t ∧ (u = s ∪ t) ⇒
           (measure m u = measure m s + measure m t)

   [ADDITIVE_INCREASING]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           additive m ⇒
           increasing m

   [ADDITIVE_SUM]  Theorem

      |- ∀m f n.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           additive m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
           (sum (0,n) (measure m o f) =
            measure m (BIGUNION (IMAGE f (count n))))

   [ALGEBRA_ALT_INTER]  Theorem

      |- ∀a.
           algebra a ⇔
           subset_class (space a) (subsets a) ∧ ∅ ∈ subsets a ∧
           (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ subsets a) ∧
           ∀s t. s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∩ t ∈ subsets a

   [ALGEBRA_COMPL]  Theorem

      |- ∀a s. algebra a ∧ s ∈ subsets a ⇒ space a DIFF s ∈ subsets a

   [ALGEBRA_DIFF]  Theorem

      |- ∀a s t.
           algebra a ∧ s ∈ subsets a ∧ t ∈ subsets a ⇒ s DIFF t ∈ subsets a

   [ALGEBRA_EMPTY]  Theorem

      |- ∀a. algebra a ⇒ ∅ ∈ subsets a

   [ALGEBRA_FINITE_UNION]  Theorem

      |- ∀a c.
           algebra a ∧ FINITE c ∧ c ⊆ subsets a ⇒ BIGUNION c ∈ subsets a

   [ALGEBRA_INTER]  Theorem

      |- ∀a s t.
           algebra a ∧ s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∩ t ∈ subsets a

   [ALGEBRA_INTER_SPACE]  Theorem

      |- ∀a s.
           algebra a ∧ s ∈ subsets a ⇒
           (space a ∩ s = s) ∧ (s ∩ space a = s)

   [ALGEBRA_SPACE]  Theorem

      |- ∀a. algebra a ⇒ space a ∈ subsets a

   [ALGEBRA_SUBSET_LAMBDA_SYSTEM]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           increasing m ∧ additive m ⇒
           measurable_sets m ⊆
           lambda_system (m_space m,POW (m_space m)) (inf_measure m)

   [ALGEBRA_UNION]  Theorem

      |- ∀a s t.
           algebra a ∧ s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∪ t ∈ subsets a

   [BIGUNION_IMAGE_Q]  Theorem

      |- ∀a f.
           sigma_algebra a ∧ f ∈ (Q_set -> subsets a) ⇒
           BIGUNION (IMAGE f Q_set) ∈ subsets a

   [BOREL_MEASURABLE_SETS]  Theorem

      |- (∀c. {x | x < c} ∈ subsets Borel) ∧
         (∀c. {x | c ≤ x} ∈ subsets Borel) ∧
         (∀c. {x | c < x} ∈ subsets Borel) ∧
         (∀c. {x | x ≤ c} ∈ subsets Borel) ∧
         (∀c d. {x | c < x ∧ x < d} ∈ subsets Borel) ∧
         (∀c d. {x | c ≤ x ∧ x < d} ∈ subsets Borel) ∧
         (∀c d. {x | c < x ∧ x ≤ d} ∈ subsets Borel) ∧
         (∀c d. {x | c ≤ x ∧ x ≤ d} ∈ subsets Borel) ∧
         (∀c. {c} ∈ subsets Borel) ∧ ∀c. {x | x ≠ c} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS1]  Theorem

      |- ∀c. {x | x < c} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS10]  Theorem

      |- ∀c. {x | x ≠ c} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS2]  Theorem

      |- ∀c. {x | c ≤ x} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS3]  Theorem

      |- ∀c. {x | x ≤ c} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS4]  Theorem

      |- ∀c. {x | c < x} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS5]  Theorem

      |- ∀c d. {x | c ≤ x ∧ x < d} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS6]  Theorem

      |- ∀c d. {x | c < x ∧ x ≤ d} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS7]  Theorem

      |- ∀c d. {x | c ≤ x ∧ x ≤ d} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS8]  Theorem

      |- ∀c d. {x | c < x ∧ x < d} ∈ subsets Borel

   [BOREL_MEASURABLE_SETS9]  Theorem

      |- ∀c. {c} ∈ subsets Borel

   [CARATHEODORY]  Theorem

      |- ∀m0.
           algebra (m_space m0,measurable_sets m0) ∧ positive m0 ∧
           countably_additive m0 ⇒
           ∃m.
             (∀s. s ∈ measurable_sets m0 ⇒ (measure m s = measure m0 s)) ∧
             ((m_space m,measurable_sets m) =
              sigma (m_space m0) (measurable_sets m0)) ∧ measure_space m

   [CARATHEODORY_LEMMA]  Theorem

      |- ∀gsig lam.
           sigma_algebra gsig ∧
           outer_measure_space (space gsig,subsets gsig,lam) ⇒
           measure_space (space gsig,lambda_system gsig lam,lam)

   [CLOSED_CDI_COMPL]  Theorem

      |- ∀p s. closed_cdi p ∧ s ∈ subsets p ⇒ space p DIFF s ∈ subsets p

   [CLOSED_CDI_DISJOINT]  Theorem

      |- ∀p f.
           closed_cdi p ∧ f ∈ (𝕌(:num) -> subsets p) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
           BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets p

   [CLOSED_CDI_DUNION]  Theorem

      |- ∀p s t.
           ∅ ∈ subsets p ∧ closed_cdi p ∧ s ∈ subsets p ∧ t ∈ subsets p ∧
           DISJOINT s t ⇒
           s ∪ t ∈ subsets p

   [CLOSED_CDI_INCREASING]  Theorem

      |- ∀p f.
           closed_cdi p ∧ f ∈ (𝕌(:num) -> subsets p) ∧ (f 0 = ∅) ∧
           (∀n. f n ⊆ f (SUC n)) ⇒
           BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets p

   [COUNTABLY_ADDITIVE]  Theorem

      |- ∀m s f.
           countably_additive m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
           (s = BIGUNION (IMAGE f 𝕌(:num))) ∧ s ∈ measurable_sets m ⇒
           measure m o f sums measure m s

   [COUNTABLY_ADDITIVE_ADDITIVE]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           countably_additive m ⇒
           additive m

   [COUNTABLY_SUBADDITIVE]  Theorem

      |- ∀m f s.
           countably_subadditive m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           summable (measure m o f) ∧ (s = BIGUNION (IMAGE f 𝕌(:num))) ∧
           s ∈ measurable_sets m ⇒
           measure m s ≤ suminf (measure m o f)

   [COUNTABLY_SUBADDITIVE_SUBADDITIVE]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           countably_subadditive m ⇒
           subadditive m

   [FN_MINUS_ADD_LE]  Theorem

      |- ∀f g x. fn_minus (λx. f x + g x) x ≤ fn_minus f x + fn_minus g x

   [FN_MINUS_CMUL]  Theorem

      |- ∀f c.
           (0 ≤ c ⇒
            (fn_minus (λx. Normal c * f x) =
             (λx. Normal c * fn_minus f x))) ∧
           (c ≤ 0 ⇒
            (fn_minus (λx. Normal c * f x) =
             (λx. -Normal c * fn_plus f x)))

   [FN_MINUS_POS]  Theorem

      |- ∀g x. 0 ≤ fn_minus g x

   [FN_MINUS_POS_ZERO]  Theorem

      |- (∀x. 0 ≤ g x) ⇒ (fn_minus g = (λx. 0))

   [FN_PLUS_ADD_LE]  Theorem

      |- ∀f g x. fn_plus (λx. f x + g x) x ≤ fn_plus f x + fn_plus g x

   [FN_PLUS_CMUL]  Theorem

      |- ∀f c.
           (0 ≤ c ⇒
            (fn_plus (λx. Normal c * f x) =
             (λx. Normal c * fn_plus f x))) ∧
           (c ≤ 0 ⇒
            (fn_plus (λx. Normal c * f x) =
             (λx. -Normal c * fn_minus f x)))

   [FN_PLUS_POS]  Theorem

      |- ∀g x. 0 ≤ fn_plus g x

   [FN_PLUS_POS_ID]  Theorem

      |- (∀x. 0 ≤ g x) ⇒ (fn_plus g = g)

   [IMAGE_SING]  Theorem

      |- ∀f x. IMAGE f {x} = {f x}

   [INCREASING]  Theorem

      |- ∀m s t.
           increasing m ∧ s ⊆ t ∧ s ∈ measurable_sets m ∧
           t ∈ measurable_sets m ⇒
           measure m s ≤ measure m t

   [INCREASING_ADDITIVE_SUMMABLE]  Theorem

      |- ∀m f.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           increasing m ∧ additive m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
           summable (measure m o f)

   [INDICATOR_FN_MUL_INTER]  Theorem

      |- ∀A B.
           (λt. indicator_fn A t * indicator_fn B t) =
           (λt. indicator_fn (A ∩ B) t)

   [INF_MEASURE_AGREES]  Theorem

      |- ∀m s.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           countably_additive m ∧ s ∈ measurable_sets m ⇒
           (inf_measure m s = measure m s)

   [INF_MEASURE_CLOSE]  Theorem

      |- ∀m s e.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧ 0 < e ∧
           s ⊆ m_space m ⇒
           ∃f l.
             f ∈ (𝕌(:num) -> measurable_sets m) ∧
             s ⊆ BIGUNION (IMAGE f 𝕌(:num)) ∧
             (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧ measure m o f sums l ∧
             l ≤ inf_measure m s + e

   [INF_MEASURE_COUNTABLY_SUBADDITIVE]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           increasing m ⇒
           countably_subadditive (m_space m,POW (m_space m),inf_measure m)

   [INF_MEASURE_EMPTY]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ⇒
           (inf_measure m ∅ = 0)

   [INF_MEASURE_INCREASING]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ⇒
           increasing (m_space m,POW (m_space m),inf_measure m)

   [INF_MEASURE_LE]  Theorem

      |- ∀m s x.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           increasing m ∧
           x ∈
           {r |
            ∃f.
              f ∈ (𝕌(:num) -> measurable_sets m) ∧
              s ⊆ BIGUNION (IMAGE f 𝕌(:num)) ∧ measure m o f sums r} ⇒
           inf_measure m s ≤ x

   [INF_MEASURE_NONEMPTY]  Theorem

      |- ∀m g s.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           s ∈ measurable_sets m ∧ g ⊆ s ⇒
           measure m s ∈
           {r |
            ∃f.
              f ∈ (𝕌(:num) -> measurable_sets m) ∧
              (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
              g ⊆ BIGUNION (IMAGE f 𝕌(:num)) ∧ measure m o f sums r}

   [INF_MEASURE_OUTER]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           increasing m ⇒
           outer_measure_space (m_space m,POW (m_space m),inf_measure m)

   [INF_MEASURE_POS]  Theorem

      |- ∀m g.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           g ⊆ m_space m ⇒
           0 ≤ inf_measure m g

   [INF_MEASURE_POS0]  Theorem

      |- ∀m g x.
           algebra (m_space m,measurable_sets m) ∧ positive m ∧
           x ∈
           {r |
            ∃f.
              f ∈ (𝕌(:num) -> measurable_sets m) ∧
              (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
              g ⊆ BIGUNION (IMAGE f 𝕌(:num)) ∧ measure m o f sums r} ⇒
           0 ≤ x

   [INF_MEASURE_POSITIVE]  Theorem

      |- ∀m.
           algebra (m_space m,measurable_sets m) ∧ positive m ⇒
           positive (m_space m,POW (m_space m),inf_measure m)

   [IN_MEASURABLE]  Theorem

      |- ∀a b f.
           f ∈ measurable a b ⇔
           sigma_algebra a ∧ sigma_algebra b ∧ f ∈ (space a -> space b) ∧
           ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c. {x | f x < c} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ABS]  Theorem

      |- ∀a f g.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           (∀x. x ∈ space a ⇒ (g x = abs (f x))) ⇒
           g ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_ADD]  Theorem

      |- ∀a f g h.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           g ∈ measurable a Borel ∧ (∀x. x ∈ space a ⇒ (h x = f x + g x)) ⇒
           h ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_ALL]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇒
           (∀c. {x | f x < c} ∩ space a ∈ subsets a) ∧
           (∀c. {x | c ≤ f x} ∩ space a ∈ subsets a) ∧
           (∀c. {x | f x ≤ c} ∩ space a ∈ subsets a) ∧
           (∀c. {x | c < f x} ∩ space a ∈ subsets a) ∧
           (∀c d. {x | c < f x ∧ f x < d} ∩ space a ∈ subsets a) ∧
           (∀c d. {x | c ≤ f x ∧ f x < d} ∩ space a ∈ subsets a) ∧
           (∀c d. {x | c < f x ∧ f x ≤ d} ∩ space a ∈ subsets a) ∧
           (∀c d. {x | c ≤ f x ∧ f x ≤ d} ∩ space a ∈ subsets a) ∧
           (∀c. {x | f x ≠ c} ∩ space a ∈ subsets a) ∧
           ∀c. {x | f x = c} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALL_MEASURE]  Theorem

      |- ∀f m.
           f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
           (∀c. {x | f x < c} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c. {x | c ≤ f x} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c. {x | f x ≤ c} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c. {x | c < f x} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c d.
              {x | c < f x ∧ f x < d} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c d.
              {x | c ≤ f x ∧ f x < d} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c d.
              {x | c < f x ∧ f x ≤ d} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c d.
              {x | c ≤ f x ∧ f x ≤ d} ∩ m_space m ∈ measurable_sets m) ∧
           (∀c. {x | f x = c} ∩ m_space m ∈ measurable_sets m) ∧
           ∀c. {x | f x ≠ c} ∩ m_space m ∈ measurable_sets m

   [IN_MEASURABLE_BOREL_ALT1]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c. {x | c ≤ f x} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT2]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c. {x | f x ≤ c} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT3]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c. {x | c < f x} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT4]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c d. {x | c ≤ f x ∧ f x < d} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT5]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c d. {x | c < f x ∧ f x ≤ d} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT6]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c d. {x | c ≤ f x ∧ f x ≤ d} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT7]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇒
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c d. {x | c < f x ∧ f x < d} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT8]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇒
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c. {x | f x = c} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_ALT9]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇒
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c. {x | f x ≠ c} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_CMUL]  Theorem

      |- ∀a f g z.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           (∀x. x ∈ space a ⇒ (g x = Normal z * f x)) ⇒
           g ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_CMUL_INDICATOR]  Theorem

      |- ∀a z s.
           sigma_algebra a ∧ s ∈ subsets a ⇒
           (λx. Normal z * indicator_fn s x) ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_CONST]  Theorem

      |- ∀a k f.
           sigma_algebra a ∧ (∀x. x ∈ space a ⇒ (f x = k)) ⇒
           f ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_FN_MINUS]  Theorem

      |- ∀a f. f ∈ measurable a Borel ⇒ fn_minus f ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_FN_PLUS]  Theorem

      |- ∀a f. f ∈ measurable a Borel ⇒ fn_plus f ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_INDICATOR]  Theorem

      |- ∀a A f.
           sigma_algebra a ∧ A ∈ subsets a ∧
           (∀x. x ∈ space a ⇒ (f x = indicator_fn A x)) ⇒
           f ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_LE]  Theorem

      |- ∀f g a.
           f ∈ measurable a Borel ∧ g ∈ measurable a Borel ⇒
           {x | f x ≤ g x} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_LT]  Theorem

      |- ∀f g a.
           f ∈ measurable a Borel ∧ g ∈ measurable a Borel ⇒
           {x | f x < g x} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_MAX]  Theorem

      |- ∀a f g.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           g ∈ measurable a Borel ⇒
           (λx. max (f x) (g x)) ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_MONO_SUP]  Theorem

      |- ∀fn f a.
           sigma_algebra a ∧ (∀n. fn n ∈ measurable a Borel) ∧
           (∀n x. x ∈ space a ⇒ fn n x ≤ fn (SUC n) x) ∧
           (∀x. x ∈ space a ⇒ (f x = sup (IMAGE (λn. fn n x) 𝕌(:num)))) ⇒
           f ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_MUL]  Theorem

      |- ∀a f g h.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           (∀x.
              x ∈ space a ⇒
              f x ≠ NegInf ∧ f x ≠ PosInf ∧ g x ≠ NegInf ∧ g x ≠ PosInf) ∧
           g ∈ measurable a Borel ∧ (∀x. x ∈ space a ⇒ (h x = f x * g x)) ⇒
           h ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_MUL_INDICATOR]  Theorem

      |- ∀a f s.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧ s ∈ subsets a ⇒
           (λx. f x * indicator_fn s x) ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ]  Theorem

      |- ∀a f.
           sigma_algebra a ⇒
           (f ∈ measurable a Borel ⇔
            (λx. f x * indicator_fn (space a) x) ∈ measurable a Borel)

   [IN_MEASURABLE_BOREL_NEGINF]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇒
           {x | f x = NegInf} ∩ space a ∈ subsets a

   [IN_MEASURABLE_BOREL_PLUS_MINUS]  Theorem

      |- ∀a f.
           f ∈ measurable a Borel ⇔
           fn_plus f ∈ measurable a Borel ∧ fn_minus f ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_POS_SIMPLE_FN]  Theorem

      |- ∀m f.
           measure_space m ∧ (∃s a x. pos_simple_fn m f s a x) ⇒
           f ∈ measurable (m_space m,measurable_sets m) Borel

   [IN_MEASURABLE_BOREL_POW]  Theorem

      |- ∀n a f.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           (∀x. x ∈ space a ⇒ f x ≠ NegInf ∧ f x ≠ PosInf) ⇒
           (λx. f x pow n) ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_SQR]  Theorem

      |- ∀a f g.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           (∀x. x ∈ space a ⇒ (g x = f x pow 2)) ⇒
           g ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_SUB]  Theorem

      |- ∀a f g h.
           sigma_algebra a ∧ f ∈ measurable a Borel ∧
           g ∈ measurable a Borel ∧ (∀x. x ∈ space a ⇒ (h x = f x − g x)) ⇒
           h ∈ measurable a Borel

   [IN_MEASURABLE_BOREL_SUM]  Theorem

      |- ∀a f g s.
           FINITE s ∧ sigma_algebra a ∧
           (∀i. i ∈ s ⇒ f i ∈ measurable a Borel) ∧
           (∀x. x ∈ space a ⇒ (g x = SIGMA (λi. f i x) s)) ⇒
           g ∈ measurable a Borel

   [IN_MEASURE_PRESERVING]  Theorem

      |- ∀m1 m2 f.
           f ∈ measure_preserving m1 m2 ⇔
           f ∈
           measurable (m_space m1,measurable_sets m1)
             (m_space m2,measurable_sets m2) ∧ measure_space m1 ∧
           measure_space m2 ∧
           ∀s.
             s ∈ measurable_sets m2 ⇒
             (measure m1 (PREIMAGE f s ∩ m_space m1) = measure m2 s)

   [IN_SIGMA]  Theorem

      |- ∀sp a x. x ∈ a ⇒ x ∈ subsets (sigma sp a)

   [LAMBDA_SYSTEM_ADDITIVE]  Theorem

      |- ∀g0 lam l1 l2.
           algebra g0 ∧ positive (space g0,subsets g0,lam) ⇒
           additive (space g0,lambda_system g0 lam,lam)

   [LAMBDA_SYSTEM_ALGEBRA]  Theorem

      |- ∀g0 lam.
           algebra g0 ∧ positive (space g0,subsets g0,lam) ⇒
           algebra (space g0,lambda_system g0 lam)

   [LAMBDA_SYSTEM_CARATHEODORY]  Theorem

      |- ∀gsig lam.
           sigma_algebra gsig ∧
           outer_measure_space (space gsig,subsets gsig,lam) ⇒
           ∀f.
             f ∈ (𝕌(:num) -> lambda_system gsig lam) ∧
             (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
             BIGUNION (IMAGE f 𝕌(:num)) ∈ lambda_system gsig lam ∧
             lam o f sums lam (BIGUNION (IMAGE f 𝕌(:num)))

   [LAMBDA_SYSTEM_COMPL]  Theorem

      |- ∀g0 lam l.
           algebra g0 ∧ positive (space g0,subsets g0,lam) ∧
           l ∈ lambda_system g0 lam ⇒
           space g0 DIFF l ∈ lambda_system g0 lam

   [LAMBDA_SYSTEM_EMPTY]  Theorem

      |- ∀g0 lam.
           algebra g0 ∧ positive (space g0,subsets g0,lam) ⇒
           ∅ ∈ lambda_system g0 lam

   [LAMBDA_SYSTEM_INCREASING]  Theorem

      |- ∀g0 lam.
           increasing (space g0,subsets g0,lam) ⇒
           increasing (space g0,lambda_system g0 lam,lam)

   [LAMBDA_SYSTEM_INTER]  Theorem

      |- ∀g0 lam l1 l2.
           algebra g0 ∧ positive (space g0,subsets g0,lam) ∧
           l1 ∈ lambda_system g0 lam ∧ l2 ∈ lambda_system g0 lam ⇒
           l1 ∩ l2 ∈ lambda_system g0 lam

   [LAMBDA_SYSTEM_POSITIVE]  Theorem

      |- ∀g0 lam.
           positive (space g0,subsets g0,lam) ⇒
           positive (space g0,lambda_system g0 lam,lam)

   [LAMBDA_SYSTEM_STRONG_ADDITIVE]  Theorem

      |- ∀g0 lam g l1 l2.
           algebra g0 ∧ positive (space g0,subsets g0,lam) ∧
           g ∈ subsets g0 ∧ DISJOINT l1 l2 ∧ l1 ∈ lambda_system g0 lam ∧
           l2 ∈ lambda_system g0 lam ⇒
           (lam ((l1 ∪ l2) ∩ g) = lam (l1 ∩ g) + lam (l2 ∩ g))

   [LAMBDA_SYSTEM_STRONG_SUM]  Theorem

      |- ∀g0 lam g f n.
           algebra g0 ∧ positive (space g0,subsets g0,lam) ∧
           g ∈ subsets g0 ∧ f ∈ (𝕌(:num) -> lambda_system g0 lam) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
           (sum (0,n) (lam o (λs. s ∩ g) o f) =
            lam (BIGUNION (IMAGE f (count n)) ∩ g))

   [MEASUBABLE_BIGUNION_LEMMA]  Theorem

      |- ∀a b f.
           sigma_algebra a ∧ sigma_algebra b ∧ f ∈ (space a -> space b) ∧
           (∀s. s ∈ subsets b ⇒ PREIMAGE f s ∈ subsets a) ⇒
           ∀c.
             countable c ∧ c ⊆ IMAGE (PREIMAGE f) (subsets b) ⇒
             BIGUNION c ∈ IMAGE (PREIMAGE f) (subsets b)

   [MEASURABLE_BIGUNION_PROPERTY]  Theorem

      |- ∀a b f.
           sigma_algebra a ∧ sigma_algebra b ∧ f ∈ (space a -> space b) ∧
           (∀s. s ∈ subsets b ⇒ PREIMAGE f s ∈ subsets a) ⇒
           ∀c.
             c ⊆ subsets b ⇒
             (PREIMAGE f (BIGUNION c) = BIGUNION (IMAGE (PREIMAGE f) c))

   [MEASURABLE_BOREL]  Theorem

      |- ∀f a.
           f ∈ measurable a Borel ⇔
           sigma_algebra a ∧ f ∈ (space a -> 𝕌(:extreal)) ∧
           ∀c. PREIMAGE f {x | x < c} ∩ space a ∈ subsets a

   [MEASURABLE_COMP]  Theorem

      |- ∀f g a b c.
           f ∈ measurable a b ∧ g ∈ measurable b c ⇒ g o f ∈ measurable a c

   [MEASURABLE_COMP_STRONG]  Theorem

      |- ∀f g a b c.
           f ∈ measurable a b ∧ sigma_algebra c ∧
           g ∈ (space b -> space c) ∧
           (∀x.
              x ∈ subsets c ⇒
              PREIMAGE g x ∩ IMAGE f (space a) ∈ subsets b) ⇒
           g o f ∈ measurable a c

   [MEASURABLE_COMP_STRONGER]  Theorem

      |- ∀f g a b c t.
           f ∈ measurable a b ∧ sigma_algebra c ∧
           g ∈ (space b -> space c) ∧ IMAGE f (space a) ⊆ t ∧
           (∀s. s ∈ subsets c ⇒ PREIMAGE g s ∩ t ∈ subsets b) ⇒
           g o f ∈ measurable a c

   [MEASURABLE_DIFF_PROPERTY]  Theorem

      |- ∀a b f.
           sigma_algebra a ∧ sigma_algebra b ∧ f ∈ (space a -> space b) ∧
           (∀s. s ∈ subsets b ⇒ PREIMAGE f s ∈ subsets a) ⇒
           ∀s.
             s ∈ subsets b ⇒
             (PREIMAGE f (space b DIFF s) = space a DIFF PREIMAGE f s)

   [MEASURABLE_I]  Theorem

      |- ∀a. sigma_algebra a ⇒ I ∈ measurable a a

   [MEASURABLE_LIFT]  Theorem

      |- ∀f a b.
           f ∈ measurable a b ⇒
           f ∈ measurable a (sigma (space b) (subsets b))

   [MEASURABLE_POW_TO_POW]  Theorem

      |- ∀m f.
           measure_space m ∧ (measurable_sets m = POW (m_space m)) ⇒
           f ∈ measurable (m_space m,measurable_sets m) (𝕌(:β),POW 𝕌(:β))

   [MEASURABLE_POW_TO_POW_IMAGE]  Theorem

      |- ∀m f.
           measure_space m ∧ (measurable_sets m = POW (m_space m)) ⇒
           f ∈
           measurable (m_space m,measurable_sets m)
             (IMAGE f (m_space m),POW (IMAGE f (m_space m)))

   [MEASURABLE_PROD_SIGMA]  Theorem

      |- ∀a a1 a2 f.
           sigma_algebra a ∧ FST o f ∈ measurable a a1 ∧
           SND o f ∈ measurable a a2 ⇒
           f ∈
           measurable a
             (sigma (space a1 × space a2)
                (prod_sets (subsets a1) (subsets a2)))

   [MEASURABLE_RANGE_REDUCE]  Theorem

      |- ∀m f s.
           measure_space m ∧
           f ∈ measurable (m_space m,measurable_sets m) (s,POW s) ∧ s ≠ ∅ ⇒
           f ∈
           measurable (m_space m,measurable_sets m)
             (s ∩ IMAGE f (m_space m),POW (s ∩ IMAGE f (m_space m)))

   [MEASURABLE_SETS_SUBSET_SPACE]  Theorem

      |- ∀m s. measure_space m ∧ s ∈ measurable_sets m ⇒ s ⊆ m_space m

   [MEASURABLE_SIGMA]  Theorem

      |- ∀f a b sp.
           sigma_algebra a ∧ subset_class sp b ∧ f ∈ (space a -> sp) ∧
           (∀s. s ∈ b ⇒ PREIMAGE f s ∩ space a ∈ subsets a) ⇒
           f ∈ measurable a (sigma sp b)

   [MEASURABLE_SIGMA_PREIMAGES]  Theorem

      |- ∀a b f.
           sigma_algebra a ∧ sigma_algebra b ∧ f ∈ (space a -> space b) ∧
           (∀s. s ∈ subsets b ⇒ PREIMAGE f s ∈ subsets a) ⇒
           sigma_algebra (space a,IMAGE (PREIMAGE f) (subsets b))

   [MEASURABLE_SUBSET]  Theorem

      |- ∀a b. measurable a b ⊆ measurable a (sigma (space b) (subsets b))

   [MEASURABLE_UP_LIFT]  Theorem

      |- ∀sp a b c f.
           f ∈ measurable (sp,a) c ∧ sigma_algebra (sp,b) ∧ a ⊆ b ⇒
           f ∈ measurable (sp,b) c

   [MEASURABLE_UP_SIGMA]  Theorem

      |- ∀a b. measurable a b ⊆ measurable (sigma (space a) (subsets a)) b

   [MEASURABLE_UP_SUBSET]  Theorem

      |- ∀sp a b c.
           a ⊆ b ∧ sigma_algebra (sp,b) ⇒
           measurable (sp,a) c ⊆ measurable (sp,b) c

   [MEASURE_ADDITIVE]  Theorem

      |- ∀m s t u.
           measure_space m ∧ s ∈ measurable_sets m ∧
           t ∈ measurable_sets m ∧ DISJOINT s t ∧ (u = s ∪ t) ⇒
           (measure m u = measure m s + measure m t)

   [MEASURE_COMPL]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           (measure m (m_space m DIFF s) =
            measure m (m_space m) − measure m s)

   [MEASURE_COMPL_SUBSET]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ∧
           t ∈ measurable_sets m ∧ t ⊆ s ⇒
           (measure m (s DIFF t) = measure m s − measure m t)

   [MEASURE_COUNTABLE_INCREASING]  Theorem

      |- ∀m s f.
           measure_space m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (f 0 = ∅) ∧ (∀n. f n ⊆ f (SUC n)) ∧
           (s = BIGUNION (IMAGE f 𝕌(:num))) ⇒
           measure m o f --> measure m s

   [MEASURE_COUNTABLY_ADDITIVE]  Theorem

      |- ∀m s f.
           measure_space m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
           (s = BIGUNION (IMAGE f 𝕌(:num))) ⇒
           measure m o f sums measure m s

   [MEASURE_DOWN]  Theorem

      |- ∀m0 m1.
           sigma_algebra (m_space m0,measurable_sets m0) ∧
           measurable_sets m0 ⊆ measurable_sets m1 ∧
           (measure m0 = measure m1) ∧ measure_space m1 ⇒
           measure_space m0

   [MEASURE_EMPTY]  Theorem

      |- ∀m. measure_space m ⇒ (measure m ∅ = 0)

   [MEASURE_PRESERVING_LIFT]  Theorem

      |- ∀m1 m2 a f.
           measure_space m1 ∧ measure_space m2 ∧
           (measurable_sets m2 = subsets (sigma (m_space m2) a)) ∧
           f ∈ measure_preserving m1 (m_space m2,a,measure m2) ⇒
           f ∈ measure_preserving m1 m2

   [MEASURE_PRESERVING_SUBSET]  Theorem

      |- ∀m1 m2 a.
           measure_space m1 ∧ measure_space m2 ∧
           (measurable_sets m2 = subsets (sigma (m_space m2) a)) ⇒
           measure_preserving m1 (m_space m2,a,measure m2) ⊆
           measure_preserving m1 m2

   [MEASURE_PRESERVING_UP_LIFT]  Theorem

      |- ∀m1 m2 f.
           measure_space m1 ∧
           f ∈ measure_preserving (m_space m1,a,measure m1) m2 ∧
           sigma_algebra (m_space m1,measurable_sets m1) ∧
           a ⊆ measurable_sets m1 ⇒
           f ∈ measure_preserving m1 m2

   [MEASURE_PRESERVING_UP_SIGMA]  Theorem

      |- ∀m1 m2 a.
           measure_space m1 ∧
           (measurable_sets m1 = subsets (sigma (m_space m1) a)) ⇒
           measure_preserving (m_space m1,a,measure m1) m2 ⊆
           measure_preserving m1 m2

   [MEASURE_PRESERVING_UP_SUBSET]  Theorem

      |- ∀m1 m2.
           measure_space m1 ∧ a ⊆ measurable_sets m1 ∧
           sigma_algebra (m_space m1,measurable_sets m1) ⇒
           measure_preserving (m_space m1,a,measure m1) m2 ⊆
           measure_preserving m1 m2

   [MEASURE_REAL_SUM_IMAGE]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ∧
           (∀x. x ∈ s ⇒ {x} ∈ measurable_sets m) ∧ FINITE s ⇒
           (measure m s = SIGMA (λx. measure m {x}) s)

   [MEASURE_SPACE_ADDITIVE]  Theorem

      |- ∀m. measure_space m ⇒ additive m

   [MEASURE_SPACE_BIGINTER]  Theorem

      |- ∀m s.
           measure_space m ∧ (∀n. s n ∈ measurable_sets m) ⇒
           BIGINTER (IMAGE s 𝕌(:num)) ∈ measurable_sets m

   [MEASURE_SPACE_BIGUNION]  Theorem

      |- ∀m s.
           measure_space m ∧ (∀n. s n ∈ measurable_sets m) ⇒
           BIGUNION (IMAGE s 𝕌(:num)) ∈ measurable_sets m

   [MEASURE_SPACE_CMUL]  Theorem

      |- ∀m c.
           measure_space m ∧ 0 ≤ c ⇒
           measure_space
             (m_space m,measurable_sets m,(λa. c * measure m a))

   [MEASURE_SPACE_DIFF]  Theorem

      |- ∀m s t.
           measure_space m ∧ s ∈ measurable_sets m ∧
           t ∈ measurable_sets m ⇒
           s DIFF t ∈ measurable_sets m

   [MEASURE_SPACE_EMPTY_MEASURABLE]  Theorem

      |- ∀m. measure_space m ⇒ ∅ ∈ measurable_sets m

   [MEASURE_SPACE_INCREASING]  Theorem

      |- ∀m. measure_space m ⇒ increasing m

   [MEASURE_SPACE_INTER]  Theorem

      |- ∀m s t.
           measure_space m ∧ s ∈ measurable_sets m ∧
           t ∈ measurable_sets m ⇒
           s ∩ t ∈ measurable_sets m

   [MEASURE_SPACE_IN_MSPACE]  Theorem

      |- ∀m A.
           measure_space m ∧ A ∈ measurable_sets m ⇒
           ∀x. x ∈ A ⇒ x ∈ m_space m

   [MEASURE_SPACE_MSPACE_MEASURABLE]  Theorem

      |- ∀m. measure_space m ⇒ m_space m ∈ measurable_sets m

   [MEASURE_SPACE_POSITIVE]  Theorem

      |- ∀m. measure_space m ⇒ positive m

   [MEASURE_SPACE_REDUCE]  Theorem

      |- ∀m. (m_space m,measurable_sets m,measure m) = m

   [MEASURE_SPACE_RESTRICTED]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           measure_space
             (s,IMAGE (λt. s ∩ t) (measurable_sets m),measure m)

   [MEASURE_SPACE_SUBSET]  Theorem

      |- ∀s s' m.
           s' ⊆ s ∧ measure_space (s,POW s,m) ⇒ measure_space (s',POW s',m)

   [MEASURE_SPACE_SUBSET_MSPACE]  Theorem

      |- ∀A m. measure_space m ∧ A ∈ measurable_sets m ⇒ A ⊆ m_space m

   [MEASURE_SPACE_UNION]  Theorem

      |- ∀m s t.
           measure_space m ∧ s ∈ measurable_sets m ∧
           t ∈ measurable_sets m ⇒
           s ∪ t ∈ measurable_sets m

   [MONOTONE_CONVERGENCE]  Theorem

      |- ∀m s f.
           measure_space m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀n. f n ⊆ f (SUC n)) ∧ (s = BIGUNION (IMAGE f 𝕌(:num))) ⇒
           measure m o f --> measure m s

   [MONOTONE_CONVERGENCE2]  Theorem

      |- ∀m f.
           measure_space m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀n. f n ⊆ f (SUC n)) ⇒
           measure m o f --> measure m (BIGUNION (IMAGE f 𝕌(:num)))

   [MONOTONE_CONVERGENCE_BIGINTER]  Theorem

      |- ∀m s f.
           measure_space m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀n. f (SUC n) ⊆ f n) ∧ (s = BIGINTER (IMAGE f 𝕌(:num))) ⇒
           measure m o f --> measure m s

   [MONOTONE_CONVERGENCE_BIGINTER2]  Theorem

      |- ∀m f.
           measure_space m ∧ f ∈ (𝕌(:num) -> measurable_sets m) ∧
           (∀n. f (SUC n) ⊆ f n) ⇒
           measure m o f --> measure m (BIGINTER (IMAGE f 𝕌(:num)))

   [OUTER_MEASURE_SPACE_POSITIVE]  Theorem

      |- ∀m. outer_measure_space m ⇒ positive m

   [POW_ALGEBRA]  Theorem

      |- algebra (sp,POW sp)

   [POW_SIGMA_ALGEBRA]  Theorem

      |- sigma_algebra (sp,POW sp)

   [SIGMA_ALGEBRA]  Theorem

      |- ∀p.
           sigma_algebra p ⇔
           subset_class (space p) (subsets p) ∧ ∅ ∈ subsets p ∧
           (∀s. s ∈ subsets p ⇒ space p DIFF s ∈ subsets p) ∧
           ∀c. countable c ∧ c ⊆ subsets p ⇒ BIGUNION c ∈ subsets p

   [SIGMA_ALGEBRA_ALGEBRA]  Theorem

      |- ∀a. sigma_algebra a ⇒ algebra a

   [SIGMA_ALGEBRA_ALT]  Theorem

      |- ∀a.
           sigma_algebra a ⇔
           algebra a ∧
           ∀f.
             f ∈ (𝕌(:num) -> subsets a) ⇒
             BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a

   [SIGMA_ALGEBRA_ALT_DISJOINT]  Theorem

      |- ∀a.
           sigma_algebra a ⇔
           algebra a ∧
           ∀f.
             f ∈ (𝕌(:num) -> subsets a) ∧
             (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
             BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a

   [SIGMA_ALGEBRA_ALT_MONO]  Theorem

      |- ∀a.
           sigma_algebra a ⇔
           algebra a ∧
           ∀f.
             f ∈ (𝕌(:num) -> subsets a) ∧ (f 0 = ∅) ∧
             (∀n. f n ⊆ f (SUC n)) ⇒
             BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a

   [SIGMA_ALGEBRA_BOREL]  Theorem

      |- sigma_algebra Borel

   [SIGMA_ALGEBRA_COUNTABLE_UNION]  Theorem

      |- ∀a c.
           sigma_algebra a ∧ countable c ∧ c ⊆ subsets a ⇒
           BIGUNION c ∈ subsets a

   [SIGMA_ALGEBRA_ENUM]  Theorem

      |- ∀a f.
           sigma_algebra a ∧ f ∈ (𝕌(:num) -> subsets a) ⇒
           BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a

   [SIGMA_ALGEBRA_FN]  Theorem

      |- ∀a.
           sigma_algebra a ⇔
           subset_class (space a) (subsets a) ∧ ∅ ∈ subsets a ∧
           (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ subsets a) ∧
           ∀f.
             f ∈ (𝕌(:num) -> subsets a) ⇒
             BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a

   [SIGMA_ALGEBRA_FN_BIGINTER]  Theorem

      |- ∀a.
           sigma_algebra a ⇒
           subset_class (space a) (subsets a) ∧ ∅ ∈ subsets a ∧
           (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ subsets a) ∧
           ∀f.
             f ∈ (𝕌(:num) -> subsets a) ⇒
             BIGINTER (IMAGE f 𝕌(:num)) ∈ subsets a

   [SIGMA_ALGEBRA_FN_DISJOINT]  Theorem

      |- ∀a.
           sigma_algebra a ⇔
           subset_class (space a) (subsets a) ∧ ∅ ∈ subsets a ∧
           (∀s. s ∈ subsets a ⇒ space a DIFF s ∈ subsets a) ∧
           (∀s t. s ∈ subsets a ∧ t ∈ subsets a ⇒ s ∪ t ∈ subsets a) ∧
           ∀f.
             f ∈ (𝕌(:num) -> subsets a) ∧
             (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
             BIGUNION (IMAGE f 𝕌(:num)) ∈ subsets a

   [SIGMA_ALGEBRA_SIGMA]  Theorem

      |- ∀sp sts. subset_class sp sts ⇒ sigma_algebra (sigma sp sts)

   [SIGMA_POW]  Theorem

      |- ∀s. sigma s (POW s) = (s,POW s)

   [SIGMA_PROPERTY]  Theorem

      |- ∀sp p a.
           subset_class sp p ∧ ∅ ∈ p ∧ a ⊆ p ∧
           (∀s. s ∈ p ∩ subsets (sigma sp a) ⇒ sp DIFF s ∈ p) ∧
           (∀c.
              countable c ∧ c ⊆ p ∩ subsets (sigma sp a) ⇒
              BIGUNION c ∈ p) ⇒
           subsets (sigma sp a) ⊆ p

   [SIGMA_PROPERTY_ALT]  Theorem

      |- ∀sp p a.
           subset_class sp p ∧ ∅ ∈ p ∧ a ⊆ p ∧
           (∀s. s ∈ p ∩ subsets (sigma sp a) ⇒ sp DIFF s ∈ p) ∧
           (∀f.
              f ∈ (𝕌(:num) -> p ∩ subsets (sigma sp a)) ⇒
              BIGUNION (IMAGE f 𝕌(:num)) ∈ p) ⇒
           subsets (sigma sp a) ⊆ p

   [SIGMA_PROPERTY_DISJOINT]  Theorem

      |- ∀sp p a.
           algebra (sp,a) ∧ a ⊆ p ∧
           (∀s. s ∈ p ∩ subsets (sigma sp a) ⇒ sp DIFF s ∈ p) ∧
           (∀f.
              f ∈ (𝕌(:num) -> p ∩ subsets (sigma sp a)) ∧ (f 0 = ∅) ∧
              (∀n. f n ⊆ f (SUC n)) ⇒
              BIGUNION (IMAGE f 𝕌(:num)) ∈ p) ∧
           (∀f.
              f ∈ (𝕌(:num) -> p ∩ subsets (sigma sp a)) ∧
              (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
              BIGUNION (IMAGE f 𝕌(:num)) ∈ p) ⇒
           subsets (sigma sp a) ⊆ p

   [SIGMA_PROPERTY_DISJOINT_LEMMA]  Theorem

      |- ∀sp a p.
           algebra (sp,a) ∧ a ⊆ p ∧ closed_cdi (sp,p) ⇒
           subsets (sigma sp a) ⊆ p

   [SIGMA_PROPERTY_DISJOINT_LEMMA1]  Theorem

      |- ∀a.
           algebra a ⇒
           ∀s t.
             s ∈ subsets a ∧ t ∈ subsets (smallest_closed_cdi a) ⇒
             s ∩ t ∈ subsets (smallest_closed_cdi a)

   [SIGMA_PROPERTY_DISJOINT_LEMMA2]  Theorem

      |- ∀a.
           algebra a ⇒
           ∀s t.
             s ∈ subsets (smallest_closed_cdi a) ∧
             t ∈ subsets (smallest_closed_cdi a) ⇒
             s ∩ t ∈ subsets (smallest_closed_cdi a)

   [SIGMA_PROPERTY_DISJOINT_WEAK]  Theorem

      |- ∀sp p a.
           algebra (sp,a) ∧ a ⊆ p ∧ subset_class sp p ∧
           (∀s. s ∈ p ⇒ sp DIFF s ∈ p) ∧
           (∀f.
              f ∈ (𝕌(:num) -> p) ∧ (f 0 = ∅) ∧ (∀n. f n ⊆ f (SUC n)) ⇒
              BIGUNION (IMAGE f 𝕌(:num)) ∈ p) ∧
           (∀f.
              f ∈ (𝕌(:num) -> p) ∧ (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
              BIGUNION (IMAGE f 𝕌(:num)) ∈ p) ⇒
           subsets (sigma sp a) ⊆ p

   [SIGMA_REDUCE]  Theorem

      |- ∀sp a. (sp,subsets (sigma sp a)) = sigma sp a

   [SIGMA_SUBSET]  Theorem

      |- ∀a b.
           sigma_algebra b ∧ a ⊆ subsets b ⇒
           subsets (sigma (space b) a) ⊆ subsets b

   [SIGMA_SUBSET_MEASURABLE_SETS]  Theorem

      |- ∀a m.
           measure_space m ∧ a ⊆ measurable_sets m ⇒
           subsets (sigma (m_space m) a) ⊆ measurable_sets m

   [SIGMA_SUBSET_SUBSETS]  Theorem

      |- ∀sp a. a ⊆ subsets (sigma sp a)

   [SMALLEST_CLOSED_CDI]  Theorem

      |- ∀a.
           algebra a ⇒
           subsets a ⊆ subsets (smallest_closed_cdi a) ∧
           closed_cdi (smallest_closed_cdi a) ∧
           subset_class (space a) (subsets (smallest_closed_cdi a))

   [SPACE]  Theorem

      |- ∀a. (space a,subsets a) = a

   [SPACE_BOREL]  Theorem

      |- space Borel = 𝕌(:extreal)

   [SPACE_SIGMA]  Theorem

      |- ∀sp a. space (sigma sp a) = sp

   [SPACE_SMALLEST_CLOSED_CDI]  Theorem

      |- ∀a. space (smallest_closed_cdi a) = space a

   [STRONG_MEASURE_SPACE_SUBSET]  Theorem

      |- ∀s s'.
           s' ⊆ m_space s ∧ measure_space s ∧ POW s' ⊆ measurable_sets s ⇒
           measure_space (s',POW s',measure s)

   [SUBADDITIVE]  Theorem

      |- ∀m s t u.
           subadditive m ∧ s ∈ measurable_sets m ∧ t ∈ measurable_sets m ∧
           (u = s ∪ t) ⇒
           measure m u ≤ measure m s + measure m t

   [SUBSET_BIGINTER]  Theorem

      |- ∀X P. X ⊆ BIGINTER P ⇔ ∀Y. Y ∈ P ⇒ X ⊆ Y

   [UNIV_SIGMA_ALGEBRA]  Theorem

      |- sigma_algebra (𝕌(:α),𝕌(:α -> bool))

   [finite_additivity_sufficient_for_finite_spaces]  Theorem

      |- ∀s m.
           sigma_algebra s ∧ FINITE (space s) ∧
           positive (space s,subsets s,m) ∧
           additive (space s,subsets s,m) ⇒
           measure_space (space s,subsets s,m)

   [finite_additivity_sufficient_for_finite_spaces2]  Theorem

      |- ∀m.
           sigma_algebra (m_space m,measurable_sets m) ∧
           FINITE (m_space m) ∧ positive m ∧ additive m ⇒
           measure_space m

   [indicator_fn_split]  Theorem

      |- ∀r s b.
           FINITE r ∧ (BIGUNION (IMAGE b r) = s) ∧
           (∀i j. i ∈ r ∧ j ∈ r ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ⇒
           ∀a.
             a ⊆ s ⇒
             (indicator_fn a =
              (λx. SIGMA (λi. indicator_fn (a ∩ b i) x) r))

   [indicator_fn_suminf]  Theorem

      |- ∀a x.
           (∀m n. m ≠ n ⇒ DISJOINT (a m) (a n)) ⇒
           (suminf (λi. indicator_fn (a i) x) =
            indicator_fn (BIGUNION (IMAGE a 𝕌(:num))) x)

   [measure_split]  Theorem

      |- ∀r b m.
           measure_space m ∧ FINITE r ∧
           (BIGUNION (IMAGE b r) = m_space m) ∧
           (∀i j. i ∈ r ∧ j ∈ r ∧ i ≠ j ⇒ DISJOINT (b i) (b j)) ∧
           (∀i. i ∈ r ⇒ b i ∈ measurable_sets m) ⇒
           ∀a.
             a ∈ measurable_sets m ⇒
             (measure m a = SIGMA (λi. measure m (a ∩ b i)) r)


*)
end
