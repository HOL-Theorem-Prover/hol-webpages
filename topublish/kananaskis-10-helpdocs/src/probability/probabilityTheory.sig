signature probabilityTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val conditional_distribution_def : thm
    val conditional_expectation_def : thm
    val conditional_prob_def : thm
    val distribution_def : thm
    val events_def : thm
    val expectation_def : thm
    val indep_def : thm
    val indep_rv_def : thm
    val joint_distribution3_def : thm
    val joint_distribution_def : thm
    val p_space_def : thm
    val possibly_def : thm
    val prob_def : thm
    val prob_space_def : thm
    val probably_def : thm
    val random_variable_def : thm
    val real_random_variable_def : thm
    val rv_conditional_expectation_def : thm
    val uniform_distribution_def : thm

  (*  Theorems  *)
    val ABS_1_MINUS_PROB : thm
    val ABS_PROB : thm
    val ADDITIVE_PROB : thm
    val COUNTABLY_ADDITIVE_PROB : thm
    val EVENTS : thm
    val EVENTS_ALGEBRA : thm
    val EVENTS_COMPL : thm
    val EVENTS_COUNTABLE_INTER : thm
    val EVENTS_COUNTABLE_UNION : thm
    val EVENTS_DIFF : thm
    val EVENTS_EMPTY : thm
    val EVENTS_INTER : thm
    val EVENTS_SIGMA_ALGEBRA : thm
    val EVENTS_SPACE : thm
    val EVENTS_UNION : thm
    val INCREASING_PROB : thm
    val INDEP_EMPTY : thm
    val INDEP_REFL : thm
    val INDEP_SPACE : thm
    val INDEP_SYM : thm
    val INTER_PSPACE : thm
    val POSITIVE_PROB : thm
    val PROB : thm
    val PROB_ADDITIVE : thm
    val PROB_COMPL : thm
    val PROB_COMPL_LE1 : thm
    val PROB_COUNTABLY_ADDITIVE : thm
    val PROB_COUNTABLY_SUBADDITIVE : thm
    val PROB_COUNTABLY_ZERO : thm
    val PROB_DISCRETE_EVENTS : thm
    val PROB_DISCRETE_EVENTS_COUNTABLE : thm
    val PROB_EMPTY : thm
    val PROB_EQUIPROBABLE_FINITE_UNIONS : thm
    val PROB_EQ_BIGUNION_IMAGE : thm
    val PROB_EQ_COMPL : thm
    val PROB_FINITELY_ADDITIVE : thm
    val PROB_INCREASING : thm
    val PROB_INCREASING_UNION : thm
    val PROB_INDEP : thm
    val PROB_LE_1 : thm
    val PROB_ONE_INTER : thm
    val PROB_POSITIVE : thm
    val PROB_REAL_SUM_IMAGE : thm
    val PROB_REAL_SUM_IMAGE_FN : thm
    val PROB_REAL_SUM_IMAGE_SPACE : thm
    val PROB_SPACE : thm
    val PROB_SPACE_ADDITIVE : thm
    val PROB_SPACE_COUNTABLY_ADDITIVE : thm
    val PROB_SPACE_INCREASING : thm
    val PROB_SPACE_POSITIVE : thm
    val PROB_SUBADDITIVE : thm
    val PROB_UNIV : thm
    val PROB_ZERO_UNION : thm
    val PSPACE : thm
    val conditional_distribution_le_1 : thm
    val conditional_distribution_pos : thm
    val distribution_lebesgue_thm1 : thm
    val distribution_lebesgue_thm2 : thm
    val distribution_partition : thm
    val distribution_pos : thm
    val distribution_prob_space : thm
    val distribution_x_eq_1_imp_distribution_y_eq_0 : thm
    val finite_expectation : thm
    val finite_expectation1 : thm
    val finite_expectation2 : thm
    val finite_marginal_product_space_POW : thm
    val finite_marginal_product_space_POW2 : thm
    val finite_marginal_product_space_POW3 : thm
    val finite_support_expectation : thm
    val joint_conditional : thm
    val joint_distribution_le : thm
    val joint_distribution_le2 : thm
    val joint_distribution_le_1 : thm
    val joint_distribution_pos : thm
    val joint_distribution_sum_mul1 : thm
    val joint_distribution_sums_1 : thm
    val joint_distribution_sym : thm
    val marginal_distribution1 : thm
    val marginal_distribution2 : thm
    val marginal_joint_zero : thm
    val marginal_joint_zero3 : thm
    val prob_x_eq_1_imp_prob_y_eq_0 : thm
    val uniform_distribution_prob_space : thm

  val probability_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [lebesgue] Parent theory of "probability"

   [conditional_distribution_def]  Definition

      |- ∀p X Y a b.
           conditional_distribution p X Y a b =
           joint_distribution p X Y (a × b) / distribution p Y b

   [conditional_expectation_def]  Definition

      |- ∀p X s.
           conditional_expectation p X s =
           @f.
             real_random_variable f p ∧
             ∀g.
               g ∈ s ⇒
               (integral p (λx. f x * indicator_fn g x) =
                integral p (λx. X x * indicator_fn g x))

   [conditional_prob_def]  Definition

      |- ∀p e1 e2.
           conditional_prob p e1 e2 =
           conditional_expectation p (indicator_fn e1) e2

   [distribution_def]  Definition

      |- ∀p X. distribution p X = (λs. prob p (PREIMAGE X s ∩ p_space p))

   [events_def]  Definition

      |- events = measurable_sets

   [expectation_def]  Definition

      |- expectation = integral

   [indep_def]  Definition

      |- ∀p a b.
           indep p a b ⇔
           a ∈ events p ∧ b ∈ events p ∧
           (prob p (a ∩ b) = prob p a * prob p b)

   [indep_rv_def]  Definition

      |- ∀p X Y s t.
           indep_rv p X Y s t ⇔
           ∀A B.
             A ∈ subsets s ∧ B ∈ subsets t ⇒
             indep p (PREIMAGE X A) (PREIMAGE Y B)

   [joint_distribution3_def]  Definition

      |- ∀p X Y Z.
           joint_distribution3 p X Y Z =
           (λa. prob p (PREIMAGE (λx. (X x,Y x,Z x)) a ∩ p_space p))

   [joint_distribution_def]  Definition

      |- ∀p X Y.
           joint_distribution p X Y =
           (λa. prob p (PREIMAGE (λx. (X x,Y x)) a ∩ p_space p))

   [p_space_def]  Definition

      |- p_space = m_space

   [possibly_def]  Definition

      |- ∀p e. possibly p e ⇔ e ∈ events p ∧ prob p e ≠ 0

   [prob_def]  Definition

      |- prob = measure

   [prob_space_def]  Definition

      |- ∀p. prob_space p ⇔ measure_space p ∧ (measure p (p_space p) = 1)

   [probably_def]  Definition

      |- ∀p e. probably p e ⇔ e ∈ events p ∧ (prob p e = 1)

   [random_variable_def]  Definition

      |- ∀X p s.
           random_variable X p s ⇔
           prob_space p ∧ X ∈ measurable (p_space p,events p) s

   [real_random_variable_def]  Definition

      |- ∀X p.
           real_random_variable X p ⇔
           prob_space p ∧
           (∀x. x ∈ p_space p ⇒ X x ≠ NegInf ∧ X x ≠ PosInf) ∧
           X ∈ measurable (p_space p,events p) Borel

   [rv_conditional_expectation_def]  Definition

      |- ∀p s X Y.
           rv_conditional_expectation p s X Y =
           conditional_expectation p X
             (IMAGE (λa. PREIMAGE Y a ∩ p_space p) (subsets s))

   [uniform_distribution_def]  Definition

      |- ∀p X s.
           uniform_distribution p X s = (λa. &CARD a / &CARD (space s))

   [ABS_1_MINUS_PROB]  Theorem

      |- ∀p s.
           prob_space p ∧ s ∈ events p ∧ prob p s ≠ 0 ⇒
           abs (1 − prob p s) < 1

   [ABS_PROB]  Theorem

      |- ∀p s. prob_space p ∧ s ∈ events p ⇒ (abs (prob p s) = prob p s)

   [ADDITIVE_PROB]  Theorem

      |- ∀p.
           additive p ⇔
           ∀s t.
             s ∈ events p ∧ t ∈ events p ∧ DISJOINT s t ⇒
             (prob p (s ∪ t) = prob p s + prob p t)

   [COUNTABLY_ADDITIVE_PROB]  Theorem

      |- ∀p.
           countably_additive p ⇔
           ∀f.
             f ∈ (𝕌(:num) -> events p) ∧
             (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
             BIGUNION (IMAGE f 𝕌(:num)) ∈ events p ⇒
             prob p o f sums prob p (BIGUNION (IMAGE f 𝕌(:num)))

   [EVENTS]  Theorem

      |- ∀a b c. events (a,b,c) = b

   [EVENTS_ALGEBRA]  Theorem

      |- ∀p. prob_space p ⇒ algebra (p_space p,events p)

   [EVENTS_COMPL]  Theorem

      |- ∀p s. prob_space p ∧ s ∈ events p ⇒ p_space p DIFF s ∈ events p

   [EVENTS_COUNTABLE_INTER]  Theorem

      |- ∀p c.
           prob_space p ∧ c ⊆ events p ∧ countable c ∧ c ≠ ∅ ⇒
           BIGINTER c ∈ events p

   [EVENTS_COUNTABLE_UNION]  Theorem

      |- ∀p c.
           prob_space p ∧ c ⊆ events p ∧ countable c ⇒
           BIGUNION c ∈ events p

   [EVENTS_DIFF]  Theorem

      |- ∀p s t.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ⇒ s DIFF t ∈ events p

   [EVENTS_EMPTY]  Theorem

      |- ∀p. prob_space p ⇒ ∅ ∈ events p

   [EVENTS_INTER]  Theorem

      |- ∀p s t.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ⇒ s ∩ t ∈ events p

   [EVENTS_SIGMA_ALGEBRA]  Theorem

      |- ∀p. prob_space p ⇒ sigma_algebra (p_space p,events p)

   [EVENTS_SPACE]  Theorem

      |- ∀p. prob_space p ⇒ p_space p ∈ events p

   [EVENTS_UNION]  Theorem

      |- ∀p s t.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ⇒ s ∪ t ∈ events p

   [INCREASING_PROB]  Theorem

      |- ∀p.
           increasing p ⇔
           ∀s t. s ∈ events p ∧ t ∈ events p ∧ s ⊆ t ⇒ prob p s ≤ prob p t

   [INDEP_EMPTY]  Theorem

      |- ∀p s. prob_space p ∧ s ∈ events p ⇒ indep p ∅ s

   [INDEP_REFL]  Theorem

      |- ∀p a.
           prob_space p ∧ a ∈ events p ⇒
           (indep p a a ⇔ (prob p a = 0) ∨ (prob p a = 1))

   [INDEP_SPACE]  Theorem

      |- ∀p s. prob_space p ∧ s ∈ events p ⇒ indep p (p_space p) s

   [INDEP_SYM]  Theorem

      |- ∀p a b. prob_space p ∧ indep p a b ⇒ indep p b a

   [INTER_PSPACE]  Theorem

      |- ∀p s. prob_space p ∧ s ∈ events p ⇒ (p_space p ∩ s = s)

   [POSITIVE_PROB]  Theorem

      |- ∀p. positive p ⇔ (prob p ∅ = 0) ∧ ∀s. s ∈ events p ⇒ 0 ≤ prob p s

   [PROB]  Theorem

      |- ∀a b c. prob (a,b,c) = c

   [PROB_ADDITIVE]  Theorem

      |- ∀p s t u.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ DISJOINT s t ∧
           (u = s ∪ t) ⇒
           (prob p u = prob p s + prob p t)

   [PROB_COMPL]  Theorem

      |- ∀p s.
           prob_space p ∧ s ∈ events p ⇒
           (prob p (p_space p DIFF s) = 1 − prob p s)

   [PROB_COMPL_LE1]  Theorem

      |- ∀p s r.
           prob_space p ∧ s ∈ events p ⇒
           (prob p (p_space p DIFF s) ≤ r ⇔ 1 − r ≤ prob p s)

   [PROB_COUNTABLY_ADDITIVE]  Theorem

      |- ∀p s f.
           prob_space p ∧ f ∈ (𝕌(:num) -> events p) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
           (s = BIGUNION (IMAGE f 𝕌(:num))) ⇒
           prob p o f sums prob p s

   [PROB_COUNTABLY_SUBADDITIVE]  Theorem

      |- ∀p f.
           prob_space p ∧ IMAGE f 𝕌(:num) ⊆ events p ∧
           summable (prob p o f) ⇒
           prob p (BIGUNION (IMAGE f 𝕌(:num))) ≤ suminf (prob p o f)

   [PROB_COUNTABLY_ZERO]  Theorem

      |- ∀p c.
           prob_space p ∧ countable c ∧ c ⊆ events p ∧
           (∀x. x ∈ c ⇒ (prob p x = 0)) ⇒
           (prob p (BIGUNION c) = 0)

   [PROB_DISCRETE_EVENTS]  Theorem

      |- ∀p.
           prob_space p ∧ FINITE (p_space p) ∧
           (∀x. x ∈ p_space p ⇒ {x} ∈ events p) ⇒
           ∀s. s ⊆ p_space p ⇒ s ∈ events p

   [PROB_DISCRETE_EVENTS_COUNTABLE]  Theorem

      |- ∀p.
           prob_space p ∧ countable (p_space p) ∧
           (∀x. x ∈ p_space p ⇒ {x} ∈ events p) ⇒
           ∀s. s ⊆ p_space p ⇒ s ∈ events p

   [PROB_EMPTY]  Theorem

      |- ∀p. prob_space p ⇒ (prob p ∅ = 0)

   [PROB_EQUIPROBABLE_FINITE_UNIONS]  Theorem

      |- ∀p s.
           prob_space p ∧ s ∈ events p ∧ (∀x. x ∈ s ⇒ {x} ∈ events p) ∧
           FINITE s ∧ (∀x y. x ∈ s ∧ y ∈ s ⇒ (prob p {x} = prob p {y})) ⇒
           (prob p s = &CARD s * prob p {CHOICE s})

   [PROB_EQ_BIGUNION_IMAGE]  Theorem

      |- ∀p.
           prob_space p ∧ f ∈ (𝕌(:num) -> events p) ∧
           g ∈ (𝕌(:num) -> events p) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (g m) (g n)) ∧
           (∀n. prob p (f n) = prob p (g n)) ⇒
           (prob p (BIGUNION (IMAGE f 𝕌(:num))) =
            prob p (BIGUNION (IMAGE g 𝕌(:num))))

   [PROB_EQ_COMPL]  Theorem

      |- ∀p s t.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧
           (prob p (p_space p DIFF s) = prob p (p_space p DIFF t)) ⇒
           (prob p s = prob p t)

   [PROB_FINITELY_ADDITIVE]  Theorem

      |- ∀p s f n.
           prob_space p ∧ f ∈ (count n -> events p) ∧
           (∀a b. a < n ∧ b < n ∧ a ≠ b ⇒ DISJOINT (f a) (f b)) ∧
           (s = BIGUNION (IMAGE f (count n))) ⇒
           (sum (0,n) (prob p o f) = prob p s)

   [PROB_INCREASING]  Theorem

      |- ∀p s t.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ s ⊆ t ⇒
           prob p s ≤ prob p t

   [PROB_INCREASING_UNION]  Theorem

      |- ∀p s f.
           prob_space p ∧ f ∈ (𝕌(:num) -> events p) ∧
           (∀n. f n ⊆ f (SUC n)) ∧ (s = BIGUNION (IMAGE f 𝕌(:num))) ⇒
           prob p o f --> prob p s

   [PROB_INDEP]  Theorem

      |- ∀p s t u.
           indep p s t ∧ (u = s ∩ t) ⇒ (prob p u = prob p s * prob p t)

   [PROB_LE_1]  Theorem

      |- ∀p s. prob_space p ∧ s ∈ events p ⇒ prob p s ≤ 1

   [PROB_ONE_INTER]  Theorem

      |- ∀p s t.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ (prob p t = 1) ⇒
           (prob p (s ∩ t) = prob p s)

   [PROB_POSITIVE]  Theorem

      |- ∀p s. prob_space p ∧ s ∈ events p ⇒ 0 ≤ prob p s

   [PROB_REAL_SUM_IMAGE]  Theorem

      |- ∀p s.
           prob_space p ∧ s ∈ events p ∧ (∀x. x ∈ s ⇒ {x} ∈ events p) ∧
           FINITE s ⇒
           (prob p s = SIGMA (λx. prob p {x}) s)

   [PROB_REAL_SUM_IMAGE_FN]  Theorem

      |- ∀p f e s.
           prob_space p ∧ e ∈ events p ∧ (∀x. x ∈ s ⇒ e ∩ f x ∈ events p) ∧
           FINITE s ∧
           (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (f x) (f y)) ∧
           (BIGUNION (IMAGE f s) ∩ p_space p = p_space p) ⇒
           (prob p e = SIGMA (λx. prob p (e ∩ f x)) s)

   [PROB_REAL_SUM_IMAGE_SPACE]  Theorem

      |- ∀p.
           prob_space p ∧ (∀x. x ∈ p_space p ⇒ {x} ∈ events p) ∧
           FINITE (p_space p) ⇒
           (SIGMA (λx. prob p {x}) (p_space p) = 1)

   [PROB_SPACE]  Theorem

      |- ∀p.
           prob_space p ⇔
           sigma_algebra (p_space p,events p) ∧ positive p ∧
           countably_additive p ∧ (prob p (p_space p) = 1)

   [PROB_SPACE_ADDITIVE]  Theorem

      |- ∀p. prob_space p ⇒ additive p

   [PROB_SPACE_COUNTABLY_ADDITIVE]  Theorem

      |- ∀p. prob_space p ⇒ countably_additive p

   [PROB_SPACE_INCREASING]  Theorem

      |- ∀p. prob_space p ⇒ increasing p

   [PROB_SPACE_POSITIVE]  Theorem

      |- ∀p. prob_space p ⇒ positive p

   [PROB_SUBADDITIVE]  Theorem

      |- ∀p s t u.
           prob_space p ∧ t ∈ events p ∧ u ∈ events p ∧ (s = t ∪ u) ⇒
           prob p s ≤ prob p t + prob p u

   [PROB_UNIV]  Theorem

      |- ∀p. prob_space p ⇒ (prob p (p_space p) = 1)

   [PROB_ZERO_UNION]  Theorem

      |- ∀p s t.
           prob_space p ∧ s ∈ events p ∧ t ∈ events p ∧ (prob p t = 0) ⇒
           (prob p (s ∪ t) = prob p s)

   [PSPACE]  Theorem

      |- ∀a b c. p_space (a,b,c) = a

   [conditional_distribution_le_1]  Theorem

      |- ∀p X Y a b.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           conditional_distribution p X Y a b ≤ 1

   [conditional_distribution_pos]  Theorem

      |- ∀p X Y a b.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           0 ≤ conditional_distribution p X Y a b

   [distribution_lebesgue_thm1]  Theorem

      |- ∀X p s A.
           random_variable X p s ∧ A ∈ subsets s ⇒
           (Normal (distribution p X A) =
            integral p (indicator_fn (PREIMAGE X A ∩ p_space p)))

   [distribution_lebesgue_thm2]  Theorem

      |- ∀X p s A.
           random_variable X p s ∧ A ∈ subsets s ⇒
           (Normal (distribution p X A) =
            integral (space s,subsets s,distribution p X) (indicator_fn A))

   [distribution_partition]  Theorem

      |- ∀p X.
           prob_space p ∧ (∀x. x ∈ p_space p ⇒ {x} ∈ events p) ∧
           FINITE (p_space p) ∧ random_variable X p Borel ⇒
           (SIGMA (λx. distribution p X {x}) (IMAGE X (p_space p)) = 1)

   [distribution_pos]  Theorem

      |- ∀p X a.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           0 ≤ distribution p X a

   [distribution_prob_space]  Theorem

      |- ∀p X s.
           random_variable X p s ⇒
           prob_space (space s,subsets s,distribution p X)

   [distribution_x_eq_1_imp_distribution_y_eq_0]  Theorem

      |- ∀X p x.
           random_variable X p
             (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
           (distribution p X {x} = 1) ⇒
           ∀y. y ≠ x ⇒ (distribution p X {y} = 0)

   [finite_expectation]  Theorem

      |- ∀p X.
           FINITE (p_space p) ∧ real_random_variable X p ⇒
           (expectation p X =
            SIGMA (λr. r * Normal (distribution p X {r}))
              (IMAGE X (p_space p)))

   [finite_expectation1]  Theorem

      |- ∀p X.
           FINITE (p_space p) ∧ real_random_variable X p ⇒
           (expectation p X =
            SIGMA (λr. r * Normal (prob p (PREIMAGE X {r} ∩ p_space p)))
              (IMAGE X (p_space p)))

   [finite_expectation2]  Theorem

      |- ∀p X.
           FINITE (IMAGE X (p_space p)) ∧ real_random_variable X p ⇒
           (expectation p X =
            SIGMA (λr. r * Normal (prob p (PREIMAGE X {r} ∩ p_space p)))
              (IMAGE X (p_space p)))

   [finite_marginal_product_space_POW]  Theorem

      |- ∀p X Y.
           (POW (p_space p) = events p) ∧
           random_variable X p
             (IMAGE X (p_space p),POW (IMAGE X (p_space p))) ∧
           random_variable Y p
             (IMAGE Y (p_space p),POW (IMAGE Y (p_space p))) ∧
           FINITE (p_space p) ⇒
           measure_space
             (IMAGE X (p_space p) × IMAGE Y (p_space p),
              POW (IMAGE X (p_space p) × IMAGE Y (p_space p)),
              (λa. prob p (PREIMAGE (λx. (X x,Y x)) a ∩ p_space p)))

   [finite_marginal_product_space_POW2]  Theorem

      |- ∀p s1 s2 X Y.
           (POW (p_space p) = events p) ∧ random_variable X p (s1,POW s1) ∧
           random_variable Y p (s2,POW s2) ∧ FINITE (p_space p) ∧
           FINITE s1 ∧ FINITE s2 ⇒
           measure_space (s1 × s2,POW (s1 × s2),joint_distribution p X Y)

   [finite_marginal_product_space_POW3]  Theorem

      |- ∀p s1 s2 s3 X Y Z.
           (POW (p_space p) = events p) ∧ random_variable X p (s1,POW s1) ∧
           random_variable Y p (s2,POW s2) ∧
           random_variable Z p (s3,POW s3) ∧ FINITE (p_space p) ∧
           FINITE s1 ∧ FINITE s2 ∧ FINITE s3 ⇒
           measure_space
             (s1 × (s2 × s3),POW (s1 × (s2 × s3)),
              joint_distribution3 p X Y Z)

   [finite_support_expectation]  Theorem

      |- ∀p X.
           FINITE (IMAGE X (p_space p)) ∧ real_random_variable X p ⇒
           (expectation p X =
            SIGMA (λr. r * Normal (distribution p X {r}))
              (IMAGE X (p_space p)))

   [joint_conditional]  Theorem

      |- ∀p X Y a b.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           (joint_distribution p X Y (a × b) =
            conditional_distribution p Y X b a * distribution p X a)

   [joint_distribution_le]  Theorem

      |- ∀p X Y a b.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           joint_distribution p X Y (a × b) ≤ distribution p X a

   [joint_distribution_le2]  Theorem

      |- ∀p X Y a b.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           joint_distribution p X Y (a × b) ≤ distribution p Y b

   [joint_distribution_le_1]  Theorem

      |- ∀p X Y a.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           joint_distribution p X Y a ≤ 1

   [joint_distribution_pos]  Theorem

      |- ∀p X Y a.
           prob_space p ∧ (events p = POW (p_space p)) ⇒
           0 ≤ joint_distribution p X Y a

   [joint_distribution_sum_mul1]  Theorem

      |- ∀p X Y f.
           prob_space p ∧ FINITE (p_space p) ∧
           (events p = POW (p_space p)) ⇒
           (SIGMA (λ(x,y). joint_distribution p X Y {(x,y)} * f x)
              (IMAGE X (p_space p) × IMAGE Y (p_space p)) =
            SIGMA (λx. distribution p X {x} * f x) (IMAGE X (p_space p)))

   [joint_distribution_sums_1]  Theorem

      |- ∀p X Y.
           prob_space p ∧ FINITE (p_space p) ∧
           (events p = POW (p_space p)) ⇒
           (SIGMA (λ(x,y). joint_distribution p X Y {(x,y)})
              (IMAGE X (p_space p) × IMAGE Y (p_space p)) =
            1)

   [joint_distribution_sym]  Theorem

      |- ∀p X Y a b.
           prob_space p ⇒
           (joint_distribution p X Y (a × b) =
            joint_distribution p Y X (b × a))

   [marginal_distribution1]  Theorem

      |- ∀p X Y a.
           prob_space p ∧ FINITE (p_space p) ∧
           (events p = POW (p_space p)) ⇒
           (distribution p X a =
            SIGMA (λx. joint_distribution p X Y (a × {x}))
              (IMAGE Y (p_space p)))

   [marginal_distribution2]  Theorem

      |- ∀p X Y b.
           prob_space p ∧ FINITE (p_space p) ∧
           (events p = POW (p_space p)) ⇒
           (distribution p Y b =
            SIGMA (λx. joint_distribution p X Y ({x} × b))
              (IMAGE X (p_space p)))

   [marginal_joint_zero]  Theorem

      |- ∀p X Y s t.
           prob_space p ∧ (events p = POW (p_space p)) ∧
           ((distribution p X s = 0) ∨ (distribution p Y t = 0)) ⇒
           (joint_distribution p X Y (s × t) = 0)

   [marginal_joint_zero3]  Theorem

      |- ∀p X Y Z s t u.
           prob_space p ∧ (events p = POW (p_space p)) ∧
           ((distribution p X s = 0) ∨ (distribution p Y t = 0) ∨
            (distribution p Z u = 0)) ⇒
           (joint_distribution3 p X Y Z (s × (t × u)) = 0)

   [prob_x_eq_1_imp_prob_y_eq_0]  Theorem

      |- ∀p x.
           prob_space p ∧ {x} ∈ events p ∧ (prob p {x} = 1) ⇒
           ∀y. {y} ∈ events p ∧ y ≠ x ⇒ (prob p {y} = 0)

   [uniform_distribution_prob_space]  Theorem

      |- ∀X p s.
           FINITE (p_space p) ∧ FINITE (space s) ∧ random_variable X p s ⇒
           prob_space (space s,subsets s,uniform_distribution p X s)


*)
end
