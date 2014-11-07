signature lebesgueTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val RADON_F_def : thm
    val RADON_F_integrals_def : thm
    val finite_space_integral_def : thm
    val fn_seq_def : thm
    val fn_seq_integral_def : thm
    val integrable_def : thm
    val integral_def : thm
    val max_fn_seq_def : thm
    val measure_absolutely_continuous_def : thm
    val negative_set_def : thm
    val pos_fn_integral_def : thm
    val pos_simple_fn_integral_def : thm
    val prod_measure3_def : thm
    val prod_measure_def : thm
    val prod_measure_space3_def : thm
    val prod_measure_space_def : thm
    val prod_sets3_def : thm
    val psfis_def : thm
    val psfs_def : thm
    val seq_sup_def : thm
    val signed_measure_space_def : thm

  (*  Theorems  *)
    val EXTREAL_SUP_FUN_SEQ_IMAGE : thm
    val EXTREAL_SUP_FUN_SEQ_MONO_IMAGE : thm
    val EXTREAL_SUP_SEQ : thm
    val IN_psfis : thm
    val IN_psfis_eq : thm
    val RN_lemma1 : thm
    val RN_lemma2 : thm
    val Radon_Nikodym : thm
    val Radon_Nikodym2 : thm
    val finite_POW_prod_measure_reduce : thm
    val finite_POW_prod_measure_reduce3 : thm
    val finite_prod_measure_space_POW : thm
    val finite_prod_measure_space_POW3 : thm
    val finite_space_POW_integral_reduce : thm
    val finite_space_integral_reduce : thm
    val finite_support_integral_reduce : thm
    val integrable_add : thm
    val integrable_add_lemma : thm
    val integrable_add_pos : thm
    val integrable_bounded : thm
    val integrable_cmul : thm
    val integrable_const : thm
    val integrable_fn_minus : thm
    val integrable_fn_plus : thm
    val integrable_indicator : thm
    val integrable_infty : thm
    val integrable_infty_null : thm
    val integrable_not_infty : thm
    val integrable_not_infty_alt : thm
    val integrable_not_infty_alt2 : thm
    val integrable_not_infty_alt3 : thm
    val integrable_plus_minus : thm
    val integrable_pos : thm
    val integrable_sub : thm
    val integrable_zero : thm
    val integral_add : thm
    val integral_add_lemma : thm
    val integral_cmul : thm
    val integral_cmul_indicator : thm
    val integral_indicator : thm
    val integral_mono : thm
    val integral_mspace : thm
    val integral_pos_fn : thm
    val integral_sequence : thm
    val integral_zero : thm
    val lebesgue_monotone_convergence : thm
    val lebesgue_monotone_convergence_lemma : thm
    val lebesgue_monotone_convergence_subset : thm
    val lemma_fn_1 : thm
    val lemma_fn_2 : thm
    val lemma_fn_3 : thm
    val lemma_fn_4 : thm
    val lemma_fn_5 : thm
    val lemma_fn_in_psfis : thm
    val lemma_fn_mono_increasing : thm
    val lemma_fn_sup : thm
    val lemma_fn_upper_bounded : thm
    val lemma_radon_max_in_F : thm
    val lemma_radon_seq_conv_sup : thm
    val max_fn_seq_def_compute : thm
    val max_fn_seq_mono : thm
    val measurable_sequence : thm
    val measure_space_finite_prod_measure_POW1 : thm
    val measure_space_finite_prod_measure_POW2 : thm
    val measure_space_finite_prod_measure_POW3 : thm
    val pos_fn_integral_add : thm
    val pos_fn_integral_cmul : thm
    val pos_fn_integral_cmul_indicator : thm
    val pos_fn_integral_cmul_infty : thm
    val pos_fn_integral_disjoint_sets : thm
    val pos_fn_integral_disjoint_sets_sum : thm
    val pos_fn_integral_indicator : thm
    val pos_fn_integral_mono : thm
    val pos_fn_integral_mono_mspace : thm
    val pos_fn_integral_mspace : thm
    val pos_fn_integral_pos : thm
    val pos_fn_integral_pos_simple_fn : thm
    val pos_fn_integral_split : thm
    val pos_fn_integral_sum : thm
    val pos_fn_integral_sum_cmul_indicator : thm
    val pos_fn_integral_suminf : thm
    val pos_fn_integral_zero : thm
    val pos_simple_fn_add : thm
    val pos_simple_fn_add_alt : thm
    val pos_simple_fn_cmul : thm
    val pos_simple_fn_cmul_alt : thm
    val pos_simple_fn_indicator : thm
    val pos_simple_fn_indicator_alt : thm
    val pos_simple_fn_integral_add : thm
    val pos_simple_fn_integral_add_alt : thm
    val pos_simple_fn_integral_cmul : thm
    val pos_simple_fn_integral_cmul_alt : thm
    val pos_simple_fn_integral_indicator : thm
    val pos_simple_fn_integral_mono : thm
    val pos_simple_fn_integral_not_infty : thm
    val pos_simple_fn_integral_present : thm
    val pos_simple_fn_integral_sub : thm
    val pos_simple_fn_integral_sum : thm
    val pos_simple_fn_integral_sum_alt : thm
    val pos_simple_fn_integral_unique : thm
    val pos_simple_fn_integral_zero : thm
    val pos_simple_fn_integral_zero_alt : thm
    val pos_simple_fn_le : thm
    val pos_simple_fn_max : thm
    val pos_simple_fn_not_infty : thm
    val pos_simple_fn_thm1 : thm
    val psfis_add : thm
    val psfis_cmul : thm
    val psfis_indicator : thm
    val psfis_intro : thm
    val psfis_mono : thm
    val psfis_not_infty : thm
    val psfis_pos : thm
    val psfis_present : thm
    val psfis_sub : thm
    val psfis_sum : thm
    val psfis_unique : thm
    val psfis_zero : thm
    val seq_sup_def_compute : thm

  val lebesgue_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [measure] Parent theory of "lebesgue"

   [RADON_F_def]  Definition

      |- ∀m v.
           RADON_F m v =
           {f |
            f ∈ measurable (m_space m,measurable_sets m) Borel ∧
            (∀x. 0 ≤ f x) ∧
            ∀A.
              A ∈ measurable_sets m ⇒
              pos_fn_integral m (λx. f x * indicator_fn A x) ≤
              Normal (measure v A)}

   [RADON_F_integrals_def]  Definition

      |- ∀m v.
           RADON_F_integrals m v =
           {r | ∃f. (r = pos_fn_integral m f) ∧ f ∈ RADON_F m v}

   [finite_space_integral_def]  Definition

      |- ∀m f.
           finite_space_integral m f =
           SIGMA (λr. r * Normal (measure m (PREIMAGE f {r} ∩ m_space m)))
             (IMAGE f (m_space m))

   [fn_seq_def]  Definition

      |- ∀m f.
           fn_seq m f =
           (λn x.
              SIGMA
                (λk.
                   &k / 2 pow n *
                   indicator_fn
                     {x |
                      x ∈ m_space m ∧ &k / 2 pow n ≤ f x ∧
                      f x < (&k + 1) / 2 pow n} x) (count (4 ** n)) +
              2 pow n * indicator_fn {x | x ∈ m_space m ∧ 2 pow n ≤ f x} x)

   [fn_seq_integral_def]  Definition

      |- ∀m f.
           fn_seq_integral m f =
           (λn.
              Normal
                (SIGMA
                   (λk.
                      &k / 2 pow n *
                      measure m
                        {x |
                         x ∈ m_space m ∧ &k / 2 pow n ≤ f x ∧
                         f x < (&k + 1) / 2 pow n}) (count (4 ** n)) +
                 2 pow n * measure m {x | x ∈ m_space m ∧ 2 pow n ≤ f x}))

   [integrable_def]  Definition

      |- ∀m f.
           integrable m f ⇔
           f ∈ measurable (m_space m,measurable_sets m) Borel ∧
           pos_fn_integral m (fn_plus f) ≠ PosInf ∧
           pos_fn_integral m (fn_minus f) ≠ PosInf

   [integral_def]  Definition

      |- ∀m f.
           integral m f =
           pos_fn_integral m (fn_plus f) − pos_fn_integral m (fn_minus f)

   [max_fn_seq_def]  Definition

      |- (∀g x. max_fn_seq g 0 x = g 0 x) ∧
         ∀g n x.
           max_fn_seq g (SUC n) x = max (max_fn_seq g n x) (g (SUC n) x)

   [measure_absolutely_continuous_def]  Definition

      |- ∀m v.
           measure_absolutely_continuous m v ⇔
           ∀A.
             A ∈ measurable_sets m ∧ (measure v A = 0) ⇒ (measure m A = 0)

   [negative_set_def]  Definition

      |- ∀m A.
           negative_set m A ⇔
           A ∈ measurable_sets m ∧
           ∀s. s ∈ measurable_sets m ∧ s ⊆ A ⇒ measure m s ≤ 0

   [pos_fn_integral_def]  Definition

      |- ∀m f.
           pos_fn_integral m f =
           sup {r | ∃g. r ∈ psfis m g ∧ ∀x. g x ≤ f x}

   [pos_simple_fn_integral_def]  Definition

      |- ∀m s a x.
           pos_simple_fn_integral m s a x =
           Normal (SIGMA (λi. x i * measure m (a i)) s)

   [prod_measure3_def]  Definition

      |- ∀m0 m1 m2.
           prod_measure3 m0 m1 m2 =
           prod_measure m0 (prod_measure_space m1 m2)

   [prod_measure_def]  Definition

      |- ∀m0 m1.
           prod_measure m0 m1 =
           (λa.
              real
                (integral m0
                   (λs0. Normal (measure m1 (PREIMAGE (λs1. (s0,s1)) a)))))

   [prod_measure_space3_def]  Definition

      |- ∀m0 m1 m2.
           prod_measure_space3 m0 m1 m2 =
           (m_space m0 × (m_space m1 × m_space m2),
            subsets
              (sigma (m_space m0 × (m_space m1 × m_space m2))
                 (prod_sets3 (measurable_sets m0) (measurable_sets m1)
                    (measurable_sets m2))),prod_measure3 m0 m1 m2)

   [prod_measure_space_def]  Definition

      |- ∀m0 m1.
           prod_measure_space m0 m1 =
           (m_space m0 × m_space m1,
            subsets
              (sigma (m_space m0 × m_space m1)
                 (prod_sets (measurable_sets m0) (measurable_sets m1))),
            prod_measure m0 m1)

   [prod_sets3_def]  Definition

      |- ∀a b c. prod_sets3 a b c = {s × (t × u) | s ∈ a ∧ t ∈ b ∧ u ∈ c}

   [psfis_def]  Definition

      |- ∀m f.
           psfis m f =
           IMAGE (λ(s,a,x). pos_simple_fn_integral m s a x) (psfs m f)

   [psfs_def]  Definition

      |- ∀m f. psfs m f = {(s,a,x) | pos_simple_fn m f s a x}

   [seq_sup_def]  Definition

      |- (∀P. seq_sup P 0 = @r. r ∈ P ∧ sup P < r + 1) ∧
         ∀P n.
           seq_sup P (SUC n) =
           @r.
             r ∈ P ∧ sup P < r + Normal ((1 / 2) pow SUC n) ∧
             seq_sup P n < r ∧ r < sup P

   [signed_measure_space_def]  Definition

      |- ∀m.
           signed_measure_space m ⇔
           sigma_algebra (m_space m,measurable_sets m) ∧
           countably_additive m

   [EXTREAL_SUP_FUN_SEQ_IMAGE]  Theorem

      |- ∀P P' f.
           (∃x. P x) ∧ (∃z. z ≠ PosInf ∧ ∀x. P x ⇒ x ≤ z) ∧
           (P = IMAGE f P') ⇒
           ∃g. (∀n. g n ∈ P') ∧ (sup (IMAGE (λn. f (g n)) 𝕌(:num)) = sup P)

   [EXTREAL_SUP_FUN_SEQ_MONO_IMAGE]  Theorem

      |- ∀P P'.
           (∃x. P x) ∧ (∃z. z ≠ PosInf ∧ ∀x. P x ⇒ x ≤ z) ∧
           (P = IMAGE f P') ∧
           (∀g1 g2. g1 ∈ P' ∧ g2 ∈ P' ∧ (∀x. g1 x ≤ g2 x) ⇒ f g1 ≤ f g2) ∧
           (∀g1 g2. g1 ∈ P' ∧ g2 ∈ P' ⇒ (λx. max (g1 x) (g2 x)) ∈ P') ⇒
           ∃g.
             (∀n. g n ∈ P') ∧ (∀x n. g n x ≤ g (SUC n) x) ∧
             (sup (IMAGE (λn. f (g n)) 𝕌(:num)) = sup P)

   [EXTREAL_SUP_SEQ]  Theorem

      |- ∀P.
           (∃x. P x) ∧ (∃z. z ≠ PosInf ∧ ∀x. P x ⇒ x ≤ z) ⇒
           ∃x.
             (∀n. x n ∈ P) ∧ (∀n. x n ≤ x (SUC n)) ∧
             (sup (IMAGE x 𝕌(:num)) = sup P)

   [IN_psfis]  Theorem

      |- ∀m r f.
           r ∈ psfis m f ⇒
           ∃s a x.
             pos_simple_fn m f s a x ∧ (r = pos_simple_fn_integral m s a x)

   [IN_psfis_eq]  Theorem

      |- ∀m r f.
           r ∈ psfis m f ⇔
           ∃s a x.
             pos_simple_fn m f s a x ∧ (r = pos_simple_fn_integral m s a x)

   [RN_lemma1]  Theorem

      |- ∀m v e.
           measure_space m ∧ measure_space v ∧ 0 < e ∧
           (m_space v = m_space m) ∧
           (measurable_sets v = measurable_sets m) ⇒
           ∃A.
             A ∈ measurable_sets m ∧
             measure m (m_space m) − measure v (m_space m) ≤
             measure m A − measure v A ∧
             ∀B.
               B ∈ measurable_sets m ∧ B ⊆ A ⇒
               -e < measure m B − measure v B

   [RN_lemma2]  Theorem

      |- ∀m v.
           measure_space m ∧ measure_space v ∧ (m_space v = m_space m) ∧
           (measurable_sets v = measurable_sets m) ⇒
           ∃A.
             A ∈ measurable_sets m ∧
             measure m (m_space m) − measure v (m_space m) ≤
             measure m A − measure v A ∧
             ∀B.
               B ∈ measurable_sets m ∧ B ⊆ A ⇒
               0 ≤ measure m B − measure v B

   [Radon_Nikodym]  Theorem

      |- ∀m v.
           measure_space m ∧ measure_space v ∧ (m_space v = m_space m) ∧
           (measurable_sets v = measurable_sets m) ∧
           measure_absolutely_continuous v m ⇒
           ∃f.
             f ∈ measurable (m_space m,measurable_sets m) Borel ∧
             (∀x. 0 ≤ f x) ∧
             ∀A.
               A ∈ measurable_sets m ⇒
               (pos_fn_integral m (λx. f x * indicator_fn A x) =
                Normal (measure v A))

   [Radon_Nikodym2]  Theorem

      |- ∀m v.
           measure_space m ∧ measure_space v ∧ (m_space v = m_space m) ∧
           (measurable_sets v = measurable_sets m) ∧
           measure_absolutely_continuous v m ⇒
           ∃f.
             f ∈ measurable (m_space m,measurable_sets m) Borel ∧
             (∀x. 0 ≤ f x) ∧ (∀x. f x ≠ PosInf) ∧
             ∀A.
               A ∈ measurable_sets m ⇒
               (pos_fn_integral m (λx. f x * indicator_fn A x) =
                Normal (measure v A))

   [finite_POW_prod_measure_reduce]  Theorem

      |- ∀m0 m1.
           measure_space m0 ∧ measure_space m1 ∧ FINITE (m_space m0) ∧
           FINITE (m_space m1) ∧ (POW (m_space m0) = measurable_sets m0) ∧
           (POW (m_space m1) = measurable_sets m1) ⇒
           ∀a0 a1.
             a0 ∈ measurable_sets m0 ∧ a1 ∈ measurable_sets m1 ⇒
             (prod_measure m0 m1 (a0 × a1) = measure m0 a0 * measure m1 a1)

   [finite_POW_prod_measure_reduce3]  Theorem

      |- ∀m0 m1 m2.
           measure_space m0 ∧ measure_space m1 ∧ measure_space m2 ∧
           FINITE (m_space m0) ∧ FINITE (m_space m1) ∧
           FINITE (m_space m2) ∧ (POW (m_space m0) = measurable_sets m0) ∧
           (POW (m_space m1) = measurable_sets m1) ∧
           (POW (m_space m2) = measurable_sets m2) ⇒
           ∀a0 a1 a2.
             a0 ∈ measurable_sets m0 ∧ a1 ∈ measurable_sets m1 ∧
             a2 ∈ measurable_sets m2 ⇒
             (prod_measure3 m0 m1 m2 (a0 × (a1 × a2)) =
              measure m0 a0 * measure m1 a1 * measure m2 a2)

   [finite_prod_measure_space_POW]  Theorem

      |- ∀s1 s2 u v.
           FINITE s1 ∧ FINITE s2 ⇒
           (prod_measure_space (s1,POW s1,u) (s2,POW s2,v) =
            (s1 × s2,POW (s1 × s2),
             prod_measure (s1,POW s1,u) (s2,POW s2,v)))

   [finite_prod_measure_space_POW3]  Theorem

      |- ∀s1 s2 s3 u v w.
           FINITE s1 ∧ FINITE s2 ∧ FINITE s3 ⇒
           (prod_measure_space3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w) =
            (s1 × (s2 × s3),POW (s1 × (s2 × s3)),
             prod_measure3 (s1,POW s1,u) (s2,POW s2,v) (s3,POW s3,w)))

   [finite_space_POW_integral_reduce]  Theorem

      |- ∀m f.
           measure_space m ∧ (POW (m_space m) = measurable_sets m) ∧
           FINITE (m_space m) ∧
           (∀x. x ∈ m_space m ⇒ f x ≠ NegInf ∧ f x ≠ PosInf) ⇒
           (integral m f =
            SIGMA (λx. f x * Normal (measure m {x})) (m_space m))

   [finite_space_integral_reduce]  Theorem

      |- ∀m f.
           measure_space m ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ∧
           (∀x. x ∈ m_space m ⇒ f x ≠ NegInf ∧ f x ≠ PosInf) ∧
           FINITE (m_space m) ⇒
           (integral m f = finite_space_integral m f)

   [finite_support_integral_reduce]  Theorem

      |- ∀m f.
           measure_space m ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ∧
           (∀x. x ∈ m_space m ⇒ f x ≠ NegInf ∧ f x ≠ PosInf) ∧
           FINITE (IMAGE f (m_space m)) ⇒
           (integral m f = finite_space_integral m f)

   [integrable_add]  Theorem

      |- ∀m f1 f2.
           measure_space m ∧ integrable m f1 ∧ integrable m f2 ⇒
           integrable m (λx. f1 x + f2 x)

   [integrable_add_lemma]  Theorem

      |- ∀m f g.
           measure_space m ∧ integrable m f ∧ integrable m g ⇒
           integrable m (λx. fn_plus f x + fn_plus g x) ∧
           integrable m (λx. fn_minus f x + fn_minus g x)

   [integrable_add_pos]  Theorem

      |- ∀m f g.
           measure_space m ∧ integrable m f ∧ integrable m g ∧
           (∀x. 0 ≤ f x) ∧ (∀x. 0 ≤ g x) ⇒
           integrable m (λx. f x + g x)

   [integrable_bounded]  Theorem

      |- ∀m f g.
           measure_space m ∧ integrable m f ∧
           g ∈ measurable (m_space m,measurable_sets m) Borel ∧
           (∀x. abs (g x) ≤ f x) ⇒
           integrable m g

   [integrable_cmul]  Theorem

      |- ∀m f c.
           measure_space m ∧ integrable m f ⇒
           integrable m (λx. Normal c * f x)

   [integrable_const]  Theorem

      |- ∀m c. measure_space m ⇒ integrable m (λx. Normal c)

   [integrable_fn_minus]  Theorem

      |- ∀m f. measure_space m ∧ integrable m f ⇒ integrable m (fn_minus f)

   [integrable_fn_plus]  Theorem

      |- ∀m f. measure_space m ∧ integrable m f ⇒ integrable m (fn_plus f)

   [integrable_indicator]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           integrable m (indicator_fn s)

   [integrable_infty]  Theorem

      |- ∀m f s.
           measure_space m ∧ integrable m f ∧ s ∈ measurable_sets m ∧
           (∀x. x ∈ s ⇒ (f x = PosInf)) ⇒
           (measure m s = 0)

   [integrable_infty_null]  Theorem

      |- ∀m f.
           measure_space m ∧ integrable m f ⇒
           null_set m {x | x ∈ m_space m ∧ (f x = PosInf)}

   [integrable_not_infty]  Theorem

      |- ∀m f.
           measure_space m ∧ integrable m f ∧ (∀x. 0 ≤ f x) ⇒
           ∃g.
             integrable m g ∧ (∀x. 0 ≤ g x) ∧
             (∀x. x ∈ m_space m ⇒ g x ≠ PosInf) ∧
             (integral m f = integral m g)

   [integrable_not_infty_alt]  Theorem

      |- ∀m f.
           measure_space m ∧ integrable m f ∧ (∀x. 0 ≤ f x) ⇒
           integrable m (λx. if f x = PosInf then 0 else f x) ∧
           (integral m f =
            integral m (λx. if f x = PosInf then 0 else f x))

   [integrable_not_infty_alt2]  Theorem

      |- ∀m f.
           measure_space m ∧ integrable m f ∧ (∀x. 0 ≤ f x) ⇒
           integrable m (λx. if f x = PosInf then 0 else f x) ∧
           (pos_fn_integral m f =
            pos_fn_integral m (λx. if f x = PosInf then 0 else f x))

   [integrable_not_infty_alt3]  Theorem

      |- ∀m f.
           measure_space m ∧ integrable m f ⇒
           integrable m
             (λx. if (f x = NegInf) ∨ (f x = PosInf) then 0 else f x) ∧
           (integral m f =
            integral m
              (λx. if (f x = NegInf) ∨ (f x = PosInf) then 0 else f x))

   [integrable_plus_minus]  Theorem

      |- ∀m f.
           measure_space m ⇒
           (integrable m f ⇔
            f ∈ measurable (m_space m,measurable_sets m) Borel ∧
            integrable m (fn_plus f) ∧ integrable m (fn_minus f))

   [integrable_pos]  Theorem

      |- ∀m f.
           measure_space m ∧ (∀x. 0 ≤ f x) ⇒
           (integrable m f ⇔
            f ∈ measurable (m_space m,measurable_sets m) Borel ∧
            pos_fn_integral m f ≠ PosInf)

   [integrable_sub]  Theorem

      |- ∀m f1 f2.
           measure_space m ∧ integrable m f1 ∧ integrable m f2 ⇒
           integrable m (λx. f1 x − f2 x)

   [integrable_zero]  Theorem

      |- ∀m c. measure_space m ⇒ integrable m (λx. 0)

   [integral_add]  Theorem

      |- ∀m f g.
           measure_space m ∧ integrable m f ∧ integrable m g ⇒
           (integral m (λx. f x + g x) = integral m f + integral m g)

   [integral_add_lemma]  Theorem

      |- ∀m f f1 f2.
           measure_space m ∧ integrable m f ∧ integrable m f1 ∧
           integrable m f2 ∧ (f = (λx. f1 x − f2 x)) ∧ (∀x. 0 ≤ f1 x) ∧
           (∀x. 0 ≤ f2 x) ⇒
           (integral m f = pos_fn_integral m f1 − pos_fn_integral m f2)

   [integral_cmul]  Theorem

      |- ∀m f c.
           measure_space m ∧ integrable m f ⇒
           (integral m (λx. Normal c * f x) = Normal c * integral m f)

   [integral_cmul_indicator]  Theorem

      |- ∀m s c.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           (integral m (λx. Normal c * indicator_fn s x) =
            Normal (c * measure m s))

   [integral_indicator]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           (integral m (indicator_fn s) = Normal (measure m s))

   [integral_mono]  Theorem

      |- ∀m f1 f2.
           measure_space m ∧ (∀t. t ∈ m_space m ⇒ f1 t ≤ f2 t) ⇒
           integral m f1 ≤ integral m f2

   [integral_mspace]  Theorem

      |- ∀m f.
           measure_space m ⇒
           (integral m f =
            integral m (λx. f x * indicator_fn (m_space m) x))

   [integral_pos_fn]  Theorem

      |- ∀m f.
           measure_space m ∧ (∀x. 0 ≤ f x) ⇒
           (integral m f = pos_fn_integral m f)

   [integral_sequence]  Theorem

      |- ∀m f.
           (∀x. 0 ≤ f x) ∧ measure_space m ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
           (pos_fn_integral m f =
            sup (IMAGE (λi. pos_fn_integral m (fn_seq m f i)) 𝕌(:num)))

   [integral_zero]  Theorem

      |- ∀m. measure_space m ⇒ (integral m (λx. 0) = 0)

   [lebesgue_monotone_convergence]  Theorem

      |- ∀m f fi.
           measure_space m ∧
           (∀i. fi i ∈ measurable (m_space m,measurable_sets m) Borel) ∧
           (∀i x. 0 ≤ fi i x) ∧ (∀x. 0 ≤ f x) ∧
           (∀x. mono_increasing (λi. fi i x)) ∧
           (∀x. x ∈ m_space m ⇒ (sup (IMAGE (λi. fi i x) 𝕌(:num)) = f x)) ⇒
           (pos_fn_integral m f =
            sup (IMAGE (λi. pos_fn_integral m (fi i)) 𝕌(:num)))

   [lebesgue_monotone_convergence_lemma]  Theorem

      |- ∀m f fi g r'.
           measure_space m ∧
           (∀i. fi i ∈ measurable (m_space m,measurable_sets m) Borel) ∧
           (∀x. mono_increasing (λi. fi i x)) ∧
           (∀x. x ∈ m_space m ⇒ (sup (IMAGE (λi. fi i x) 𝕌(:num)) = f x)) ∧
           r' ∈ psfis m g ∧ (∀x. g x ≤ f x) ∧ (∀i x. 0 ≤ fi i x) ⇒
           r' ≤ sup (IMAGE (λi. pos_fn_integral m (fi i)) 𝕌(:num))

   [lebesgue_monotone_convergence_subset]  Theorem

      |- ∀m f fi A.
           measure_space m ∧
           (∀i. fi i ∈ measurable (m_space m,measurable_sets m) Borel) ∧
           (∀i x. 0 ≤ fi i x) ∧ (∀x. 0 ≤ f x) ∧
           (∀x. x ∈ m_space m ⇒ (sup (IMAGE (λi. fi i x) 𝕌(:num)) = f x)) ∧
           (∀x. mono_increasing (λi. fi i x)) ∧ A ∈ measurable_sets m ⇒
           (pos_fn_integral m (λx. f x * indicator_fn A x) =
            sup
              (IMAGE
                 (λi. pos_fn_integral m (λx. fi i x * indicator_fn A x))
                 𝕌(:num)))

   [lemma_fn_1]  Theorem

      |- ∀m f n x k.
           x ∈ m_space m ∧ k ∈ count (4 ** n) ∧ &k / 2 pow n ≤ f x ∧
           f x < (&k + 1) / 2 pow n ⇒
           (fn_seq m f n x = &k / 2 pow n)

   [lemma_fn_2]  Theorem

      |- ∀m f n x.
           x ∈ m_space m ∧ 2 pow n ≤ f x ⇒ (fn_seq m f n x = 2 pow n)

   [lemma_fn_3]  Theorem

      |- ∀m f n x.
           x ∈ m_space m ∧ 0 ≤ f x ⇒
           2 pow n ≤ f x ∨
           ∃k.
             k ∈ count (4 ** n) ∧ &k / 2 pow n ≤ f x ∧
             f x < (&k + 1) / 2 pow n

   [lemma_fn_4]  Theorem

      |- ∀m f n x. x ∉ m_space m ⇒ (fn_seq m f n x = 0)

   [lemma_fn_5]  Theorem

      |- ∀m f n x. 0 ≤ f x ⇒ 0 ≤ fn_seq m f n x

   [lemma_fn_in_psfis]  Theorem

      |- ∀m f n.
           (∀x. 0 ≤ f x) ∧ measure_space m ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
           fn_seq_integral m f n ∈ psfis m (fn_seq m f n)

   [lemma_fn_mono_increasing]  Theorem

      |- ∀m f x. 0 ≤ f x ⇒ mono_increasing (λn. fn_seq m f n x)

   [lemma_fn_sup]  Theorem

      |- ∀m f x.
           x ∈ m_space m ∧ 0 ≤ f x ⇒
           (sup (IMAGE (λn. fn_seq m f n x) 𝕌(:num)) = f x)

   [lemma_fn_upper_bounded]  Theorem

      |- ∀m f n x. 0 ≤ f x ⇒ fn_seq m f n x ≤ f x

   [lemma_radon_max_in_F]  Theorem

      |- ∀f g m v.
           measure_space m ∧ measure_space v ∧ (m_space v = m_space m) ∧
           (measurable_sets v = measurable_sets m) ∧ f ∈ RADON_F m v ∧
           g ∈ RADON_F m v ⇒
           (λx. max (f x) (g x)) ∈ RADON_F m v

   [lemma_radon_seq_conv_sup]  Theorem

      |- ∀f m v.
           measure_space m ∧ measure_space v ∧ (m_space v = m_space m) ∧
           (measurable_sets v = measurable_sets m) ⇒
           ∃f_n.
             (∀n. f_n n ∈ RADON_F m v) ∧ (∀x n. f_n n x ≤ f_n (SUC n) x) ∧
             (sup (IMAGE (λn. pos_fn_integral m (f_n n)) 𝕌(:num)) =
              sup (RADON_F_integrals m v))

   [max_fn_seq_def_compute]  Theorem

      |- (∀g x. max_fn_seq g 0 x = g 0 x) ∧
         (∀g n x.
            max_fn_seq g (NUMERAL (BIT1 n)) x =
            max (max_fn_seq g (NUMERAL (BIT1 n) − 1) x)
              (g (NUMERAL (BIT1 n)) x)) ∧
         ∀g n x.
           max_fn_seq g (NUMERAL (BIT2 n)) x =
           max (max_fn_seq g (NUMERAL (BIT1 n)) x) (g (NUMERAL (BIT2 n)) x)

   [max_fn_seq_mono]  Theorem

      |- ∀g n x. max_fn_seq g n x ≤ max_fn_seq g (SUC n) x

   [measurable_sequence]  Theorem

      |- ∀m f.
           measure_space m ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
           (∃fi ri.
              (∀x. mono_increasing (λi. fi i x)) ∧
              (∀x.
                 x ∈ m_space m ⇒
                 (sup (IMAGE (λi. fi i x) 𝕌(:num)) = fn_plus f x)) ∧
              (∀i. ri i ∈ psfis m (fi i)) ∧ (∀i x. fi i x ≤ fn_plus f x) ∧
              (∀i x. 0 ≤ fi i x) ∧
              (pos_fn_integral m (fn_plus f) =
               sup (IMAGE (λi. pos_fn_integral m (fi i)) 𝕌(:num)))) ∧
           ∃gi vi.
             (∀x. mono_increasing (λi. gi i x)) ∧
             (∀x.
                x ∈ m_space m ⇒
                (sup (IMAGE (λi. gi i x) 𝕌(:num)) = fn_minus f x)) ∧
             (∀i. vi i ∈ psfis m (gi i)) ∧ (∀i x. gi i x ≤ fn_minus f x) ∧
             (∀i x. 0 ≤ gi i x) ∧
             (pos_fn_integral m (fn_minus f) =
              sup (IMAGE (λi. pos_fn_integral m (gi i)) 𝕌(:num)))

   [measure_space_finite_prod_measure_POW1]  Theorem

      |- ∀m0 m1.
           measure_space m0 ∧ measure_space m1 ∧ FINITE (m_space m0) ∧
           FINITE (m_space m1) ∧ (POW (m_space m0) = measurable_sets m0) ∧
           (POW (m_space m1) = measurable_sets m1) ⇒
           measure_space (prod_measure_space m0 m1)

   [measure_space_finite_prod_measure_POW2]  Theorem

      |- ∀m0 m1.
           measure_space m0 ∧ measure_space m1 ∧ FINITE (m_space m0) ∧
           FINITE (m_space m1) ∧ (POW (m_space m0) = measurable_sets m0) ∧
           (POW (m_space m1) = measurable_sets m1) ⇒
           measure_space
             (m_space m0 × m_space m1,POW (m_space m0 × m_space m1),
              prod_measure m0 m1)

   [measure_space_finite_prod_measure_POW3]  Theorem

      |- ∀m0 m1 m2.
           measure_space m0 ∧ measure_space m1 ∧ measure_space m2 ∧
           FINITE (m_space m0) ∧ FINITE (m_space m1) ∧
           FINITE (m_space m2) ∧ (POW (m_space m0) = measurable_sets m0) ∧
           (POW (m_space m1) = measurable_sets m1) ∧
           (POW (m_space m2) = measurable_sets m2) ⇒
           measure_space
             (m_space m0 × (m_space m1 × m_space m2),
              POW (m_space m0 × (m_space m1 × m_space m2)),
              prod_measure3 m0 m1 m2)

   [pos_fn_integral_add]  Theorem

      |- ∀m f g.
           measure_space m ∧ (∀x. 0 ≤ f x ∧ 0 ≤ g x) ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ∧
           g ∈ measurable (m_space m,measurable_sets m) Borel ⇒
           (pos_fn_integral m (λx. f x + g x) =
            pos_fn_integral m f + pos_fn_integral m g)

   [pos_fn_integral_cmul]  Theorem

      |- ∀f c.
           measure_space m ∧ (∀x. x ∈ m_space m ⇒ 0 ≤ f x) ∧ 0 ≤ c ⇒
           (pos_fn_integral m (λx. Normal c * f x) =
            Normal c * pos_fn_integral m f)

   [pos_fn_integral_cmul_indicator]  Theorem

      |- ∀m s c.
           measure_space m ∧ s ∈ measurable_sets m ∧ 0 ≤ c ⇒
           (pos_fn_integral m (λx. Normal c * indicator_fn s x) =
            Normal (c * measure m s))

   [pos_fn_integral_cmul_infty]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           (pos_fn_integral m (λx. PosInf * indicator_fn s x) =
            PosInf * Normal (measure m s))

   [pos_fn_integral_disjoint_sets]  Theorem

      |- ∀m f s t.
           measure_space m ∧ DISJOINT s t ∧ s ∈ measurable_sets m ∧
           t ∈ measurable_sets m ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ∧
           (∀x. 0 ≤ f x) ⇒
           (pos_fn_integral m (λx. f x * indicator_fn (s ∪ t) x) =
            pos_fn_integral m (λx. f x * indicator_fn s x) +
            pos_fn_integral m (λx. f x * indicator_fn t x))

   [pos_fn_integral_disjoint_sets_sum]  Theorem

      |- ∀m f s a.
           FINITE s ∧ measure_space m ∧
           (∀i. i ∈ s ⇒ a i ∈ measurable_sets m) ∧ (∀x. 0 ≤ f x) ∧
           (∀i j. i ∈ s ∧ j ∈ s ∧ i ≠ j ⇒ DISJOINT (a i) (a j)) ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
           (pos_fn_integral m
              (λx. f x * indicator_fn (BIGUNION (IMAGE a s)) x) =
            SIGMA (λi. pos_fn_integral m (λx. f x * indicator_fn (a i) x))
              s)

   [pos_fn_integral_indicator]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           (pos_fn_integral m (indicator_fn s) = Normal (measure m s))

   [pos_fn_integral_mono]  Theorem

      |- ∀f g.
           (∀x. 0 ≤ f x ∧ f x ≤ g x) ⇒
           pos_fn_integral m f ≤ pos_fn_integral m g

   [pos_fn_integral_mono_mspace]  Theorem

      |- ∀m f g.
           measure_space m ∧ (∀x. x ∈ m_space m ⇒ g x ≤ f x) ∧
           (∀x. 0 ≤ f x) ∧ (∀x. 0 ≤ g x) ⇒
           pos_fn_integral m g ≤ pos_fn_integral m f

   [pos_fn_integral_mspace]  Theorem

      |- ∀m f.
           measure_space m ∧ (∀x. 0 ≤ f x) ⇒
           (pos_fn_integral m f =
            pos_fn_integral m (λx. f x * indicator_fn (m_space m) x))

   [pos_fn_integral_pos]  Theorem

      |- ∀m f. measure_space m ∧ (∀x. 0 ≤ f x) ⇒ 0 ≤ pos_fn_integral m f

   [pos_fn_integral_pos_simple_fn]  Theorem

      |- ∀m f s a x.
           measure_space m ∧ pos_simple_fn m f s a x ⇒
           (pos_fn_integral m f = pos_simple_fn_integral m s a x)

   [pos_fn_integral_split]  Theorem

      |- ∀m f s.
           measure_space m ∧ s ∈ measurable_sets m ∧ (∀x. 0 ≤ f x) ∧
           f ∈ measurable (m_space m,measurable_sets m) Borel ⇒
           (pos_fn_integral m f =
            pos_fn_integral m (λx. f x * indicator_fn s x) +
            pos_fn_integral m
              (λx. f x * indicator_fn (m_space m DIFF s) x))

   [pos_fn_integral_sum]  Theorem

      |- ∀m f s.
           FINITE s ∧ measure_space m ∧ (∀i. i ∈ s ⇒ ∀x. 0 ≤ f i x) ∧
           (∀i.
              i ∈ s ⇒
              f i ∈ measurable (m_space m,measurable_sets m) Borel) ⇒
           (pos_fn_integral m (λx. SIGMA (λi. f i x) s) =
            SIGMA (λi. pos_fn_integral m (f i)) s)

   [pos_fn_integral_sum_cmul_indicator]  Theorem

      |- ∀m s a x.
           measure_space m ∧ FINITE s ∧ (∀i. i ∈ s ⇒ 0 ≤ x i) ∧
           (∀i. i ∈ s ⇒ a i ∈ measurable_sets m) ⇒
           (pos_fn_integral m
              (λt. SIGMA (λi. Normal (x i) * indicator_fn (a i) t) s) =
            Normal (SIGMA (λi. x i * measure m (a i)) s))

   [pos_fn_integral_suminf]  Theorem

      |- ∀m f.
           measure_space m ∧ (∀i x. 0 ≤ f i x) ∧
           (∀i. f i ∈ measurable (m_space m,measurable_sets m) Borel) ⇒
           (pos_fn_integral m (λx. suminf (λi. f i x)) =
            suminf (λi. pos_fn_integral m (f i)))

   [pos_fn_integral_zero]  Theorem

      |- ∀m. measure_space m ⇒ (pos_fn_integral m (λx. 0) = 0)

   [pos_simple_fn_add]  Theorem

      |- ∀m f g.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s' a' x' ⇒
           ∃s'' a'' x''. pos_simple_fn m (λt. f t + g t) s'' a'' x''

   [pos_simple_fn_add_alt]  Theorem

      |- ∀m f g s a x y.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s a y ⇒
           pos_simple_fn m (λt. f t + g t) s a (λi. x i + y i)

   [pos_simple_fn_cmul]  Theorem

      |- ∀m f z.
           measure_space m ∧ pos_simple_fn m f s a x ∧ 0 ≤ z ⇒
           ∃s' a' x'. pos_simple_fn m (λt. Normal z * f t) s' a' x'

   [pos_simple_fn_cmul_alt]  Theorem

      |- ∀m f s a x z.
           measure_space m ∧ 0 ≤ z ∧ pos_simple_fn m f s a x ⇒
           pos_simple_fn m (λt. Normal z * f t) s a (λi. z * x i)

   [pos_simple_fn_indicator]  Theorem

      |- ∀m A.
           measure_space m ∧ A ∈ measurable_sets m ⇒
           ∃s a x. pos_simple_fn m (indicator_fn A) s a x

   [pos_simple_fn_indicator_alt]  Theorem

      |- ∀m s.
           measure_space m ∧ s ∈ measurable_sets m ⇒
           pos_simple_fn m (indicator_fn s) {0; 1}
             (λi. if i = 0 then m_space m DIFF s else s)
             (λi. if i = 0 then 0 else 1)

   [pos_simple_fn_integral_add]  Theorem

      |- ∀m f s a x g s' b y.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s' b y ⇒
           ∃s'' c z.
             pos_simple_fn m (λx. f x + g x) s'' c z ∧
             (pos_simple_fn_integral m s a x +
              pos_simple_fn_integral m s' b y =
              pos_simple_fn_integral m s'' c z)

   [pos_simple_fn_integral_add_alt]  Theorem

      |- ∀m f s a x g y.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s a y ⇒
           (pos_simple_fn_integral m s a x +
            pos_simple_fn_integral m s a y =
            pos_simple_fn_integral m s a (λi. x i + y i))

   [pos_simple_fn_integral_cmul]  Theorem

      |- ∀m f s a x z.
           measure_space m ∧ pos_simple_fn m f s a x ∧ 0 ≤ z ⇒
           pos_simple_fn m (λx. Normal z * f x) s a (λi. z * x i) ∧
           (pos_simple_fn_integral m s a (λi. z * x i) =
            Normal z * pos_simple_fn_integral m s a x)

   [pos_simple_fn_integral_cmul_alt]  Theorem

      |- ∀m f s a x z.
           measure_space m ∧ 0 ≤ z ∧ pos_simple_fn m f s a x ⇒
           ∃s' a' x'.
             pos_simple_fn m (λt. Normal z * f t) s' a' x' ∧
             (pos_simple_fn_integral m s' a' x' =
              Normal z * pos_simple_fn_integral m s a x)

   [pos_simple_fn_integral_indicator]  Theorem

      |- ∀m A.
           measure_space m ∧ A ∈ measurable_sets m ⇒
           ∃s a x.
             pos_simple_fn m (indicator_fn A) s a x ∧
             (pos_simple_fn_integral m s a x = Normal (measure m A))

   [pos_simple_fn_integral_mono]  Theorem

      |- ∀m f s a x g s' b y.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s' b y ∧ (∀x. x ∈ m_space m ⇒ f x ≤ g x) ⇒
           pos_simple_fn_integral m s a x ≤ pos_simple_fn_integral m s' b y

   [pos_simple_fn_integral_not_infty]  Theorem

      |- ∀m s a x.
           pos_simple_fn_integral m s a x ≠ NegInf ∧
           pos_simple_fn_integral m s a x ≠ PosInf

   [pos_simple_fn_integral_present]  Theorem

      |- ∀m f s a x g s' b y.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s' b y ⇒
           ∃z z' c k.
             (∀t.
                t ∈ m_space m ⇒
                (f t =
                 SIGMA (λi. Normal (z i) * indicator_fn (c i) t) k)) ∧
             (∀t.
                t ∈ m_space m ⇒
                (g t =
                 SIGMA (λi. Normal (z' i) * indicator_fn (c i) t) k)) ∧
             (pos_simple_fn_integral m s a x =
              pos_simple_fn_integral m k c z) ∧
             (pos_simple_fn_integral m s' b y =
              pos_simple_fn_integral m k c z') ∧ FINITE k ∧
             (∀i. i ∈ k ⇒ 0 ≤ z i) ∧ (∀i. i ∈ k ⇒ 0 ≤ z' i) ∧
             (∀i j. i ∈ k ∧ j ∈ k ∧ i ≠ j ⇒ DISJOINT (c i) (c j)) ∧
             (∀i. i ∈ k ⇒ c i ∈ measurable_sets m) ∧
             (BIGUNION (IMAGE c k) = m_space m)

   [pos_simple_fn_integral_sub]  Theorem

      |- ∀m f s a x g s' b y.
           measure_space m ∧ (∀x. g x ≤ f x) ∧ (∀x. g x ≠ PosInf) ∧
           pos_simple_fn m f s a x ∧ pos_simple_fn m g s' b y ⇒
           ∃s'' c z.
             pos_simple_fn m (λx. f x − g x) s'' c z ∧
             (pos_simple_fn_integral m s a x −
              pos_simple_fn_integral m s' b y =
              pos_simple_fn_integral m s'' c z)

   [pos_simple_fn_integral_sum]  Theorem

      |- ∀m f s a x P.
           measure_space m ∧
           (∀i. i ∈ P ⇒ pos_simple_fn m (f i) s a (x i)) ∧ FINITE P ∧
           P ≠ ∅ ⇒
           pos_simple_fn m (λt. SIGMA (λi. f i t) P) s a
             (λi. SIGMA (λj. x j i) P) ∧
           (pos_simple_fn_integral m s a (λj. SIGMA (λi. x i j) P) =
            SIGMA (λi. pos_simple_fn_integral m s a (x i)) P)

   [pos_simple_fn_integral_sum_alt]  Theorem

      |- ∀m f s a x P.
           measure_space m ∧
           (∀i. i ∈ P ⇒ pos_simple_fn m (f i) (s i) (a i) (x i)) ∧
           FINITE P ∧ P ≠ ∅ ⇒
           ∃c k z.
             pos_simple_fn m (λt. SIGMA (λi. f i t) P) k c z ∧
             (pos_simple_fn_integral m k c z =
              SIGMA (λi. pos_simple_fn_integral m (s i) (a i) (x i)) P)

   [pos_simple_fn_integral_unique]  Theorem

      |- ∀m f s a x s' b y.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m f s' b y ⇒
           (pos_simple_fn_integral m s a x =
            pos_simple_fn_integral m s' b y)

   [pos_simple_fn_integral_zero]  Theorem

      |- ∀m s a x.
           measure_space m ∧ pos_simple_fn m (λt. 0) s a x ⇒
           (pos_simple_fn_integral m s a x = 0)

   [pos_simple_fn_integral_zero_alt]  Theorem

      |- ∀m s a x.
           measure_space m ∧ pos_simple_fn m g s a x ∧
           (∀x. x ∈ m_space m ⇒ (g x = 0)) ⇒
           (pos_simple_fn_integral m s a x = 0)

   [pos_simple_fn_le]  Theorem

      |- ∀m f g s a x x' i.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s a x' ∧ (∀x. x ∈ m_space m ⇒ g x ≤ f x) ∧
           i ∈ s ∧ a i ≠ ∅ ⇒
           Normal (x' i) ≤ Normal (x i)

   [pos_simple_fn_max]  Theorem

      |- ∀m f s a x g s'b y.
           measure_space m ∧ pos_simple_fn m f s a x ∧
           pos_simple_fn m g s' b y ⇒
           ∃s'' a'' x''. pos_simple_fn m (λx. max (f x) (g x)) s'' a'' x''

   [pos_simple_fn_not_infty]  Theorem

      |- ∀m f s a x.
           pos_simple_fn m f s a x ⇒
           ∀x. x ∈ m_space m ⇒ f x ≠ NegInf ∧ f x ≠ PosInf

   [pos_simple_fn_thm1]  Theorem

      |- ∀m f s a x i y.
           measure_space m ∧ pos_simple_fn m f s a x ∧ i ∈ s ∧ y ∈ a i ⇒
           (f y = Normal (x i))

   [psfis_add]  Theorem

      |- ∀m f g a b.
           measure_space m ∧ a ∈ psfis m f ∧ b ∈ psfis m g ⇒
           a + b ∈ psfis m (λx. f x + g x)

   [psfis_cmul]  Theorem

      |- ∀m f a z.
           measure_space m ∧ a ∈ psfis m f ∧ 0 ≤ z ⇒
           Normal z * a ∈ psfis m (λx. Normal z * f x)

   [psfis_indicator]  Theorem

      |- ∀m A.
           measure_space m ∧ A ∈ measurable_sets m ⇒
           Normal (measure m A) ∈ psfis m (indicator_fn A)

   [psfis_intro]  Theorem

      |- ∀m a x P.
           measure_space m ∧ (∀i. i ∈ P ⇒ a i ∈ measurable_sets m) ∧
           (∀i. i ∈ P ⇒ 0 ≤ x i) ∧ FINITE P ⇒
           Normal (SIGMA (λi. x i * measure m (a i)) P) ∈
           psfis m (λt. SIGMA (λi. Normal (x i) * indicator_fn (a i) t) P)

   [psfis_mono]  Theorem

      |- ∀m f g a b.
           measure_space m ∧ a ∈ psfis m f ∧ b ∈ psfis m g ∧
           (∀x. x ∈ m_space m ⇒ f x ≤ g x) ⇒
           a ≤ b

   [psfis_not_infty]  Theorem

      |- ∀m f a. a ∈ psfis m f ⇒ a ≠ NegInf ∧ a ≠ PosInf

   [psfis_pos]  Theorem

      |- ∀m f a.
           measure_space m ∧ a ∈ psfis m f ⇒ ∀x. x ∈ m_space m ⇒ 0 ≤ f x

   [psfis_present]  Theorem

      |- ∀m f g a b.
           measure_space m ∧ a ∈ psfis m f ∧ b ∈ psfis m g ⇒
           ∃z z' c k.
             (∀t.
                t ∈ m_space m ⇒
                (f t =
                 SIGMA (λi. Normal (z i) * indicator_fn (c i) t) k)) ∧
             (∀t.
                t ∈ m_space m ⇒
                (g t =
                 SIGMA (λi. Normal (z' i) * indicator_fn (c i) t) k)) ∧
             (a = pos_simple_fn_integral m k c z) ∧
             (b = pos_simple_fn_integral m k c z') ∧ FINITE k ∧
             (∀i. i ∈ k ⇒ 0 ≤ z i) ∧ (∀i. i ∈ k ⇒ 0 ≤ z' i) ∧
             (∀i j. i ∈ k ∧ j ∈ k ∧ i ≠ j ⇒ DISJOINT (c i) (c j)) ∧
             (∀i. i ∈ k ⇒ c i ∈ measurable_sets m) ∧
             (BIGUNION (IMAGE c k) = m_space m)

   [psfis_sub]  Theorem

      |- ∀m f g a b.
           measure_space m ∧ (∀x. g x ≤ f x) ∧ (∀x. g x ≠ PosInf) ∧
           a ∈ psfis m f ∧ b ∈ psfis m g ⇒
           a − b ∈ psfis m (λx. f x − g x)

   [psfis_sum]  Theorem

      |- ∀m f a P.
           measure_space m ∧ (∀i. i ∈ P ⇒ a i ∈ psfis m (f i)) ∧ FINITE P ⇒
           SIGMA a P ∈ psfis m (λt. SIGMA (λi. f i t) P)

   [psfis_unique]  Theorem

      |- ∀m f a b.
           measure_space m ∧ a ∈ psfis m f ∧ b ∈ psfis m f ⇒ (a = b)

   [psfis_zero]  Theorem

      |- ∀m a. measure_space m ⇒ (a ∈ psfis m (λx. 0) ⇔ (a = 0))

   [seq_sup_def_compute]  Theorem

      |- (∀P. seq_sup P 0 = @r. r ∈ P ∧ sup P < r + 1) ∧
         (∀P n.
            seq_sup P (NUMERAL (BIT1 n)) =
            @r.
              r ∈ P ∧ sup P < r + Normal ((1 / 2) pow NUMERAL (BIT1 n)) ∧
              seq_sup P (NUMERAL (BIT1 n) − 1) < r ∧ r < sup P) ∧
         ∀P n.
           seq_sup P (NUMERAL (BIT2 n)) =
           @r.
             r ∈ P ∧ sup P < r + Normal ((1 / 2) pow NUMERAL (BIT2 n)) ∧
             seq_sup P (NUMERAL (BIT1 n)) < r ∧ r < sup P


*)
end
