signature numRingTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val num_canonical_sum_merge_def : thm
    val num_canonical_sum_prod_def : thm
    val num_canonical_sum_scalar2_def : thm
    val num_canonical_sum_scalar3_def : thm
    val num_canonical_sum_scalar_def : thm
    val num_canonical_sum_simplify_def : thm
    val num_ics_aux_def : thm
    val num_interp_cs_def : thm
    val num_interp_m_def : thm
    val num_interp_sp_def : thm
    val num_interp_vl_def : thm
    val num_ivl_aux_def : thm
    val num_monom_insert_def : thm
    val num_spolynom_normalize_def : thm
    val num_spolynom_simplify_def : thm
    val num_varlist_insert_def : thm

  (*  Theorems  *)
    val num_rewrites : thm
    val num_ring_thms : thm
    val num_semi_ring : thm

  val numRing_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ringNorm] Parent theory of "numRing"

   [num_canonical_sum_merge_def]  Definition

      |- num_canonical_sum_merge =
         canonical_sum_merge (semi_ring 0 1 $+ mult)

   [num_canonical_sum_prod_def]  Definition

      |- num_canonical_sum_prod =
         canonical_sum_prod (semi_ring 0 1 $+ mult)

   [num_canonical_sum_scalar2_def]  Definition

      |- num_canonical_sum_scalar2 =
         canonical_sum_scalar2 (semi_ring 0 1 $+ mult)

   [num_canonical_sum_scalar3_def]  Definition

      |- num_canonical_sum_scalar3 =
         canonical_sum_scalar3 (semi_ring 0 1 $+ mult)

   [num_canonical_sum_scalar_def]  Definition

      |- num_canonical_sum_scalar =
         canonical_sum_scalar (semi_ring 0 1 $+ mult)

   [num_canonical_sum_simplify_def]  Definition

      |- num_canonical_sum_simplify =
         canonical_sum_simplify (semi_ring 0 1 $+ mult)

   [num_ics_aux_def]  Definition

      |- num_ics_aux = ics_aux (semi_ring 0 1 $+ mult)

   [num_interp_cs_def]  Definition

      |- num_interp_cs = interp_cs (semi_ring 0 1 $+ mult)

   [num_interp_m_def]  Definition

      |- num_interp_m = interp_m (semi_ring 0 1 $+ mult)

   [num_interp_sp_def]  Definition

      |- num_interp_sp = interp_sp (semi_ring 0 1 $+ mult)

   [num_interp_vl_def]  Definition

      |- num_interp_vl = interp_vl (semi_ring 0 1 $+ mult)

   [num_ivl_aux_def]  Definition

      |- num_ivl_aux = ivl_aux (semi_ring 0 1 $+ mult)

   [num_monom_insert_def]  Definition

      |- num_monom_insert = monom_insert (semi_ring 0 1 $+ mult)

   [num_spolynom_normalize_def]  Definition

      |- num_spolynom_normalize =
         spolynom_normalize (semi_ring 0 1 $+ mult)

   [num_spolynom_simplify_def]  Definition

      |- num_spolynom_simplify = spolynom_simplify (semi_ring 0 1 $+ mult)

   [num_varlist_insert_def]  Definition

      |- num_varlist_insert = varlist_insert (semi_ring 0 1 $+ mult)

   [num_rewrites]  Theorem

      |- ((∀n. 0 + n = n) ∧ (∀n. n + 0 = n) ∧
          (∀n m. NUMERAL n + NUMERAL m = NUMERAL (numeral$iZ (n + m))) ∧
          (∀n. mult 0 n = 0) ∧ (∀n. mult n 0 = 0) ∧
          (∀n m. mult (NUMERAL n) (NUMERAL m) = NUMERAL (mult n m)) ∧
          (∀n. 0 − n = 0) ∧ (∀n. n − 0 = n) ∧
          (∀n m. NUMERAL n − NUMERAL m = NUMERAL (n − m)) ∧
          (∀n. 0 ** NUMERAL (BIT1 n) = 0) ∧
          (∀n. 0 ** NUMERAL (BIT2 n) = 0) ∧ (∀n. n ** 0 = 1) ∧
          (∀n m. NUMERAL n ** NUMERAL m = NUMERAL (n ** m)) ∧ (SUC 0 = 1) ∧
          (∀n. SUC (NUMERAL n) = NUMERAL (SUC n)) ∧ (PRE 0 = 0) ∧
          (∀n. PRE (NUMERAL n) = NUMERAL (PRE n)) ∧
          (∀n. (NUMERAL n = 0) ⇔ (n = ZERO)) ∧
          (∀n. (0 = NUMERAL n) ⇔ (n = ZERO)) ∧
          (∀n m. (NUMERAL n = NUMERAL m) ⇔ (n = m)) ∧ (∀n. n < 0 ⇔ F) ∧
          (∀n. 0 < NUMERAL n ⇔ ZERO < n) ∧
          (∀n m. NUMERAL n < NUMERAL m ⇔ n < m) ∧ (∀n. 0 > n ⇔ F) ∧
          (∀n. NUMERAL n > 0 ⇔ ZERO < n) ∧
          (∀n m. NUMERAL n > NUMERAL m ⇔ m < n) ∧ (∀n. 0 ≤ n ⇔ T) ∧
          (∀n. NUMERAL n ≤ 0 ⇔ n ≤ ZERO) ∧
          (∀n m. NUMERAL n ≤ NUMERAL m ⇔ n ≤ m) ∧ (∀n. n ≥ 0 ⇔ T) ∧
          (∀n. 0 ≥ n ⇔ (n = 0)) ∧ (∀n m. NUMERAL n ≥ NUMERAL m ⇔ m ≤ n) ∧
          (∀n. ODD (NUMERAL n) ⇔ ODD n) ∧ (∀n. EVEN (NUMERAL n) ⇔ EVEN n) ∧
          ¬ODD 0 ∧ EVEN 0) ∧
         (∀n m.
            ((ZERO = BIT1 n) ⇔ F) ∧ ((BIT1 n = ZERO) ⇔ F) ∧
            ((ZERO = BIT2 n) ⇔ F) ∧ ((BIT2 n = ZERO) ⇔ F) ∧
            ((BIT1 n = BIT2 m) ⇔ F) ∧ ((BIT2 n = BIT1 m) ⇔ F) ∧
            ((BIT1 n = BIT1 m) ⇔ (n = m)) ∧
            ((BIT2 n = BIT2 m) ⇔ (n = m))) ∧
         ((SUC ZERO = BIT1 ZERO) ∧ (∀n. SUC (BIT1 n) = BIT2 n) ∧
          ∀n. SUC (BIT2 n) = BIT1 (SUC n)) ∧
         ((numeral$iiSUC ZERO = BIT2 ZERO) ∧
          (numeral$iiSUC (BIT1 n) = BIT1 (SUC n)) ∧
          (numeral$iiSUC (BIT2 n) = BIT2 (SUC n))) ∧
         (∀n m.
            (numeral$iZ (ZERO + n) = n) ∧ (numeral$iZ (n + ZERO) = n) ∧
            (numeral$iZ (BIT1 n + BIT1 m) = BIT2 (numeral$iZ (n + m))) ∧
            (numeral$iZ (BIT1 n + BIT2 m) = BIT1 (SUC (n + m))) ∧
            (numeral$iZ (BIT2 n + BIT1 m) = BIT1 (SUC (n + m))) ∧
            (numeral$iZ (BIT2 n + BIT2 m) = BIT2 (SUC (n + m))) ∧
            (SUC (ZERO + n) = SUC n) ∧ (SUC (n + ZERO) = SUC n) ∧
            (SUC (BIT1 n + BIT1 m) = BIT1 (SUC (n + m))) ∧
            (SUC (BIT1 n + BIT2 m) = BIT2 (SUC (n + m))) ∧
            (SUC (BIT2 n + BIT1 m) = BIT2 (SUC (n + m))) ∧
            (SUC (BIT2 n + BIT2 m) = BIT1 (numeral$iiSUC (n + m))) ∧
            (numeral$iiSUC (ZERO + n) = numeral$iiSUC n) ∧
            (numeral$iiSUC (n + ZERO) = numeral$iiSUC n) ∧
            (numeral$iiSUC (BIT1 n + BIT1 m) = BIT2 (SUC (n + m))) ∧
            (numeral$iiSUC (BIT1 n + BIT2 m) =
             BIT1 (numeral$iiSUC (n + m))) ∧
            (numeral$iiSUC (BIT2 n + BIT1 m) =
             BIT1 (numeral$iiSUC (n + m))) ∧
            (numeral$iiSUC (BIT2 n + BIT2 m) =
             BIT2 (numeral$iiSUC (n + m)))) ∧
         (∀n m.
            (mult ZERO n = ZERO) ∧ (mult n ZERO = ZERO) ∧
            (mult (BIT1 n) m = numeral$iZ (numeral$iDUB (mult n m) + m)) ∧
            (mult (BIT2 n) m = numeral$iDUB (numeral$iZ (mult n m + m)))) ∧
         (∀n.
            (numeral$iDUB (BIT1 n) = BIT2 (numeral$iDUB n)) ∧
            (numeral$iDUB (BIT2 n) = BIT2 (BIT1 n)) ∧
            (numeral$iDUB ZERO = ZERO)) ∧ ((ALT_ZERO = ALT_ZERO) ⇔ T) ∧
         ((0 = 0) ⇔ T)

   [num_ring_thms]  Theorem

      |- is_semi_ring (semi_ring 0 1 $+ mult) ∧
         (∀vm p.
            num_interp_sp vm p =
            num_interp_cs vm (num_spolynom_simplify p)) ∧
         (((∀vm c. num_interp_sp vm (SPconst c) = c) ∧
           (∀vm i. num_interp_sp vm (SPvar i) = varmap_find i vm) ∧
           (∀vm p1 p2.
              num_interp_sp vm (SPplus p1 p2) =
              num_interp_sp vm p1 + num_interp_sp vm p2) ∧
           ∀vm p1 p2.
             num_interp_sp vm (SPmult p1 p2) =
             mult (num_interp_sp vm p1) (num_interp_sp vm p2)) ∧
          (∀x v2 v1. varmap_find End_idx (Node_vm x v1 v2) = x) ∧
          (∀x v2 v1 i1.
             varmap_find (Right_idx i1) (Node_vm x v1 v2) =
             varmap_find i1 v2) ∧
          (∀x v2 v1 i1.
             varmap_find (Left_idx i1) (Node_vm x v1 v2) =
             varmap_find i1 v1) ∧ ∀i. varmap_find i Empty_vm = @x. T) ∧
         ((∀t2 t1 l2 l1 c2 c1.
             num_canonical_sum_merge (Cons_monom c1 l1 t1)
               (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1
                  (num_canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
               (Cons_monom (c1 + c2) l1 (num_canonical_sum_merge t1 t2))
               (Cons_monom c2 l2
                  (num_canonical_sum_merge (Cons_monom c1 l1 t1) t2))) ∧
          (∀t2 t1 l2 l1 c1.
             num_canonical_sum_merge (Cons_monom c1 l1 t1)
               (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1
                  (num_canonical_sum_merge t1 (Cons_varlist l2 t2)))
               (Cons_monom (c1 + 1) l1 (num_canonical_sum_merge t1 t2))
               (Cons_varlist l2
                  (num_canonical_sum_merge (Cons_monom c1 l1 t1) t2))) ∧
          (∀t2 t1 l2 l1 c2.
             num_canonical_sum_merge (Cons_varlist l1 t1)
               (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1
                  (num_canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
               (Cons_monom (1 + c2) l1 (num_canonical_sum_merge t1 t2))
               (Cons_monom c2 l2
                  (num_canonical_sum_merge (Cons_varlist l1 t1) t2))) ∧
          (∀t2 t1 l2 l1.
             num_canonical_sum_merge (Cons_varlist l1 t1)
               (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1
                  (num_canonical_sum_merge t1 (Cons_varlist l2 t2)))
               (Cons_monom (1 + 1) l1 (num_canonical_sum_merge t1 t2))
               (Cons_varlist l2
                  (num_canonical_sum_merge (Cons_varlist l1 t1) t2))) ∧
          (∀s1. num_canonical_sum_merge s1 Nil_monom = s1) ∧
          (∀v6 v5 v4.
             num_canonical_sum_merge Nil_monom (Cons_monom v4 v5 v6) =
             Cons_monom v4 v5 v6) ∧
          ∀v8 v7.
            num_canonical_sum_merge Nil_monom (Cons_varlist v7 v8) =
            Cons_varlist v7 v8) ∧
         ((∀t2 l2 l1 c2 c1.
             num_monom_insert c1 l1 (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1 (Cons_monom c2 l2 t2))
               (Cons_monom (c1 + c2) l1 t2)
               (Cons_monom c2 l2 (num_monom_insert c1 l1 t2))) ∧
          (∀t2 l2 l1 c1.
             num_monom_insert c1 l1 (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1 (Cons_varlist l2 t2))
               (Cons_monom (c1 + 1) l1 t2)
               (Cons_varlist l2 (num_monom_insert c1 l1 t2))) ∧
          ∀l1 c1.
            num_monom_insert c1 l1 Nil_monom =
            Cons_monom c1 l1 Nil_monom) ∧
         ((∀t2 l2 l1 c2.
             num_varlist_insert l1 (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1 (Cons_monom c2 l2 t2))
               (Cons_monom (1 + c2) l1 t2)
               (Cons_monom c2 l2 (num_varlist_insert l1 t2))) ∧
          (∀t2 l2 l1.
             num_varlist_insert l1 (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1 (Cons_varlist l2 t2))
               (Cons_monom (1 + 1) l1 t2)
               (Cons_varlist l2 (num_varlist_insert l1 t2))) ∧
          ∀l1.
            num_varlist_insert l1 Nil_monom = Cons_varlist l1 Nil_monom) ∧
         ((∀c0 c l t.
             num_canonical_sum_scalar c0 (Cons_monom c l t) =
             Cons_monom (mult c0 c) l (num_canonical_sum_scalar c0 t)) ∧
          (∀c0 l t.
             num_canonical_sum_scalar c0 (Cons_varlist l t) =
             Cons_monom c0 l (num_canonical_sum_scalar c0 t)) ∧
          ∀c0. num_canonical_sum_scalar c0 Nil_monom = Nil_monom) ∧
         ((∀l0 c l t.
             num_canonical_sum_scalar2 l0 (Cons_monom c l t) =
             num_monom_insert c (list_merge index_lt l0 l)
               (num_canonical_sum_scalar2 l0 t)) ∧
          (∀l0 l t.
             num_canonical_sum_scalar2 l0 (Cons_varlist l t) =
             num_varlist_insert (list_merge index_lt l0 l)
               (num_canonical_sum_scalar2 l0 t)) ∧
          ∀l0. num_canonical_sum_scalar2 l0 Nil_monom = Nil_monom) ∧
         ((∀c0 l0 c l t.
             num_canonical_sum_scalar3 c0 l0 (Cons_monom c l t) =
             num_monom_insert (mult c0 c) (list_merge index_lt l0 l)
               (num_canonical_sum_scalar3 c0 l0 t)) ∧
          (∀c0 l0 l t.
             num_canonical_sum_scalar3 c0 l0 (Cons_varlist l t) =
             num_monom_insert c0 (list_merge index_lt l0 l)
               (num_canonical_sum_scalar3 c0 l0 t)) ∧
          ∀c0 l0. num_canonical_sum_scalar3 c0 l0 Nil_monom = Nil_monom) ∧
         ((∀c1 l1 t1 s2.
             num_canonical_sum_prod (Cons_monom c1 l1 t1) s2 =
             num_canonical_sum_merge (num_canonical_sum_scalar3 c1 l1 s2)
               (num_canonical_sum_prod t1 s2)) ∧
          (∀l1 t1 s2.
             num_canonical_sum_prod (Cons_varlist l1 t1) s2 =
             num_canonical_sum_merge (num_canonical_sum_scalar2 l1 s2)
               (num_canonical_sum_prod t1 s2)) ∧
          ∀s2. num_canonical_sum_prod Nil_monom s2 = Nil_monom) ∧
         ((∀c l t.
             num_canonical_sum_simplify (Cons_monom c l t) =
             if c = 0 then num_canonical_sum_simplify t
             else if c = 1 then
               Cons_varlist l (num_canonical_sum_simplify t)
             else Cons_monom c l (num_canonical_sum_simplify t)) ∧
          (∀l t.
             num_canonical_sum_simplify (Cons_varlist l t) =
             Cons_varlist l (num_canonical_sum_simplify t)) ∧
          (num_canonical_sum_simplify Nil_monom = Nil_monom)) ∧
         ((∀vm x. num_ivl_aux vm x [] = varmap_find x vm) ∧
          ∀vm x x' t'.
            num_ivl_aux vm x (x'::t') =
            mult (varmap_find x vm) (num_ivl_aux vm x' t')) ∧
         ((∀vm. num_interp_vl vm [] = 1) ∧
          ∀vm x t. num_interp_vl vm (x::t) = num_ivl_aux vm x t) ∧
         ((∀vm c. num_interp_m vm c [] = c) ∧
          ∀vm c x t.
            num_interp_m vm c (x::t) = mult c (num_ivl_aux vm x t)) ∧
         ((∀vm a. num_ics_aux vm a Nil_monom = a) ∧
          (∀vm a l t.
             num_ics_aux vm a (Cons_varlist l t) =
             a + num_ics_aux vm (num_interp_vl vm l) t) ∧
          ∀vm a c l t.
            num_ics_aux vm a (Cons_monom c l t) =
            a + num_ics_aux vm (num_interp_m vm c l) t) ∧
         ((∀vm. num_interp_cs vm Nil_monom = 0) ∧
          (∀vm l t.
             num_interp_cs vm (Cons_varlist l t) =
             num_ics_aux vm (num_interp_vl vm l) t) ∧
          ∀vm c l t.
            num_interp_cs vm (Cons_monom c l t) =
            num_ics_aux vm (num_interp_m vm c l) t) ∧
         ((∀i.
             num_spolynom_normalize (SPvar i) =
             Cons_varlist [i] Nil_monom) ∧
          (∀c.
             num_spolynom_normalize (SPconst c) =
             Cons_monom c [] Nil_monom) ∧
          (∀l r.
             num_spolynom_normalize (SPplus l r) =
             num_canonical_sum_merge (num_spolynom_normalize l)
               (num_spolynom_normalize r)) ∧
          ∀l r.
            num_spolynom_normalize (SPmult l r) =
            num_canonical_sum_prod (num_spolynom_normalize l)
              (num_spolynom_normalize r)) ∧
         ∀x.
           num_spolynom_simplify x =
           num_canonical_sum_simplify (num_spolynom_normalize x)

   [num_semi_ring]  Theorem

      |- is_semi_ring (semi_ring 0 1 $+ mult)


*)
end
