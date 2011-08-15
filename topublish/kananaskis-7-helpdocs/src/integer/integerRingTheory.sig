signature integerRingTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val int_interp_p_def : thm
    val int_polynom_normalize_def : thm
    val int_polynom_simplify_def : thm
    val int_r_canonical_sum_merge_def : thm
    val int_r_canonical_sum_prod_def : thm
    val int_r_canonical_sum_scalar2_def : thm
    val int_r_canonical_sum_scalar3_def : thm
    val int_r_canonical_sum_scalar_def : thm
    val int_r_canonical_sum_simplify_def : thm
    val int_r_ics_aux_def : thm
    val int_r_interp_cs_def : thm
    val int_r_interp_m_def : thm
    val int_r_interp_sp_def : thm
    val int_r_interp_vl_def : thm
    val int_r_ivl_aux_def : thm
    val int_r_monom_insert_def : thm
    val int_r_spolynom_normalize_def : thm
    val int_r_spolynom_simplify_def : thm
    val int_r_varlist_insert_def : thm
  
  (*  Theorems  *)
    val int_calculate : thm
    val int_is_ring : thm
    val int_rewrites : thm
    val int_ring_thms : thm
  
  val integerRing_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [integer] Parent theory of "integerRing"
   
   [ringNorm] Parent theory of "integerRing"
   
   [int_interp_p_def]  Definition
      
      |- int_interp_p = interp_p (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_polynom_normalize_def]  Definition
      
      |- int_polynom_normalize =
         polynom_normalize (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_polynom_simplify_def]  Definition
      
      |- int_polynom_simplify =
         polynom_simplify (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_canonical_sum_merge_def]  Definition
      
      |- int_r_canonical_sum_merge =
         r_canonical_sum_merge (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_canonical_sum_prod_def]  Definition
      
      |- int_r_canonical_sum_prod =
         r_canonical_sum_prod (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_canonical_sum_scalar2_def]  Definition
      
      |- int_r_canonical_sum_scalar2 =
         r_canonical_sum_scalar2 (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_canonical_sum_scalar3_def]  Definition
      
      |- int_r_canonical_sum_scalar3 =
         r_canonical_sum_scalar3 (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_canonical_sum_scalar_def]  Definition
      
      |- int_r_canonical_sum_scalar =
         r_canonical_sum_scalar (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_canonical_sum_simplify_def]  Definition
      
      |- int_r_canonical_sum_simplify =
         r_canonical_sum_simplify (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_ics_aux_def]  Definition
      
      |- int_r_ics_aux = r_ics_aux (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_interp_cs_def]  Definition
      
      |- int_r_interp_cs =
         r_interp_cs (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_interp_m_def]  Definition
      
      |- int_r_interp_m =
         r_interp_m (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_interp_sp_def]  Definition
      
      |- int_r_interp_sp =
         r_interp_sp (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_interp_vl_def]  Definition
      
      |- int_r_interp_vl =
         r_interp_vl (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_ivl_aux_def]  Definition
      
      |- int_r_ivl_aux = r_ivl_aux (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_monom_insert_def]  Definition
      
      |- int_r_monom_insert =
         r_monom_insert (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_spolynom_normalize_def]  Definition
      
      |- int_r_spolynom_normalize =
         r_spolynom_normalize (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_spolynom_simplify_def]  Definition
      
      |- int_r_spolynom_simplify =
         r_spolynom_simplify (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_r_varlist_insert_def]  Definition
      
      |- int_r_varlist_insert =
         r_varlist_insert (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_calculate]  Theorem
      
      |- (&n + &m = &(n + m)) ∧
         (-&n + &m = if n ≤ m then &(m − n) else -&(n − m)) ∧
         (&n + -&m = if m ≤ n then &(n − m) else -&(m − n)) ∧
         (-&n + -&m = -&(n + m)) ∧ (&n * &m = &(n * m)) ∧
         (-&n * &m = -&(n * m)) ∧ (&n * -&m = -&(n * m)) ∧
         (-&n * -&m = &(n * m)) ∧ ((&n = &m) ⇔ (n = m)) ∧
         ((&n = -&m) ⇔ (n = 0) ∧ (m = 0)) ∧
         ((-&n = &m) ⇔ (n = 0) ∧ (m = 0)) ∧ ((-&n = -&m) ⇔ (n = m)) ∧
         (--x = x) ∧ (-0 = 0)
   
   [int_is_ring]  Theorem
      
      |- is_ring (ring int_0 int_1 $+ $* numeric_negate)
   
   [int_rewrites]  Theorem
      
      |- ((&n + &m = &(n + m)) ∧
          (-&n + &m = if n ≤ m then &(m − n) else -&(n − m)) ∧
          (&n + -&m = if m ≤ n then &(n − m) else -&(m − n)) ∧
          (-&n + -&m = -&(n + m)) ∧ (&n * &m = &(n * m)) ∧
          (-&n * &m = -&(n * m)) ∧ (&n * -&m = -&(n * m)) ∧
          (-&n * -&m = &(n * m)) ∧ ((&n = &m) ⇔ (n = m)) ∧
          ((&n = -&m) ⇔ (n = 0) ∧ (m = 0)) ∧
          ((-&n = &m) ⇔ (n = 0) ∧ (m = 0)) ∧ ((-&n = -&m) ⇔ (n = m)) ∧
          (--x = x) ∧ (-0 = 0)) ∧ (int_0 = 0) ∧ (int_1 = 1) ∧
         (∀n m.
            (ZERO < BIT1 n ⇔ T) ∧ (ZERO < BIT2 n ⇔ T) ∧ (n < ZERO ⇔ F) ∧
            (BIT1 n < BIT1 m ⇔ n < m) ∧ (BIT2 n < BIT2 m ⇔ n < m) ∧
            (BIT1 n < BIT2 m ⇔ ¬(m < n)) ∧ (BIT2 n < BIT1 m ⇔ n < m)) ∧
         (∀n m.
            (ZERO ≤ n ⇔ T) ∧ (BIT1 n ≤ ZERO ⇔ F) ∧ (BIT2 n ≤ ZERO ⇔ F) ∧
            (BIT1 n ≤ BIT1 m ⇔ n ≤ m) ∧ (BIT1 n ≤ BIT2 m ⇔ n ≤ m) ∧
            (BIT2 n ≤ BIT1 m ⇔ ¬(m ≤ n)) ∧ (BIT2 n ≤ BIT2 m ⇔ n ≤ m)) ∧
         (∀n m.
            NUMERAL (n − m) =
            if m < n then NUMERAL (numeral$iSUB T n m) else 0) ∧
         (∀b n m.
            (numeral$iSUB b ZERO x = ZERO) ∧ (numeral$iSUB T n ZERO = n) ∧
            (numeral$iSUB F (BIT1 n) ZERO = numeral$iDUB n) ∧
            (numeral$iSUB T (BIT1 n) (BIT1 m) =
             numeral$iDUB (numeral$iSUB T n m)) ∧
            (numeral$iSUB F (BIT1 n) (BIT1 m) =
             BIT1 (numeral$iSUB F n m)) ∧
            (numeral$iSUB T (BIT1 n) (BIT2 m) =
             BIT1 (numeral$iSUB F n m)) ∧
            (numeral$iSUB F (BIT1 n) (BIT2 m) =
             numeral$iDUB (numeral$iSUB F n m)) ∧
            (numeral$iSUB F (BIT2 n) ZERO = BIT1 n) ∧
            (numeral$iSUB T (BIT2 n) (BIT1 m) =
             BIT1 (numeral$iSUB T n m)) ∧
            (numeral$iSUB F (BIT2 n) (BIT1 m) =
             numeral$iDUB (numeral$iSUB T n m)) ∧
            (numeral$iSUB T (BIT2 n) (BIT2 m) =
             numeral$iDUB (numeral$iSUB T n m)) ∧
            (numeral$iSUB F (BIT2 n) (BIT2 m) =
             BIT1 (numeral$iSUB F n m))) ∧
         ∀t.
           (T ∧ t ⇔ t) ∧ (t ∧ T ⇔ t) ∧ (F ∧ t ⇔ F) ∧ (t ∧ F ⇔ F) ∧
           (t ∧ t ⇔ t)
   
   [int_ring_thms]  Theorem
      
      |- is_ring (ring int_0 int_1 $+ $* numeric_negate) ∧
         (∀vm p.
            int_interp_p vm p =
            int_r_interp_cs vm (int_polynom_simplify p)) ∧
         (((∀vm c. int_interp_p vm (Pconst c) = c) ∧
           (∀vm i. int_interp_p vm (Pvar i) = varmap_find i vm) ∧
           (∀vm p1 p2.
              int_interp_p vm (Pplus p1 p2) =
              int_interp_p vm p1 + int_interp_p vm p2) ∧
           (∀vm p1 p2.
              int_interp_p vm (Pmult p1 p2) =
              int_interp_p vm p1 * int_interp_p vm p2) ∧
           ∀vm p1. int_interp_p vm (Popp p1) = -int_interp_p vm p1) ∧
          (∀x v2 v1. varmap_find End_idx (Node_vm x v1 v2) = x) ∧
          (∀x v2 v1 i1.
             varmap_find (Right_idx i1) (Node_vm x v1 v2) =
             varmap_find i1 v2) ∧
          (∀x v2 v1 i1.
             varmap_find (Left_idx i1) (Node_vm x v1 v2) =
             varmap_find i1 v1) ∧
          (∀v5. varmap_find (Left_idx v5) Empty_vm = @x. T) ∧
          (∀v6. varmap_find (Right_idx v6) Empty_vm = @x. T) ∧
          (varmap_find End_idx Empty_vm = @x. T)) ∧
         ((∀t2 t1 l2 l1 c2 c1.
             int_r_canonical_sum_merge (Cons_monom c1 l1 t1)
               (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1
                  (int_r_canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
               (Cons_monom (c1 + c2) l1 (int_r_canonical_sum_merge t1 t2))
               (Cons_monom c2 l2
                  (int_r_canonical_sum_merge (Cons_monom c1 l1 t1) t2))) ∧
          (∀t2 t1 l2 l1 c1.
             int_r_canonical_sum_merge (Cons_monom c1 l1 t1)
               (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1
                  (int_r_canonical_sum_merge t1 (Cons_varlist l2 t2)))
               (Cons_monom (c1 + int_1) l1
                  (int_r_canonical_sum_merge t1 t2))
               (Cons_varlist l2
                  (int_r_canonical_sum_merge (Cons_monom c1 l1 t1) t2))) ∧
          (∀t2 t1 l2 l1 c2.
             int_r_canonical_sum_merge (Cons_varlist l1 t1)
               (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1
                  (int_r_canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
               (Cons_monom (int_1 + c2) l1
                  (int_r_canonical_sum_merge t1 t2))
               (Cons_monom c2 l2
                  (int_r_canonical_sum_merge (Cons_varlist l1 t1) t2))) ∧
          (∀t2 t1 l2 l1.
             int_r_canonical_sum_merge (Cons_varlist l1 t1)
               (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1
                  (int_r_canonical_sum_merge t1 (Cons_varlist l2 t2)))
               (Cons_monom (int_1 + int_1) l1
                  (int_r_canonical_sum_merge t1 t2))
               (Cons_varlist l2
                  (int_r_canonical_sum_merge (Cons_varlist l1 t1) t2))) ∧
          (int_r_canonical_sum_merge Nil_monom Nil_monom = Nil_monom) ∧
          (∀v6 v5 v4.
             int_r_canonical_sum_merge (Cons_monom v4 v5 v6) Nil_monom =
             Cons_monom v4 v5 v6) ∧
          (∀v8 v7.
             int_r_canonical_sum_merge (Cons_varlist v7 v8) Nil_monom =
             Cons_varlist v7 v8) ∧
          (∀v16 v15 v14.
             int_r_canonical_sum_merge Nil_monom (Cons_monom v14 v15 v16) =
             Cons_monom v14 v15 v16) ∧
          ∀v18 v17.
            int_r_canonical_sum_merge Nil_monom (Cons_varlist v17 v18) =
            Cons_varlist v17 v18) ∧
         ((∀t2 l2 l1 c2 c1.
             int_r_monom_insert c1 l1 (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1 (Cons_monom c2 l2 t2))
               (Cons_monom (c1 + c2) l1 t2)
               (Cons_monom c2 l2 (int_r_monom_insert c1 l1 t2))) ∧
          (∀t2 l2 l1 c1.
             int_r_monom_insert c1 l1 (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1 (Cons_varlist l2 t2))
               (Cons_monom (c1 + int_1) l1 t2)
               (Cons_varlist l2 (int_r_monom_insert c1 l1 t2))) ∧
          ∀l1 c1.
            int_r_monom_insert c1 l1 Nil_monom =
            Cons_monom c1 l1 Nil_monom) ∧
         ((∀t2 l2 l1 c2.
             int_r_varlist_insert l1 (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1 (Cons_monom c2 l2 t2))
               (Cons_monom (int_1 + c2) l1 t2)
               (Cons_monom c2 l2 (int_r_varlist_insert l1 t2))) ∧
          (∀t2 l2 l1.
             int_r_varlist_insert l1 (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1 (Cons_varlist l2 t2))
               (Cons_monom (int_1 + int_1) l1 t2)
               (Cons_varlist l2 (int_r_varlist_insert l1 t2))) ∧
          ∀l1.
            int_r_varlist_insert l1 Nil_monom =
            Cons_varlist l1 Nil_monom) ∧
         ((∀c0 c l t.
             int_r_canonical_sum_scalar c0 (Cons_monom c l t) =
             Cons_monom (c0 * c) l (int_r_canonical_sum_scalar c0 t)) ∧
          (∀c0 l t.
             int_r_canonical_sum_scalar c0 (Cons_varlist l t) =
             Cons_monom c0 l (int_r_canonical_sum_scalar c0 t)) ∧
          ∀c0. int_r_canonical_sum_scalar c0 Nil_monom = Nil_monom) ∧
         ((∀l0 c l t.
             int_r_canonical_sum_scalar2 l0 (Cons_monom c l t) =
             int_r_monom_insert c (list_merge index_lt l0 l)
               (int_r_canonical_sum_scalar2 l0 t)) ∧
          (∀l0 l t.
             int_r_canonical_sum_scalar2 l0 (Cons_varlist l t) =
             int_r_varlist_insert (list_merge index_lt l0 l)
               (int_r_canonical_sum_scalar2 l0 t)) ∧
          ∀l0. int_r_canonical_sum_scalar2 l0 Nil_monom = Nil_monom) ∧
         ((∀c0 l0 c l t.
             int_r_canonical_sum_scalar3 c0 l0 (Cons_monom c l t) =
             int_r_monom_insert (c0 * c) (list_merge index_lt l0 l)
               (int_r_canonical_sum_scalar3 c0 l0 t)) ∧
          (∀c0 l0 l t.
             int_r_canonical_sum_scalar3 c0 l0 (Cons_varlist l t) =
             int_r_monom_insert c0 (list_merge index_lt l0 l)
               (int_r_canonical_sum_scalar3 c0 l0 t)) ∧
          ∀c0 l0.
            int_r_canonical_sum_scalar3 c0 l0 Nil_monom = Nil_monom) ∧
         ((∀c1 l1 t1 s2.
             int_r_canonical_sum_prod (Cons_monom c1 l1 t1) s2 =
             int_r_canonical_sum_merge
               (int_r_canonical_sum_scalar3 c1 l1 s2)
               (int_r_canonical_sum_prod t1 s2)) ∧
          (∀l1 t1 s2.
             int_r_canonical_sum_prod (Cons_varlist l1 t1) s2 =
             int_r_canonical_sum_merge (int_r_canonical_sum_scalar2 l1 s2)
               (int_r_canonical_sum_prod t1 s2)) ∧
          ∀s2. int_r_canonical_sum_prod Nil_monom s2 = Nil_monom) ∧
         ((∀c l t.
             int_r_canonical_sum_simplify (Cons_monom c l t) =
             if c = int_0 then
               int_r_canonical_sum_simplify t
             else if c = int_1 then
               Cons_varlist l (int_r_canonical_sum_simplify t)
             else
               Cons_monom c l (int_r_canonical_sum_simplify t)) ∧
          (∀l t.
             int_r_canonical_sum_simplify (Cons_varlist l t) =
             Cons_varlist l (int_r_canonical_sum_simplify t)) ∧
          (int_r_canonical_sum_simplify Nil_monom = Nil_monom)) ∧
         ((∀vm x. int_r_ivl_aux vm x [] = varmap_find x vm) ∧
          ∀vm x x' t'.
            int_r_ivl_aux vm x (x'::t') =
            varmap_find x vm * int_r_ivl_aux vm x' t') ∧
         ((∀vm. int_r_interp_vl vm [] = int_1) ∧
          ∀vm x t. int_r_interp_vl vm (x::t) = int_r_ivl_aux vm x t) ∧
         ((∀vm c. int_r_interp_m vm c [] = c) ∧
          ∀vm c x t.
            int_r_interp_m vm c (x::t) = c * int_r_ivl_aux vm x t) ∧
         ((∀vm a. int_r_ics_aux vm a Nil_monom = a) ∧
          (∀vm a l t.
             int_r_ics_aux vm a (Cons_varlist l t) =
             a + int_r_ics_aux vm (int_r_interp_vl vm l) t) ∧
          ∀vm a c l t.
            int_r_ics_aux vm a (Cons_monom c l t) =
            a + int_r_ics_aux vm (int_r_interp_m vm c l) t) ∧
         ((∀vm. int_r_interp_cs vm Nil_monom = int_0) ∧
          (∀vm l t.
             int_r_interp_cs vm (Cons_varlist l t) =
             int_r_ics_aux vm (int_r_interp_vl vm l) t) ∧
          ∀vm c l t.
            int_r_interp_cs vm (Cons_monom c l t) =
            int_r_ics_aux vm (int_r_interp_m vm c l) t) ∧
         ((∀i.
             int_polynom_normalize (Pvar i) = Cons_varlist [i] Nil_monom) ∧
          (∀c.
             int_polynom_normalize (Pconst c) =
             Cons_monom c [] Nil_monom) ∧
          (∀pl pr.
             int_polynom_normalize (Pplus pl pr) =
             int_r_canonical_sum_merge (int_polynom_normalize pl)
               (int_polynom_normalize pr)) ∧
          (∀pl pr.
             int_polynom_normalize (Pmult pl pr) =
             int_r_canonical_sum_prod (int_polynom_normalize pl)
               (int_polynom_normalize pr)) ∧
          ∀p.
            int_polynom_normalize (Popp p) =
            int_r_canonical_sum_scalar3 (-int_1) []
              (int_polynom_normalize p)) ∧
         ∀x.
           int_polynom_simplify x =
           int_r_canonical_sum_simplify (int_polynom_normalize x)
   
   
*)
end
