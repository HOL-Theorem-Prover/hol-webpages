signature ratRingTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val rat_interp_p_def : thm
    val rat_polynom_normalize_def : thm
    val rat_polynom_simplify_def : thm
    val rat_r_canonical_sum_merge_def : thm
    val rat_r_canonical_sum_prod_def : thm
    val rat_r_canonical_sum_scalar2_def : thm
    val rat_r_canonical_sum_scalar3_def : thm
    val rat_r_canonical_sum_scalar_def : thm
    val rat_r_canonical_sum_simplify_def : thm
    val rat_r_ics_aux_def : thm
    val rat_r_interp_cs_def : thm
    val rat_r_interp_m_def : thm
    val rat_r_interp_sp_def : thm
    val rat_r_interp_vl_def : thm
    val rat_r_ivl_aux_def : thm
    val rat_r_monom_insert_def : thm
    val rat_r_spolynom_normalize_def : thm
    val rat_r_spolynom_simplify_def : thm
    val rat_r_varlist_insert_def : thm

  (*  Theorems  *)
    val RAT_IS_RING : thm
    val rat_ring_thms : thm

  val ratRing_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [rat] Parent theory of "ratRing"

   [rat_interp_p_def]  Definition

      |- rat_interp_p = interp_p (ring 0 1 $+ $* numeric_negate)

   [rat_polynom_normalize_def]  Definition

      |- rat_polynom_normalize =
         polynom_normalize (ring 0 1 $+ $* numeric_negate)

   [rat_polynom_simplify_def]  Definition

      |- rat_polynom_simplify =
         polynom_simplify (ring 0 1 $+ $* numeric_negate)

   [rat_r_canonical_sum_merge_def]  Definition

      |- rat_r_canonical_sum_merge =
         r_canonical_sum_merge (ring 0 1 $+ $* numeric_negate)

   [rat_r_canonical_sum_prod_def]  Definition

      |- rat_r_canonical_sum_prod =
         r_canonical_sum_prod (ring 0 1 $+ $* numeric_negate)

   [rat_r_canonical_sum_scalar2_def]  Definition

      |- rat_r_canonical_sum_scalar2 =
         r_canonical_sum_scalar2 (ring 0 1 $+ $* numeric_negate)

   [rat_r_canonical_sum_scalar3_def]  Definition

      |- rat_r_canonical_sum_scalar3 =
         r_canonical_sum_scalar3 (ring 0 1 $+ $* numeric_negate)

   [rat_r_canonical_sum_scalar_def]  Definition

      |- rat_r_canonical_sum_scalar =
         r_canonical_sum_scalar (ring 0 1 $+ $* numeric_negate)

   [rat_r_canonical_sum_simplify_def]  Definition

      |- rat_r_canonical_sum_simplify =
         r_canonical_sum_simplify (ring 0 1 $+ $* numeric_negate)

   [rat_r_ics_aux_def]  Definition

      |- rat_r_ics_aux = r_ics_aux (ring 0 1 $+ $* numeric_negate)

   [rat_r_interp_cs_def]  Definition

      |- rat_r_interp_cs = r_interp_cs (ring 0 1 $+ $* numeric_negate)

   [rat_r_interp_m_def]  Definition

      |- rat_r_interp_m = r_interp_m (ring 0 1 $+ $* numeric_negate)

   [rat_r_interp_sp_def]  Definition

      |- rat_r_interp_sp = r_interp_sp (ring 0 1 $+ $* numeric_negate)

   [rat_r_interp_vl_def]  Definition

      |- rat_r_interp_vl = r_interp_vl (ring 0 1 $+ $* numeric_negate)

   [rat_r_ivl_aux_def]  Definition

      |- rat_r_ivl_aux = r_ivl_aux (ring 0 1 $+ $* numeric_negate)

   [rat_r_monom_insert_def]  Definition

      |- rat_r_monom_insert =
         r_monom_insert (ring 0 1 $+ $* numeric_negate)

   [rat_r_spolynom_normalize_def]  Definition

      |- rat_r_spolynom_normalize =
         r_spolynom_normalize (ring 0 1 $+ $* numeric_negate)

   [rat_r_spolynom_simplify_def]  Definition

      |- rat_r_spolynom_simplify =
         r_spolynom_simplify (ring 0 1 $+ $* numeric_negate)

   [rat_r_varlist_insert_def]  Definition

      |- rat_r_varlist_insert =
         r_varlist_insert (ring 0 1 $+ $* numeric_negate)

   [RAT_IS_RING]  Theorem

      |- is_ring (ring 0 1 $+ $* numeric_negate)

   [rat_ring_thms]  Theorem

      |- is_ring (ring 0 1 $+ $* numeric_negate) ∧
         (∀vm p.
            rat_interp_p vm p =
            rat_r_interp_cs vm (rat_polynom_simplify p)) ∧
         (((∀vm c. rat_interp_p vm (Pconst c) = c) ∧
           (∀vm i. rat_interp_p vm (Pvar i) = varmap_find i vm) ∧
           (∀vm p1 p2.
              rat_interp_p vm (Pplus p1 p2) =
              rat_interp_p vm p1 + rat_interp_p vm p2) ∧
           (∀vm p1 p2.
              rat_interp_p vm (Pmult p1 p2) =
              rat_interp_p vm p1 * rat_interp_p vm p2) ∧
           ∀vm p1. rat_interp_p vm (Popp p1) = -rat_interp_p vm p1) ∧
          (∀x v2 v1. varmap_find End_idx (Node_vm x v1 v2) = x) ∧
          (∀x v2 v1 i1.
             varmap_find (Right_idx i1) (Node_vm x v1 v2) =
             varmap_find i1 v2) ∧
          (∀x v2 v1 i1.
             varmap_find (Left_idx i1) (Node_vm x v1 v2) =
             varmap_find i1 v1) ∧ ∀i. varmap_find i Empty_vm = @x. T) ∧
         ((∀t2 t1 l2 l1 c2 c1.
             rat_r_canonical_sum_merge (Cons_monom c1 l1 t1)
               (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1
                  (rat_r_canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
               (Cons_monom (c1 + c2) l1 (rat_r_canonical_sum_merge t1 t2))
               (Cons_monom c2 l2
                  (rat_r_canonical_sum_merge (Cons_monom c1 l1 t1) t2))) ∧
          (∀t2 t1 l2 l1 c1.
             rat_r_canonical_sum_merge (Cons_monom c1 l1 t1)
               (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1
                  (rat_r_canonical_sum_merge t1 (Cons_varlist l2 t2)))
               (Cons_monom (c1 + 1) l1 (rat_r_canonical_sum_merge t1 t2))
               (Cons_varlist l2
                  (rat_r_canonical_sum_merge (Cons_monom c1 l1 t1) t2))) ∧
          (∀t2 t1 l2 l1 c2.
             rat_r_canonical_sum_merge (Cons_varlist l1 t1)
               (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1
                  (rat_r_canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
               (Cons_monom (1 + c2) l1 (rat_r_canonical_sum_merge t1 t2))
               (Cons_monom c2 l2
                  (rat_r_canonical_sum_merge (Cons_varlist l1 t1) t2))) ∧
          (∀t2 t1 l2 l1.
             rat_r_canonical_sum_merge (Cons_varlist l1 t1)
               (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1
                  (rat_r_canonical_sum_merge t1 (Cons_varlist l2 t2)))
               (Cons_monom (1 + 1) l1 (rat_r_canonical_sum_merge t1 t2))
               (Cons_varlist l2
                  (rat_r_canonical_sum_merge (Cons_varlist l1 t1) t2))) ∧
          (∀s1. rat_r_canonical_sum_merge s1 Nil_monom = s1) ∧
          (∀v6 v5 v4.
             rat_r_canonical_sum_merge Nil_monom (Cons_monom v4 v5 v6) =
             Cons_monom v4 v5 v6) ∧
          ∀v8 v7.
            rat_r_canonical_sum_merge Nil_monom (Cons_varlist v7 v8) =
            Cons_varlist v7 v8) ∧
         ((∀t2 l2 l1 c2 c1.
             rat_r_monom_insert c1 l1 (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1 (Cons_monom c2 l2 t2))
               (Cons_monom (c1 + c2) l1 t2)
               (Cons_monom c2 l2 (rat_r_monom_insert c1 l1 t2))) ∧
          (∀t2 l2 l1 c1.
             rat_r_monom_insert c1 l1 (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_monom c1 l1 (Cons_varlist l2 t2))
               (Cons_monom (c1 + 1) l1 t2)
               (Cons_varlist l2 (rat_r_monom_insert c1 l1 t2))) ∧
          ∀l1 c1.
            rat_r_monom_insert c1 l1 Nil_monom =
            Cons_monom c1 l1 Nil_monom) ∧
         ((∀t2 l2 l1 c2.
             rat_r_varlist_insert l1 (Cons_monom c2 l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1 (Cons_monom c2 l2 t2))
               (Cons_monom (1 + c2) l1 t2)
               (Cons_monom c2 l2 (rat_r_varlist_insert l1 t2))) ∧
          (∀t2 l2 l1.
             rat_r_varlist_insert l1 (Cons_varlist l2 t2) =
             compare (list_compare index_compare l1 l2)
               (Cons_varlist l1 (Cons_varlist l2 t2))
               (Cons_monom (1 + 1) l1 t2)
               (Cons_varlist l2 (rat_r_varlist_insert l1 t2))) ∧
          ∀l1.
            rat_r_varlist_insert l1 Nil_monom =
            Cons_varlist l1 Nil_monom) ∧
         ((∀c0 c l t.
             rat_r_canonical_sum_scalar c0 (Cons_monom c l t) =
             Cons_monom (c0 * c) l (rat_r_canonical_sum_scalar c0 t)) ∧
          (∀c0 l t.
             rat_r_canonical_sum_scalar c0 (Cons_varlist l t) =
             Cons_monom c0 l (rat_r_canonical_sum_scalar c0 t)) ∧
          ∀c0. rat_r_canonical_sum_scalar c0 Nil_monom = Nil_monom) ∧
         ((∀l0 c l t.
             rat_r_canonical_sum_scalar2 l0 (Cons_monom c l t) =
             rat_r_monom_insert c (list_merge index_lt l0 l)
               (rat_r_canonical_sum_scalar2 l0 t)) ∧
          (∀l0 l t.
             rat_r_canonical_sum_scalar2 l0 (Cons_varlist l t) =
             rat_r_varlist_insert (list_merge index_lt l0 l)
               (rat_r_canonical_sum_scalar2 l0 t)) ∧
          ∀l0. rat_r_canonical_sum_scalar2 l0 Nil_monom = Nil_monom) ∧
         ((∀c0 l0 c l t.
             rat_r_canonical_sum_scalar3 c0 l0 (Cons_monom c l t) =
             rat_r_monom_insert (c0 * c) (list_merge index_lt l0 l)
               (rat_r_canonical_sum_scalar3 c0 l0 t)) ∧
          (∀c0 l0 l t.
             rat_r_canonical_sum_scalar3 c0 l0 (Cons_varlist l t) =
             rat_r_monom_insert c0 (list_merge index_lt l0 l)
               (rat_r_canonical_sum_scalar3 c0 l0 t)) ∧
          ∀c0 l0.
            rat_r_canonical_sum_scalar3 c0 l0 Nil_monom = Nil_monom) ∧
         ((∀c1 l1 t1 s2.
             rat_r_canonical_sum_prod (Cons_monom c1 l1 t1) s2 =
             rat_r_canonical_sum_merge
               (rat_r_canonical_sum_scalar3 c1 l1 s2)
               (rat_r_canonical_sum_prod t1 s2)) ∧
          (∀l1 t1 s2.
             rat_r_canonical_sum_prod (Cons_varlist l1 t1) s2 =
             rat_r_canonical_sum_merge (rat_r_canonical_sum_scalar2 l1 s2)
               (rat_r_canonical_sum_prod t1 s2)) ∧
          ∀s2. rat_r_canonical_sum_prod Nil_monom s2 = Nil_monom) ∧
         ((∀c l t.
             rat_r_canonical_sum_simplify (Cons_monom c l t) =
             if c = 0 then rat_r_canonical_sum_simplify t
             else if c = 1 then
               Cons_varlist l (rat_r_canonical_sum_simplify t)
             else Cons_monom c l (rat_r_canonical_sum_simplify t)) ∧
          (∀l t.
             rat_r_canonical_sum_simplify (Cons_varlist l t) =
             Cons_varlist l (rat_r_canonical_sum_simplify t)) ∧
          (rat_r_canonical_sum_simplify Nil_monom = Nil_monom)) ∧
         ((∀vm x. rat_r_ivl_aux vm x [] = varmap_find x vm) ∧
          ∀vm x x' t'.
            rat_r_ivl_aux vm x (x'::t') =
            varmap_find x vm * rat_r_ivl_aux vm x' t') ∧
         ((∀vm. rat_r_interp_vl vm [] = 1) ∧
          ∀vm x t. rat_r_interp_vl vm (x::t) = rat_r_ivl_aux vm x t) ∧
         ((∀vm c. rat_r_interp_m vm c [] = c) ∧
          ∀vm c x t.
            rat_r_interp_m vm c (x::t) = c * rat_r_ivl_aux vm x t) ∧
         ((∀vm a. rat_r_ics_aux vm a Nil_monom = a) ∧
          (∀vm a l t.
             rat_r_ics_aux vm a (Cons_varlist l t) =
             a + rat_r_ics_aux vm (rat_r_interp_vl vm l) t) ∧
          ∀vm a c l t.
            rat_r_ics_aux vm a (Cons_monom c l t) =
            a + rat_r_ics_aux vm (rat_r_interp_m vm c l) t) ∧
         ((∀vm. rat_r_interp_cs vm Nil_monom = 0) ∧
          (∀vm l t.
             rat_r_interp_cs vm (Cons_varlist l t) =
             rat_r_ics_aux vm (rat_r_interp_vl vm l) t) ∧
          ∀vm c l t.
            rat_r_interp_cs vm (Cons_monom c l t) =
            rat_r_ics_aux vm (rat_r_interp_m vm c l) t) ∧
         ((∀i.
             rat_polynom_normalize (Pvar i) = Cons_varlist [i] Nil_monom) ∧
          (∀c.
             rat_polynom_normalize (Pconst c) =
             Cons_monom c [] Nil_monom) ∧
          (∀pl pr.
             rat_polynom_normalize (Pplus pl pr) =
             rat_r_canonical_sum_merge (rat_polynom_normalize pl)
               (rat_polynom_normalize pr)) ∧
          (∀pl pr.
             rat_polynom_normalize (Pmult pl pr) =
             rat_r_canonical_sum_prod (rat_polynom_normalize pl)
               (rat_polynom_normalize pr)) ∧
          ∀p.
            rat_polynom_normalize (Popp p) =
            rat_r_canonical_sum_scalar3 (-1) []
              (rat_polynom_normalize p)) ∧
         ∀x.
           rat_polynom_simplify x =
           rat_r_canonical_sum_simplify (rat_polynom_normalize x)


*)
end
