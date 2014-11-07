signature ringNormTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val interp_p_def : thm
    val polynom_TY_DEF : thm
    val polynom_case_def : thm
    val polynom_normalize_def : thm
    val polynom_simplify_def : thm
    val polynom_size_def : thm
    val r_canonical_sum_merge_def : thm
    val r_canonical_sum_prod_def : thm
    val r_canonical_sum_scalar2_def : thm
    val r_canonical_sum_scalar3_def : thm
    val r_canonical_sum_scalar_def : thm
    val r_canonical_sum_simplify_def : thm
    val r_ics_aux_def : thm
    val r_interp_cs_def : thm
    val r_interp_m_def : thm
    val r_interp_sp_def : thm
    val r_interp_vl_def : thm
    val r_ivl_aux_def : thm
    val r_monom_insert_def : thm
    val r_spolynom_normalize_def : thm
    val r_spolynom_simplify_def : thm
    val r_varlist_insert_def : thm

  (*  Theorems  *)
    val canonical_sum_merge_def : thm
    val canonical_sum_prod_def : thm
    val canonical_sum_scalar2_def : thm
    val canonical_sum_scalar3_def : thm
    val canonical_sum_scalar_def : thm
    val canonical_sum_simplify_def : thm
    val datatype_polynom : thm
    val ics_aux_def : thm
    val interp_cs_def : thm
    val interp_m_def : thm
    val interp_sp_def : thm
    val interp_vl_def : thm
    val ivl_aux_def : thm
    val monom_insert_def : thm
    val polynom_11 : thm
    val polynom_Axiom : thm
    val polynom_case_cong : thm
    val polynom_distinct : thm
    val polynom_induction : thm
    val polynom_nchotomy : thm
    val polynom_normalize_ok : thm
    val polynom_simplify_ok : thm
    val spolynom_normalize_def : thm
    val spolynom_simplify_def : thm
    val varlist_insert_def : thm

  val ringNorm_grammars : type_grammar.grammar * term_grammar.grammar

  val IMPORT : abstraction.inst_infos ->
    { interp_p_def : thm,
      polynom_simplify_def : thm,
      polynom_normalize_def : thm,
      polynom_size_def : thm,
      polynom_case_def : thm,
      polynom_TY_DEF : thm,
      r_canonical_sum_merge_def : thm,
      r_monom_insert_def : thm,
      r_varlist_insert_def : thm,
      r_canonical_sum_scalar_def : thm,
      r_canonical_sum_scalar2_def : thm,
      r_canonical_sum_scalar3_def : thm,
      r_canonical_sum_prod_def : thm,
      r_canonical_sum_simplify_def : thm,
      r_ivl_aux_def : thm,
      r_interp_vl_def : thm,
      r_interp_m_def : thm,
      r_ics_aux_def : thm,
      r_interp_cs_def : thm,
      r_spolynom_normalize_def : thm,
      r_spolynom_simplify_def : thm,
      r_interp_sp_def : thm,
      polynom_simplify_ok : thm,
      polynom_normalize_ok : thm,
      polynom_induction : thm,
      polynom_Axiom : thm,
      polynom_nchotomy : thm,
      polynom_case_cong : thm,
      polynom_distinct : thm,
      polynom_11 : thm,
      datatype_polynom : thm,
      spolynom_simplify_def : thm,
      spolynom_normalize_def : thm,
      interp_cs_def : thm,
      ics_aux_def : thm,
      interp_m_def : thm,
      interp_vl_def : thm,
      ivl_aux_def : thm,
      canonical_sum_simplify_def : thm,
      canonical_sum_prod_def : thm,
      canonical_sum_scalar3_def : thm,
      canonical_sum_scalar2_def : thm,
      canonical_sum_scalar_def : thm,
      varlist_insert_def : thm,
      monom_insert_def : thm,
      canonical_sum_merge_def : thm,
      interp_sp_def : thm }

(*
   [canonical] Parent theory of "ringNorm"

   [ring] Parent theory of "ringNorm"

   [interp_p_def]  Definition

      |- (∀r vm c. interp_p r vm (Pconst c) = c) ∧
         (∀r vm i. interp_p r vm (Pvar i) = varmap_find i vm) ∧
         (∀r vm p1 p2.
            interp_p r vm (Pplus p1 p2) =
            RP r (interp_p r vm p1) (interp_p r vm p2)) ∧
         (∀r vm p1 p2.
            interp_p r vm (Pmult p1 p2) =
            RM r (interp_p r vm p1) (interp_p r vm p2)) ∧
         ∀r vm p1. interp_p r vm (Popp p1) = RN r (interp_p r vm p1)

   [polynom_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'polynom' .
                  (∀a0'.
                     (∃a.
                        a0' =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0' =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB)
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'polynom' a0 ∧ 'polynom' a1) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC (SUC 0))) (ARB,ARB)
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'polynom' a0 ∧ 'polynom' a1) ∨
                     (∃a.
                        (a0' =
                         (λa.
                            ind_type$CONSTR (SUC (SUC (SUC (SUC 0))))
                              (ARB,ARB)
                              (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                           a) ∧ 'polynom' a) ⇒
                     'polynom' a0') ⇒
                  'polynom' a0') rep

   [polynom_case_def]  Definition

      |- (∀a f f1 f2 f3 f4. polynom_CASE (Pvar a) f f1 f2 f3 f4 = f a) ∧
         (∀a f f1 f2 f3 f4. polynom_CASE (Pconst a) f f1 f2 f3 f4 = f1 a) ∧
         (∀a0 a1 f f1 f2 f3 f4.
            polynom_CASE (Pplus a0 a1) f f1 f2 f3 f4 = f2 a0 a1) ∧
         (∀a0 a1 f f1 f2 f3 f4.
            polynom_CASE (Pmult a0 a1) f f1 f2 f3 f4 = f3 a0 a1) ∧
         ∀a f f1 f2 f3 f4. polynom_CASE (Popp a) f f1 f2 f3 f4 = f4 a

   [polynom_normalize_def]  Definition

      |- (∀r i.
            polynom_normalize r (Pvar i) = Cons_varlist [i] Nil_monom) ∧
         (∀r c.
            polynom_normalize r (Pconst c) = Cons_monom c [] Nil_monom) ∧
         (∀r pl pr.
            polynom_normalize r (Pplus pl pr) =
            r_canonical_sum_merge r (polynom_normalize r pl)
              (polynom_normalize r pr)) ∧
         (∀r pl pr.
            polynom_normalize r (Pmult pl pr) =
            r_canonical_sum_prod r (polynom_normalize r pl)
              (polynom_normalize r pr)) ∧
         ∀r p.
           polynom_normalize r (Popp p) =
           r_canonical_sum_scalar3 r (RN r (R1 r)) []
             (polynom_normalize r p)

   [polynom_simplify_def]  Definition

      |- ∀r x.
           polynom_simplify r x =
           r_canonical_sum_simplify r (polynom_normalize r x)

   [polynom_size_def]  Definition

      |- (∀f a. polynom_size f (Pvar a) = 1 + index_size a) ∧
         (∀f a. polynom_size f (Pconst a) = 1 + f a) ∧
         (∀f a0 a1.
            polynom_size f (Pplus a0 a1) =
            1 + (polynom_size f a0 + polynom_size f a1)) ∧
         (∀f a0 a1.
            polynom_size f (Pmult a0 a1) =
            1 + (polynom_size f a0 + polynom_size f a1)) ∧
         ∀f a. polynom_size f (Popp a) = 1 + polynom_size f a

   [r_canonical_sum_merge_def]  Definition

      |- ∀r. r_canonical_sum_merge r = canonical_sum_merge (semi_ring_of r)

   [r_canonical_sum_prod_def]  Definition

      |- ∀r. r_canonical_sum_prod r = canonical_sum_prod (semi_ring_of r)

   [r_canonical_sum_scalar2_def]  Definition

      |- ∀r.
           r_canonical_sum_scalar2 r =
           canonical_sum_scalar2 (semi_ring_of r)

   [r_canonical_sum_scalar3_def]  Definition

      |- ∀r.
           r_canonical_sum_scalar3 r =
           canonical_sum_scalar3 (semi_ring_of r)

   [r_canonical_sum_scalar_def]  Definition

      |- ∀r.
           r_canonical_sum_scalar r = canonical_sum_scalar (semi_ring_of r)

   [r_canonical_sum_simplify_def]  Definition

      |- ∀r.
           r_canonical_sum_simplify r =
           canonical_sum_simplify (semi_ring_of r)

   [r_ics_aux_def]  Definition

      |- ∀r. r_ics_aux r = ics_aux (semi_ring_of r)

   [r_interp_cs_def]  Definition

      |- ∀r. r_interp_cs r = interp_cs (semi_ring_of r)

   [r_interp_m_def]  Definition

      |- ∀r. r_interp_m r = interp_m (semi_ring_of r)

   [r_interp_sp_def]  Definition

      |- ∀r. r_interp_sp r = interp_sp (semi_ring_of r)

   [r_interp_vl_def]  Definition

      |- ∀r. r_interp_vl r = interp_vl (semi_ring_of r)

   [r_ivl_aux_def]  Definition

      |- ∀r. r_ivl_aux r = ivl_aux (semi_ring_of r)

   [r_monom_insert_def]  Definition

      |- ∀r. r_monom_insert r = monom_insert (semi_ring_of r)

   [r_spolynom_normalize_def]  Definition

      |- ∀r. r_spolynom_normalize r = spolynom_normalize (semi_ring_of r)

   [r_spolynom_simplify_def]  Definition

      |- ∀r. r_spolynom_simplify r = spolynom_simplify (semi_ring_of r)

   [r_varlist_insert_def]  Definition

      |- ∀r. r_varlist_insert r = varlist_insert (semi_ring_of r)

   [canonical_sum_merge_def]  Theorem

      |- ∀r.
           (∀t2 t1 l2 l1 c2 c1.
              r_canonical_sum_merge r (Cons_monom c1 l1 t1)
                (Cons_monom c2 l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_monom c1 l1
                   (r_canonical_sum_merge r t1 (Cons_monom c2 l2 t2)))
                (Cons_monom (RP r c1 c2) l1
                   (r_canonical_sum_merge r t1 t2))
                (Cons_monom c2 l2
                   (r_canonical_sum_merge r (Cons_monom c1 l1 t1) t2))) ∧
           (∀t2 t1 l2 l1 c1.
              r_canonical_sum_merge r (Cons_monom c1 l1 t1)
                (Cons_varlist l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_monom c1 l1
                   (r_canonical_sum_merge r t1 (Cons_varlist l2 t2)))
                (Cons_monom (RP r c1 (R1 r)) l1
                   (r_canonical_sum_merge r t1 t2))
                (Cons_varlist l2
                   (r_canonical_sum_merge r (Cons_monom c1 l1 t1) t2))) ∧
           (∀t2 t1 l2 l1 c2.
              r_canonical_sum_merge r (Cons_varlist l1 t1)
                (Cons_monom c2 l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_varlist l1
                   (r_canonical_sum_merge r t1 (Cons_monom c2 l2 t2)))
                (Cons_monom (RP r (R1 r) c2) l1
                   (r_canonical_sum_merge r t1 t2))
                (Cons_monom c2 l2
                   (r_canonical_sum_merge r (Cons_varlist l1 t1) t2))) ∧
           (∀t2 t1 l2 l1.
              r_canonical_sum_merge r (Cons_varlist l1 t1)
                (Cons_varlist l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_varlist l1
                   (r_canonical_sum_merge r t1 (Cons_varlist l2 t2)))
                (Cons_monom (RP r (R1 r) (R1 r)) l1
                   (r_canonical_sum_merge r t1 t2))
                (Cons_varlist l2
                   (r_canonical_sum_merge r (Cons_varlist l1 t1) t2))) ∧
           (∀s1. r_canonical_sum_merge r s1 Nil_monom = s1) ∧
           (∀v6 v5 v4.
              r_canonical_sum_merge r Nil_monom (Cons_monom v4 v5 v6) =
              Cons_monom v4 v5 v6) ∧
           ∀v8 v7.
             r_canonical_sum_merge r Nil_monom (Cons_varlist v7 v8) =
             Cons_varlist v7 v8

   [canonical_sum_prod_def]  Theorem

      |- ∀r.
           (∀c1 l1 t1 s2.
              r_canonical_sum_prod r (Cons_monom c1 l1 t1) s2 =
              r_canonical_sum_merge r (r_canonical_sum_scalar3 r c1 l1 s2)
                (r_canonical_sum_prod r t1 s2)) ∧
           (∀l1 t1 s2.
              r_canonical_sum_prod r (Cons_varlist l1 t1) s2 =
              r_canonical_sum_merge r (r_canonical_sum_scalar2 r l1 s2)
                (r_canonical_sum_prod r t1 s2)) ∧
           ∀s2. r_canonical_sum_prod r Nil_monom s2 = Nil_monom

   [canonical_sum_scalar2_def]  Theorem

      |- ∀r.
           (∀l0 c l t.
              r_canonical_sum_scalar2 r l0 (Cons_monom c l t) =
              r_monom_insert r c (list_merge index_lt l0 l)
                (r_canonical_sum_scalar2 r l0 t)) ∧
           (∀l0 l t.
              r_canonical_sum_scalar2 r l0 (Cons_varlist l t) =
              r_varlist_insert r (list_merge index_lt l0 l)
                (r_canonical_sum_scalar2 r l0 t)) ∧
           ∀l0. r_canonical_sum_scalar2 r l0 Nil_monom = Nil_monom

   [canonical_sum_scalar3_def]  Theorem

      |- ∀r.
           (∀c0 l0 c l t.
              r_canonical_sum_scalar3 r c0 l0 (Cons_monom c l t) =
              r_monom_insert r (RM r c0 c) (list_merge index_lt l0 l)
                (r_canonical_sum_scalar3 r c0 l0 t)) ∧
           (∀c0 l0 l t.
              r_canonical_sum_scalar3 r c0 l0 (Cons_varlist l t) =
              r_monom_insert r c0 (list_merge index_lt l0 l)
                (r_canonical_sum_scalar3 r c0 l0 t)) ∧
           ∀c0 l0. r_canonical_sum_scalar3 r c0 l0 Nil_monom = Nil_monom

   [canonical_sum_scalar_def]  Theorem

      |- ∀r.
           (∀c0 c l t.
              r_canonical_sum_scalar r c0 (Cons_monom c l t) =
              Cons_monom (RM r c0 c) l (r_canonical_sum_scalar r c0 t)) ∧
           (∀c0 l t.
              r_canonical_sum_scalar r c0 (Cons_varlist l t) =
              Cons_monom c0 l (r_canonical_sum_scalar r c0 t)) ∧
           ∀c0. r_canonical_sum_scalar r c0 Nil_monom = Nil_monom

   [canonical_sum_simplify_def]  Theorem

      |- ∀r.
           (∀c l t.
              r_canonical_sum_simplify r (Cons_monom c l t) =
              if c = R0 r then r_canonical_sum_simplify r t
              else if c = R1 r then
                Cons_varlist l (r_canonical_sum_simplify r t)
              else Cons_monom c l (r_canonical_sum_simplify r t)) ∧
           (∀l t.
              r_canonical_sum_simplify r (Cons_varlist l t) =
              Cons_varlist l (r_canonical_sum_simplify r t)) ∧
           (r_canonical_sum_simplify r Nil_monom = Nil_monom)

   [datatype_polynom]  Theorem

      |- DATATYPE (polynom Pvar Pconst Pplus Pmult Popp)

   [ics_aux_def]  Theorem

      |- ∀r.
           (∀vm a. r_ics_aux r vm a Nil_monom = a) ∧
           (∀vm a l t.
              r_ics_aux r vm a (Cons_varlist l t) =
              RP r a (r_ics_aux r vm (r_interp_vl r vm l) t)) ∧
           ∀vm a c l t.
             r_ics_aux r vm a (Cons_monom c l t) =
             RP r a (r_ics_aux r vm (r_interp_m r vm c l) t)

   [interp_cs_def]  Theorem

      |- ∀r.
           (∀vm. r_interp_cs r vm Nil_monom = R0 r) ∧
           (∀vm l t.
              r_interp_cs r vm (Cons_varlist l t) =
              r_ics_aux r vm (r_interp_vl r vm l) t) ∧
           ∀vm c l t.
             r_interp_cs r vm (Cons_monom c l t) =
             r_ics_aux r vm (r_interp_m r vm c l) t

   [interp_m_def]  Theorem

      |- ∀r.
           (∀vm c. r_interp_m r vm c [] = c) ∧
           ∀vm c x t.
             r_interp_m r vm c (x::t) = RM r c (r_ivl_aux r vm x t)

   [interp_sp_def]  Theorem

      |- ∀r.
           (∀vm c. r_interp_sp r vm (SPconst c) = c) ∧
           (∀vm i. r_interp_sp r vm (SPvar i) = varmap_find i vm) ∧
           (∀vm p1 p2.
              r_interp_sp r vm (SPplus p1 p2) =
              RP r (r_interp_sp r vm p1) (r_interp_sp r vm p2)) ∧
           ∀vm p1 p2.
             r_interp_sp r vm (SPmult p1 p2) =
             RM r (r_interp_sp r vm p1) (r_interp_sp r vm p2)

   [interp_vl_def]  Theorem

      |- ∀r.
           (∀vm. r_interp_vl r vm [] = R1 r) ∧
           ∀vm x t. r_interp_vl r vm (x::t) = r_ivl_aux r vm x t

   [ivl_aux_def]  Theorem

      |- ∀r.
           (∀vm x. r_ivl_aux r vm x [] = varmap_find x vm) ∧
           ∀vm x x' t'.
             r_ivl_aux r vm x (x'::t') =
             RM r (varmap_find x vm) (r_ivl_aux r vm x' t')

   [monom_insert_def]  Theorem

      |- ∀r.
           (∀t2 l2 l1 c2 c1.
              r_monom_insert r c1 l1 (Cons_monom c2 l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_monom c1 l1 (Cons_monom c2 l2 t2))
                (Cons_monom (RP r c1 c2) l1 t2)
                (Cons_monom c2 l2 (r_monom_insert r c1 l1 t2))) ∧
           (∀t2 l2 l1 c1.
              r_monom_insert r c1 l1 (Cons_varlist l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_monom c1 l1 (Cons_varlist l2 t2))
                (Cons_monom (RP r c1 (R1 r)) l1 t2)
                (Cons_varlist l2 (r_monom_insert r c1 l1 t2))) ∧
           ∀l1 c1.
             r_monom_insert r c1 l1 Nil_monom = Cons_monom c1 l1 Nil_monom

   [polynom_11]  Theorem

      |- (∀a a'. (Pvar a = Pvar a') ⇔ (a = a')) ∧
         (∀a a'. (Pconst a = Pconst a') ⇔ (a = a')) ∧
         (∀a0 a1 a0' a1'.
            (Pplus a0 a1 = Pplus a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         (∀a0 a1 a0' a1'.
            (Pmult a0 a1 = Pmult a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         ∀a a'. (Popp a = Popp a') ⇔ (a = a')

   [polynom_Axiom]  Theorem

      |- ∀f0 f1 f2 f3 f4.
           ∃fn.
             (∀a. fn (Pvar a) = f0 a) ∧ (∀a. fn (Pconst a) = f1 a) ∧
             (∀a0 a1. fn (Pplus a0 a1) = f2 a0 a1 (fn a0) (fn a1)) ∧
             (∀a0 a1. fn (Pmult a0 a1) = f3 a0 a1 (fn a0) (fn a1)) ∧
             ∀a. fn (Popp a) = f4 a (fn a)

   [polynom_case_cong]  Theorem

      |- ∀M M' f f1 f2 f3 f4.
           (M = M') ∧ (∀a. (M' = Pvar a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Pconst a) ⇒ (f1 a = f1' a)) ∧
           (∀a0 a1. (M' = Pplus a0 a1) ⇒ (f2 a0 a1 = f2' a0 a1)) ∧
           (∀a0 a1. (M' = Pmult a0 a1) ⇒ (f3 a0 a1 = f3' a0 a1)) ∧
           (∀a. (M' = Popp a) ⇒ (f4 a = f4' a)) ⇒
           (polynom_CASE M f f1 f2 f3 f4 =
            polynom_CASE M' f' f1' f2' f3' f4')

   [polynom_distinct]  Theorem

      |- (∀a' a. Pvar a ≠ Pconst a') ∧ (∀a1 a0 a. Pvar a ≠ Pplus a0 a1) ∧
         (∀a1 a0 a. Pvar a ≠ Pmult a0 a1) ∧ (∀a' a. Pvar a ≠ Popp a') ∧
         (∀a1 a0 a. Pconst a ≠ Pplus a0 a1) ∧
         (∀a1 a0 a. Pconst a ≠ Pmult a0 a1) ∧ (∀a' a. Pconst a ≠ Popp a') ∧
         (∀a1' a1 a0' a0. Pplus a0 a1 ≠ Pmult a0' a1') ∧
         (∀a1 a0 a. Pplus a0 a1 ≠ Popp a) ∧ ∀a1 a0 a. Pmult a0 a1 ≠ Popp a

   [polynom_induction]  Theorem

      |- ∀P.
           (∀i. P (Pvar i)) ∧ (∀a. P (Pconst a)) ∧
           (∀p p0. P p ∧ P p0 ⇒ P (Pplus p p0)) ∧
           (∀p p0. P p ∧ P p0 ⇒ P (Pmult p p0)) ∧ (∀p. P p ⇒ P (Popp p)) ⇒
           ∀p. P p

   [polynom_nchotomy]  Theorem

      |- ∀pp.
           (∃i. pp = Pvar i) ∨ (∃a. pp = Pconst a) ∨
           (∃p p0. pp = Pplus p p0) ∨ (∃p p0. pp = Pmult p p0) ∨
           ∃p. pp = Popp p

   [polynom_normalize_ok]  Theorem

      |- ∀r.
           is_ring r ⇒
           ∀vm p.
             r_interp_cs r vm (polynom_normalize r p) = interp_p r vm p

   [polynom_simplify_ok]  Theorem

      |- ∀r.
           is_ring r ⇒
           ∀vm p. r_interp_cs r vm (polynom_simplify r p) = interp_p r vm p

   [spolynom_normalize_def]  Theorem

      |- ∀r.
           (∀i.
              r_spolynom_normalize r (SPvar i) =
              Cons_varlist [i] Nil_monom) ∧
           (∀c.
              r_spolynom_normalize r (SPconst c) =
              Cons_monom c [] Nil_monom) ∧
           (∀l r'.
              r_spolynom_normalize r (SPplus l r') =
              r_canonical_sum_merge r (r_spolynom_normalize r l)
                (r_spolynom_normalize r r')) ∧
           ∀l r'.
             r_spolynom_normalize r (SPmult l r') =
             r_canonical_sum_prod r (r_spolynom_normalize r l)
               (r_spolynom_normalize r r')

   [spolynom_simplify_def]  Theorem

      |- ∀r x.
           r_spolynom_simplify r x =
           r_canonical_sum_simplify r (r_spolynom_normalize r x)

   [varlist_insert_def]  Theorem

      |- ∀r.
           (∀t2 l2 l1 c2.
              r_varlist_insert r l1 (Cons_monom c2 l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_varlist l1 (Cons_monom c2 l2 t2))
                (Cons_monom (RP r (R1 r) c2) l1 t2)
                (Cons_monom c2 l2 (r_varlist_insert r l1 t2))) ∧
           (∀t2 l2 l1.
              r_varlist_insert r l1 (Cons_varlist l2 t2) =
              compare (list_compare index_compare l1 l2)
                (Cons_varlist l1 (Cons_varlist l2 t2))
                (Cons_monom (RP r (R1 r) (R1 r)) l1 t2)
                (Cons_varlist l2 (r_varlist_insert r l1 t2))) ∧
           ∀l1. r_varlist_insert r l1 Nil_monom = Cons_varlist l1 Nil_monom


*)
end
