signature canonicalTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val canonical_sum_TY_DEF : thm
    val canonical_sum_case_def : thm
    val canonical_sum_merge_curried_def : thm
    val canonical_sum_merge_tupled_primitive_def : thm
    val canonical_sum_prod_def : thm
    val canonical_sum_repfns : thm
    val canonical_sum_scalar2_def : thm
    val canonical_sum_scalar3_def : thm
    val canonical_sum_scalar_def : thm
    val canonical_sum_simplify_def : thm
    val canonical_sum_size_def : thm
    val ics_aux_def : thm
    val interp_cs_def : thm
    val interp_m_def : thm
    val interp_sp_def : thm
    val interp_vl_def : thm
    val ivl_aux_def : thm
    val monom_insert_curried_def : thm
    val monom_insert_tupled_primitive_def : thm
    val spolynom_TY_DEF : thm
    val spolynom_case_def : thm
    val spolynom_normalize_def : thm
    val spolynom_repfns : thm
    val spolynom_simplify_def : thm
    val spolynom_size_def : thm
    val varlist_insert_curried_def : thm
    val varlist_insert_tupled_primitive_def : thm
  
  (*  Theorems  *)
    val canonical_sum_11 : thm
    val canonical_sum_Axiom : thm
    val canonical_sum_case_cong : thm
    val canonical_sum_distinct : thm
    val canonical_sum_induction : thm
    val canonical_sum_merge_def : thm
    val canonical_sum_merge_ind : thm
    val canonical_sum_merge_ok : thm
    val canonical_sum_nchotomy : thm
    val canonical_sum_prod_ok : thm
    val canonical_sum_scalar2_ok : thm
    val canonical_sum_scalar3_ok : thm
    val canonical_sum_scalar_ok : thm
    val canonical_sum_simplify_ok : thm
    val datatype_canonical_sum : thm
    val datatype_spolynom : thm
    val ics_aux_ok : thm
    val interp_m_ok : thm
    val ivl_aux_ok : thm
    val monom_insert_def : thm
    val monom_insert_ind : thm
    val monom_insert_ok : thm
    val spolynom_11 : thm
    val spolynom_Axiom : thm
    val spolynom_case_cong : thm
    val spolynom_distinct : thm
    val spolynom_induction : thm
    val spolynom_nchotomy : thm
    val spolynomial_normalize_ok : thm
    val spolynomial_simplify_ok : thm
    val varlist_insert_def : thm
    val varlist_insert_ind : thm
    val varlist_insert_ok : thm
    val varlist_merge_ok : thm
  
  val canonical_grammars : type_grammar.grammar * term_grammar.grammar
  
  val IMPORT : abstraction.inst_infos ->
    { interp_sp_def : thm,
      spolynom_simplify_def : thm,
      spolynom_normalize_def : thm,
      spolynom_size_def : thm,
      spolynom_case_def : thm,
      spolynom_repfns : thm,
      spolynom_TY_DEF : thm,
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
      varlist_insert_curried_def : thm,
      varlist_insert_tupled_primitive_def : thm,
      monom_insert_curried_def : thm,
      monom_insert_tupled_primitive_def : thm,
      canonical_sum_merge_curried_def : thm,
      canonical_sum_merge_tupled_primitive_def : thm,
      canonical_sum_size_def : thm,
      canonical_sum_case_def : thm,
      canonical_sum_repfns : thm,
      canonical_sum_TY_DEF : thm,
      spolynomial_simplify_ok : thm,
      spolynomial_normalize_ok : thm,
      spolynom_induction : thm,
      spolynom_Axiom : thm,
      spolynom_nchotomy : thm,
      spolynom_case_cong : thm,
      spolynom_distinct : thm,
      spolynom_11 : thm,
      datatype_spolynom : thm,
      canonical_sum_simplify_ok : thm,
      canonical_sum_prod_ok : thm,
      canonical_sum_scalar3_ok : thm,
      canonical_sum_scalar2_ok : thm,
      canonical_sum_scalar_ok : thm,
      varlist_insert_ok : thm,
      monom_insert_ok : thm,
      canonical_sum_merge_ok : thm,
      interp_m_ok : thm,
      ics_aux_ok : thm,
      varlist_merge_ok : thm,
      ivl_aux_ok : thm,
      varlist_insert_def : thm,
      varlist_insert_ind : thm,
      monom_insert_def : thm,
      monom_insert_ind : thm,
      canonical_sum_merge_def : thm,
      canonical_sum_merge_ind : thm,
      canonical_sum_induction : thm,
      canonical_sum_Axiom : thm,
      canonical_sum_nchotomy : thm,
      canonical_sum_case_cong : thm,
      canonical_sum_distinct : thm,
      canonical_sum_11 : thm,
      datatype_canonical_sum : thm }
  
(*
   [quote] Parent theory of "canonical"
   
   [semi_ring] Parent theory of "canonical"
   
   [canonical_sum_TY_DEF]  Definition
      
      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'canonical_sum' .
                  (∀a0'.
                     (a0' = ind_type$CONSTR 0 (ARB,ARB) (λn. ind_type$BOTTOM)) ∨
                     (∃a0 a1 a2.
                        (a0' =
                         (λa0 a1 a2.
                            ind_type$CONSTR (SUC 0) (a0,a1)
                              (ind_type$FCONS a2 (λn. ind_type$BOTTOM))) a0 a1 a2) ∧
                        'canonical_sum' a2) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC 0)) (ARB,a0)
                              (ind_type$FCONS a1 (λn. ind_type$BOTTOM))) a0 a1) ∧
                        'canonical_sum' a1) ⇒
                     'canonical_sum' a0') ⇒
                  'canonical_sum' a0') rep
   
   [canonical_sum_case_def]  Definition
      
      |- (∀v f f1. canonical_sum_case v f f1 Nil_monom = v) ∧
         (∀v f f1 a0 a1 a2.
            canonical_sum_case v f f1 (Cons_monom a0 a1 a2) = f a0 a1 a2) ∧
         ∀v f f1 a0 a1. canonical_sum_case v f f1 (Cons_varlist a0 a1) = f1 a0 a1
   
   [canonical_sum_merge_curried_def]  Definition
      
      |- ∀x x1 x2. canonical_sum_merge x x1 x2 = canonical_sum_merge_tupled (x,x1,x2)
   
   [canonical_sum_merge_tupled_primitive_def]  Definition
      
      |- canonical_sum_merge_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀l2 c2 t2 t1 l1 c1 sr.
                 R (sr,Cons_monom c1 l1 t1,t2)
                   (sr,Cons_monom c1 l1 t1,Cons_monom c2 l2 t2)) ∧
              (∀l1 c1 t2 l2 c2 t1 sr.
                 R (sr,t1,Cons_monom c2 l2 t2)
                   (sr,Cons_monom c1 l1 t1,Cons_monom c2 l2 t2)) ∧
              (∀l2 c2 l1 c1 t2 t1 sr.
                 R (sr,t1,t2) (sr,Cons_monom c1 l1 t1,Cons_monom c2 l2 t2)) ∧
              (∀l2 t2 t1 l1 c1 sr.
                 R (sr,Cons_monom c1 l1 t1,t2)
                   (sr,Cons_monom c1 l1 t1,Cons_varlist l2 t2)) ∧
              (∀l1 c1 t2 l2 t1 sr.
                 R (sr,t1,Cons_varlist l2 t2)
                   (sr,Cons_monom c1 l1 t1,Cons_varlist l2 t2)) ∧
              (∀l2 l1 c1 t2 t1 sr.
                 R (sr,t1,t2) (sr,Cons_monom c1 l1 t1,Cons_varlist l2 t2)) ∧
              (∀l2 c2 t2 t1 l1 sr.
                 R (sr,Cons_varlist l1 t1,t2)
                   (sr,Cons_varlist l1 t1,Cons_monom c2 l2 t2)) ∧
              (∀l1 t2 l2 c2 t1 sr.
                 R (sr,t1,Cons_monom c2 l2 t2)
                   (sr,Cons_varlist l1 t1,Cons_monom c2 l2 t2)) ∧
              (∀l2 c2 l1 t2 t1 sr.
                 R (sr,t1,t2) (sr,Cons_varlist l1 t1,Cons_monom c2 l2 t2)) ∧
              (∀l2 l1 t2 t1 sr.
                 R (sr,t1,t2) (sr,Cons_varlist l1 t1,Cons_varlist l2 t2)) ∧
              (∀l1 t2 l2 t1 sr.
                 R (sr,t1,Cons_varlist l2 t2)
                   (sr,Cons_varlist l1 t1,Cons_varlist l2 t2)) ∧
              ∀l2 t2 t1 l1 sr.
                R (sr,Cons_varlist l1 t1,t2)
                  (sr,Cons_varlist l1 t1,Cons_varlist l2 t2))
           (λcanonical_sum_merge_tupled a.
              case a of
                 (sr,Nil_monom,Nil_monom) -> I Nil_monom
              || (sr,Nil_monom,Cons_monom v19 v20 v21) -> I (Cons_monom v19 v20 v21)
              || (sr,Nil_monom,Cons_varlist v22 v23) -> I (Cons_varlist v22 v23)
              || (sr,Cons_monom c1 l1 t1,Nil_monom) -> I (Cons_monom c1 l1 t1)
              || (sr,Cons_monom c1 l1 t1,Cons_monom c2 l2 t2) ->
                   I
                     (compare (list_compare index_compare l1 l2)
                        (Cons_monom c1 l1
                           (canonical_sum_merge_tupled (sr,t1,Cons_monom c2 l2 t2)))
                        (Cons_monom (SRP sr c1 c2) l1
                           (canonical_sum_merge_tupled (sr,t1,t2)))
                        (Cons_monom c2 l2
                           (canonical_sum_merge_tupled (sr,Cons_monom c1 l1 t1,t2))))
              || (sr,Cons_monom c1 l1 t1,Cons_varlist l2' t2') ->
                   I
                     (compare (list_compare index_compare l1 l2')
                        (Cons_monom c1 l1
                           (canonical_sum_merge_tupled (sr,t1,Cons_varlist l2' t2')))
                        (Cons_monom (SRP sr c1 (SR1 sr)) l1
                           (canonical_sum_merge_tupled (sr,t1,t2')))
                        (Cons_varlist l2'
                           (canonical_sum_merge_tupled
                              (sr,Cons_monom c1 l1 t1,t2'))))
              || (sr,Cons_varlist l1' t1',Nil_monom) -> I (Cons_varlist l1' t1')
              || (sr,Cons_varlist l1' t1',Cons_monom c2' l2'' t2'') ->
                   I
                     (compare (list_compare index_compare l1' l2'')
                        (Cons_varlist l1'
                           (canonical_sum_merge_tupled
                              (sr,t1',Cons_monom c2' l2'' t2'')))
                        (Cons_monom (SRP sr (SR1 sr) c2') l1'
                           (canonical_sum_merge_tupled (sr,t1',t2'')))
                        (Cons_monom c2' l2''
                           (canonical_sum_merge_tupled
                              (sr,Cons_varlist l1' t1',t2''))))
              || (sr,Cons_varlist l1' t1',Cons_varlist l2''' t2''') ->
                   I
                     (compare (list_compare index_compare l1' l2''')
                        (Cons_varlist l1'
                           (canonical_sum_merge_tupled
                              (sr,t1',Cons_varlist l2''' t2''')))
                        (Cons_monom (SRP sr (SR1 sr) (SR1 sr)) l1'
                           (canonical_sum_merge_tupled (sr,t1',t2''')))
                        (Cons_varlist l2'''
                           (canonical_sum_merge_tupled
                              (sr,Cons_varlist l1' t1',t2''')))))
   
   [canonical_sum_prod_def]  Definition
      
      |- (∀sr c1 l1 t1 s2.
            canonical_sum_prod sr (Cons_monom c1 l1 t1) s2 =
            canonical_sum_merge sr (canonical_sum_scalar3 sr c1 l1 s2)
              (canonical_sum_prod sr t1 s2)) ∧
         (∀sr l1 t1 s2.
            canonical_sum_prod sr (Cons_varlist l1 t1) s2 =
            canonical_sum_merge sr (canonical_sum_scalar2 sr l1 s2)
              (canonical_sum_prod sr t1 s2)) ∧
         ∀sr s2. canonical_sum_prod sr Nil_monom s2 = Nil_monom
   
   [canonical_sum_repfns]  Definition
      
      |- (∀a. mk_canonical_sum (dest_canonical_sum a) = a) ∧
         ∀r.
           (λa0'.
              ∀'canonical_sum' .
                (∀a0'.
                   (a0' = ind_type$CONSTR 0 (ARB,ARB) (λn. ind_type$BOTTOM)) ∨
                   (∃a0 a1 a2.
                      (a0' =
                       (λa0 a1 a2.
                          ind_type$CONSTR (SUC 0) (a0,a1)
                            (ind_type$FCONS a2 (λn. ind_type$BOTTOM))) a0 a1 a2) ∧
                      'canonical_sum' a2) ∨
                   (∃a0 a1.
                      (a0' =
                       (λa0 a1.
                          ind_type$CONSTR (SUC (SUC 0)) (ARB,a0)
                            (ind_type$FCONS a1 (λn. ind_type$BOTTOM))) a0 a1) ∧
                      'canonical_sum' a1) ⇒
                   'canonical_sum' a0') ⇒
                'canonical_sum' a0') r ⇔
           (dest_canonical_sum (mk_canonical_sum r) = r)
   
   [canonical_sum_scalar2_def]  Definition
      
      |- (∀sr l0 c l t.
            canonical_sum_scalar2 sr l0 (Cons_monom c l t) =
            monom_insert sr c (list_merge index_lt l0 l)
              (canonical_sum_scalar2 sr l0 t)) ∧
         (∀sr l0 l t.
            canonical_sum_scalar2 sr l0 (Cons_varlist l t) =
            varlist_insert sr (list_merge index_lt l0 l)
              (canonical_sum_scalar2 sr l0 t)) ∧
         ∀sr l0. canonical_sum_scalar2 sr l0 Nil_monom = Nil_monom
   
   [canonical_sum_scalar3_def]  Definition
      
      |- (∀sr c0 l0 c l t.
            canonical_sum_scalar3 sr c0 l0 (Cons_monom c l t) =
            monom_insert sr (SRM sr c0 c) (list_merge index_lt l0 l)
              (canonical_sum_scalar3 sr c0 l0 t)) ∧
         (∀sr c0 l0 l t.
            canonical_sum_scalar3 sr c0 l0 (Cons_varlist l t) =
            monom_insert sr c0 (list_merge index_lt l0 l)
              (canonical_sum_scalar3 sr c0 l0 t)) ∧
         ∀sr c0 l0. canonical_sum_scalar3 sr c0 l0 Nil_monom = Nil_monom
   
   [canonical_sum_scalar_def]  Definition
      
      |- (∀sr c0 c l t.
            canonical_sum_scalar sr c0 (Cons_monom c l t) =
            Cons_monom (SRM sr c0 c) l (canonical_sum_scalar sr c0 t)) ∧
         (∀sr c0 l t.
            canonical_sum_scalar sr c0 (Cons_varlist l t) =
            Cons_monom c0 l (canonical_sum_scalar sr c0 t)) ∧
         ∀sr c0. canonical_sum_scalar sr c0 Nil_monom = Nil_monom
   
   [canonical_sum_simplify_def]  Definition
      
      |- (∀sr c l t.
            canonical_sum_simplify sr (Cons_monom c l t) =
            if c = SR0 sr then
              canonical_sum_simplify sr t
            else if c = SR1 sr then
              Cons_varlist l (canonical_sum_simplify sr t)
            else
              Cons_monom c l (canonical_sum_simplify sr t)) ∧
         (∀sr l t.
            canonical_sum_simplify sr (Cons_varlist l t) =
            Cons_varlist l (canonical_sum_simplify sr t)) ∧
         ∀sr. canonical_sum_simplify sr Nil_monom = Nil_monom
   
   [canonical_sum_size_def]  Definition
      
      |- (∀f. canonical_sum_size f Nil_monom = 0) ∧
         (∀f a0 a1 a2.
            canonical_sum_size f (Cons_monom a0 a1 a2) =
            1 + (f a0 + (list_size index_size a1 + canonical_sum_size f a2))) ∧
         ∀f a0 a1.
           canonical_sum_size f (Cons_varlist a0 a1) =
           1 + (list_size index_size a0 + canonical_sum_size f a1)
   
   [ics_aux_def]  Definition
      
      |- (∀sr vm a. ics_aux sr vm a Nil_monom = a) ∧
         (∀sr vm a l t.
            ics_aux sr vm a (Cons_varlist l t) =
            SRP sr a (ics_aux sr vm (interp_vl sr vm l) t)) ∧
         ∀sr vm a c l t.
           ics_aux sr vm a (Cons_monom c l t) =
           SRP sr a (ics_aux sr vm (interp_m sr vm c l) t)
   
   [interp_cs_def]  Definition
      
      |- (∀sr vm. interp_cs sr vm Nil_monom = SR0 sr) ∧
         (∀sr vm l t.
            interp_cs sr vm (Cons_varlist l t) =
            ics_aux sr vm (interp_vl sr vm l) t) ∧
         ∀sr vm c l t.
           interp_cs sr vm (Cons_monom c l t) = ics_aux sr vm (interp_m sr vm c l) t
   
   [interp_m_def]  Definition
      
      |- (∀sr vm c. interp_m sr vm c [] = c) ∧
         ∀sr vm c x t. interp_m sr vm c (x::t) = SRM sr c (ivl_aux sr vm x t)
   
   [interp_sp_def]  Definition
      
      |- (∀sr vm c. interp_sp sr vm (SPconst c) = c) ∧
         (∀sr vm i. interp_sp sr vm (SPvar i) = varmap_find i vm) ∧
         (∀sr vm p1 p2.
            interp_sp sr vm (SPplus p1 p2) =
            SRP sr (interp_sp sr vm p1) (interp_sp sr vm p2)) ∧
         ∀sr vm p1 p2.
           interp_sp sr vm (SPmult p1 p2) =
           SRM sr (interp_sp sr vm p1) (interp_sp sr vm p2)
   
   [interp_vl_def]  Definition
      
      |- (∀sr vm. interp_vl sr vm [] = SR1 sr) ∧
         ∀sr vm x t. interp_vl sr vm (x::t) = ivl_aux sr vm x t
   
   [ivl_aux_def]  Definition
      
      |- (∀sr vm x. ivl_aux sr vm x [] = varmap_find x vm) ∧
         ∀sr vm x x' t'.
           ivl_aux sr vm x (x'::t') = SRM sr (varmap_find x vm) (ivl_aux sr vm x' t')
   
   [monom_insert_curried_def]  Definition
      
      |- ∀x x1 x2 x3. monom_insert x x1 x2 x3 = monom_insert_tupled (x,x1,x2,x3)
   
   [monom_insert_tupled_primitive_def]  Definition
      
      |- monom_insert_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀l2 c2 t2 l1 c1 sr. R (sr,c1,l1,t2) (sr,c1,l1,Cons_monom c2 l2 t2)) ∧
              ∀l2 t2 l1 c1 sr. R (sr,c1,l1,t2) (sr,c1,l1,Cons_varlist l2 t2))
           (λmonom_insert_tupled a.
              case a of
                 (sr,c1,l1,Nil_monom) -> I (Cons_monom c1 l1 Nil_monom)
              || (sr,c1,l1,Cons_monom c2 l2 t2) ->
                   I
                     (compare (list_compare index_compare l1 l2)
                        (Cons_monom c1 l1 (Cons_monom c2 l2 t2))
                        (Cons_monom (SRP sr c1 c2) l1 t2)
                        (Cons_monom c2 l2 (monom_insert_tupled (sr,c1,l1,t2))))
              || (sr,c1,l1,Cons_varlist l2' t2') ->
                   I
                     (compare (list_compare index_compare l1 l2')
                        (Cons_monom c1 l1 (Cons_varlist l2' t2'))
                        (Cons_monom (SRP sr c1 (SR1 sr)) l1 t2')
                        (Cons_varlist l2' (monom_insert_tupled (sr,c1,l1,t2')))))
   
   [spolynom_TY_DEF]  Definition
      
      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'spolynom' .
                  (∀a0'.
                     (∃a.
                        a0' =
                        (λa. ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0' =
                        (λa. ind_type$CONSTR (SUC 0) (ARB,a) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB)
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'spolynom' a0 ∧ 'spolynom' a1) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC (SUC 0))) (ARB,ARB)
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'spolynom' a0 ∧ 'spolynom' a1) ⇒
                     'spolynom' a0') ⇒
                  'spolynom' a0') rep
   
   [spolynom_case_def]  Definition
      
      |- (∀f f1 f2 f3 a. spolynom_case f f1 f2 f3 (SPvar a) = f a) ∧
         (∀f f1 f2 f3 a. spolynom_case f f1 f2 f3 (SPconst a) = f1 a) ∧
         (∀f f1 f2 f3 a0 a1. spolynom_case f f1 f2 f3 (SPplus a0 a1) = f2 a0 a1) ∧
         ∀f f1 f2 f3 a0 a1. spolynom_case f f1 f2 f3 (SPmult a0 a1) = f3 a0 a1
   
   [spolynom_normalize_def]  Definition
      
      |- (∀sr i. spolynom_normalize sr (SPvar i) = Cons_varlist [i] Nil_monom) ∧
         (∀sr c. spolynom_normalize sr (SPconst c) = Cons_monom c [] Nil_monom) ∧
         (∀sr l r.
            spolynom_normalize sr (SPplus l r) =
            canonical_sum_merge sr (spolynom_normalize sr l)
              (spolynom_normalize sr r)) ∧
         ∀sr l r.
           spolynom_normalize sr (SPmult l r) =
           canonical_sum_prod sr (spolynom_normalize sr l) (spolynom_normalize sr r)
   
   [spolynom_repfns]  Definition
      
      |- (∀a. mk_spolynom (dest_spolynom a) = a) ∧
         ∀r.
           (λa0'.
              ∀'spolynom' .
                (∀a0'.
                   (∃a.
                      a0' =
                      (λa. ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                   (∃a.
                      a0' =
                      (λa. ind_type$CONSTR (SUC 0) (ARB,a) (λn. ind_type$BOTTOM))
                        a) ∨
                   (∃a0 a1.
                      (a0' =
                       (λa0 a1.
                          ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB)
                            (ind_type$FCONS a0
                               (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))) a0 a1) ∧
                      'spolynom' a0 ∧ 'spolynom' a1) ∨
                   (∃a0 a1.
                      (a0' =
                       (λa0 a1.
                          ind_type$CONSTR (SUC (SUC (SUC 0))) (ARB,ARB)
                            (ind_type$FCONS a0
                               (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))) a0 a1) ∧
                      'spolynom' a0 ∧ 'spolynom' a1) ⇒
                   'spolynom' a0') ⇒
                'spolynom' a0') r ⇔ (dest_spolynom (mk_spolynom r) = r)
   
   [spolynom_simplify_def]  Definition
      
      |- ∀sr x.
           spolynom_simplify sr x =
           canonical_sum_simplify sr (spolynom_normalize sr x)
   
   [spolynom_size_def]  Definition
      
      |- (∀f a. spolynom_size f (SPvar a) = 1 + index_size a) ∧
         (∀f a. spolynom_size f (SPconst a) = 1 + f a) ∧
         (∀f a0 a1.
            spolynom_size f (SPplus a0 a1) =
            1 + (spolynom_size f a0 + spolynom_size f a1)) ∧
         ∀f a0 a1.
           spolynom_size f (SPmult a0 a1) =
           1 + (spolynom_size f a0 + spolynom_size f a1)
   
   [varlist_insert_curried_def]  Definition
      
      |- ∀x x1 x2. varlist_insert x x1 x2 = varlist_insert_tupled (x,x1,x2)
   
   [varlist_insert_tupled_primitive_def]  Definition
      
      |- varlist_insert_tupled =
         WFREC
           (@R.
              WF R ∧ (∀l2 c2 t2 l1 sr. R (sr,l1,t2) (sr,l1,Cons_monom c2 l2 t2)) ∧
              ∀l2 t2 l1 sr. R (sr,l1,t2) (sr,l1,Cons_varlist l2 t2))
           (λvarlist_insert_tupled a.
              case a of
                 (sr,l1,Nil_monom) -> I (Cons_varlist l1 Nil_monom)
              || (sr,l1,Cons_monom c2 l2 t2) ->
                   I
                     (compare (list_compare index_compare l1 l2)
                        (Cons_varlist l1 (Cons_monom c2 l2 t2))
                        (Cons_monom (SRP sr (SR1 sr) c2) l1 t2)
                        (Cons_monom c2 l2 (varlist_insert_tupled (sr,l1,t2))))
              || (sr,l1,Cons_varlist l2' t2') ->
                   I
                     (compare (list_compare index_compare l1 l2')
                        (Cons_varlist l1 (Cons_varlist l2' t2'))
                        (Cons_monom (SRP sr (SR1 sr) (SR1 sr)) l1 t2')
                        (Cons_varlist l2' (varlist_insert_tupled (sr,l1,t2')))))
   
   [canonical_sum_11]  Theorem
      
      |- (∀a0 a1 a2 a0' a1' a2'.
            (Cons_monom a0 a1 a2 = Cons_monom a0' a1' a2') ⇔
            (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2')) ∧
         ∀a0 a1 a0' a1'.
           (Cons_varlist a0 a1 = Cons_varlist a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')
   
   [canonical_sum_Axiom]  Theorem
      
      |- ∀f0 f1 f2.
           ∃fn.
             (fn Nil_monom = f0) ∧
             (∀a0 a1 a2. fn (Cons_monom a0 a1 a2) = f1 a0 a1 a2 (fn a2)) ∧
             ∀a0 a1. fn (Cons_varlist a0 a1) = f2 a0 a1 (fn a1)
   
   [canonical_sum_case_cong]  Theorem
      
      |- ∀M M' v f f1.
           (M = M') ∧ ((M' = Nil_monom) ⇒ (v = v')) ∧
           (∀a0 a1 a2. (M' = Cons_monom a0 a1 a2) ⇒ (f a0 a1 a2 = f' a0 a1 a2)) ∧
           (∀a0 a1. (M' = Cons_varlist a0 a1) ⇒ (f1 a0 a1 = f1' a0 a1)) ⇒
           (canonical_sum_case v f f1 M = canonical_sum_case v' f' f1' M')
   
   [canonical_sum_distinct]  Theorem
      
      |- (∀a2 a1 a0. Nil_monom ≠ Cons_monom a0 a1 a2) ∧
         (∀a1 a0. Nil_monom ≠ Cons_varlist a0 a1) ∧
         ∀a2 a1' a1 a0' a0. Cons_monom a0 a1 a2 ≠ Cons_varlist a0' a1'
   
   [canonical_sum_induction]  Theorem
      
      |- ∀P.
           P Nil_monom ∧ (∀c. P c ⇒ ∀l a. P (Cons_monom a l c)) ∧
           (∀c. P c ⇒ ∀l. P (Cons_varlist l c)) ⇒
           ∀c. P c
   
   [canonical_sum_merge_def]  Theorem
      
      |- (∀t2 t1 sr l2 l1 c2 c1.
            canonical_sum_merge sr (Cons_monom c1 l1 t1) (Cons_monom c2 l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_monom c1 l1 (canonical_sum_merge sr t1 (Cons_monom c2 l2 t2)))
              (Cons_monom (SRP sr c1 c2) l1 (canonical_sum_merge sr t1 t2))
              (Cons_monom c2 l2 (canonical_sum_merge sr (Cons_monom c1 l1 t1) t2))) ∧
         (∀t2 t1 sr l2 l1 c1.
            canonical_sum_merge sr (Cons_monom c1 l1 t1) (Cons_varlist l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_monom c1 l1 (canonical_sum_merge sr t1 (Cons_varlist l2 t2)))
              (Cons_monom (SRP sr c1 (SR1 sr)) l1 (canonical_sum_merge sr t1 t2))
              (Cons_varlist l2 (canonical_sum_merge sr (Cons_monom c1 l1 t1) t2))) ∧
         (∀t2 t1 sr l2 l1 c2.
            canonical_sum_merge sr (Cons_varlist l1 t1) (Cons_monom c2 l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_varlist l1 (canonical_sum_merge sr t1 (Cons_monom c2 l2 t2)))
              (Cons_monom (SRP sr (SR1 sr) c2) l1 (canonical_sum_merge sr t1 t2))
              (Cons_monom c2 l2 (canonical_sum_merge sr (Cons_varlist l1 t1) t2))) ∧
         (∀t2 t1 sr l2 l1.
            canonical_sum_merge sr (Cons_varlist l1 t1) (Cons_varlist l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_varlist l1 (canonical_sum_merge sr t1 (Cons_varlist l2 t2)))
              (Cons_monom (SRP sr (SR1 sr) (SR1 sr)) l1
                 (canonical_sum_merge sr t1 t2))
              (Cons_varlist l2 (canonical_sum_merge sr (Cons_varlist l1 t1) t2))) ∧
         (∀sr. canonical_sum_merge sr Nil_monom Nil_monom = Nil_monom) ∧
         (∀v6 v5 v4 sr.
            canonical_sum_merge sr (Cons_monom v4 v5 v6) Nil_monom =
            Cons_monom v4 v5 v6) ∧
         (∀v8 v7 sr.
            canonical_sum_merge sr (Cons_varlist v7 v8) Nil_monom =
            Cons_varlist v7 v8) ∧
         (∀v16 v15 v14 sr.
            canonical_sum_merge sr Nil_monom (Cons_monom v14 v15 v16) =
            Cons_monom v14 v15 v16) ∧
         ∀v18 v17 sr.
           canonical_sum_merge sr Nil_monom (Cons_varlist v17 v18) =
           Cons_varlist v17 v18
   
   [canonical_sum_merge_ind]  Theorem
      
      |- ∀P.
           (∀sr c1 l1 t1 c2 l2 t2.
              P sr t1 t2 ∧ P sr t1 (Cons_monom c2 l2 t2) ∧
              P sr (Cons_monom c1 l1 t1) t2 ⇒
              P sr (Cons_monom c1 l1 t1) (Cons_monom c2 l2 t2)) ∧
           (∀sr c1 l1 t1 l2 t2.
              P sr t1 t2 ∧ P sr t1 (Cons_varlist l2 t2) ∧
              P sr (Cons_monom c1 l1 t1) t2 ⇒
              P sr (Cons_monom c1 l1 t1) (Cons_varlist l2 t2)) ∧
           (∀sr l1 t1 c2 l2 t2.
              P sr t1 t2 ∧ P sr t1 (Cons_monom c2 l2 t2) ∧
              P sr (Cons_varlist l1 t1) t2 ⇒
              P sr (Cons_varlist l1 t1) (Cons_monom c2 l2 t2)) ∧
           (∀sr l1 t1 l2 t2.
              P sr t1 t2 ∧ P sr t1 (Cons_varlist l2 t2) ∧
              P sr (Cons_varlist l1 t1) t2 ⇒
              P sr (Cons_varlist l1 t1) (Cons_varlist l2 t2)) ∧
           (∀sr. P sr Nil_monom Nil_monom) ∧
           (∀sr v4 v5 v6. P sr (Cons_monom v4 v5 v6) Nil_monom) ∧
           (∀sr v7 v8. P sr (Cons_varlist v7 v8) Nil_monom) ∧
           (∀sr v14 v15 v16. P sr Nil_monom (Cons_monom v14 v15 v16)) ∧
           (∀sr v17 v18. P sr Nil_monom (Cons_varlist v17 v18)) ⇒
           ∀v v1 v2. P v v1 v2
   
   [canonical_sum_merge_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm x y.
             interp_cs sr vm (canonical_sum_merge sr x y) =
             SRP sr (interp_cs sr vm x) (interp_cs sr vm y)
   
   [canonical_sum_nchotomy]  Theorem
      
      |- ∀cc.
           (cc = Nil_monom) ∨ (∃a l c. cc = Cons_monom a l c) ∨
           ∃l c. cc = Cons_varlist l c
   
   [canonical_sum_prod_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm x y.
             interp_cs sr vm (canonical_sum_prod sr x y) =
             SRM sr (interp_cs sr vm x) (interp_cs sr vm y)
   
   [canonical_sum_scalar2_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm l s.
             interp_cs sr vm (canonical_sum_scalar2 sr l s) =
             SRM sr (interp_vl sr vm l) (interp_cs sr vm s)
   
   [canonical_sum_scalar3_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm c l s.
             interp_cs sr vm (canonical_sum_scalar3 sr c l s) =
             SRM sr (SRM sr c (interp_vl sr vm l)) (interp_cs sr vm s)
   
   [canonical_sum_scalar_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm a s.
             interp_cs sr vm (canonical_sum_scalar sr a s) =
             SRM sr a (interp_cs sr vm s)
   
   [canonical_sum_simplify_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm s. interp_cs sr vm (canonical_sum_simplify sr s) = interp_cs sr vm s
   
   [datatype_canonical_sum]  Theorem
      
      |- DATATYPE (canonical_sum Nil_monom Cons_monom Cons_varlist)
   
   [datatype_spolynom]  Theorem
      
      |- DATATYPE (spolynom SPvar SPconst SPplus SPmult)
   
   [ics_aux_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm x s. ics_aux sr vm x s = SRP sr x (interp_cs sr vm s)
   
   [interp_m_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm x l. interp_m sr vm x l = SRM sr x (interp_vl sr vm l)
   
   [ivl_aux_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm v i. ivl_aux sr vm i v = SRM sr (varmap_find i vm) (interp_vl sr vm v)
   
   [monom_insert_def]  Theorem
      
      |- (∀t2 sr l2 l1 c2 c1.
            monom_insert sr c1 l1 (Cons_monom c2 l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_monom c1 l1 (Cons_monom c2 l2 t2))
              (Cons_monom (SRP sr c1 c2) l1 t2)
              (Cons_monom c2 l2 (monom_insert sr c1 l1 t2))) ∧
         (∀t2 sr l2 l1 c1.
            monom_insert sr c1 l1 (Cons_varlist l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_monom c1 l1 (Cons_varlist l2 t2))
              (Cons_monom (SRP sr c1 (SR1 sr)) l1 t2)
              (Cons_varlist l2 (monom_insert sr c1 l1 t2))) ∧
         ∀sr l1 c1. monom_insert sr c1 l1 Nil_monom = Cons_monom c1 l1 Nil_monom
   
   [monom_insert_ind]  Theorem
      
      |- ∀P.
           (∀sr c1 l1 c2 l2 t2. P sr c1 l1 t2 ⇒ P sr c1 l1 (Cons_monom c2 l2 t2)) ∧
           (∀sr c1 l1 l2 t2. P sr c1 l1 t2 ⇒ P sr c1 l1 (Cons_varlist l2 t2)) ∧
           (∀sr c1 l1. P sr c1 l1 Nil_monom) ⇒
           ∀v v1 v2 v3. P v v1 v2 v3
   
   [monom_insert_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm a l s.
             interp_cs sr vm (monom_insert sr a l s) =
             SRP sr (SRM sr a (interp_vl sr vm l)) (interp_cs sr vm s)
   
   [spolynom_11]  Theorem
      
      |- (∀a a'. (SPvar a = SPvar a') ⇔ (a = a')) ∧
         (∀a a'. (SPconst a = SPconst a') ⇔ (a = a')) ∧
         (∀a0 a1 a0' a1'.
            (SPplus a0 a1 = SPplus a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         ∀a0 a1 a0' a1'. (SPmult a0 a1 = SPmult a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')
   
   [spolynom_Axiom]  Theorem
      
      |- ∀f0 f1 f2 f3.
           ∃fn.
             (∀a. fn (SPvar a) = f0 a) ∧ (∀a. fn (SPconst a) = f1 a) ∧
             (∀a0 a1. fn (SPplus a0 a1) = f2 a0 a1 (fn a0) (fn a1)) ∧
             ∀a0 a1. fn (SPmult a0 a1) = f3 a0 a1 (fn a0) (fn a1)
   
   [spolynom_case_cong]  Theorem
      
      |- ∀M M' f f1 f2 f3.
           (M = M') ∧ (∀a. (M' = SPvar a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = SPconst a) ⇒ (f1 a = f1' a)) ∧
           (∀a0 a1. (M' = SPplus a0 a1) ⇒ (f2 a0 a1 = f2' a0 a1)) ∧
           (∀a0 a1. (M' = SPmult a0 a1) ⇒ (f3 a0 a1 = f3' a0 a1)) ⇒
           (spolynom_case f f1 f2 f3 M = spolynom_case f' f1' f2' f3' M')
   
   [spolynom_distinct]  Theorem
      
      |- (∀a' a. SPvar a ≠ SPconst a') ∧ (∀a1 a0 a. SPvar a ≠ SPplus a0 a1) ∧
         (∀a1 a0 a. SPvar a ≠ SPmult a0 a1) ∧ (∀a1 a0 a. SPconst a ≠ SPplus a0 a1) ∧
         (∀a1 a0 a. SPconst a ≠ SPmult a0 a1) ∧
         ∀a1' a1 a0' a0. SPplus a0 a1 ≠ SPmult a0' a1'
   
   [spolynom_induction]  Theorem
      
      |- ∀P.
           (∀i. P (SPvar i)) ∧ (∀a. P (SPconst a)) ∧
           (∀s s0. P s ∧ P s0 ⇒ P (SPplus s s0)) ∧
           (∀s s0. P s ∧ P s0 ⇒ P (SPmult s s0)) ⇒
           ∀s. P s
   
   [spolynom_nchotomy]  Theorem
      
      |- ∀ss.
           (∃i. ss = SPvar i) ∨ (∃a. ss = SPconst a) ∨ (∃s s0. ss = SPplus s s0) ∨
           ∃s s0. ss = SPmult s s0
   
   [spolynomial_normalize_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm p. interp_cs sr vm (spolynom_normalize sr p) = interp_sp sr vm p
   
   [spolynomial_simplify_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm p. interp_cs sr vm (spolynom_simplify sr p) = interp_sp sr vm p
   
   [varlist_insert_def]  Theorem
      
      |- (∀t2 sr l2 l1 c2.
            varlist_insert sr l1 (Cons_monom c2 l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_varlist l1 (Cons_monom c2 l2 t2))
              (Cons_monom (SRP sr (SR1 sr) c2) l1 t2)
              (Cons_monom c2 l2 (varlist_insert sr l1 t2))) ∧
         (∀t2 sr l2 l1.
            varlist_insert sr l1 (Cons_varlist l2 t2) =
            compare (list_compare index_compare l1 l2)
              (Cons_varlist l1 (Cons_varlist l2 t2))
              (Cons_monom (SRP sr (SR1 sr) (SR1 sr)) l1 t2)
              (Cons_varlist l2 (varlist_insert sr l1 t2))) ∧
         ∀sr l1. varlist_insert sr l1 Nil_monom = Cons_varlist l1 Nil_monom
   
   [varlist_insert_ind]  Theorem
      
      |- ∀P.
           (∀sr l1 c2 l2 t2. P sr l1 t2 ⇒ P sr l1 (Cons_monom c2 l2 t2)) ∧
           (∀sr l1 l2 t2. P sr l1 t2 ⇒ P sr l1 (Cons_varlist l2 t2)) ∧
           (∀sr l1. P sr l1 Nil_monom) ⇒
           ∀v v1 v2. P v v1 v2
   
   [varlist_insert_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm l s.
             interp_cs sr vm (varlist_insert sr l s) =
             SRP sr (interp_vl sr vm l) (interp_cs sr vm s)
   
   [varlist_merge_ok]  Theorem
      
      |- ∀sr.
           is_semi_ring sr ⇒
           ∀vm x y.
             interp_vl sr vm (list_merge index_lt x y) =
             SRM sr (interp_vl sr vm x) (interp_vl sr vm y)
   
   
*)
end
