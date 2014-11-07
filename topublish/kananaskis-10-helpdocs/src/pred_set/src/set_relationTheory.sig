signature set_relationTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val RREFL_EXP_def : thm
    val RRUNIV_def : thm
    val acyclic_def : thm
    val all_choices_def : thm
    val antisym_def : thm
    val chain_def : thm
    val domain_def : thm
    val fchains_def : thm
    val finite_prefixes_def : thm
    val get_min_def : thm
    val irreflexive_def : thm
    val linear_order_def : thm
    val maximal_elements_def : thm
    val minimal_elements_def : thm
    val nth_min_curried_def : thm
    val nth_min_tupled_primitive_def : thm
    val num_order_def : thm
    val partial_order_def : thm
    val per_def : thm
    val per_restrict_def : thm
    val range_def : thm
    val rcomp_def : thm
    val reflexive_def : thm
    val rel_to_reln_def : thm
    val reln_to_rel_def : thm
    val rrestrict_def : thm
    val strict_def : thm
    val strict_linear_order_def : thm
    val tc_def : thm
    val transitive_def : thm
    val univ_reln_def : thm
    val upper_bounds_def : thm

  (*  Theorems  *)
    val REL_RESTRICT_UNIV : thm
    val RREFL_EXP_RSUBSET : thm
    val RREFL_EXP_UNIV : thm
    val acyclic_WF : thm
    val acyclic_bigunion : thm
    val acyclic_irreflexive : thm
    val acyclic_reln_to_rel_conv : thm
    val acyclic_rrestrict : thm
    val acyclic_subset : thm
    val acyclic_union : thm
    val all_choices_thm : thm
    val antisym_reln_to_rel_conv : thm
    val countable_per : thm
    val domain_to_rel_conv : thm
    val empty_linear_order : thm
    val empty_strict_linear_order : thm
    val extend_linear_order : thm
    val finite_acyclic_has_maximal : thm
    val finite_acyclic_has_maximal_path : thm
    val finite_acyclic_has_minimal : thm
    val finite_acyclic_has_minimal_path : thm
    val finite_linear_order_has_maximal : thm
    val finite_linear_order_has_minimal : thm
    val finite_prefix_linear_order_has_unique_minimal : thm
    val finite_prefix_po_has_minimal_path : thm
    val finite_prefixes_comp : thm
    val finite_prefixes_inj_image : thm
    val finite_prefixes_range : thm
    val finite_prefixes_subset : thm
    val finite_prefixes_union : thm
    val finite_strict_linear_order_has_maximal : thm
    val finite_strict_linear_order_has_minimal : thm
    val in_domain : thm
    val in_range : thm
    val in_rel_to_reln : thm
    val in_rrestrict : thm
    val irreflexive_reln_to_rel_conv : thm
    val irreflexive_reln_to_rel_conv_UNIV : thm
    val linear_order : thm
    val linear_order_dom_rng : thm
    val linear_order_num_order : thm
    val linear_order_of_countable_po : thm
    val linear_order_reln_to_rel_conv_UNIV : thm
    val linear_order_restrict : thm
    val linear_order_subset : thm
    val maximal_TC : thm
    val maximal_linear_order : thm
    val maximal_union : thm
    val minimal_TC : thm
    val minimal_linear_order : thm
    val minimal_linear_order_unique : thm
    val minimal_union : thm
    val nat_order_iso_thm : thm
    val nth_min_def : thm
    val nth_min_def_compute : thm
    val nth_min_ind : thm
    val num_order_finite_prefix : thm
    val partial_order_dom_rng : thm
    val partial_order_linear_order : thm
    val partial_order_reln_to_rel_conv : thm
    val partial_order_reln_to_rel_conv_UNIV : thm
    val partial_order_subset : thm
    val per_delete : thm
    val per_restrict_per : thm
    val range_to_rel_conv : thm
    val rcomp_to_rel_conv : thm
    val reflexive_reln_to_rel_conv : thm
    val reflexive_reln_to_rel_conv_UNIV : thm
    val rel_to_reln_11 : thm
    val rel_to_reln_inv : thm
    val rel_to_reln_swap : thm
    val reln_rel_conv_thms : thm
    val reln_to_rel_11 : thm
    val reln_to_rel_app : thm
    val reln_to_rel_inv : thm
    val rextension : thm
    val rrestrict_rrestrict : thm
    val rrestrict_tc : thm
    val rrestrict_to_rel_conv : thm
    val rrestrict_union : thm
    val rtc_ind_right : thm
    val strict_linear_order : thm
    val strict_linear_order_acyclic : thm
    val strict_linear_order_dom_rng : thm
    val strict_linear_order_reln_to_rel_conv_UNIV : thm
    val strict_linear_order_restrict : thm
    val strict_linear_order_union_acyclic : thm
    val strict_partial_order : thm
    val strict_partial_order_acyclic : thm
    val strict_rrestrict : thm
    val strict_to_rel_conv : thm
    val tc_cases : thm
    val tc_cases_left : thm
    val tc_cases_right : thm
    val tc_domain_range : thm
    val tc_empty : thm
    val tc_implication : thm
    val tc_ind : thm
    val tc_ind_left : thm
    val tc_ind_right : thm
    val tc_rules : thm
    val tc_strongind : thm
    val tc_strongind_left : thm
    val tc_strongind_right : thm
    val tc_to_rel_conv : thm
    val tc_transitive : thm
    val tc_union : thm
    val transitive_tc : thm
    val upper_bounds_lem : thm
    val zorns_lemma : thm

  val set_relation_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [pred_set] Parent theory of "set_relation"

   [RREFL_EXP_def]  Definition

      |- ∀R s. RREFL_EXP R s = R RUNION (λx y. (x = y) ∧ x ∉ s)

   [RRUNIV_def]  Definition

      |- ∀s. RRUNIV s = (λx y. x ∈ s ∧ y ∈ s)

   [acyclic_def]  Definition

      |- ∀r. acyclic r ⇔ ∀x. (x,x) ∉ tc r

   [all_choices_def]  Definition

      |- ∀xss.
           all_choices xss =
           {IMAGE choice xss | choice | ∀xs. xs ∈ xss ⇒ choice xs ∈ xs}

   [antisym_def]  Definition

      |- ∀r. antisym r ⇔ ∀x y. (x,y) ∈ r ∧ (y,x) ∈ r ⇒ (x = y)

   [chain_def]  Definition

      |- ∀s r. chain s r ⇔ ∀x y. x ∈ s ∧ y ∈ s ⇒ (x,y) ∈ r ∨ (y,x) ∈ r

   [domain_def]  Definition

      |- ∀r. domain r = {x | ∃y. (x,y) ∈ r}

   [fchains_def]  Definition

      |- ∀r.
           fchains r =
           {k |
            chain k r ∧ k ≠ ∅ ∧
            ∀C.
              chain C r ∧ C ⊆ k ∧ (upper_bounds C r DIFF C) ∩ k ≠ ∅ ⇒
              CHOICE (upper_bounds C r DIFF C) ∈
              minimal_elements ((upper_bounds C r DIFF C) ∩ k) r}

   [finite_prefixes_def]  Definition

      |- ∀r s. finite_prefixes r s ⇔ ∀e. e ∈ s ⇒ FINITE {e' | (e',e) ∈ r}

   [get_min_def]  Definition

      |- ∀r' s r.
           get_min r' (s,r) =
           (let mins = minimal_elements (minimal_elements s r) r'
            in
              if SING mins then SOME (CHOICE mins) else NONE)

   [irreflexive_def]  Definition

      |- ∀r s. irreflexive r s ⇔ ∀x. x ∈ s ⇒ (x,x) ∉ r

   [linear_order_def]  Definition

      |- ∀r s.
           linear_order r s ⇔
           domain r ⊆ s ∧ range r ⊆ s ∧ transitive r ∧ antisym r ∧
           ∀x y. x ∈ s ∧ y ∈ s ⇒ (x,y) ∈ r ∨ (y,x) ∈ r

   [maximal_elements_def]  Definition

      |- ∀xs r.
           maximal_elements xs r =
           {x | x ∈ xs ∧ ∀x'. x' ∈ xs ∧ (x,x') ∈ r ⇒ (x = x')}

   [minimal_elements_def]  Definition

      |- ∀xs r.
           minimal_elements xs r =
           {x | x ∈ xs ∧ ∀x'. x' ∈ xs ∧ (x',x) ∈ r ⇒ (x = x')}

   [nth_min_curried_def]  Definition

      |- ∀x x1 x2. nth_min x x1 x2 = nth_min_tupled (x,x1,x2)

   [nth_min_tupled_primitive_def]  Definition

      |- nth_min_tupled =
         WFREC
           (@R.
              WF R ∧
              ∀n r s r' min.
                (min = get_min r' (s,r)) ∧ min ≠ NONE ⇒
                R (r',(s DELETE THE min,r),n) (r',(s,r),SUC n))
           (λnth_min_tupled a.
              case a of
                (r',(s,r),0) => I (get_min r' (s,r))
              | (r',(s,r),SUC n) =>
                  I
                    (let min = get_min r' (s,r)
                     in
                       if min = NONE then NONE
                       else nth_min_tupled (r',(s DELETE THE min,r),n)))

   [num_order_def]  Definition

      |- ∀f s. num_order f s = {(x,y) | x ∈ s ∧ y ∈ s ∧ f x ≤ f y}

   [partial_order_def]  Definition

      |- ∀r s.
           partial_order r s ⇔
           domain r ⊆ s ∧ range r ⊆ s ∧ transitive r ∧ reflexive r s ∧
           antisym r

   [per_def]  Definition

      |- ∀xs xss.
           per xs xss ⇔
           BIGUNION xss ⊆ xs ∧ ∅ ∉ xss ∧
           ∀xs1 xs2. xs1 ∈ xss ∧ xs2 ∈ xss ∧ xs1 ≠ xs2 ⇒ DISJOINT xs1 xs2

   [per_restrict_def]  Definition

      |- ∀xss xs. per_restrict xss xs = {xs' ∩ xs | xs' ∈ xss} DELETE ∅

   [range_def]  Definition

      |- ∀r. range r = {y | ∃x. (x,y) ∈ r}

   [rcomp_def]  Definition

      |- ∀r1 r2. r1 OO r2 = {(x,y) | ∃z. (x,z) ∈ r1 ∧ (z,y) ∈ r2}

   [reflexive_def]  Definition

      |- ∀r s. reflexive r s ⇔ ∀x. x ∈ s ⇒ (x,x) ∈ r

   [rel_to_reln_def]  Definition

      |- ∀R. rel_to_reln R = {(x,y) | R x y}

   [reln_to_rel_def]  Definition

      |- ∀r. reln_to_rel r = (λx y. (x,y) ∈ r)

   [rrestrict_def]  Definition

      |- ∀r s. rrestrict r s = {(x,y) | (x,y) ∈ r ∧ x ∈ s ∧ y ∈ s}

   [strict_def]  Definition

      |- ∀r. strict r = {(x,y) | (x,y) ∈ r ∧ x ≠ y}

   [strict_linear_order_def]  Definition

      |- ∀r s.
           strict_linear_order r s ⇔
           domain r ⊆ s ∧ range r ⊆ s ∧ transitive r ∧ (∀x. (x,x) ∉ r) ∧
           ∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ (x,y) ∈ r ∨ (y,x) ∈ r

   [tc_def]  Definition

      |- tc =
         (λr a0.
            ∀tc'.
              (∀a0.
                 (∃x y. (a0 = (x,y)) ∧ r (x,y)) ∨
                 (∃x y. (a0 = (x,y)) ∧ ∃z. tc' (x,z) ∧ tc' (z,y)) ⇒
                 tc' a0) ⇒
              tc' a0)

   [transitive_def]  Definition

      |- ∀r. transitive r ⇔ ∀x y z. (x,y) ∈ r ∧ (y,z) ∈ r ⇒ (x,z) ∈ r

   [univ_reln_def]  Definition

      |- ∀xs. univ_reln xs = {(x1,x2) | x1 ∈ xs ∧ x2 ∈ xs}

   [upper_bounds_def]  Definition

      |- ∀s r. upper_bounds s r = {x | x ∈ range r ∧ ∀y. y ∈ s ⇒ (y,x) ∈ r}

   [REL_RESTRICT_UNIV]  Theorem

      |- REL_RESTRICT R pred_set$UNIV = R

   [RREFL_EXP_RSUBSET]  Theorem

      |- R RSUBSET RREFL_EXP R s

   [RREFL_EXP_UNIV]  Theorem

      |- RREFL_EXP R pred_set$UNIV = R

   [acyclic_WF]  Theorem

      |- FINITE s ∧ acyclic r ∧ domain r ⊆ s ∧ range r ⊆ s ⇒
         WF (reln_to_rel r)

   [acyclic_bigunion]  Theorem

      |- ∀rs.
           (∀r r'.
              r ∈ rs ∧ r' ∈ rs ∧ r ≠ r' ⇒
              DISJOINT (domain r ∪ range r) (domain r' ∪ range r')) ∧
           (∀r. r ∈ rs ⇒ acyclic r) ⇒
           acyclic (BIGUNION rs)

   [acyclic_irreflexive]  Theorem

      |- ∀r x. acyclic r ⇒ (x,x) ∉ r

   [acyclic_reln_to_rel_conv]  Theorem

      |- acyclic r ⇔ irreflexive (reln_to_rel r)⁺

   [acyclic_rrestrict]  Theorem

      |- ∀r s. acyclic r ⇒ acyclic (rrestrict r s)

   [acyclic_subset]  Theorem

      |- ∀r1 r2. acyclic r1 ∧ r2 ⊆ r1 ⇒ acyclic r2

   [acyclic_union]  Theorem

      |- ∀r r'.
           DISJOINT (domain r ∪ range r) (domain r' ∪ range r') ∧
           acyclic r ∧ acyclic r' ⇒
           acyclic (r ∪ r')

   [all_choices_thm]  Theorem

      |- ∀x s y. x ∈ all_choices s ∧ y ∈ x ⇒ ∃z. z ∈ s ∧ y ∈ z

   [antisym_reln_to_rel_conv]  Theorem

      |- antisym r ⇔ antisymmetric (reln_to_rel r)

   [countable_per]  Theorem

      |- ∀xs xss. countable xs ∧ per xs xss ⇒ countable xss

   [domain_to_rel_conv]  Theorem

      |- domain r = RDOM (reln_to_rel r)

   [empty_linear_order]  Theorem

      |- ∀r. linear_order r ∅ ⇔ (r = ∅)

   [empty_strict_linear_order]  Theorem

      |- ∀r. strict_linear_order r ∅ ⇔ (r = ∅)

   [extend_linear_order]  Theorem

      |- ∀r s x.
           x ∉ s ∧ linear_order r s ⇒
           linear_order (r ∪ {(y,x) | y | y ∈ s ∪ {x}}) (s ∪ {x})

   [finite_acyclic_has_maximal]  Theorem

      |- ∀s.
           FINITE s ⇒ s ≠ ∅ ⇒ ∀r. acyclic r ⇒ ∃x. x ∈ maximal_elements s r

   [finite_acyclic_has_maximal_path]  Theorem

      |- ∀s r x.
           FINITE s ∧ acyclic r ∧ x ∈ s ∧ x ∉ maximal_elements s r ⇒
           ∃y. y ∈ maximal_elements s r ∧ (x,y) ∈ tc r

   [finite_acyclic_has_minimal]  Theorem

      |- ∀s.
           FINITE s ⇒ s ≠ ∅ ⇒ ∀r. acyclic r ⇒ ∃x. x ∈ minimal_elements s r

   [finite_acyclic_has_minimal_path]  Theorem

      |- ∀s r x.
           FINITE s ∧ acyclic r ∧ x ∈ s ∧ x ∉ minimal_elements s r ⇒
           ∃y. y ∈ minimal_elements s r ∧ (y,x) ∈ tc r

   [finite_linear_order_has_maximal]  Theorem

      |- ∀s r.
           FINITE s ∧ linear_order r s ∧ s ≠ ∅ ⇒
           ∃x. x ∈ maximal_elements s r

   [finite_linear_order_has_minimal]  Theorem

      |- ∀s r.
           FINITE s ∧ linear_order r s ∧ s ≠ ∅ ⇒
           ∃x. x ∈ minimal_elements s r

   [finite_prefix_linear_order_has_unique_minimal]  Theorem

      |- ∀r s s'.
           linear_order r s ∧ finite_prefixes r s ∧ x ∈ s' ∧ s' ⊆ s ⇒
           SING (minimal_elements s' r)

   [finite_prefix_po_has_minimal_path]  Theorem

      |- ∀r s x s'.
           partial_order r s ∧ finite_prefixes r s ∧
           x ∉ minimal_elements s' r ∧ x ∈ s' ∧ s' ⊆ s ⇒
           ∃x'. x' ∈ minimal_elements s' r ∧ (x',x) ∈ r

   [finite_prefixes_comp]  Theorem

      |- ∀r1 r2 s1 s2.
           finite_prefixes r1 s1 ∧ finite_prefixes r2 s2 ∧
           {x | ∃y. y ∈ s2 ∧ (x,y) ∈ r2} ⊆ s1 ⇒
           finite_prefixes (r1 OO r2) s2

   [finite_prefixes_inj_image]  Theorem

      |- ∀f r s.
           (∀x y. (f x = f y) ⇒ (x = y)) ∧ finite_prefixes r s ⇒
           finite_prefixes {(f x,f y) | (x,y) ∈ r} (IMAGE f s)

   [finite_prefixes_range]  Theorem

      |- ∀r s t.
           finite_prefixes r s ∧ DISJOINT t (range r) ⇒
           finite_prefixes r (s ∪ t)

   [finite_prefixes_subset]  Theorem

      |- ∀r s s'.
           finite_prefixes r s ∧ s' ⊆ s ⇒
           finite_prefixes r s' ∧ finite_prefixes (rrestrict r s') s'

   [finite_prefixes_union]  Theorem

      |- ∀r1 r2 s1 s2.
           finite_prefixes r1 s1 ∧ finite_prefixes r2 s2 ⇒
           finite_prefixes (r1 ∪ r2) (s1 ∩ s2)

   [finite_strict_linear_order_has_maximal]  Theorem

      |- ∀s r.
           FINITE s ∧ strict_linear_order r s ∧ s ≠ ∅ ⇒
           ∃x. x ∈ maximal_elements s r

   [finite_strict_linear_order_has_minimal]  Theorem

      |- ∀s r.
           FINITE s ∧ strict_linear_order r s ∧ s ≠ ∅ ⇒
           ∃x. x ∈ minimal_elements s r

   [in_domain]  Theorem

      |- ∀x r. x ∈ domain r ⇔ ∃y. (x,y) ∈ r

   [in_range]  Theorem

      |- ∀y r. y ∈ range r ⇔ ∃x. (x,y) ∈ r

   [in_rel_to_reln]  Theorem

      |- xy ∈ rel_to_reln R ⇔ R (FST xy) (SND xy)

   [in_rrestrict]  Theorem

      |- ∀x y r s. (x,y) ∈ rrestrict r s ⇔ (x,y) ∈ r ∧ x ∈ s ∧ y ∈ s

   [irreflexive_reln_to_rel_conv]  Theorem

      |- irreflexive r s ⇔ irreflexive (REL_RESTRICT (reln_to_rel r) s)

   [irreflexive_reln_to_rel_conv_UNIV]  Theorem

      |- irreflexive r pred_set$UNIV ⇔ irreflexive (reln_to_rel r)

   [linear_order]  Theorem

      |- ∀r s.
           strict_linear_order r s ⇒ linear_order (r ∪ {(x,x) | x ∈ s}) s

   [linear_order_dom_rng]  Theorem

      |- ∀r s x y. (x,y) ∈ r ∧ linear_order r s ⇒ x ∈ s ∧ y ∈ s

   [linear_order_num_order]  Theorem

      |- ∀f s t. INJ f s t ⇒ linear_order (num_order f s) s

   [linear_order_of_countable_po]  Theorem

      |- ∀r s.
           countable s ∧ partial_order r s ∧ finite_prefixes r s ⇒
           ∃r'. linear_order r' s ∧ finite_prefixes r' s ∧ r ⊆ r'

   [linear_order_reln_to_rel_conv_UNIV]  Theorem

      |- linear_order r pred_set$UNIV ⇔ WeakLinearOrder (reln_to_rel r)

   [linear_order_restrict]  Theorem

      |- ∀s r s'. linear_order r s ⇒ linear_order (rrestrict r s') (s ∩ s')

   [linear_order_subset]  Theorem

      |- ∀r s s'.
           linear_order r s ∧ s' ⊆ s ⇒ linear_order (rrestrict r s') s'

   [maximal_TC]  Theorem

      |- ∀s r.
           domain r ⊆ s ∧ range r ⊆ s ⇒
           (maximal_elements s (tc r) = maximal_elements s r)

   [maximal_linear_order]  Theorem

      |- ∀s r x y.
           y ∈ s ∧ linear_order r s ∧ x ∈ maximal_elements s r ⇒ (y,x) ∈ r

   [maximal_union]  Theorem

      |- ∀e s r1 r2.
           e ∈ maximal_elements s (r1 ∪ r2) ⇒
           e ∈ maximal_elements s r1 ∧ e ∈ maximal_elements s r2

   [minimal_TC]  Theorem

      |- ∀s r.
           domain r ⊆ s ∧ range r ⊆ s ⇒
           (minimal_elements s (tc r) = minimal_elements s r)

   [minimal_linear_order]  Theorem

      |- ∀s r x y.
           y ∈ s ∧ linear_order r s ∧ x ∈ minimal_elements s r ⇒ (x,y) ∈ r

   [minimal_linear_order_unique]  Theorem

      |- ∀r s s' x y.
           linear_order r s ∧ x ∈ minimal_elements s' r ∧
           y ∈ minimal_elements s' r ∧ s' ⊆ s ⇒
           (x = y)

   [minimal_union]  Theorem

      |- ∀e s r1 r2.
           e ∈ minimal_elements s (r1 ∪ r2) ⇒
           e ∈ minimal_elements s r1 ∧ e ∈ minimal_elements s r2

   [nat_order_iso_thm]  Theorem

      |- ∀f s.
           (∀n m. (f m = f n) ∧ f m ≠ NONE ⇒ (m = n)) ∧
           (∀x. x ∈ s ⇒ ∃m. f m = SOME x) ∧
           (∀m x. (f m = SOME x) ⇒ x ∈ s) ⇒
           linear_order
             {(x,y) | ∃m n. m ≤ n ∧ (f m = SOME x) ∧ (f n = SOME y)} s ∧
           finite_prefixes
             {(x,y) | ∃m n. m ≤ n ∧ (f m = SOME x) ∧ (f n = SOME y)} s

   [nth_min_def]  Theorem

      |- (∀s r' r. nth_min r' (s,r) 0 = get_min r' (s,r)) ∧
         ∀s r' r n.
           nth_min r' (s,r) (SUC n) =
           (let min = get_min r' (s,r)
            in
              if min = NONE then NONE
              else nth_min r' (s DELETE THE min,r) n)

   [nth_min_def_compute]  Theorem

      |- (∀s r' r. nth_min r' (s,r) 0 = get_min r' (s,r)) ∧
         (∀s r' r n.
            nth_min r' (s,r) (NUMERAL (BIT1 n)) =
            (let min = get_min r' (s,r)
             in
               if min = NONE then NONE
               else
                 nth_min r' (s DELETE THE min,r) (NUMERAL (BIT1 n) − 1))) ∧
         ∀s r' r n.
           nth_min r' (s,r) (NUMERAL (BIT2 n)) =
           (let min = get_min r' (s,r)
            in
              if min = NONE then NONE
              else nth_min r' (s DELETE THE min,r) (NUMERAL (BIT1 n)))

   [nth_min_ind]  Theorem

      |- ∀P.
           (∀r' s r. P r' (s,r) 0) ∧
           (∀r' s r n.
              (∀min.
                 (min = get_min r' (s,r)) ∧ min ≠ NONE ⇒
                 P r' (s DELETE THE min,r) n) ⇒
              P r' (s,r) (SUC n)) ⇒
           ∀v v1 v2 v3. P v (v1,v2) v3

   [num_order_finite_prefix]  Theorem

      |- ∀f s t. INJ f s t ⇒ finite_prefixes (num_order f s) s

   [partial_order_dom_rng]  Theorem

      |- ∀r s x y. (x,y) ∈ r ∧ partial_order r s ⇒ x ∈ s ∧ y ∈ s

   [partial_order_linear_order]  Theorem

      |- ∀r s. linear_order r s ⇒ partial_order r s

   [partial_order_reln_to_rel_conv]  Theorem

      |- partial_order r s ⇔
         reln_to_rel r RSUBSET RRUNIV s ∧
         WeakOrder (RREFL_EXP (reln_to_rel r) s)

   [partial_order_reln_to_rel_conv_UNIV]  Theorem

      |- partial_order r pred_set$UNIV ⇔ WeakOrder (reln_to_rel r)

   [partial_order_subset]  Theorem

      |- ∀r s s'.
           partial_order r s ∧ s' ⊆ s ⇒ partial_order (rrestrict r s') s'

   [per_delete]  Theorem

      |- ∀xs xss e.
           per xs xss ⇒
           per (xs DELETE e)
             {es | es ∈ IMAGE (λes. es DELETE e) xss ∧ es ≠ ∅}

   [per_restrict_per]  Theorem

      |- ∀r s s'. per s r ⇒ per s' (per_restrict r s')

   [range_to_rel_conv]  Theorem

      |- range r = RRANGE (reln_to_rel r)

   [rcomp_to_rel_conv]  Theorem

      |- r1 OO r2 = rel_to_reln (reln_to_rel r2 O reln_to_rel r1)

   [reflexive_reln_to_rel_conv]  Theorem

      |- transitive r ⇔ transitive (reln_to_rel r)

   [reflexive_reln_to_rel_conv_UNIV]  Theorem

      |- reflexive r pred_set$UNIV ⇔ reflexive (reln_to_rel r)

   [rel_to_reln_11]  Theorem

      |- (rel_to_reln R1 = rel_to_reln R2) ⇔ (R1 = R2)

   [rel_to_reln_inv]  Theorem

      |- reln_to_rel (rel_to_reln R) = R

   [rel_to_reln_swap]  Theorem

      |- (r = rel_to_reln R) ⇔ (reln_to_rel r = R)

   [reln_rel_conv_thms]  Theorem

      |- ((xy ∈ rel_to_reln R ⇔ R (FST xy) (SND xy)) ∧
          (reln_to_rel r x y ⇔ (x,y) ∈ r) ∧
          (reln_to_rel (rel_to_reln R) = R) ∧
          (rel_to_reln (reln_to_rel r) = r) ∧
          ((reln_to_rel r1 = reln_to_rel r2) ⇔ (r1 = r2)) ∧
          ((rel_to_reln R1 = rel_to_reln R2) ⇔ (R1 = R2))) ∧
         (RREFL_EXP R pred_set$UNIV = R) ∧
         (REL_RESTRICT R pred_set$UNIV = R) ∧
         (domain r = RDOM (reln_to_rel r)) ∧
         (range r = RRANGE (reln_to_rel r)) ∧
         (strict r = rel_to_reln (STRORD (reln_to_rel r))) ∧
         (rrestrict r s = rel_to_reln (REL_RESTRICT (reln_to_rel r) s)) ∧
         (r1 OO r2 = rel_to_reln (reln_to_rel r2 O reln_to_rel r1)) ∧
         (univ_reln s = rel_to_reln (RRUNIV s)) ∧
         (tc r = rel_to_reln (reln_to_rel r)⁺) ∧
         (acyclic r ⇔ irreflexive (reln_to_rel r)⁺) ∧
         (irreflexive r s ⇔ irreflexive (REL_RESTRICT (reln_to_rel r) s)) ∧
         (reflexive r s ⇔ reflexive (RREFL_EXP (reln_to_rel r) s)) ∧
         (transitive r ⇔ transitive (reln_to_rel r)) ∧
         (antisym r ⇔ antisymmetric (reln_to_rel r)) ∧
         (partial_order r pred_set$UNIV ⇔ WeakOrder (reln_to_rel r)) ∧
         (linear_order r pred_set$UNIV ⇔ WeakLinearOrder (reln_to_rel r)) ∧
         (strict_linear_order r pred_set$UNIV ⇔
          StrongLinearOrder (reln_to_rel r))

   [reln_to_rel_11]  Theorem

      |- (reln_to_rel r1 = reln_to_rel r2) ⇔ (r1 = r2)

   [reln_to_rel_app]  Theorem

      |- reln_to_rel r x y ⇔ (x,y) ∈ r

   [reln_to_rel_inv]  Theorem

      |- rel_to_reln (reln_to_rel r) = r

   [rextension]  Theorem

      |- ∀s t. (s = t) ⇔ ∀x y. (x,y) ∈ s ⇔ (x,y) ∈ t

   [rrestrict_rrestrict]  Theorem

      |- ∀r x y. rrestrict (rrestrict r x) y = rrestrict r (x ∩ y)

   [rrestrict_tc]  Theorem

      |- ∀e e'. (e,e') ∈ tc (rrestrict r x) ⇒ (e,e') ∈ tc r

   [rrestrict_to_rel_conv]  Theorem

      |- univ_reln s = rel_to_reln (RRUNIV s)

   [rrestrict_union]  Theorem

      |- ∀r1 r2 s. rrestrict (r1 ∪ r2) s = rrestrict r1 s ∪ rrestrict r2 s

   [rtc_ind_right]  Theorem

      |- ∀r tc'.
           (∀x. x ∈ domain r ∨ x ∈ range r ⇒ tc' x x) ∧
           (∀x y. (∃z. tc' x z ∧ (z,y) ∈ r) ⇒ tc' x y) ⇒
           ∀x y. (x,y) ∈ tc r ⇒ tc' x y

   [strict_linear_order]  Theorem

      |- ∀r s. linear_order r s ⇒ strict_linear_order (strict r) s

   [strict_linear_order_acyclic]  Theorem

      |- ∀r s. strict_linear_order r s ⇒ acyclic r

   [strict_linear_order_dom_rng]  Theorem

      |- ∀r s x y. (x,y) ∈ r ∧ strict_linear_order r s ⇒ x ∈ s ∧ y ∈ s

   [strict_linear_order_reln_to_rel_conv_UNIV]  Theorem

      |- strict_linear_order r pred_set$UNIV ⇔
         StrongLinearOrder (reln_to_rel r)

   [strict_linear_order_restrict]  Theorem

      |- ∀s r s'.
           strict_linear_order r s ⇒
           strict_linear_order (rrestrict r s') (s ∩ s')

   [strict_linear_order_union_acyclic]  Theorem

      |- ∀r1 r2 s.
           strict_linear_order r1 s ∧ domain r2 ∪ range r2 ⊆ s ⇒
           (acyclic (r1 ∪ r2) ⇔ r2 ⊆ r1)

   [strict_partial_order]  Theorem

      |- ∀r s.
           partial_order r s ⇒
           domain (strict r) ⊆ s ∧ range (strict r) ⊆ s ∧
           transitive (strict r) ∧ antisym (strict r)

   [strict_partial_order_acyclic]  Theorem

      |- ∀r s. partial_order r s ⇒ acyclic (strict r)

   [strict_rrestrict]  Theorem

      |- ∀r s. strict (rrestrict r s) = rrestrict (strict r) s

   [strict_to_rel_conv]  Theorem

      |- strict r = rel_to_reln (STRORD (reln_to_rel r))

   [tc_cases]  Theorem

      |- ∀r x y. (x,y) ∈ tc r ⇔ (x,y) ∈ r ∨ ∃z. (x,z) ∈ tc r ∧ (z,y) ∈ tc r

   [tc_cases_left]  Theorem

      |- ∀r x y. (x,y) ∈ tc r ⇔ (x,y) ∈ r ∨ ∃z. (x,z) ∈ r ∧ (z,y) ∈ tc r

   [tc_cases_right]  Theorem

      |- ∀r x y. (x,y) ∈ tc r ⇔ (x,y) ∈ r ∨ ∃z. (x,z) ∈ tc r ∧ (z,y) ∈ r

   [tc_domain_range]  Theorem

      |- ∀x y. (x,y) ∈ tc r ⇒ x ∈ domain r ∧ y ∈ range r

   [tc_empty]  Theorem

      |- ∀x y. (x,y) ∉ tc ∅

   [tc_implication]  Theorem

      |- ∀r1 r2.
           (∀x y. (x,y) ∈ r1 ⇒ (x,y) ∈ r2) ⇒
           ∀x y. (x,y) ∈ tc r1 ⇒ (x,y) ∈ tc r2

   [tc_ind]  Theorem

      |- ∀r tc'.
           (∀x y. (x,y) ∈ r ⇒ tc' x y) ∧
           (∀x y. (∃z. tc' x z ∧ tc' z y) ⇒ tc' x y) ⇒
           ∀x y. (x,y) ∈ tc r ⇒ tc' x y

   [tc_ind_left]  Theorem

      |- ∀r tc'.
           (∀x y. (x,y) ∈ r ⇒ tc' x y) ∧
           (∀x y. (∃z. (x,z) ∈ r ∧ tc' z y) ⇒ tc' x y) ⇒
           ∀x y. (x,y) ∈ tc r ⇒ tc' x y

   [tc_ind_right]  Theorem

      |- ∀r tc'.
           (∀x y. (x,y) ∈ r ⇒ tc' x y) ∧
           (∀x y. (∃z. tc' x z ∧ (z,y) ∈ r) ⇒ tc' x y) ⇒
           ∀x y. (x,y) ∈ tc r ⇒ tc' x y

   [tc_rules]  Theorem

      |- ∀r.
           (∀x y. (x,y) ∈ r ⇒ (x,y) ∈ tc r) ∧
           ∀x y. (∃z. (x,z) ∈ tc r ∧ (z,y) ∈ tc r) ⇒ (x,y) ∈ tc r

   [tc_strongind]  Theorem

      |- ∀r tc'.
           (∀x y. (x,y) ∈ r ⇒ tc' x y) ∧
           (∀x y.
              (∃z. (x,z) ∈ tc r ∧ tc' x z ∧ (z,y) ∈ tc r ∧ tc' z y) ⇒
              tc' x y) ⇒
           ∀x y. (x,y) ∈ tc r ⇒ tc' x y

   [tc_strongind_left]  Theorem

      |- ∀r tc'.
           (∀x y. (x,y) ∈ r ⇒ tc' x y) ∧
           (∀x y. (∃z. (x,z) ∈ r ∧ (z,y) ∈ tc r ∧ tc' z y) ⇒ tc' x y) ⇒
           ∀x y. (x,y) ∈ tc r ⇒ tc' x y

   [tc_strongind_right]  Theorem

      |- ∀r tc'.
           (∀x y. (x,y) ∈ r ⇒ tc' x y) ∧
           (∀x y. (∃z. (x,z) ∈ tc r ∧ tc' x z ∧ (z,y) ∈ r) ⇒ tc' x y) ⇒
           ∀x y. (x,y) ∈ tc r ⇒ tc' x y

   [tc_to_rel_conv]  Theorem

      |- tc r = rel_to_reln (reln_to_rel r)⁺

   [tc_transitive]  Theorem

      |- ∀r. transitive (tc r)

   [tc_union]  Theorem

      |- ∀x y. (x,y) ∈ tc r1 ⇒ ∀r2. (x,y) ∈ tc (r1 ∪ r2)

   [transitive_tc]  Theorem

      |- ∀r. transitive r ⇒ (tc r = r)

   [upper_bounds_lem]  Theorem

      |- ∀r s x1 x2.
           transitive r ∧ x1 ∈ upper_bounds s r ∧ (x1,x2) ∈ r ⇒
           x2 ∈ upper_bounds s r

   [zorns_lemma]  Theorem

      |- ∀r s.
           s ≠ ∅ ∧ partial_order r s ∧
           (∀t. chain t r ⇒ upper_bounds t r ≠ ∅) ⇒
           ∃x. x ∈ maximal_elements s r


*)
end
