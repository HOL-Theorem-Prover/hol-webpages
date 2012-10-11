signature inftreeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val iLf_def : thm
    val iNd_def : thm
    val inftree_TY_DEF : thm
    val inftree_bijections : thm
    val inftree_case_def : thm
    val inftree_rec_def : thm
    val is_tree_def : thm
    val relrec_def : thm

  (*  Theorems  *)
    val iNd_is_tree : thm
    val inftree_11 : thm
    val inftree_Axiom : thm
    val inftree_distinct : thm
    val inftree_ind : thm
    val inftree_nchotomy : thm
    val is_tree_cases : thm
    val is_tree_ind : thm
    val is_tree_rules : thm
    val is_tree_strongind : thm
    val relrec_cases : thm
    val relrec_ind : thm
    val relrec_rules : thm
    val relrec_strongind : thm

  val inftree_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "inftree"

   [iLf_def]  Definition

      |- ∀a. iLf a = to_inftree (λp. INL a)

   [iNd_def]  Definition

      |- ∀b f.
           iNd b f =
           to_inftree
             (λp. if p = [] then INR b else from_inftree (f (HD p)) (TL p))

   [inftree_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION is_tree rep

   [inftree_bijections]  Definition

      |- (∀a. to_inftree (from_inftree a) = a) ∧
         ∀r. is_tree r ⇔ (from_inftree (to_inftree r) = r)

   [inftree_case_def]  Definition

      |- (∀lf nd a. inftree_case lf nd (iLf a) = lf a) ∧
         ∀lf nd b d. inftree_case lf nd (iNd b d) = nd b d

   [inftree_rec_def]  Definition

      |- ∀lf nd t. inftree_rec lf nd t = @r. relrec lf nd t r

   [is_tree_def]  Definition

      |- is_tree =
         (λa0.
            ∀is_tree'.
              (∀a0.
                 (∃a. a0 = (λp. INL a)) ∨
                 (∃f b.
                    (a0 =
                     (λp. if p = [] then INR b else f (HD p) (TL p))) ∧
                    ∀d. is_tree' (f d)) ⇒
                 is_tree' a0) ⇒
              is_tree' a0)

   [relrec_def]  Definition

      |- relrec =
         (λa0 a1 a2 a3.
            ∀relrec'.
              (∀a0 a1 a2 a3.
                 (∃a. (a2 = iLf a) ∧ (a3 = a0 a)) ∨
                 (∃b df g.
                    (a2 = iNd b df) ∧ (a3 = a1 b g) ∧
                    ∀d. relrec' a0 a1 (df d) (g d)) ⇒
                 relrec' a0 a1 a2 a3) ⇒
              relrec' a0 a1 a2 a3)

   [iNd_is_tree]  Theorem

      |- ∀b f.
           is_tree
             (λp. if p = [] then INR b else from_inftree (f (HD p)) (TL p))

   [inftree_11]  Theorem

      |- ((iLf a1 = iLf a2) ⇔ (a1 = a2)) ∧
         ((iNd b1 f1 = iNd b2 f2) ⇔ (b1 = b2) ∧ (f1 = f2))

   [inftree_Axiom]  Theorem

      |- ∀lf nd.
           ∃f. (∀a. f (iLf a) = lf a) ∧ ∀b d. f (iNd b d) = nd b d (f o d)

   [inftree_distinct]  Theorem

      |- iLf a ≠ iNd b f

   [inftree_ind]  Theorem

      |- ∀P.
           (∀a. P (iLf a)) ∧ (∀b f. (∀d. P (f d)) ⇒ P (iNd b f)) ⇒ ∀t. P t

   [inftree_nchotomy]  Theorem

      |- ∀t. (∃a. t = iLf a) ∨ ∃b d. t = iNd b d

   [is_tree_cases]  Theorem

      |- ∀a0.
           is_tree a0 ⇔
           (∃a. a0 = (λp. INL a)) ∨
           ∃f b.
             (a0 = (λp. if p = [] then INR b else f (HD p) (TL p))) ∧
             ∀d. is_tree (f d)

   [is_tree_ind]  Theorem

      |- ∀is_tree'.
           (∀a. is_tree' (λp. INL a)) ∧
           (∀f b.
              (∀d. is_tree' (f d)) ⇒
              is_tree' (λp. if p = [] then INR b else f (HD p) (TL p))) ⇒
           ∀a0. is_tree a0 ⇒ is_tree' a0

   [is_tree_rules]  Theorem

      |- (∀a. is_tree (λp. INL a)) ∧
         ∀f b.
           (∀d. is_tree (f d)) ⇒
           is_tree (λp. if p = [] then INR b else f (HD p) (TL p))

   [is_tree_strongind]  Theorem

      |- ∀is_tree'.
           (∀a. is_tree' (λp. INL a)) ∧
           (∀f b.
              (∀d. is_tree (f d) ∧ is_tree' (f d)) ⇒
              is_tree' (λp. if p = [] then INR b else f (HD p) (TL p))) ⇒
           ∀a0. is_tree a0 ⇒ is_tree' a0

   [relrec_cases]  Theorem

      |- ∀a0 a1 a2 a3.
           relrec a0 a1 a2 a3 ⇔
           (∃a. (a2 = iLf a) ∧ (a3 = a0 a)) ∨
           ∃b df g.
             (a2 = iNd b df) ∧ (a3 = a1 b g) ∧
             ∀d. relrec a0 a1 (df d) (g d)

   [relrec_ind]  Theorem

      |- ∀relrec'.
           (∀lf nd a. relrec' lf nd (iLf a) (lf a)) ∧
           (∀lf nd b df g.
              (∀d. relrec' lf nd (df d) (g d)) ⇒
              relrec' lf nd (iNd b df) (nd b g)) ⇒
           ∀a0 a1 a2 a3. relrec a0 a1 a2 a3 ⇒ relrec' a0 a1 a2 a3

   [relrec_rules]  Theorem

      |- (∀lf nd a. relrec lf nd (iLf a) (lf a)) ∧
         ∀lf nd b df g.
           (∀d. relrec lf nd (df d) (g d)) ⇒
           relrec lf nd (iNd b df) (nd b g)

   [relrec_strongind]  Theorem

      |- ∀relrec'.
           (∀lf nd a. relrec' lf nd (iLf a) (lf a)) ∧
           (∀lf nd b df g.
              (∀d.
                 relrec lf nd (df d) (g d) ∧ relrec' lf nd (df d) (g d)) ⇒
              relrec' lf nd (iNd b df) (nd b g)) ⇒
           ∀a0 a1 a2 a3. relrec a0 a1 a2 a3 ⇒ relrec' a0 a1 a2 a3


*)
end
