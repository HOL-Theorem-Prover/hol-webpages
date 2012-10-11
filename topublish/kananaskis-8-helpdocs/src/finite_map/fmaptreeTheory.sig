signature fmaptreeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val FTNode_def : thm
    val apply_path_def : thm
    val construct_def : thm
    val fmap_bij_thm : thm
    val fmaptree_TY_DEF : thm
    val fmtreerec_def : thm
    val fupd_at_path_def : thm
    val item_map_def : thm
    val relrec_def : thm
    val update_at_path_def : thm
    val wf_def : thm

  (*  Theorems  *)
    val FTNode_11 : thm
    val applicable_paths_FINITE : thm
    val apply_path_SNOC : thm
    val fmaptree_nchotomy : thm
    val fmtree_Axiom : thm
    val fmtreerec_thm : thm
    val ft_ind : thm
    val item_thm : thm
    val map_thm : thm
    val relrec_cases : thm
    val relrec_ind : thm
    val relrec_rules : thm
    val relrec_strongind : thm
    val wf_cases : thm
    val wf_ind : thm
    val wf_rules : thm
    val wf_strongind : thm

  val fmaptree_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "fmaptree"

   [FTNode_def]  Definition

      |- ∀i fm. FTNode i fm = fromF (construct i (toF o_f fm))

   [apply_path_def]  Definition

      |- (∀ft. apply_path [] ft = SOME ft) ∧
         ∀h t ft.
           apply_path (h::t) ft =
           if h ∈ FDOM (map ft) then apply_path t (map ft ' h) else NONE

   [construct_def]  Definition

      |- ∀a kfm kl.
           construct a kfm kl =
           case kl of
             [] => SOME a
           | h::t => if h ∈ FDOM kfm then kfm ' h t else NONE

   [fmap_bij_thm]  Definition

      |- (∀a. fromF (toF a) = a) ∧ ∀r. wf r ⇔ (toF (fromF r) = r)

   [fmaptree_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION wf rep

   [fmtreerec_def]  Definition

      |- ∀h ft. fmtreerec h ft = @r. relrec h ft r

   [fupd_at_path_def]  Definition

      |- (∀f ft. fupd_at_path [] f ft = f ft) ∧
         ∀h t f ft.
           fupd_at_path (h::t) f ft =
           if h ∈ FDOM (map ft) then
             case fupd_at_path t f (map ft ' h) of
               NONE => NONE
             | SOME ft' => SOME (FTNode (item ft) (map ft |+ (h,ft')))
           else
             NONE

   [item_map_def]  Definition

      |- ∀ft. ft = FTNode (item ft) (map ft)

   [relrec_def]  Definition

      |- relrec =
         (λh a0 a1.
            ∀relrec'.
              (∀a0 a1.
                 (∃i fm rfm.
                    (a0 = FTNode i fm) ∧ (a1 = h i rfm fm) ∧
                    (FDOM rfm = FDOM fm) ∧
                    ∀d. d ∈ FDOM fm ⇒ relrec' (fm ' d) (rfm ' d)) ⇒
                 relrec' a0 a1) ⇒
              relrec' a0 a1)

   [update_at_path_def]  Definition

      |- (∀a ft. update_at_path [] a ft = SOME (FTNode a (map ft))) ∧
         ∀h t a ft.
           update_at_path (h::t) a ft =
           if h ∈ FDOM (map ft) then
             case update_at_path t a (map ft ' h) of
               NONE => NONE
             | SOME ft' => SOME (FTNode (item ft) (map ft |+ (h,ft')))
           else
             NONE

   [wf_def]  Definition

      |- wf =
         (λa0.
            ∀wf'.
              (∀a0.
                 (∃a fm.
                    (a0 = construct a fm) ∧
                    ∀k. k ∈ FDOM fm ⇒ wf' (fm ' k)) ⇒
                 wf' a0) ⇒
              wf' a0)

   [FTNode_11]  Theorem

      |- (FTNode i1 f1 = FTNode i2 f2) ⇔ (i1 = i2) ∧ (f1 = f2)

   [applicable_paths_FINITE]  Theorem

      |- ∀ft. FINITE {p | ∃ft'. apply_path p ft = SOME ft'}

   [apply_path_SNOC]  Theorem

      |- ∀ft x p.
           apply_path (p ++ [x]) ft =
           case apply_path p ft of
             NONE => NONE
           | SOME ft' => FLOOKUP (map ft') x

   [fmaptree_nchotomy]  Theorem

      |- ∀ft. ∃i fm. ft = FTNode i fm

   [fmtree_Axiom]  Theorem

      |- ∀h. ∃f. ∀i fm. f (FTNode i fm) = h i fm (f o_f fm)

   [fmtreerec_thm]  Theorem

      |- fmtreerec h (FTNode i fm) = h i (fmtreerec h o_f fm) fm

   [ft_ind]  Theorem

      |- ∀P.
           (∀a fm. (∀k. k ∈ FDOM fm ⇒ P (fm ' k)) ⇒ P (FTNode a fm)) ⇒
           ∀ft. P ft

   [item_thm]  Theorem

      |- item (FTNode i fm) = i

   [map_thm]  Theorem

      |- map (FTNode i fm) = fm

   [relrec_cases]  Theorem

      |- ∀h a0 a1.
           relrec h a0 a1 ⇔
           ∃i fm rfm.
             (a0 = FTNode i fm) ∧ (a1 = h i rfm fm) ∧
             (FDOM rfm = FDOM fm) ∧
             ∀d. d ∈ FDOM fm ⇒ relrec h (fm ' d) (rfm ' d)

   [relrec_ind]  Theorem

      |- ∀h relrec'.
           (∀i fm rfm.
              (FDOM rfm = FDOM fm) ∧
              (∀d. d ∈ FDOM fm ⇒ relrec' (fm ' d) (rfm ' d)) ⇒
              relrec' (FTNode i fm) (h i rfm fm)) ⇒
           ∀a0 a1. relrec h a0 a1 ⇒ relrec' a0 a1

   [relrec_rules]  Theorem

      |- ∀h i fm rfm.
           (FDOM rfm = FDOM fm) ∧
           (∀d. d ∈ FDOM fm ⇒ relrec h (fm ' d) (rfm ' d)) ⇒
           relrec h (FTNode i fm) (h i rfm fm)

   [relrec_strongind]  Theorem

      |- ∀h relrec'.
           (∀i fm rfm.
              (FDOM rfm = FDOM fm) ∧
              (∀d.
                 d ∈ FDOM fm ⇒
                 relrec h (fm ' d) (rfm ' d) ∧
                 relrec' (fm ' d) (rfm ' d)) ⇒
              relrec' (FTNode i fm) (h i rfm fm)) ⇒
           ∀a0 a1. relrec h a0 a1 ⇒ relrec' a0 a1

   [wf_cases]  Theorem

      |- ∀a0.
           wf a0 ⇔
           ∃a fm. (a0 = construct a fm) ∧ ∀k. k ∈ FDOM fm ⇒ wf (fm ' k)

   [wf_ind]  Theorem

      |- ∀wf'.
           (∀a fm.
              (∀k. k ∈ FDOM fm ⇒ wf' (fm ' k)) ⇒ wf' (construct a fm)) ⇒
           ∀a0. wf a0 ⇒ wf' a0

   [wf_rules]  Theorem

      |- ∀a fm. (∀k. k ∈ FDOM fm ⇒ wf (fm ' k)) ⇒ wf (construct a fm)

   [wf_strongind]  Theorem

      |- ∀wf'.
           (∀a fm.
              (∀k. k ∈ FDOM fm ⇒ wf (fm ' k) ∧ wf' (fm ' k)) ⇒
              wf' (construct a fm)) ⇒
           ∀a0. wf a0 ⇒ wf' a0


*)
end
