signature quoteTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val index_TY_DEF : thm
    val index_case_def : thm
    val index_compare_curried_def : thm
    val index_compare_tupled_primitive_def : thm
    val index_lt_def : thm
    val index_size_def : thm
    val varmap_TY_DEF : thm
    val varmap_case_def : thm
    val varmap_find_curried_def : thm
    val varmap_find_tupled_primitive_def : thm
    val varmap_size_def : thm

  (*  Theorems  *)
    val compare_index_equal : thm
    val compare_list_index : thm
    val datatype_index : thm
    val datatype_varmap : thm
    val index_11 : thm
    val index_Axiom : thm
    val index_case_cong : thm
    val index_compare_def : thm
    val index_compare_ind : thm
    val index_distinct : thm
    val index_induction : thm
    val index_nchotomy : thm
    val varmap_11 : thm
    val varmap_Axiom : thm
    val varmap_case_cong : thm
    val varmap_distinct : thm
    val varmap_find_def : thm
    val varmap_find_ind : thm
    val varmap_induction : thm
    val varmap_nchotomy : thm

  val quote_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [prelim] Parent theory of "quote"

   [index_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'index' .
                  (∀a0.
                     (∃a.
                        (a0 =
                         (λa.
                            ind_type$CONSTR 0 ARB
                              (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                           a) ∧ 'index' a) ∨
                     (∃a.
                        (a0 =
                         (λa.
                            ind_type$CONSTR (SUC 0) ARB
                              (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                           a) ∧ 'index' a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC 0)) ARB
                        (λn. ind_type$BOTTOM)) ⇒
                     'index' a0) ⇒
                  'index' a0) rep

   [index_case_def]  Definition

      |- (∀a f f1 v. index_CASE (Left_idx a) f f1 v = f a) ∧
         (∀a f f1 v. index_CASE (Right_idx a) f f1 v = f1 a) ∧
         ∀f f1 v. index_CASE End_idx f f1 v = v

   [index_compare_curried_def]  Definition

      |- ∀x x1. index_compare x x1 = index_compare_tupled (x,x1)

   [index_compare_tupled_primitive_def]  Definition

      |- index_compare_tupled =
         WFREC
           (@R.
              WF R ∧ (∀m' n'. R (n',m') (Left_idx n',Left_idx m')) ∧
              ∀m' n'. R (n',m') (Right_idx n',Right_idx m'))
           (λindex_compare_tupled a.
              case a of
                (Left_idx n',Left_idx m') =>
                  I (index_compare_tupled (n',m'))
              | (Left_idx n',Right_idx m'') => I LESS
              | (Left_idx n',End_idx) => I GREATER
              | (Right_idx n'',Left_idx m'''') => I GREATER
              | (Right_idx n'',Right_idx m''') =>
                  I (index_compare_tupled (n'',m'''))
              | (Right_idx n'',End_idx) => I GREATER
              | (End_idx,Left_idx v12) => I LESS
              | (End_idx,Right_idx v13) => I LESS
              | (End_idx,End_idx) => I EQUAL)

   [index_lt_def]  Definition

      |- ∀i1 i2. index_lt i1 i2 ⇔ (index_compare i1 i2 = LESS)

   [index_size_def]  Definition

      |- (∀a. index_size (Left_idx a) = 1 + index_size a) ∧
         (∀a. index_size (Right_idx a) = 1 + index_size a) ∧
         (index_size End_idx = 0)

   [varmap_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'varmap' .
                  (∀a0'.
                     (a0' = ind_type$CONSTR 0 ARB (λn. ind_type$BOTTOM)) ∨
                     (∃a0 a1 a2.
                        (a0' =
                         (λa0 a1 a2.
                            ind_type$CONSTR (SUC 0) a0
                              (ind_type$FCONS a1
                                 (ind_type$FCONS a2
                                    (λn. ind_type$BOTTOM)))) a0 a1 a2) ∧
                        'varmap' a1 ∧ 'varmap' a2) ⇒
                     'varmap' a0') ⇒
                  'varmap' a0') rep

   [varmap_case_def]  Definition

      |- (∀v f. varmap_CASE Empty_vm v f = v) ∧
         ∀a0 a1 a2 v f. varmap_CASE (Node_vm a0 a1 a2) v f = f a0 a1 a2

   [varmap_find_curried_def]  Definition

      |- ∀x x1. varmap_find x x1 = varmap_find_tupled (x,x1)

   [varmap_find_tupled_primitive_def]  Definition

      |- varmap_find_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀v1 x v2 i1. R (i1,v2) (Right_idx i1,Node_vm x v1 v2)) ∧
              ∀v2 x v1 i1. R (i1,v1) (Left_idx i1,Node_vm x v1 v2))
           (λvarmap_find_tupled a.
              case a of
                (v3,Empty_vm) => I (@x. T)
              | (Left_idx i1',Node_vm x v1 v2) =>
                  I (varmap_find_tupled (i1',v1))
              | (Right_idx i1,Node_vm x v1 v2) =>
                  I (varmap_find_tupled (i1,v2))
              | (End_idx,Node_vm x v1 v2) => I x)

   [varmap_size_def]  Definition

      |- (∀f. varmap_size f Empty_vm = 0) ∧
         ∀f a0 a1 a2.
           varmap_size f (Node_vm a0 a1 a2) =
           1 + (f a0 + (varmap_size f a1 + varmap_size f a2))

   [compare_index_equal]  Theorem

      |- ∀i1 i2. (index_compare i1 i2 = EQUAL) ⇔ (i1 = i2)

   [compare_list_index]  Theorem

      |- ∀l1 l2. (list_compare index_compare l1 l2 = EQUAL) ⇔ (l1 = l2)

   [datatype_index]  Theorem

      |- DATATYPE (index Left_idx Right_idx End_idx)

   [datatype_varmap]  Theorem

      |- DATATYPE (varmap Empty_vm Node_vm)

   [index_11]  Theorem

      |- (∀a a'. (Left_idx a = Left_idx a') ⇔ (a = a')) ∧
         ∀a a'. (Right_idx a = Right_idx a') ⇔ (a = a')

   [index_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (∀a. fn (Left_idx a) = f0 a (fn a)) ∧
             (∀a. fn (Right_idx a) = f1 a (fn a)) ∧ (fn End_idx = f2)

   [index_case_cong]  Theorem

      |- ∀M M' f f1 v.
           (M = M') ∧ (∀a. (M' = Left_idx a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = Right_idx a) ⇒ (f1 a = f1' a)) ∧
           ((M' = End_idx) ⇒ (v = v')) ⇒
           (index_CASE M f f1 v = index_CASE M' f' f1' v')

   [index_compare_def]  Theorem

      |- (index_compare End_idx End_idx = EQUAL) ∧
         (∀v10. index_compare End_idx (Left_idx v10) = LESS) ∧
         (∀v11. index_compare End_idx (Right_idx v11) = LESS) ∧
         (∀v2. index_compare (Left_idx v2) End_idx = GREATER) ∧
         (∀v3. index_compare (Right_idx v3) End_idx = GREATER) ∧
         (∀n' m'.
            index_compare (Left_idx n') (Left_idx m') =
            index_compare n' m') ∧
         (∀n' m'. index_compare (Left_idx n') (Right_idx m') = LESS) ∧
         (∀n' m'.
            index_compare (Right_idx n') (Right_idx m') =
            index_compare n' m') ∧
         ∀n' m'. index_compare (Right_idx n') (Left_idx m') = GREATER

   [index_compare_ind]  Theorem

      |- ∀P.
           P End_idx End_idx ∧ (∀v10. P End_idx (Left_idx v10)) ∧
           (∀v11. P End_idx (Right_idx v11)) ∧
           (∀v2. P (Left_idx v2) End_idx) ∧
           (∀v3. P (Right_idx v3) End_idx) ∧
           (∀n' m'. P n' m' ⇒ P (Left_idx n') (Left_idx m')) ∧
           (∀n' m'. P (Left_idx n') (Right_idx m')) ∧
           (∀n' m'. P n' m' ⇒ P (Right_idx n') (Right_idx m')) ∧
           (∀n' m'. P (Right_idx n') (Left_idx m')) ⇒
           ∀v v1. P v v1

   [index_distinct]  Theorem

      |- (∀a' a. Left_idx a ≠ Right_idx a') ∧ (∀a. Left_idx a ≠ End_idx) ∧
         ∀a. Right_idx a ≠ End_idx

   [index_induction]  Theorem

      |- ∀P.
           (∀i. P i ⇒ P (Left_idx i)) ∧ (∀i. P i ⇒ P (Right_idx i)) ∧
           P End_idx ⇒
           ∀i. P i

   [index_nchotomy]  Theorem

      |- ∀ii.
           (∃i. ii = Left_idx i) ∨ (∃i. ii = Right_idx i) ∨ (ii = End_idx)

   [varmap_11]  Theorem

      |- ∀a0 a1 a2 a0' a1' a2'.
           (Node_vm a0 a1 a2 = Node_vm a0' a1' a2') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2')

   [varmap_Axiom]  Theorem

      |- ∀f0 f1.
           ∃fn.
             (fn Empty_vm = f0) ∧
             ∀a0 a1 a2. fn (Node_vm a0 a1 a2) = f1 a0 a1 a2 (fn a1) (fn a2)

   [varmap_case_cong]  Theorem

      |- ∀M M' v f.
           (M = M') ∧ ((M' = Empty_vm) ⇒ (v = v')) ∧
           (∀a0 a1 a2.
              (M' = Node_vm a0 a1 a2) ⇒ (f a0 a1 a2 = f' a0 a1 a2)) ⇒
           (varmap_CASE M v f = varmap_CASE M' v' f')

   [varmap_distinct]  Theorem

      |- ∀a2 a1 a0. Empty_vm ≠ Node_vm a0 a1 a2

   [varmap_find_def]  Theorem

      |- (∀x v2 v1. varmap_find End_idx (Node_vm x v1 v2) = x) ∧
         (∀x v2 v1 i1.
            varmap_find (Right_idx i1) (Node_vm x v1 v2) =
            varmap_find i1 v2) ∧
         (∀x v2 v1 i1.
            varmap_find (Left_idx i1) (Node_vm x v1 v2) =
            varmap_find i1 v1) ∧ ∀i. varmap_find i Empty_vm = @x. T

   [varmap_find_ind]  Theorem

      |- ∀P.
           (∀x v1 v2. P End_idx (Node_vm x v1 v2)) ∧
           (∀i1 x v1 v2. P i1 v2 ⇒ P (Right_idx i1) (Node_vm x v1 v2)) ∧
           (∀i1 x v1 v2. P i1 v1 ⇒ P (Left_idx i1) (Node_vm x v1 v2)) ∧
           (∀i. P i Empty_vm) ⇒
           ∀v v1. P v v1

   [varmap_induction]  Theorem

      |- ∀P.
           P Empty_vm ∧ (∀v v0. P v ∧ P v0 ⇒ ∀a. P (Node_vm a v v0)) ⇒
           ∀v. P v

   [varmap_nchotomy]  Theorem

      |- ∀vv. (vv = Empty_vm) ∨ ∃a v v0. vv = Node_vm a v v0


*)
end
