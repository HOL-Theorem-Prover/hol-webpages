signature patriciaTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ADD_LIST_def : thm
    val ADD_curried_def : thm
    val ADD_tupled_primitive_def : thm
    val BRANCHING_BIT_curried_def : thm
    val BRANCHING_BIT_tupled_primitive_def : thm
    val BRANCH_primitive_def : thm
    val DEPTH_def : thm
    val EVERY_LEAF_def : thm
    val EXISTS_LEAF_def : thm
    val FIND_def : thm
    val INSERT_PTREE_def : thm
    val IN_PTREE_def : thm
    val IS_EMPTY_primitive_def : thm
    val IS_PTREE_def : thm
    val JOIN_def : thm
    val KEYS_def : thm
    val NUMSET_OF_PTREE_def : thm
    val PEEK_curried_def : thm
    val PEEK_tupled_primitive_def : thm
    val PTREE_OF_NUMSET_def : thm
    val REMOVE_def : thm
    val SIZE_def : thm
    val TRANSFORM_def : thm
    val TRAVERSE_AUX_def : thm
    val TRAVERSE_def : thm
    val UNION_PTREE_def : thm
    val ptree_TY_DEF : thm
    val ptree_case_def : thm
    val ptree_size_def : thm

  (*  Theorems  *)
    val ADD_ADD : thm
    val ADD_ADD_SYM : thm
    val ADD_INSERT : thm
    val ADD_IS_PTREE : thm
    val ADD_LIST_IS_PTREE : thm
    val ADD_TRANSFORM : thm
    val ADD_def : thm
    val ADD_ind : thm
    val ALL_DISTINCT_TRAVERSE : thm
    val BRANCH : thm
    val BRANCHING_BIT : thm
    val BRANCHING_BIT_SYM : thm
    val BRANCHING_BIT_ZERO : thm
    val BRANCHING_BIT_def : thm
    val BRANCHING_BIT_ind : thm
    val BRANCH_def : thm
    val BRANCH_ind : thm
    val CARD_LIST_TO_SET : thm
    val CARD_NUMSET_OF_PTREE : thm
    val DELETE_UNION : thm
    val EMPTY_IS_PTREE : thm
    val EVERY_LEAF_ADD : thm
    val EVERY_LEAF_BRANCH : thm
    val EVERY_LEAF_PEEK : thm
    val EVERY_LEAF_REMOVE : thm
    val EVERY_LEAF_TRANSFORM : thm
    val FILTER_ALL : thm
    val FILTER_NONE : thm
    val FINITE_NUMSET_OF_PTREE : thm
    val INSERT_PTREE_IS_PTREE : thm
    val IN_NUMSET_OF_PTREE : thm
    val IN_PTREE_EMPTY : thm
    val IN_PTREE_INSERT_PTREE : thm
    val IN_PTREE_OF_NUMSET : thm
    val IN_PTREE_OF_NUMSET_EMPTY : thm
    val IN_PTREE_REMOVE : thm
    val IN_PTREE_UNION_PTREE : thm
    val IS_EMPTY_def : thm
    val IS_EMPTY_ind : thm
    val IS_PTREE_BRANCH : thm
    val IS_PTREE_PEEK : thm
    val KEYS_PEEK : thm
    val MEM_ALL_DISTINCT_IMP_PERM : thm
    val MEM_TRAVERSE : thm
    val MEM_TRAVERSE_INSERT_PTREE : thm
    val MEM_TRAVERSE_PEEK : thm
    val MONO_EVERY_LEAF : thm
    val NOT_ADD_EMPTY : thm
    val NOT_KEY_LEFT_AND_RIGHT : thm
    val NUMSET_OF_PTREE_EMPTY : thm
    val NUMSET_OF_PTREE_PTREE_OF_NUMSET : thm
    val NUMSET_OF_PTREE_PTREE_OF_NUMSET_EMPTY : thm
    val PEEK_ADD : thm
    val PEEK_INSERT_PTREE : thm
    val PEEK_NONE : thm
    val PEEK_REMOVE : thm
    val PEEK_TRANSFORM : thm
    val PEEK_def : thm
    val PEEK_ind : thm
    val PERM_ADD : thm
    val PERM_DELETE_PTREE : thm
    val PERM_INSERT_PTREE : thm
    val PERM_NOT_ADD : thm
    val PERM_NOT_REMOVE : thm
    val PERM_REMOVE : thm
    val PTREE_EQ : thm
    val PTREE_EXTENSION : thm
    val PTREE_OF_NUMSET_DELETE : thm
    val PTREE_OF_NUMSET_EMPTY : thm
    val PTREE_OF_NUMSET_INSERT : thm
    val PTREE_OF_NUMSET_INSERT_EMPTY : thm
    val PTREE_OF_NUMSET_IS_PTREE : thm
    val PTREE_OF_NUMSET_IS_PTREE_EMPTY : thm
    val PTREE_OF_NUMSET_NUMSET_OF_PTREE : thm
    val PTREE_OF_NUMSET_UNION : thm
    val PTREE_TRAVERSE_EQ : thm
    val QSORT_MEM_EQ : thm
    val REMOVE_ADD : thm
    val REMOVE_ADD_EQ : thm
    val REMOVE_IS_PTREE : thm
    val REMOVE_REMOVE : thm
    val REMOVE_TRANSFORM : thm
    val SIZE : thm
    val SIZE_ADD : thm
    val SIZE_PTREE_OF_NUMSET : thm
    val SIZE_PTREE_OF_NUMSET_EMPTY : thm
    val SIZE_REMOVE : thm
    val TRANSFORM_BRANCH : thm
    val TRANSFORM_EMPTY : thm
    val TRANSFORM_IS_PTREE : thm
    val TRAVERSE_AUX : thm
    val TRAVERSE_TRANSFORM : thm
    val UNION_PTREE_ASSOC : thm
    val UNION_PTREE_COMM : thm
    val UNION_PTREE_COMM_EMPTY : thm
    val UNION_PTREE_EMPTY : thm
    val UNION_PTREE_IS_PTREE : thm
    val datatype_ptree : thm
    val ptree_11 : thm
    val ptree_Axiom : thm
    val ptree_case_cong : thm
    val ptree_distinct : thm
    val ptree_induction : thm
    val ptree_nchotomy : thm

  val patricia_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [sorting] Parent theory of "patricia"

   [words] Parent theory of "patricia"

   [ADD_LIST_def]  Definition

      |- $|++ = FOLDL $|+

   [ADD_curried_def]  Definition

      |- ∀x x1. x |+ x1 = ADD_tupled (x,x1)

   [ADD_tupled_primitive_def]  Definition

      |- ADD_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀l e r p k m.
                 MOD_2EXP_EQ m k p ∧ ¬BIT m k ⇒
                 R (r,k,e) (Branch p m l r,k,e)) ∧
              ∀r e l p k m.
                MOD_2EXP_EQ m k p ∧ BIT m k ⇒
                R (l,k,e) (Branch p m l r,k,e))
           (λADD_tupled a.
              case a of
                (<{}>,k,e) => I (Leaf k e)
              | (Leaf j d,k',e') =>
                  I
                    (if j = k' then
                       Leaf k' e'
                     else
                       JOIN (k',Leaf k' e',j,Leaf j d))
              | (Branch p m l r,k'',e'') =>
                  I
                    (if MOD_2EXP_EQ m k'' p then
                       if BIT m k'' then
                         Branch p m (ADD_tupled (l,k'',e'')) r
                       else
                         Branch p m l (ADD_tupled (r,k'',e''))
                     else
                       JOIN (k'',Leaf k'' e'',p,Branch p m l r)))

   [BRANCHING_BIT_curried_def]  Definition

      |- ∀x x1. BRANCHING_BIT x x1 = BRANCHING_BIT_tupled (x,x1)

   [BRANCHING_BIT_tupled_primitive_def]  Definition

      |- BRANCHING_BIT_tupled =
         WFREC
           (@R.
              WF R ∧
              ∀p1 p0.
                ¬((ODD p0 ⇔ EVEN p1) ∨ (p0 = p1)) ⇒
                R (DIV2 p0,DIV2 p1) (p0,p1))
           (λBRANCHING_BIT_tupled a.
              case a of
                (p0,p1) =>
                  I
                    (if (ODD p0 ⇔ EVEN p1) ∨ (p0 = p1) then
                       0
                     else
                       SUC (BRANCHING_BIT_tupled (DIV2 p0,DIV2 p1))))

   [BRANCH_primitive_def]  Definition

      |- BRANCH =
         WFREC (@R. WF R)
           (λBRANCH a.
              case a of
                (v,v2,<{}>,<{}>) => I <{}>
              | (v,v2,<{}>,Leaf v36 v37) => I (Leaf v36 v37)
              | (v,v2,<{}>,Branch v38 v39 v40 v41) =>
                  I (Branch v38 v39 v40 v41)
              | (v,v2,Leaf v18 v19,<{}>) => I (Leaf v18 v19)
              | (v,v2,Leaf v18 v19,Leaf v48 v49) =>
                  I (Branch v v2 (Leaf v18 v19) (Leaf v48 v49))
              | (v,v2,Leaf v18 v19,Branch v50 v51 v52 v53) =>
                  I (Branch v v2 (Leaf v18 v19) (Branch v50 v51 v52 v53))
              | (v,v2,Branch v20 v21 v22 v23,<{}>) =>
                  I (Branch v20 v21 v22 v23)
              | (v,v2,Branch v20 v21 v22 v23,Leaf v60 v61) =>
                  I (Branch v v2 (Branch v20 v21 v22 v23) (Leaf v60 v61))
              | (v,v2,Branch v20 v21 v22 v23,Branch v62 v63 v64 v65) =>
                  I
                    (Branch v v2 (Branch v20 v21 v22 v23)
                       (Branch v62 v63 v64 v65)))

   [DEPTH_def]  Definition

      |- (DEPTH <{}> = 0) ∧ (∀j d. DEPTH (Leaf j d) = 1) ∧
         ∀p m l r. DEPTH (Branch p m l r) = 1 + MAX (DEPTH l) (DEPTH r)

   [EVERY_LEAF_def]  Definition

      |- (∀P. EVERY_LEAF P <{}> ⇔ T) ∧
         (∀P j d. EVERY_LEAF P (Leaf j d) ⇔ P j d) ∧
         ∀P p m l r.
           EVERY_LEAF P (Branch p m l r) ⇔ EVERY_LEAF P l ∧ EVERY_LEAF P r

   [EXISTS_LEAF_def]  Definition

      |- (∀P. EXISTS_LEAF P <{}> ⇔ F) ∧
         (∀P j d. EXISTS_LEAF P (Leaf j d) ⇔ P j d) ∧
         ∀P p m l r.
           EXISTS_LEAF P (Branch p m l r) ⇔
           EXISTS_LEAF P l ∨ EXISTS_LEAF P r

   [FIND_def]  Definition

      |- ∀t k. FIND t k = THE (t ' k)

   [INSERT_PTREE_def]  Definition

      |- ∀n t. n INSERT_PTREE t = t |+ (n,())

   [IN_PTREE_def]  Definition

      |- ∀n t. n IN_PTREE t ⇔ IS_SOME (t ' n)

   [IS_EMPTY_primitive_def]  Definition

      |- IS_EMPTY =
         WFREC (@R. WF R)
           (λIS_EMPTY a.
              case a of
                <{}> => I T
              | Leaf v6 v7 => I F
              | Branch v8 v9 v10 v11 => I F)

   [IS_PTREE_def]  Definition

      |- (IS_PTREE <{}> ⇔ T) ∧ (∀k d. IS_PTREE (Leaf k d) ⇔ T) ∧
         ∀p m l r.
           IS_PTREE (Branch p m l r) ⇔
           p < 2 ** m ∧ IS_PTREE l ∧ IS_PTREE r ∧ l ≠ <{}> ∧ r ≠ <{}> ∧
           EVERY_LEAF (λk d. MOD_2EXP_EQ m k p ∧ BIT m k) l ∧
           EVERY_LEAF (λk d. MOD_2EXP_EQ m k p ∧ ¬BIT m k) r

   [JOIN_def]  Definition

      |- ∀p0 t0 p1 t1.
           JOIN (p0,t0,p1,t1) =
           (let m = BRANCHING_BIT p0 p1
            in
              if BIT m p0 then
                Branch (MOD_2EXP m p0) m t0 t1
              else
                Branch (MOD_2EXP m p0) m t1 t0)

   [KEYS_def]  Definition

      |- ∀t. KEYS t = QSORT $< (TRAVERSE t)

   [NUMSET_OF_PTREE_def]  Definition

      |- ∀t. NUMSET_OF_PTREE t = LIST_TO_SET (TRAVERSE t)

   [PEEK_curried_def]  Definition

      |- ∀x x1. x ' x1 = PEEK_tupled (x,x1)

   [PEEK_tupled_primitive_def]  Definition

      |- PEEK_tupled =
         WFREC
           (@R.
              WF R ∧
              ∀p r l k m.
                R (if BIT m k then l else r,k) (Branch p m l r,k))
           (λPEEK_tupled a.
              case a of
                (<{}>,k) => I NONE
              | (Leaf j d,k) => I (if k = j then SOME d else NONE)
              | (Branch p m l r,k) =>
                  I (PEEK_tupled (if BIT m k then l else r,k)))

   [PTREE_OF_NUMSET_def]  Definition

      |- ∀t s. t |++ s = FOLDL (combin$C $INSERT_PTREE) t (SET_TO_LIST s)

   [REMOVE_def]  Definition

      |- (∀k. <{}> \\ k = <{}>) ∧
         (∀j d k. Leaf j d \\ k = if j = k then <{}> else Leaf j d) ∧
         ∀p m l r k.
           Branch p m l r \\ k =
           if MOD_2EXP_EQ m k p then
             if BIT m k then
               BRANCH (p,m,l \\ k,r)
             else
               BRANCH (p,m,l,r \\ k)
           else
             Branch p m l r

   [SIZE_def]  Definition

      |- ∀t. SIZE t = LENGTH (TRAVERSE t)

   [TRANSFORM_def]  Definition

      |- (∀f. TRANSFORM f <{}> = <{}>) ∧
         (∀f j d. TRANSFORM f (Leaf j d) = Leaf j (f d)) ∧
         ∀f p m l r.
           TRANSFORM f (Branch p m l r) =
           Branch p m (TRANSFORM f l) (TRANSFORM f r)

   [TRAVERSE_AUX_def]  Definition

      |- (∀a. TRAVERSE_AUX <{}> a = a) ∧
         (∀k d a. TRAVERSE_AUX (Leaf k d) a = k::a) ∧
         ∀p m l r a.
           TRAVERSE_AUX (Branch p m l r) a =
           TRAVERSE_AUX l (TRAVERSE_AUX r a)

   [TRAVERSE_def]  Definition

      |- (TRAVERSE <{}> = []) ∧ (∀j d. TRAVERSE (Leaf j d) = [j]) ∧
         ∀p m l r. TRAVERSE (Branch p m l r) = TRAVERSE l ++ TRAVERSE r

   [UNION_PTREE_def]  Definition

      |- ∀t1 t2. t1 UNION_PTREE t2 = t1 |++ NUMSET_OF_PTREE t2

   [ptree_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'ptree' .
                  (∀a0'.
                     (a0' =
                      ind_type$CONSTR 0 (ARB,ARB,ARB)
                        (λn. ind_type$BOTTOM)) ∨
                     (∃a0 a1.
                        a0' =
                        (λa0 a1.
                           ind_type$CONSTR (SUC 0) (a0,a1,ARB)
                             (λn. ind_type$BOTTOM)) a0 a1) ∨
                     (∃a0 a1 a2 a3.
                        (a0' =
                         (λa0 a1 a2 a3.
                            ind_type$CONSTR (SUC (SUC 0)) (a0,ARB,a1)
                              (ind_type$FCONS a2
                                 (ind_type$FCONS a3
                                    (λn. ind_type$BOTTOM)))) a0 a1 a2 a3) ∧
                        'ptree' a2 ∧ 'ptree' a3) ⇒
                     'ptree' a0') ⇒
                  'ptree' a0') rep

   [ptree_case_def]  Definition

      |- (∀v f f1. ptree_case v f f1 <{}> = v) ∧
         (∀v f f1 a0 a1. ptree_case v f f1 (Leaf a0 a1) = f a0 a1) ∧
         ∀v f f1 a0 a1 a2 a3.
           ptree_case v f f1 (Branch a0 a1 a2 a3) = f1 a0 a1 a2 a3

   [ptree_size_def]  Definition

      |- (∀f. ptree_size f <{}> = 0) ∧
         (∀f a0 a1. ptree_size f (Leaf a0 a1) = 1 + (a0 + f a1)) ∧
         ∀f a0 a1 a2 a3.
           ptree_size f (Branch a0 a1 a2 a3) =
           1 + (a0 + (a1 + (ptree_size f a2 + ptree_size f a3)))

   [ADD_ADD]  Theorem

      |- ∀t k d e. t |+ (k,d) |+ (k,e) = t |+ (k,e)

   [ADD_ADD_SYM]  Theorem

      |- ∀t k j d e.
           IS_PTREE t ∧ k ≠ j ⇒ (t |+ (k,d) |+ (j,e) = t |+ (j,e) |+ (k,d))

   [ADD_INSERT]  Theorem

      |- ∀v t n. t |+ (n,v) = n INSERT_PTREE t

   [ADD_IS_PTREE]  Theorem

      |- ∀t x. IS_PTREE t ⇒ IS_PTREE (t |+ x)

   [ADD_LIST_IS_PTREE]  Theorem

      |- ∀t l. IS_PTREE t ⇒ IS_PTREE (t |++ l)

   [ADD_TRANSFORM]  Theorem

      |- ∀f t k d. TRANSFORM f (t |+ (k,d)) = TRANSFORM f t |+ (k,f d)

   [ADD_def]  Theorem

      |- (∀k e. <{}> |+ (k,e) = Leaf k e) ∧
         (∀k j e d.
            Leaf j d |+ (k,e) =
            if j = k then Leaf k e else JOIN (k,Leaf k e,j,Leaf j d)) ∧
         ∀r p m l k e.
           Branch p m l r |+ (k,e) =
           if MOD_2EXP_EQ m k p then
             if BIT m k then
               Branch p m (l |+ (k,e)) r
             else
               Branch p m l (r |+ (k,e))
           else
             JOIN (k,Leaf k e,p,Branch p m l r)

   [ADD_ind]  Theorem

      |- ∀P.
           (∀k e. P <{}> (k,e)) ∧ (∀j d k e. P (Leaf j d) (k,e)) ∧
           (∀p m l r k e.
              (MOD_2EXP_EQ m k p ∧ ¬BIT m k ⇒ P r (k,e)) ∧
              (MOD_2EXP_EQ m k p ∧ BIT m k ⇒ P l (k,e)) ⇒
              P (Branch p m l r) (k,e)) ⇒
           ∀v v1 v2. P v (v1,v2)

   [ALL_DISTINCT_TRAVERSE]  Theorem

      |- ∀t. IS_PTREE t ⇒ ALL_DISTINCT (TRAVERSE t)

   [BRANCH]  Theorem

      |- ∀p m l r.
           BRANCH (p,m,l,r) =
           if l = <{}> then r else if r = <{}> then l else Branch p m l r

   [BRANCHING_BIT]  Theorem

      |- ∀a b.
           a ≠ b ⇒ (BIT (BRANCHING_BIT a b) a ⇎ BIT (BRANCHING_BIT a b) b)

   [BRANCHING_BIT_SYM]  Theorem

      |- ∀a b. BRANCHING_BIT a b = BRANCHING_BIT b a

   [BRANCHING_BIT_ZERO]  Theorem

      |- ∀a b. (BRANCHING_BIT a b = 0) ⇔ (ODD a ⇔ EVEN b) ∨ (a = b)

   [BRANCHING_BIT_def]  Theorem

      |- ∀p1 p0.
           BRANCHING_BIT p0 p1 =
           if (ODD p0 ⇔ EVEN p1) ∨ (p0 = p1) then
             0
           else
             SUC (BRANCHING_BIT (DIV2 p0) (DIV2 p1))

   [BRANCHING_BIT_ind]  Theorem

      |- ∀P.
           (∀p0 p1.
              (¬((ODD p0 ⇔ EVEN p1) ∨ (p0 = p1)) ⇒ P (DIV2 p0) (DIV2 p1)) ⇒
              P p0 p1) ⇒
           ∀v v1. P v v1

   [BRANCH_def]  Theorem

      |- (BRANCH (p,m,<{}>,<{}>) = <{}>) ∧
         (BRANCH (p,m,<{}>,Leaf v24 v25) = Leaf v24 v25) ∧
         (BRANCH (p,m,<{}>,Branch v26 v27 v28 v29) =
          Branch v26 v27 v28 v29) ∧
         (BRANCH (p,m,Leaf v6 v7,<{}>) = Leaf v6 v7) ∧
         (BRANCH (p,m,Branch v8 v9 v10 v11,<{}>) = Branch v8 v9 v10 v11) ∧
         (BRANCH (p,m,Leaf v12 v13,Leaf v42 v43) =
          Branch p m (Leaf v12 v13) (Leaf v42 v43)) ∧
         (BRANCH (p,m,Leaf v12 v13,Branch v44 v45 v46 v47) =
          Branch p m (Leaf v12 v13) (Branch v44 v45 v46 v47)) ∧
         (BRANCH (p,m,Branch v14 v15 v16 v17,Leaf v54 v55) =
          Branch p m (Branch v14 v15 v16 v17) (Leaf v54 v55)) ∧
         (BRANCH (p,m,Branch v14 v15 v16 v17,Branch v56 v57 v58 v59) =
          Branch p m (Branch v14 v15 v16 v17) (Branch v56 v57 v58 v59))

   [BRANCH_ind]  Theorem

      |- ∀P.
           (∀p m. P (p,m,<{}>,<{}>)) ∧
           (∀p m v24 v25. P (p,m,<{}>,Leaf v24 v25)) ∧
           (∀p m v26 v27 v28 v29. P (p,m,<{}>,Branch v26 v27 v28 v29)) ∧
           (∀p m v6 v7. P (p,m,Leaf v6 v7,<{}>)) ∧
           (∀p m v8 v9 v10 v11. P (p,m,Branch v8 v9 v10 v11,<{}>)) ∧
           (∀p m v12 v13 v42 v43. P (p,m,Leaf v12 v13,Leaf v42 v43)) ∧
           (∀p m v12 v13 v44 v45 v46 v47.
              P (p,m,Leaf v12 v13,Branch v44 v45 v46 v47)) ∧
           (∀p m v14 v15 v16 v17 v54 v55.
              P (p,m,Branch v14 v15 v16 v17,Leaf v54 v55)) ∧
           (∀p m v14 v15 v16 v17 v56 v57 v58 v59.
              P (p,m,Branch v14 v15 v16 v17,Branch v56 v57 v58 v59)) ⇒
           ∀v v1 v2 v3. P (v,v1,v2,v3)

   [CARD_LIST_TO_SET]  Theorem

      |- ∀l. ALL_DISTINCT l ⇒ (CARD (LIST_TO_SET l) = LENGTH l)

   [CARD_NUMSET_OF_PTREE]  Theorem

      |- ∀t. IS_PTREE t ⇒ (CARD (NUMSET_OF_PTREE t) = SIZE t)

   [DELETE_UNION]  Theorem

      |- ∀x s1 s2. s1 ∪ s2 DELETE x = s1 DELETE x ∪ (s2 DELETE x)

   [EMPTY_IS_PTREE]  Theorem

      |- IS_PTREE <{}>

   [EVERY_LEAF_ADD]  Theorem

      |- ∀P t k d. P k d ∧ EVERY_LEAF P t ⇒ EVERY_LEAF P (t |+ (k,d))

   [EVERY_LEAF_BRANCH]  Theorem

      |- ∀P p m l r.
           EVERY_LEAF P (BRANCH (p,m,l,r)) ⇔
           EVERY_LEAF P l ∧ EVERY_LEAF P r

   [EVERY_LEAF_PEEK]  Theorem

      |- ∀P t k. EVERY_LEAF P t ∧ IS_SOME (t ' k) ⇒ P k (THE (t ' k))

   [EVERY_LEAF_REMOVE]  Theorem

      |- ∀P t k. EVERY_LEAF P t ⇒ EVERY_LEAF P (t \\ k)

   [EVERY_LEAF_TRANSFORM]  Theorem

      |- ∀P Q f t.
           (∀k d. P k d ⇒ Q k (f d)) ∧ EVERY_LEAF P t ⇒
           EVERY_LEAF Q (TRANSFORM f t)

   [FILTER_ALL]  Theorem

      |- ∀P l. (∀n. n < LENGTH l ⇒ ¬P (EL n l)) ⇔ (FILTER P l = [])

   [FILTER_NONE]  Theorem

      |- ∀P l. (∀n. n < LENGTH l ⇒ P (EL n l)) ⇒ (FILTER P l = l)

   [FINITE_NUMSET_OF_PTREE]  Theorem

      |- ∀t. FINITE (NUMSET_OF_PTREE t)

   [INSERT_PTREE_IS_PTREE]  Theorem

      |- ∀t x. IS_PTREE t ⇒ IS_PTREE (x INSERT_PTREE t)

   [IN_NUMSET_OF_PTREE]  Theorem

      |- ∀t n. IS_PTREE t ⇒ (n ∈ NUMSET_OF_PTREE t ⇔ n IN_PTREE t)

   [IN_PTREE_EMPTY]  Theorem

      |- ∀n. ¬(n IN_PTREE <{}>)

   [IN_PTREE_INSERT_PTREE]  Theorem

      |- ∀t m n.
           IS_PTREE t ⇒
           (n IN_PTREE m INSERT_PTREE t ⇔ (m = n) ∨ n IN_PTREE t)

   [IN_PTREE_OF_NUMSET]  Theorem

      |- ∀t s n.
           IS_PTREE t ∧ FINITE s ⇒
           (n IN_PTREE t |++ s ⇔ n IN_PTREE t ∨ n ∈ s)

   [IN_PTREE_OF_NUMSET_EMPTY]  Theorem

      |- ∀s n. FINITE s ⇒ (n ∈ s ⇔ n IN_PTREE <{}> |++ s)

   [IN_PTREE_REMOVE]  Theorem

      |- ∀t m n. IS_PTREE t ⇒ (n IN_PTREE t \\ m ⇔ n ≠ m ∧ n IN_PTREE t)

   [IN_PTREE_UNION_PTREE]  Theorem

      |- ∀t1 t2 n.
           IS_PTREE t1 ∧ IS_PTREE t2 ⇒
           (n IN_PTREE t1 UNION_PTREE t2 ⇔ n IN_PTREE t1 ∨ n IN_PTREE t2)

   [IS_EMPTY_def]  Theorem

      |- (IS_EMPTY <{}> ⇔ T) ∧ (IS_EMPTY (Leaf v v1) ⇔ F) ∧
         (IS_EMPTY (Branch v2 v3 v4 v5) ⇔ F)

   [IS_EMPTY_ind]  Theorem

      |- ∀P.
           P <{}> ∧ (∀v v1. P (Leaf v v1)) ∧
           (∀v2 v3 v4 v5. P (Branch v2 v3 v4 v5)) ⇒
           ∀v. P v

   [IS_PTREE_BRANCH]  Theorem

      |- ∀p m l r.
           p < 2 ** m ∧ ¬((l = <{}>) ∧ (r = <{}>)) ∧
           EVERY_LEAF (λk d. MOD_2EXP_EQ m k p ∧ BIT m k) l ∧
           EVERY_LEAF (λk d. MOD_2EXP_EQ m k p ∧ ¬BIT m k) r ∧ IS_PTREE l ∧
           IS_PTREE r ⇒
           IS_PTREE (BRANCH (p,m,l,r))

   [IS_PTREE_PEEK]  Theorem

      |- (∀k. ¬IS_SOME (<{}> ' k)) ∧
         (∀k j b. IS_SOME (Leaf j b ' k) ⇔ (j = k)) ∧
         ∀p m l r.
           IS_PTREE (Branch p m l r) ⇒
           (∃k. BIT m k ∧ IS_SOME (l ' k)) ∧
           (∃k. ¬BIT m k ∧ IS_SOME (r ' k)) ∧
           ∀k n.
             ¬MOD_2EXP_EQ m k p ∨ n < m ∧ (BIT n p ⇎ BIT n k) ⇒
             ¬IS_SOME (l ' k) ∧ ¬IS_SOME (r ' k)

   [KEYS_PEEK]  Theorem

      |- ∀t1 t2.
           IS_PTREE t1 ∧ IS_PTREE t2 ⇒
           ((KEYS t1 = KEYS t2) ⇔ (TRAVERSE t1 = TRAVERSE t2))

   [MEM_ALL_DISTINCT_IMP_PERM]  Theorem

      |- ∀l1 l2.
           ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 ∧ (∀x. MEM x l1 ⇔ MEM x l2) ⇒
           PERM l1 l2

   [MEM_TRAVERSE]  Theorem

      |- ∀t k. IS_PTREE t ⇒ (MEM k (TRAVERSE t) ⇔ k ∈ NUMSET_OF_PTREE t)

   [MEM_TRAVERSE_INSERT_PTREE]  Theorem

      |- ∀t x h.
           IS_PTREE t ⇒
           (MEM x (TRAVERSE (h INSERT_PTREE t)) ⇔
            (x = h) ∨ x ≠ h ∧ MEM x (TRAVERSE t))

   [MEM_TRAVERSE_PEEK]  Theorem

      |- ∀t k. IS_PTREE t ⇒ (MEM k (TRAVERSE t) ⇔ IS_SOME (t ' k))

   [MONO_EVERY_LEAF]  Theorem

      |- ∀P Q t. (∀k d. P k d ⇒ Q k d) ∧ EVERY_LEAF P t ⇒ EVERY_LEAF Q t

   [NOT_ADD_EMPTY]  Theorem

      |- ∀t k d. t |+ (k,d) ≠ <{}>

   [NOT_KEY_LEFT_AND_RIGHT]  Theorem

      |- ∀p m l r k j.
           IS_PTREE (Branch p m l r) ∧ IS_SOME (l ' k) ∧ IS_SOME (r ' j) ⇒
           k ≠ j

   [NUMSET_OF_PTREE_EMPTY]  Theorem

      |- NUMSET_OF_PTREE <{}> = ∅

   [NUMSET_OF_PTREE_PTREE_OF_NUMSET]  Theorem

      |- ∀t s.
           IS_PTREE t ∧ FINITE s ⇒
           (NUMSET_OF_PTREE (t |++ s) = NUMSET_OF_PTREE t ∪ s)

   [NUMSET_OF_PTREE_PTREE_OF_NUMSET_EMPTY]  Theorem

      |- ∀s. FINITE s ⇒ (NUMSET_OF_PTREE (<{}> |++ s) = s)

   [PEEK_ADD]  Theorem

      |- ∀t k d j.
           IS_PTREE t ⇒
           ((t |+ (k,d)) ' j = if k = j then SOME d else t ' j)

   [PEEK_INSERT_PTREE]  Theorem

      |- ∀t k j.
           IS_PTREE t ⇒
           ((k INSERT_PTREE t) ' j = if k = j then SOME () else t ' j)

   [PEEK_NONE]  Theorem

      |- ∀P t k. (∀d. ¬P k d) ∧ EVERY_LEAF P t ⇒ (t ' k = NONE)

   [PEEK_REMOVE]  Theorem

      |- ∀t k j.
           IS_PTREE t ⇒ ((t \\ k) ' j = if k = j then NONE else t ' j)

   [PEEK_TRANSFORM]  Theorem

      |- ∀f t k.
           TRANSFORM f t ' k =
           case t ' k of NONE => NONE | SOME x => SOME (f x)

   [PEEK_def]  Theorem

      |- (∀k. <{}> ' k = NONE) ∧
         (∀k j d. Leaf j d ' k = if k = j then SOME d else NONE) ∧
         ∀r p m l k. Branch p m l r ' k = (if BIT m k then l else r) ' k

   [PEEK_ind]  Theorem

      |- ∀P.
           (∀k. P <{}> k) ∧ (∀j d k. P (Leaf j d) k) ∧
           (∀p m l r k.
              P (if BIT m k then l else r) k ⇒ P (Branch p m l r) k) ⇒
           ∀v v1. P v v1

   [PERM_ADD]  Theorem

      |- ∀t k d.
           IS_PTREE t ∧ ¬MEM k (TRAVERSE t) ⇒
           PERM (TRAVERSE (t |+ (k,d))) (k::TRAVERSE t)

   [PERM_DELETE_PTREE]  Theorem

      |- ∀t k.
           IS_PTREE t ∧ MEM k (TRAVERSE t) ⇒
           PERM (TRAVERSE (t \\ k)) (FILTER (λx. x ≠ k) (TRAVERSE t))

   [PERM_INSERT_PTREE]  Theorem

      |- ∀t s.
           FINITE s ⇒
           IS_PTREE t ⇒
           PERM
             (TRAVERSE (FOLDL (combin$C $INSERT_PTREE) t (SET_TO_LIST s)))
             (SET_TO_LIST (NUMSET_OF_PTREE t ∪ s))

   [PERM_NOT_ADD]  Theorem

      |- ∀t k d.
           IS_PTREE t ∧ MEM k (TRAVERSE t) ⇒
           (TRAVERSE (t |+ (k,d)) = TRAVERSE t)

   [PERM_NOT_REMOVE]  Theorem

      |- ∀t k.
           IS_PTREE t ∧ ¬MEM k (TRAVERSE t) ⇒
           (TRAVERSE (t \\ k) = TRAVERSE t)

   [PERM_REMOVE]  Theorem

      |- ∀t k.
           IS_PTREE t ∧ MEM k (TRAVERSE t) ⇒
           PERM (TRAVERSE (t \\ k)) (FILTER (λx. x ≠ k) (TRAVERSE t))

   [PTREE_EQ]  Theorem

      |- ∀t1 t2.
           IS_PTREE t1 ∧ IS_PTREE t2 ⇒ ((∀k. t1 ' k = t2 ' k) ⇔ (t1 = t2))

   [PTREE_EXTENSION]  Theorem

      |- ∀t1 t2.
           IS_PTREE t1 ∧ IS_PTREE t2 ⇒
           ((t1 = t2) ⇔ ∀x. x IN_PTREE t1 ⇔ x IN_PTREE t2)

   [PTREE_OF_NUMSET_DELETE]  Theorem

      |- ∀s x. FINITE s ⇒ (<{}> |++ (s DELETE x) = (<{}> |++ s) \\ x)

   [PTREE_OF_NUMSET_EMPTY]  Theorem

      |- ∀t. t |++ ∅ = t

   [PTREE_OF_NUMSET_INSERT]  Theorem

      |- ∀t s x.
           IS_PTREE t ∧ FINITE s ⇒
           (t |++ (x INSERT s) = x INSERT_PTREE t |++ s)

   [PTREE_OF_NUMSET_INSERT_EMPTY]  Theorem

      |- ∀s x.
           FINITE s ⇒ (<{}> |++ (x INSERT s) = x INSERT_PTREE <{}> |++ s)

   [PTREE_OF_NUMSET_IS_PTREE]  Theorem

      |- ∀t s. IS_PTREE t ⇒ IS_PTREE (t |++ s)

   [PTREE_OF_NUMSET_IS_PTREE_EMPTY]  Theorem

      |- ∀s. IS_PTREE (<{}> |++ s)

   [PTREE_OF_NUMSET_NUMSET_OF_PTREE]  Theorem

      |- ∀t s.
           IS_PTREE t ∧ FINITE s ⇒
           (<{}> |++ (NUMSET_OF_PTREE t ∪ s) = t |++ s)

   [PTREE_OF_NUMSET_UNION]  Theorem

      |- ∀t s1 s2.
           IS_PTREE t ∧ FINITE s1 ∧ FINITE s2 ⇒
           (t |++ (s1 ∪ s2) = t |++ s1 |++ s2)

   [PTREE_TRAVERSE_EQ]  Theorem

      |- ∀t1 t2.
           IS_PTREE t1 ∧ IS_PTREE t2 ⇒
           ((∀k. MEM k (TRAVERSE t1) ⇔ MEM k (TRAVERSE t2)) ⇔
            (TRAVERSE t1 = TRAVERSE t2))

   [QSORT_MEM_EQ]  Theorem

      |- ∀l2 l1 R. (QSORT R l1 = QSORT R l2) ⇒ ∀x. MEM x l1 ⇔ MEM x l2

   [REMOVE_ADD]  Theorem

      |- ∀t k d j.
           IS_PTREE t ⇒
           (t |+ (k,d) \\ j = if k = j then t \\ j else t \\ j |+ (k,d))

   [REMOVE_ADD_EQ]  Theorem

      |- ∀t k d. t |+ (k,d) \\ k = t \\ k

   [REMOVE_IS_PTREE]  Theorem

      |- ∀t k. IS_PTREE t ⇒ IS_PTREE (t \\ k)

   [REMOVE_REMOVE]  Theorem

      |- ∀t k. IS_PTREE t ⇒ (t \\ k \\ k = t \\ k)

   [REMOVE_TRANSFORM]  Theorem

      |- ∀f t k. TRANSFORM f (t \\ k) = TRANSFORM f t \\ k

   [SIZE]  Theorem

      |- (SIZE <{}> = 0) ∧ (∀k d. SIZE (Leaf k d) = 1) ∧
         ∀p m l r. SIZE (Branch p m l r) = SIZE l + SIZE r

   [SIZE_ADD]  Theorem

      |- ∀t k d.
           IS_PTREE t ⇒
           (SIZE (t |+ (k,d)) =
            if MEM k (TRAVERSE t) then SIZE t else SIZE t + 1)

   [SIZE_PTREE_OF_NUMSET]  Theorem

      |- ∀t s.
           FINITE s ⇒
           IS_PTREE t ∧ ALL_DISTINCT (TRAVERSE t ++ SET_TO_LIST s) ⇒
           (SIZE (t |++ s) = SIZE t + CARD s)

   [SIZE_PTREE_OF_NUMSET_EMPTY]  Theorem

      |- ∀s. FINITE s ⇒ (SIZE (<{}> |++ s) = CARD s)

   [SIZE_REMOVE]  Theorem

      |- ∀t k.
           IS_PTREE t ⇒
           (SIZE (t \\ k) =
            if MEM k (TRAVERSE t) then SIZE t − 1 else SIZE t)

   [TRANSFORM_BRANCH]  Theorem

      |- ∀f p m l r.
           TRANSFORM f (BRANCH (p,m,l,r)) =
           BRANCH (p,m,TRANSFORM f l,TRANSFORM f r)

   [TRANSFORM_EMPTY]  Theorem

      |- ∀f t. (TRANSFORM f t = <{}>) ⇔ (t = <{}>)

   [TRANSFORM_IS_PTREE]  Theorem

      |- ∀f t. IS_PTREE t ⇒ IS_PTREE (TRANSFORM f t)

   [TRAVERSE_AUX]  Theorem

      |- ∀t. TRAVERSE t = TRAVERSE_AUX t []

   [TRAVERSE_TRANSFORM]  Theorem

      |- ∀f t. TRAVERSE (TRANSFORM f t) = TRAVERSE t

   [UNION_PTREE_ASSOC]  Theorem

      |- ∀t1 t2 t3.
           IS_PTREE t1 ∧ IS_PTREE t2 ∧ IS_PTREE t3 ⇒
           (t1 UNION_PTREE (t2 UNION_PTREE t3) =
            t1 UNION_PTREE t2 UNION_PTREE t3)

   [UNION_PTREE_COMM]  Theorem

      |- ∀t1 t2.
           IS_PTREE t1 ∧ IS_PTREE t2 ⇒
           (t1 UNION_PTREE t2 = t2 UNION_PTREE t1)

   [UNION_PTREE_COMM_EMPTY]  Theorem

      |- ∀t. IS_PTREE t ⇒ (<{}> UNION_PTREE t = t UNION_PTREE <{}>)

   [UNION_PTREE_EMPTY]  Theorem

      |- (∀t. t UNION_PTREE <{}> = t) ∧
         ∀t. IS_PTREE t ⇒ (<{}> UNION_PTREE t = t)

   [UNION_PTREE_IS_PTREE]  Theorem

      |- ∀t1 t2. IS_PTREE t1 ∧ IS_PTREE t2 ⇒ IS_PTREE (t1 UNION_PTREE t2)

   [datatype_ptree]  Theorem

      |- DATATYPE (ptree <{}> Leaf Branch)

   [ptree_11]  Theorem

      |- (∀a0 a1 a0' a1'.
            (Leaf a0 a1 = Leaf a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         ∀a0 a1 a2 a3 a0' a1' a2' a3'.
           (Branch a0 a1 a2 a3 = Branch a0' a1' a2' a3') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3')

   [ptree_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (fn <{}> = f0) ∧ (∀a0 a1. fn (Leaf a0 a1) = f1 a0 a1) ∧
             ∀a0 a1 a2 a3.
               fn (Branch a0 a1 a2 a3) = f2 a0 a1 a2 a3 (fn a2) (fn a3)

   [ptree_case_cong]  Theorem

      |- ∀M M' v f f1.
           (M = M') ∧ ((M' = <{}>) ⇒ (v = v')) ∧
           (∀a0 a1. (M' = Leaf a0 a1) ⇒ (f a0 a1 = f' a0 a1)) ∧
           (∀a0 a1 a2 a3.
              (M' = Branch a0 a1 a2 a3) ⇒
              (f1 a0 a1 a2 a3 = f1' a0 a1 a2 a3)) ⇒
           (ptree_case v f f1 M = ptree_case v' f' f1' M')

   [ptree_distinct]  Theorem

      |- (∀a1 a0. <{}> ≠ Leaf a0 a1) ∧
         (∀a3 a2 a1 a0. <{}> ≠ Branch a0 a1 a2 a3) ∧
         ∀a3 a2 a1' a1 a0' a0. Leaf a0 a1 ≠ Branch a0' a1' a2 a3

   [ptree_induction]  Theorem

      |- ∀P.
           P <{}> ∧ (∀n a. P (Leaf n a)) ∧
           (∀p p0. P p ∧ P p0 ⇒ ∀n n0. P (Branch n0 n p p0)) ⇒
           ∀p. P p

   [ptree_nchotomy]  Theorem

      |- ∀pp.
           (pp = <{}>) ∨ (∃n a. pp = Leaf n a) ∨
           ∃n0 n p p0. pp = Branch n0 n p p0


*)
end
