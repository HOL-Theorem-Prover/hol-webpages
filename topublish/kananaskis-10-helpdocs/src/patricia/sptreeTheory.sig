signature sptreeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val delete_def : thm
    val difference_def : thm
    val domain_def : thm
    val foldi_def : thm
    val fromAList_primitive_def : thm
    val fromList_def : thm
    val insert_curried_def : thm
    val insert_tupled_primitive_def : thm
    val inter_def : thm
    val inter_eq_def : thm
    val lookup_curried_def : thm
    val lookup_tupled_primitive_def : thm
    val lrnext_def : thm
    val mk_BN_curried_def : thm
    val mk_BN_tupled_primitive_def : thm
    val mk_BS_curried_def : thm
    val mk_BS_tupled_primitive_def : thm
    val mk_wf_def : thm
    val size_def : thm
    val spt_TY_DEF : thm
    val spt_case_def : thm
    val spt_size_def : thm
    val toAList_def : thm
    val toListA_def : thm
    val toList_def : thm
    val union_def : thm
    val wf_def : thm

  (*  Theorems  *)
    val ALOOKUP_toAList : thm
    val FINITE_domain : thm
    val MEM_toAList : thm
    val datatype_spt : thm
    val delete_compute : thm
    val delete_mk_wf : thm
    val domain_delete : thm
    val domain_empty : thm
    val domain_foldi : thm
    val domain_fromAList : thm
    val domain_fromList : thm
    val domain_insert : thm
    val domain_inter : thm
    val domain_lookup : thm
    val domain_mk_wf : thm
    val domain_sing : thm
    val domain_union : thm
    val fromAList_def : thm
    val fromAList_ind : thm
    val fromAList_toAList : thm
    val insert_compute : thm
    val insert_def : thm
    val insert_ind : thm
    val insert_mk_wf : thm
    val insert_notEmpty : thm
    val insert_union : thm
    val inter_LN : thm
    val inter_assoc : thm
    val inter_eq : thm
    val isEmpty_toList : thm
    val isEmpty_toListA : thm
    val isEmpty_union : thm
    val lookup_NONE_domain : thm
    val lookup_compute : thm
    val lookup_def : thm
    val lookup_delete : thm
    val lookup_difference : thm
    val lookup_fromAList : thm
    val lookup_fromAList_toAList : thm
    val lookup_fromList : thm
    val lookup_ind : thm
    val lookup_insert : thm
    val lookup_insert1 : thm
    val lookup_inter : thm
    val lookup_inter_eq : thm
    val lookup_mk_wf : thm
    val lookup_union : thm
    val lrnext_thm : thm
    val mk_BN_def : thm
    val mk_BN_ind : thm
    val mk_BS_def : thm
    val mk_BS_ind : thm
    val mk_wf_eq : thm
    val set_foldi_keys : thm
    val spt_11 : thm
    val spt_Axiom : thm
    val spt_case_cong : thm
    val spt_distinct : thm
    val spt_eq_thm : thm
    val spt_induction : thm
    val spt_nchotomy : thm
    val toListA_append : thm
    val union_LN : thm
    val union_assoc : thm
    val union_mk_wf : thm
    val wf_delete : thm
    val wf_fromAList : thm
    val wf_insert : thm
    val wf_inter : thm
    val wf_mk_id : thm
    val wf_mk_wf : thm
    val wf_union : thm

  val sptree_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [alist] Parent theory of "sptree"

   [logroot] Parent theory of "sptree"

   [delete_def]  Definition

      |- (∀k. isEmpty (delete k LN)) ∧
         (∀k a. delete k (LS a) = if k = 0 then LN else LS a) ∧
         (∀k t1 t2.
            delete k (BN t1 t2) =
            if k = 0 then BN t1 t2
            else if EVEN k then mk_BN (delete ((k − 1) DIV 2) t1) t2
            else mk_BN t1 (delete ((k − 1) DIV 2) t2)) ∧
         ∀k t1 a t2.
           delete k (BS t1 a t2) =
           if k = 0 then BN t1 t2
           else if EVEN k then mk_BS (delete ((k − 1) DIV 2) t1) a t2
           else mk_BS t1 a (delete ((k − 1) DIV 2) t2)

   [difference_def]  Definition

      |- (∀t. isEmpty (difference LN t)) ∧
         (∀a t.
            difference (LS a) t =
            case t of
              LN => LS a
            | LS b => LN
            | BN t1 t2 => LS a
            | BS t1' b' t2' => LN) ∧
         (∀t1 t2 t.
            difference (BN t1 t2) t =
            case t of
              LN => BN t1 t2
            | LS a => BN t1 t2
            | BN t1' t2' => mk_BN (difference t1 t1') (difference t2 t2')
            | BS t1'' a'' t2'' =>
                mk_BN (difference t1 t1'') (difference t2 t2'')) ∧
         ∀t1 a t2 t.
           difference (BS t1 a t2) t =
           case t of
             LN => BS t1 a t2
           | LS a' => BN t1 t2
           | BN t1' t2' => mk_BS (difference t1 t1') a (difference t2 t2')
           | BS t1'' a''' t2'' =>
               mk_BN (difference t1 t1'') (difference t2 t2'')

   [domain_def]  Definition

      |- (domain LN = ∅) ∧ (∀v0. domain (LS v0) = {0}) ∧
         (∀t1 t2.
            domain (BN t1 t2) =
            IMAGE (λn. 2 * n + 2) (domain t1) ∪
            IMAGE (λn. 2 * n + 1) (domain t2)) ∧
         ∀t1 v1 t2.
           domain (BS t1 v1 t2) =
           {0} ∪ IMAGE (λn. 2 * n + 2) (domain t1) ∪
           IMAGE (λn. 2 * n + 1) (domain t2)

   [foldi_def]  Definition

      |- (∀f i acc. foldi f i acc LN = acc) ∧
         (∀f i acc a. foldi f i acc (LS a) = f i a acc) ∧
         (∀f i acc t1 t2.
            foldi f i acc (BN t1 t2) =
            (let inc = sptree$lrnext i
             in
               foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2)) ∧
         ∀f i acc t1 a t2.
           foldi f i acc (BS t1 a t2) =
           (let inc = sptree$lrnext i
            in
              foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc t1)) t2)

   [fromAList_primitive_def]  Definition

      |- fromAList =
         WFREC (@R. WF R ∧ ∀y x xs. R xs ((x,y)::xs))
           (λfromAList a.
              case a of
                [] => I LN
              | (x,y)::xs => I (insert x y (fromAList xs)))

   [fromList_def]  Definition

      |- ∀l.
           fromList l =
           SND (FOLDL (λ(i,t) a. (i + 1,insert i a t)) (0,LN) l)

   [insert_curried_def]  Definition

      |- ∀x x1 x2. insert x x1 x2 = insert_tupled (x,x1,x2)

   [insert_tupled_primitive_def]  Definition

      |- insert_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀a k. k ≠ 0 ∧ ¬EVEN k ⇒ R ((k − 1) DIV 2,a,LN) (k,a,LN)) ∧
              (∀a k. k ≠ 0 ∧ EVEN k ⇒ R ((k − 1) DIV 2,a,LN) (k,a,LN)) ∧
              (∀a' a k.
                 k ≠ 0 ∧ ¬EVEN k ⇒ R ((k − 1) DIV 2,a,LN) (k,a,LS a')) ∧
              (∀a' a k.
                 k ≠ 0 ∧ EVEN k ⇒ R ((k − 1) DIV 2,a,LN) (k,a,LS a')) ∧
              (∀t1 t2 a k.
                 k ≠ 0 ∧ ¬EVEN k ⇒ R ((k − 1) DIV 2,a,t2) (k,a,BN t1 t2)) ∧
              (∀t2 t1 a k.
                 k ≠ 0 ∧ EVEN k ⇒ R ((k − 1) DIV 2,a,t1) (k,a,BN t1 t2)) ∧
              (∀t2 a' t1 a k.
                 k ≠ 0 ∧ EVEN k ⇒
                 R ((k − 1) DIV 2,a,t1) (k,a,BS t1 a' t2)) ∧
              ∀a' t1 t2 a k.
                k ≠ 0 ∧ ¬EVEN k ⇒ R ((k − 1) DIV 2,a,t2) (k,a,BS t1 a' t2))
           (λinsert_tupled a''.
              case a'' of
                (k,a,LN) =>
                  I
                    (if k = 0 then LS a
                     else if EVEN k then
                       BN (insert_tupled ((k − 1) DIV 2,a,LN)) LN
                     else BN LN (insert_tupled ((k − 1) DIV 2,a,LN)))
              | (k,a,LS a') =>
                  I
                    (if k = 0 then LS a
                     else if EVEN k then
                       BS (insert_tupled ((k − 1) DIV 2,a,LN)) a' LN
                     else BS LN a' (insert_tupled ((k − 1) DIV 2,a,LN)))
              | (k,a,BN t1 t2) =>
                  I
                    (if k = 0 then BS t1 a t2
                     else if EVEN k then
                       BN (insert_tupled ((k − 1) DIV 2,a,t1)) t2
                     else BN t1 (insert_tupled ((k − 1) DIV 2,a,t2)))
              | (k,a,BS t1' a''' t2') =>
                  I
                    (if k = 0 then BS t1' a t2'
                     else if EVEN k then
                       BS (insert_tupled ((k − 1) DIV 2,a,t1')) a''' t2'
                     else
                       BS t1' a''' (insert_tupled ((k − 1) DIV 2,a,t2'))))

   [inter_def]  Definition

      |- (∀t. isEmpty (inter LN t)) ∧
         (∀a t.
            inter (LS a) t =
            case t of
              LN => LN
            | LS b => LS a
            | BN t1 t2 => LN
            | BS t1' v4 t2' => LS a) ∧
         (∀t1 t2 t.
            inter (BN t1 t2) t =
            case t of
              LN => LN
            | LS a => LN
            | BN t1' t2' => mk_BN (inter t1 t1') (inter t2 t2')
            | BS t1'' a'' t2'' => mk_BN (inter t1 t1'') (inter t2 t2'')) ∧
         ∀t1 a t2 t.
           inter (BS t1 a t2) t =
           case t of
             LN => LN
           | LS a' => LS a
           | BN t1' t2' => mk_BN (inter t1 t1') (inter t2 t2')
           | BS t1'' a''' t2'' => mk_BS (inter t1 t1'') a (inter t2 t2'')

   [inter_eq_def]  Definition

      |- (∀t. isEmpty (inter_eq LN t)) ∧
         (∀a t.
            inter_eq (LS a) t =
            case t of
              LN => LN
            | LS b => if a = b then LS a else LN
            | BN t1 t2 => LN
            | BS t1' b' t2' => if a = b' then LS a else LN) ∧
         (∀t1 t2 t.
            inter_eq (BN t1 t2) t =
            case t of
              LN => LN
            | LS a => LN
            | BN t1' t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
            | BS t1'' a'' t2'' =>
                mk_BN (inter_eq t1 t1'') (inter_eq t2 t2'')) ∧
         ∀t1 a t2 t.
           inter_eq (BS t1 a t2) t =
           case t of
             LN => LN
           | LS a' => if a' = a then LS a else LN
           | BN t1' t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
           | BS t1'' a''' t2'' =>
               if a''' = a then
                 mk_BS (inter_eq t1 t1'') a (inter_eq t2 t2'')
               else mk_BN (inter_eq t1 t1'') (inter_eq t2 t2'')

   [lookup_curried_def]  Definition

      |- ∀x x1. lookup x x1 = lookup_tupled (x,x1)

   [lookup_tupled_primitive_def]  Definition

      |- lookup_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀t2 t1 k.
                 k ≠ 0 ⇒
                 R ((k − 1) DIV 2,if EVEN k then t1 else t2)
                   (k,BN t1 t2)) ∧
              ∀a t2 t1 k.
                k ≠ 0 ⇒
                R ((k − 1) DIV 2,if EVEN k then t1 else t2) (k,BS t1 a t2))
           (λlookup_tupled a'.
              case a' of
                (k,LN) => I NONE
              | (k,LS a) => I (if k = 0 then SOME a else NONE)
              | (k,BN t1 t2) =>
                  I
                    (if k = 0 then NONE
                     else
                       lookup_tupled
                         ((k − 1) DIV 2,if EVEN k then t1 else t2))
              | (k,BS t1' a'' t2') =>
                  I
                    (if k = 0 then SOME a''
                     else
                       lookup_tupled
                         ((k − 1) DIV 2,if EVEN k then t1' else t2')))

   [lrnext_def]  Definition

      |- (sptree$lrnext ZERO = 1) ∧
         (∀n. sptree$lrnext (BIT1 n) = 2 * sptree$lrnext n) ∧
         ∀n. sptree$lrnext (BIT2 n) = 2 * sptree$lrnext n

   [mk_BN_curried_def]  Definition

      |- ∀x x1. mk_BN x x1 = mk_BN_tupled (x,x1)

   [mk_BN_tupled_primitive_def]  Definition

      |- mk_BN_tupled =
         WFREC (@R. WF R)
           (λmk_BN_tupled a.
              case a of
                (LN,LN) => I LN
              | (LN,LS v20) => I (BN LN (LS v20))
              | (LN,BN v21 v22) => I (BN LN (BN v21 v22))
              | (LN,BS v23 v24 v25) => I (BN LN (BS v23 v24 v25))
              | (LS v8,v1) => I (BN (LS v8) v1)
              | (BN v9 v10,v1) => I (BN (BN v9 v10) v1)
              | (BS v11 v12 v13,v1) => I (BN (BS v11 v12 v13) v1))

   [mk_BS_curried_def]  Definition

      |- ∀x x1 x2. mk_BS x x1 x2 = mk_BS_tupled (x,x1,x2)

   [mk_BS_tupled_primitive_def]  Definition

      |- mk_BS_tupled =
         WFREC (@R. WF R)
           (λmk_BS_tupled a.
              case a of
                (LN,x,LN) => I (LS x)
              | (LS v22,x,LN) => I (BS (LS v22) x LN)
              | (BN v23 v24,x,LN) => I (BS (BN v23 v24) x LN)
              | (BS v25 v26 v27,x,LN) => I (BS (BS v25 v26 v27) x LN)
              | (v,x,LS v10) => I (BS v x (LS v10))
              | (v,x,BN v11 v12) => I (BS v x (BN v11 v12))
              | (v,x,BS v13 v14 v15) => I (BS v x (BS v13 v14 v15)))

   [mk_wf_def]  Definition

      |- isEmpty (mk_wf LN) ∧ (∀x. mk_wf (LS x) = LS x) ∧
         (∀t1 t2. mk_wf (BN t1 t2) = mk_BN (mk_wf t1) (mk_wf t2)) ∧
         ∀t1 x t2. mk_wf (BS t1 x t2) = mk_BS (mk_wf t1) x (mk_wf t2)

   [size_def]  Definition

      |- (size LN = 0) ∧ (∀a. size (LS a) = 1) ∧
         (∀t1 t2. size (BN t1 t2) = size t1 + size t2) ∧
         ∀t1 a t2. size (BS t1 a t2) = size t1 + size t2 + 1

   [spt_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'spt' .
                  (∀a0'.
                     (a0' = ind_type$CONSTR 0 ARB (λn. ind_type$BOTTOM)) ∨
                     (∃a.
                        a0' =
                        (λa.
                           ind_type$CONSTR (SUC 0) a (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC 0)) ARB
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'spt' a0 ∧ 'spt' a1) ∨
                     (∃a0 a1 a2.
                        (a0' =
                         (λa0 a1 a2.
                            ind_type$CONSTR (SUC (SUC (SUC 0))) a1
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a2
                                    (λn. ind_type$BOTTOM)))) a0 a1 a2) ∧
                        'spt' a0 ∧ 'spt' a2) ⇒
                     'spt' a0') ⇒
                  'spt' a0') rep

   [spt_case_def]  Definition

      |- (∀v f f1 f2. spt_CASE LN v f f1 f2 = v) ∧
         (∀a v f f1 f2. spt_CASE (LS a) v f f1 f2 = f a) ∧
         (∀a0 a1 v f f1 f2. spt_CASE (BN a0 a1) v f f1 f2 = f1 a0 a1) ∧
         ∀a0 a1 a2 v f f1 f2.
           spt_CASE (BS a0 a1 a2) v f f1 f2 = f2 a0 a1 a2

   [spt_size_def]  Definition

      |- (∀f. spt_size f LN = 0) ∧ (∀f a. spt_size f (LS a) = 1 + f a) ∧
         (∀f a0 a1.
            spt_size f (BN a0 a1) = 1 + (spt_size f a0 + spt_size f a1)) ∧
         ∀f a0 a1 a2.
           spt_size f (BS a0 a1 a2) =
           1 + (spt_size f a0 + (f a1 + spt_size f a2))

   [toAList_def]  Definition

      |- toAList = foldi (λk v a. (k,v)::a) 0 []

   [toListA_def]  Definition

      |- (∀acc. toListA acc LN = acc) ∧
         (∀acc a. toListA acc (LS a) = a::acc) ∧
         (∀acc t1 t2.
            toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) ∧
         ∀acc t1 a t2.
           toListA acc (BS t1 a t2) = toListA (a::toListA acc t2) t1

   [toList_def]  Definition

      |- ∀m. toList m = toListA [] m

   [union_def]  Definition

      |- (∀t. union LN t = t) ∧
         (∀a t.
            union (LS a) t =
            case t of
              LN => LS a
            | LS b => LS a
            | BN t1 t2 => BS t1 a t2
            | BS t1' v4 t2' => BS t1' a t2') ∧
         (∀t1 t2 t.
            union (BN t1 t2) t =
            case t of
              LN => BN t1 t2
            | LS a => BS t1 a t2
            | BN t1' t2' => BN (union t1 t1') (union t2 t2')
            | BS t1'' a'' t2'' => BS (union t1 t1'') a'' (union t2 t2'')) ∧
         ∀t1 a t2 t.
           union (BS t1 a t2) t =
           case t of
             LN => BS t1 a t2
           | LS a' => BS t1 a t2
           | BN t1' t2' => BS (union t1 t1') a (union t2 t2')
           | BS t1'' a''' t2'' => BS (union t1 t1'') a (union t2 t2'')

   [wf_def]  Definition

      |- (wf LN ⇔ T) ∧ (∀a. wf (LS a) ⇔ T) ∧
         (∀t1 t2.
            wf (BN t1 t2) ⇔ wf t1 ∧ wf t2 ∧ ¬(isEmpty t1 ∧ isEmpty t2)) ∧
         ∀t1 a t2.
           wf (BS t1 a t2) ⇔ wf t1 ∧ wf t2 ∧ ¬(isEmpty t1 ∧ isEmpty t2)

   [ALOOKUP_toAList]  Theorem

      |- ∀t x. ALOOKUP (toAList t) x = lookup x t

   [FINITE_domain]  Theorem

      |- FINITE (domain t)

   [MEM_toAList]  Theorem

      |- ∀t k v. MEM (k,v) (toAList t) ⇔ (lookup k t = SOME v)

   [datatype_spt]  Theorem

      |- DATATYPE (spt LN LS BN BS)

   [delete_compute]  Theorem

      |- (delete (NUMERAL n) t = delete n t) ∧ isEmpty (delete 0 LN) ∧
         isEmpty (delete 0 (LS a)) ∧ (delete 0 (BN t1 t2) = BN t1 t2) ∧
         (delete 0 (BS t1 a t2) = BN t1 t2) ∧ isEmpty (delete ZERO LN) ∧
         isEmpty (delete ZERO (LS a)) ∧
         (delete ZERO (BN t1 t2) = BN t1 t2) ∧
         (delete ZERO (BS t1 a t2) = BN t1 t2) ∧
         isEmpty (delete (BIT1 n) LN) ∧ (delete (BIT1 n) (LS a) = LS a) ∧
         (delete (BIT1 n) (BN t1 t2) = mk_BN t1 (delete n t2)) ∧
         (delete (BIT1 n) (BS t1 a t2) = mk_BS t1 a (delete n t2)) ∧
         isEmpty (delete (BIT2 n) LN) ∧ (delete (BIT2 n) (LS a) = LS a) ∧
         (delete (BIT2 n) (BN t1 t2) = mk_BN (delete n t1) t2) ∧
         (delete (BIT2 n) (BS t1 a t2) = mk_BS (delete n t1) a t2)

   [delete_mk_wf]  Theorem

      |- ∀x t. delete x (mk_wf t) = mk_wf (delete x t)

   [domain_delete]  Theorem

      |- domain (delete k t) = domain t DELETE k

   [domain_empty]  Theorem

      |- ∀t. wf t ⇒ (isEmpty t ⇔ (domain t = ∅))

   [domain_foldi]  Theorem

      |- domain t = foldi (λk v a. k INSERT a) 0 ∅ t

   [domain_fromAList]  Theorem

      |- ∀ls. domain (fromAList ls) = set (MAP FST ls)

   [domain_fromList]  Theorem

      |- domain (fromList l) = count (LENGTH l)

   [domain_insert]  Theorem

      |- domain (insert k v t) = k INSERT domain t

   [domain_inter]  Theorem

      |- domain (inter t1 t2) = domain t1 ∩ domain t2

   [domain_lookup]  Theorem

      |- ∀t k. k ∈ domain t ⇔ ∃v. lookup k t = SOME v

   [domain_mk_wf]  Theorem

      |- ∀t. domain (mk_wf t) = domain t

   [domain_sing]  Theorem

      |- domain (insert k v LN) = {k}

   [domain_union]  Theorem

      |- domain (union t1 t2) = domain t1 ∪ domain t2

   [fromAList_def]  Theorem

      |- isEmpty (fromAList []) ∧
         ∀y xs x. fromAList ((x,y)::xs) = insert x y (fromAList xs)

   [fromAList_ind]  Theorem

      |- ∀P. P [] ∧ (∀x y xs. P xs ⇒ P ((x,y)::xs)) ⇒ ∀v. P v

   [fromAList_toAList]  Theorem

      |- ∀t. wf t ⇒ (fromAList (toAList t) = t)

   [insert_compute]  Theorem

      |- (insert (NUMERAL n) a t = insert n a t) ∧ (insert 0 a LN = LS a) ∧
         (insert 0 a (LS a') = LS a) ∧
         (insert 0 a (BN t1 t2) = BS t1 a t2) ∧
         (insert 0 a (BS t1 a' t2) = BS t1 a t2) ∧
         (insert ZERO a LN = LS a) ∧ (insert ZERO a (LS a') = LS a) ∧
         (insert ZERO a (BN t1 t2) = BS t1 a t2) ∧
         (insert ZERO a (BS t1 a' t2) = BS t1 a t2) ∧
         (insert (BIT1 n) a LN = BN LN (insert n a LN)) ∧
         (insert (BIT1 n) a (LS a') = BS LN a' (insert n a LN)) ∧
         (insert (BIT1 n) a (BN t1 t2) = BN t1 (insert n a t2)) ∧
         (insert (BIT1 n) a (BS t1 a' t2) = BS t1 a' (insert n a t2)) ∧
         (insert (BIT2 n) a LN = BN (insert n a LN) LN) ∧
         (insert (BIT2 n) a (LS a') = BS (insert n a LN) a' LN) ∧
         (insert (BIT2 n) a (BN t1 t2) = BN (insert n a t1) t2) ∧
         (insert (BIT2 n) a (BS t1 a' t2) = BS (insert n a t1) a' t2)

   [insert_def]  Theorem

      |- (∀k a.
            insert k a LN =
            if k = 0 then LS a
            else if EVEN k then BN (insert ((k − 1) DIV 2) a LN) LN
            else BN LN (insert ((k − 1) DIV 2) a LN)) ∧
         (∀k a' a.
            insert k a (LS a') =
            if k = 0 then LS a
            else if EVEN k then BS (insert ((k − 1) DIV 2) a LN) a' LN
            else BS LN a' (insert ((k − 1) DIV 2) a LN)) ∧
         (∀t2 t1 k a.
            insert k a (BN t1 t2) =
            if k = 0 then BS t1 a t2
            else if EVEN k then BN (insert ((k − 1) DIV 2) a t1) t2
            else BN t1 (insert ((k − 1) DIV 2) a t2)) ∧
         ∀t2 t1 k a' a.
           insert k a (BS t1 a' t2) =
           if k = 0 then BS t1 a t2
           else if EVEN k then BS (insert ((k − 1) DIV 2) a t1) a' t2
           else BS t1 a' (insert ((k − 1) DIV 2) a t2)

   [insert_ind]  Theorem

      |- ∀P.
           (∀k a.
              (k ≠ 0 ∧ EVEN k ⇒ P ((k − 1) DIV 2) a LN) ∧
              (k ≠ 0 ∧ ¬EVEN k ⇒ P ((k − 1) DIV 2) a LN) ⇒
              P k a LN) ∧
           (∀k a a'.
              (k ≠ 0 ∧ EVEN k ⇒ P ((k − 1) DIV 2) a LN) ∧
              (k ≠ 0 ∧ ¬EVEN k ⇒ P ((k − 1) DIV 2) a LN) ⇒
              P k a (LS a')) ∧
           (∀k a t1 t2.
              (k ≠ 0 ∧ EVEN k ⇒ P ((k − 1) DIV 2) a t1) ∧
              (k ≠ 0 ∧ ¬EVEN k ⇒ P ((k − 1) DIV 2) a t2) ⇒
              P k a (BN t1 t2)) ∧
           (∀k a t1 a' t2.
              (k ≠ 0 ∧ EVEN k ⇒ P ((k − 1) DIV 2) a t1) ∧
              (k ≠ 0 ∧ ¬EVEN k ⇒ P ((k − 1) DIV 2) a t2) ⇒
              P k a (BS t1 a' t2)) ⇒
           ∀v v1 v2. P v v1 v2

   [insert_mk_wf]  Theorem

      |- ∀x v t. insert x v (mk_wf t) = mk_wf (insert x v t)

   [insert_notEmpty]  Theorem

      |- insert k a t ≠ LN

   [insert_union]  Theorem

      |- ∀k v s. insert k v s = union (insert k v LN) s

   [inter_LN]  Theorem

      |- ∀t. isEmpty (inter t LN) ∧ isEmpty (inter LN t)

   [inter_assoc]  Theorem

      |- ∀t1 t2 t3. inter t1 (inter t2 t3) = inter (inter t1 t2) t3

   [inter_eq]  Theorem

      |- ∀t1 t2 t3 t4.
           (inter t1 t2 = inter t3 t4) ⇔
           ∀x. lookup x (inter t1 t2) = lookup x (inter t3 t4)

   [isEmpty_toList]  Theorem

      |- ∀t. wf t ⇒ (isEmpty t ⇔ (toList t = []))

   [isEmpty_toListA]  Theorem

      |- ∀t acc. wf t ⇒ (isEmpty t ⇔ (toListA acc t = acc))

   [isEmpty_union]  Theorem

      |- isEmpty (union m1 m2) ⇔ isEmpty m1 ∧ isEmpty m2

   [lookup_NONE_domain]  Theorem

      |- (lookup k t = NONE) ⇔ k ∉ domain t

   [lookup_compute]  Theorem

      |- (lookup (NUMERAL n) t = lookup n t) ∧ (lookup 0 LN = NONE) ∧
         (lookup 0 (LS a) = SOME a) ∧ (lookup 0 (BN t1 t2) = NONE) ∧
         (lookup 0 (BS t1 a t2) = SOME a) ∧ (lookup ZERO LN = NONE) ∧
         (lookup ZERO (LS a) = SOME a) ∧ (lookup ZERO (BN t1 t2) = NONE) ∧
         (lookup ZERO (BS t1 a t2) = SOME a) ∧
         (lookup (BIT1 n) LN = NONE) ∧ (lookup (BIT1 n) (LS a) = NONE) ∧
         (lookup (BIT1 n) (BN t1 t2) = lookup n t2) ∧
         (lookup (BIT1 n) (BS t1 a t2) = lookup n t2) ∧
         (lookup (BIT2 n) LN = NONE) ∧ (lookup (BIT2 n) (LS a) = NONE) ∧
         (lookup (BIT2 n) (BN t1 t2) = lookup n t1) ∧
         (lookup (BIT2 n) (BS t1 a t2) = lookup n t1)

   [lookup_def]  Theorem

      |- (∀k. lookup k LN = NONE) ∧
         (∀k a. lookup k (LS a) = if k = 0 then SOME a else NONE) ∧
         (∀t2 t1 k.
            lookup k (BN t1 t2) =
            if k = 0 then NONE
            else lookup ((k − 1) DIV 2) (if EVEN k then t1 else t2)) ∧
         ∀t2 t1 k a.
           lookup k (BS t1 a t2) =
           if k = 0 then SOME a
           else lookup ((k − 1) DIV 2) (if EVEN k then t1 else t2)

   [lookup_delete]  Theorem

      |- ∀t k1 k2.
           lookup k1 (delete k2 t) = if k1 = k2 then NONE else lookup k1 t

   [lookup_difference]  Theorem

      |- ∀m1 m2 k.
           lookup k (difference m1 m2) =
           if lookup k m2 = NONE then lookup k m1 else NONE

   [lookup_fromAList]  Theorem

      |- ∀ls x. lookup x (fromAList ls) = ALOOKUP ls x

   [lookup_fromAList_toAList]  Theorem

      |- ∀t x. lookup x (fromAList (toAList t)) = lookup x t

   [lookup_fromList]  Theorem

      |- lookup n (fromList l) =
         if n < LENGTH l then SOME (EL n l) else NONE

   [lookup_ind]  Theorem

      |- ∀P.
           (∀k. P k LN) ∧ (∀k a. P k (LS a)) ∧
           (∀k t1 t2.
              (k ≠ 0 ⇒ P ((k − 1) DIV 2) (if EVEN k then t1 else t2)) ⇒
              P k (BN t1 t2)) ∧
           (∀k t1 a t2.
              (k ≠ 0 ⇒ P ((k − 1) DIV 2) (if EVEN k then t1 else t2)) ⇒
              P k (BS t1 a t2)) ⇒
           ∀v v1. P v v1

   [lookup_insert]  Theorem

      |- ∀k2 v t k1.
           lookup k1 (insert k2 v t) =
           if k1 = k2 then SOME v else lookup k1 t

   [lookup_insert1]  Theorem

      |- ∀k a t. lookup k (insert k a t) = SOME a

   [lookup_inter]  Theorem

      |- ∀m1 m2 k.
           lookup k (inter m1 m2) =
           case (lookup k m1,lookup k m2) of
             (SOME v,SOME w) => SOME v
           | _ => NONE

   [lookup_inter_eq]  Theorem

      |- ∀m1 m2 k.
           lookup k (inter_eq m1 m2) =
           case lookup k m1 of
             NONE => NONE
           | SOME v => if lookup k m2 = SOME v then SOME v else NONE

   [lookup_mk_wf]  Theorem

      |- ∀x t. lookup x (mk_wf t) = lookup x t

   [lookup_union]  Theorem

      |- ∀m1 m2 k.
           lookup k (union m1 m2) =
           case lookup k m1 of NONE => lookup k m2 | SOME v => SOME v

   [lrnext_thm]  Theorem

      |- (∀a. sptree$lrnext 0 = 1) ∧
         (∀n a. sptree$lrnext (NUMERAL n) = sptree$lrnext n) ∧
         (sptree$lrnext ZERO = 1) ∧
         (∀n. sptree$lrnext (BIT1 n) = 2 * sptree$lrnext n) ∧
         ∀n. sptree$lrnext (BIT2 n) = 2 * sptree$lrnext n

   [mk_BN_def]  Theorem

      |- isEmpty (mk_BN LN LN) ∧ (mk_BN LN (LS v14) = BN LN (LS v14)) ∧
         (mk_BN LN (BN v15 v16) = BN LN (BN v15 v16)) ∧
         (mk_BN LN (BS v17 v18 v19) = BN LN (BS v17 v18 v19)) ∧
         (mk_BN (LS v2) t2 = BN (LS v2) t2) ∧
         (mk_BN (BN v3 v4) t2 = BN (BN v3 v4) t2) ∧
         (mk_BN (BS v5 v6 v7) t2 = BN (BS v5 v6 v7) t2)

   [mk_BN_ind]  Theorem

      |- ∀P.
           P LN LN ∧ (∀v14. P LN (LS v14)) ∧
           (∀v15 v16. P LN (BN v15 v16)) ∧
           (∀v17 v18 v19. P LN (BS v17 v18 v19)) ∧ (∀v2 t2. P (LS v2) t2) ∧
           (∀v3 v4 t2. P (BN v3 v4) t2) ∧
           (∀v5 v6 v7 t2. P (BS v5 v6 v7) t2) ⇒
           ∀v v1. P v v1

   [mk_BS_def]  Theorem

      |- (mk_BS LN x LN = LS x) ∧
         (mk_BS (LS v16) x LN = BS (LS v16) x LN) ∧
         (mk_BS (BN v17 v18) x LN = BS (BN v17 v18) x LN) ∧
         (mk_BS (BS v19 v20 v21) x LN = BS (BS v19 v20 v21) x LN) ∧
         (mk_BS t1 x (LS v4) = BS t1 x (LS v4)) ∧
         (mk_BS t1 x (BN v5 v6) = BS t1 x (BN v5 v6)) ∧
         (mk_BS t1 x (BS v7 v8 v9) = BS t1 x (BS v7 v8 v9))

   [mk_BS_ind]  Theorem

      |- ∀P.
           (∀x. P LN x LN) ∧ (∀v16 x. P (LS v16) x LN) ∧
           (∀v17 v18 x. P (BN v17 v18) x LN) ∧
           (∀v19 v20 v21 x. P (BS v19 v20 v21) x LN) ∧
           (∀t1 x v4. P t1 x (LS v4)) ∧ (∀t1 x v5 v6. P t1 x (BN v5 v6)) ∧
           (∀t1 x v7 v8 v9. P t1 x (BS v7 v8 v9)) ⇒
           ∀v v1 v2. P v v1 v2

   [mk_wf_eq]  Theorem

      |- ∀t1 t2. (mk_wf t1 = mk_wf t2) ⇔ ∀x. lookup x t1 = lookup x t2

   [set_foldi_keys]  Theorem

      |- ∀t a i.
           foldi (λk v a. k INSERT a) i a t =
           a ∪ IMAGE (λn. i + sptree$lrnext i * n) (domain t)

   [spt_11]  Theorem

      |- (∀a a'. (LS a = LS a') ⇔ (a = a')) ∧
         (∀a0 a1 a0' a1'.
            (BN a0 a1 = BN a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         ∀a0 a1 a2 a0' a1' a2'.
           (BS a0 a1 a2 = BS a0' a1' a2') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2')

   [spt_Axiom]  Theorem

      |- ∀f0 f1 f2 f3.
           ∃fn.
             (fn LN = f0) ∧ (∀a. fn (LS a) = f1 a) ∧
             (∀a0 a1. fn (BN a0 a1) = f2 a0 a1 (fn a0) (fn a1)) ∧
             ∀a0 a1 a2. fn (BS a0 a1 a2) = f3 a1 a0 a2 (fn a0) (fn a2)

   [spt_case_cong]  Theorem

      |- ∀M M' v f f1 f2.
           (M = M') ∧ (isEmpty M' ⇒ (v = v')) ∧
           (∀a. (M' = LS a) ⇒ (f a = f' a)) ∧
           (∀a0 a1. (M' = BN a0 a1) ⇒ (f1 a0 a1 = f1' a0 a1)) ∧
           (∀a0 a1 a2. (M' = BS a0 a1 a2) ⇒ (f2 a0 a1 a2 = f2' a0 a1 a2)) ⇒
           (spt_CASE M v f f1 f2 = spt_CASE M' v' f' f1' f2')

   [spt_distinct]  Theorem

      |- (∀a. LN ≠ LS a) ∧ (∀a1 a0. LN ≠ BN a0 a1) ∧
         (∀a2 a1 a0. LN ≠ BS a0 a1 a2) ∧ (∀a1 a0 a. LS a ≠ BN a0 a1) ∧
         (∀a2 a1 a0 a. LS a ≠ BS a0 a1 a2) ∧
         ∀a2 a1' a1 a0' a0. BN a0 a1 ≠ BS a0' a1' a2

   [spt_eq_thm]  Theorem

      |- ∀t1 t2.
           wf t1 ∧ wf t2 ⇒ ((t1 = t2) ⇔ ∀n. lookup n t1 = lookup n t2)

   [spt_induction]  Theorem

      |- ∀P.
           P LN ∧ (∀a. P (LS a)) ∧ (∀s s0. P s ∧ P s0 ⇒ P (BN s s0)) ∧
           (∀s s0. P s ∧ P s0 ⇒ ∀a. P (BS s a s0)) ⇒
           ∀s. P s

   [spt_nchotomy]  Theorem

      |- ∀ss.
           isEmpty ss ∨ (∃a. ss = LS a) ∨ (∃s s0. ss = BN s s0) ∨
           ∃s a s0. ss = BS s a s0

   [toListA_append]  Theorem

      |- ∀t acc. toListA acc t = toListA [] t ++ acc

   [union_LN]  Theorem

      |- ∀t. (union t LN = t) ∧ (union LN t = t)

   [union_assoc]  Theorem

      |- ∀t1 t2 t3. union t1 (union t2 t3) = union (union t1 t2) t3

   [union_mk_wf]  Theorem

      |- ∀t1 t2. inter (mk_wf t1) (mk_wf t2) = mk_wf (inter t1 t2)

   [wf_delete]  Theorem

      |- ∀t k. wf t ⇒ wf (delete k t)

   [wf_fromAList]  Theorem

      |- ∀ls. wf (fromAList ls)

   [wf_insert]  Theorem

      |- ∀k a t. wf t ⇒ wf (insert k a t)

   [wf_inter]  Theorem

      |- ∀m1 m2. wf (inter m1 m2)

   [wf_mk_id]  Theorem

      |- ∀t. wf t ⇒ (mk_wf t = t)

   [wf_mk_wf]  Theorem

      |- ∀t. wf (mk_wf t)

   [wf_union]  Theorem

      |- ∀m1 m2. wf m1 ∧ wf m2 ⇒ wf (union m1 m2)


*)
end
