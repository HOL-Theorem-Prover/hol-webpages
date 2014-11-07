signature listTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ALL_DISTINCT : thm
    val APPEND : thm
    val DROP_def : thm
    val EL : thm
    val EVERY_DEF : thm
    val EVERYi_DEF : thm
    val EXISTS_DEF : thm
    val FILTER : thm
    val FIND_def : thm
    val FLAT : thm
    val FOLDL : thm
    val FOLDR : thm
    val FRONT_DEF : thm
    val GENLIST : thm
    val GENLIST_AUX : thm
    val HD : thm
    val INDEX_FIND_def : thm
    val INDEX_OF_def : thm
    val LAST_DEF : thm
    val LENGTH : thm
    val LEN_DEF : thm
    val LIST_APPLY_DEF : thm
    val LIST_BIND_DEF : thm
    val LIST_IGNORE_BIND_DEF : thm
    val LIST_LIFT2_DEF : thm
    val LIST_TO_SET_DEF : thm
    val LLEX_DEF : thm
    val LRC_def : thm
    val LUPDATE_def : thm
    val MAP : thm
    val NULL_DEF : thm
    val PAD_LEFT : thm
    val PAD_RIGHT : thm
    val REVERSE_DEF : thm
    val REV_DEF : thm
    val SET_TO_LIST_primitive : thm
    val SNOC : thm
    val SUM : thm
    val SUM_ACC_DEF : thm
    val TAKE_def : thm
    val TL : thm
    val UNZIP : thm
    val ZIP : thm
    val dropWhile_def : thm
    val isPREFIX : thm
    val list_TY_DEF : thm
    val list_case_def : thm
    val list_size_def : thm
    val nub_def : thm
    val splitAtPki_DEF : thm

  (*  Theorems  *)
    val ALL_DISTINCT_APPEND : thm
    val ALL_DISTINCT_CARD_LIST_TO_SET : thm
    val ALL_DISTINCT_DROP : thm
    val ALL_DISTINCT_EL_IMP : thm
    val ALL_DISTINCT_FILTER : thm
    val ALL_DISTINCT_FILTER_EL_IMP : thm
    val ALL_DISTINCT_GENLIST : thm
    val ALL_DISTINCT_MAP : thm
    val ALL_DISTINCT_MAP_INJ : thm
    val ALL_DISTINCT_REVERSE : thm
    val ALL_DISTINCT_SET_TO_LIST : thm
    val ALL_DISTINCT_SING : thm
    val ALL_DISTINCT_SNOC : thm
    val ALL_DISTINCT_ZIP : thm
    val ALL_DISTINCT_ZIP_SWAP : thm
    val APPEND_11 : thm
    val APPEND_11_LENGTH : thm
    val APPEND_ASSOC : thm
    val APPEND_EQ_APPEND : thm
    val APPEND_EQ_APPEND_MID : thm
    val APPEND_EQ_CONS : thm
    val APPEND_EQ_SELF : thm
    val APPEND_EQ_SING : thm
    val APPEND_FRONT_LAST : thm
    val APPEND_LENGTH_EQ : thm
    val APPEND_NIL : thm
    val APPEND_SNOC : thm
    val APPEND_eq_NIL : thm
    val BIGUNION_IMAGE_set_SUBSET : thm
    val CARD_LIST_TO_SET : thm
    val CONS : thm
    val CONS_11 : thm
    val CONS_ACYCLIC : thm
    val DISJOINT_GENLIST_PLUS : thm
    val DROP_0 : thm
    val DROP_LENGTH_TOO_LONG : thm
    val DROP_NIL : thm
    val DROP_compute : thm
    val DROP_splitAtPki : thm
    val EL_ALL_DISTINCT_EL_EQ : thm
    val EL_GENLIST : thm
    val EL_LENGTH_SNOC : thm
    val EL_LENGTH_dropWhile_REVERSE : thm
    val EL_LUPDATE : thm
    val EL_MAP : thm
    val EL_REVERSE : thm
    val EL_SNOC : thm
    val EL_ZIP : thm
    val EL_compute : thm
    val EL_restricted : thm
    val EL_simp : thm
    val EL_simp_restricted : thm
    val EQ_LIST : thm
    val EVERY2_EVERY : thm
    val EVERY2_LENGTH : thm
    val EVERY2_LUPDATE_same : thm
    val EVERY2_MAP : thm
    val EVERY2_MEM_MONO : thm
    val EVERY2_REVERSE : thm
    val EVERY2_THM : thm
    val EVERY2_cong : thm
    val EVERY2_mono : thm
    val EVERY2_refl : thm
    val EVERY2_sym : thm
    val EVERY2_trans : thm
    val EVERY_APPEND : thm
    val EVERY_CONG : thm
    val EVERY_CONJ : thm
    val EVERY_EL : thm
    val EVERY_FILTER : thm
    val EVERY_FILTER_IMP : thm
    val EVERY_GENLIST : thm
    val EVERY_MAP : thm
    val EVERY_MEM : thm
    val EVERY_MEM_MONO : thm
    val EVERY_MONOTONIC : thm
    val EVERY_NOT_EXISTS : thm
    val EVERY_SIMP : thm
    val EVERY_SNOC : thm
    val EXISTS_APPEND : thm
    val EXISTS_CONG : thm
    val EXISTS_GENLIST : thm
    val EXISTS_LIST : thm
    val EXISTS_LIST_EQ_MAP : thm
    val EXISTS_MAP : thm
    val EXISTS_MEM : thm
    val EXISTS_NOT_EVERY : thm
    val EXISTS_SIMP : thm
    val EXISTS_SNOC : thm
    val FILTER_ALL_DISTINCT : thm
    val FILTER_APPEND_DISTRIB : thm
    val FILTER_COND_REWRITE : thm
    val FILTER_EQ_APPEND : thm
    val FILTER_EQ_CONS : thm
    val FILTER_EQ_ID : thm
    val FILTER_EQ_NIL : thm
    val FILTER_NEQ_ID : thm
    val FILTER_NEQ_NIL : thm
    val FILTER_REVERSE : thm
    val FINITE_LIST_TO_SET : thm
    val FLAT_APPEND : thm
    val FLAT_EQ_NIL : thm
    val FOLDL2_FOLDL : thm
    val FOLDL2_cong : thm
    val FOLDL2_def : thm
    val FOLDL2_ind : thm
    val FOLDL_CONG : thm
    val FOLDL_EQ_FOLDR : thm
    val FOLDL_SNOC : thm
    val FOLDL_UNION_BIGUNION : thm
    val FOLDL_UNION_BIGUNION_paired : thm
    val FOLDL_ZIP_SAME : thm
    val FOLDR_CONG : thm
    val FOLDR_CONS : thm
    val FORALL_LIST : thm
    val FRONT_CONS : thm
    val FRONT_CONS_EQ_NIL : thm
    val FRONT_SNOC : thm
    val GENLIST_APPEND : thm
    val GENLIST_AUX_compute : thm
    val GENLIST_CONS : thm
    val GENLIST_EL : thm
    val GENLIST_EL_MAP : thm
    val GENLIST_FUN_EQ : thm
    val GENLIST_GENLIST_AUX : thm
    val GENLIST_NUMERALS : thm
    val GENLIST_PLUS_APPEND : thm
    val HD_GENLIST : thm
    val HD_GENLIST_COR : thm
    val HD_dropWhile : thm
    val IMAGE_EL_count_LENGTH : thm
    val INFINITE_LIST_UNIV : thm
    val INJ_MAP_EQ : thm
    val IN_LIST_TO_SET : thm
    val ITSET_eq_FOLDL_SET_TO_LIST : thm
    val LAST_APPEND_CONS : thm
    val LAST_CONS : thm
    val LAST_CONS_cond : thm
    val LAST_EL : thm
    val LAST_REVERSE : thm
    val LAST_SNOC : thm
    val LAST_compute : thm
    val LENGTH_APPEND : thm
    val LENGTH_CONS : thm
    val LENGTH_DROP : thm
    val LENGTH_EQ_CONS : thm
    val LENGTH_EQ_NIL : thm
    val LENGTH_EQ_NUM : thm
    val LENGTH_EQ_NUM_compute : thm
    val LENGTH_EQ_SUM : thm
    val LENGTH_FILTER_LEQ_MONO : thm
    val LENGTH_FRONT_CONS : thm
    val LENGTH_GENLIST : thm
    val LENGTH_LEN : thm
    val LENGTH_LUPDATE : thm
    val LENGTH_MAP : thm
    val LENGTH_NIL : thm
    val LENGTH_NIL_SYM : thm
    val LENGTH_REVERSE : thm
    val LENGTH_SNOC : thm
    val LENGTH_TAKE : thm
    val LENGTH_TL : thm
    val LENGTH_UNZIP : thm
    val LENGTH_ZIP : thm
    val LENGTH_dropWhile_LESS_EQ : thm
    val LENGTH_o_REVERSE : thm
    val LEN_LENGTH_LEM : thm
    val LIST_APPLY_o : thm
    val LIST_BIND_APPEND : thm
    val LIST_BIND_ID : thm
    val LIST_BIND_LIST_BIND : thm
    val LIST_BIND_MAP : thm
    val LIST_BIND_THM : thm
    val LIST_EQ : thm
    val LIST_EQ_MAP_PAIR : thm
    val LIST_EQ_REWRITE : thm
    val LIST_NOT_EQ : thm
    val LIST_REL_CONJ : thm
    val LIST_REL_CONS1 : thm
    val LIST_REL_CONS2 : thm
    val LIST_REL_EL_EQN : thm
    val LIST_REL_EVERY_ZIP : thm
    val LIST_REL_LENGTH : thm
    val LIST_REL_MAP1 : thm
    val LIST_REL_MAP2 : thm
    val LIST_REL_NIL : thm
    val LIST_REL_cases : thm
    val LIST_REL_def : thm
    val LIST_REL_ind : thm
    val LIST_REL_mono : thm
    val LIST_REL_rules : thm
    val LIST_REL_strongind : thm
    val LIST_REL_trans : thm
    val LIST_TO_SET : thm
    val LIST_TO_SET_APPEND : thm
    val LIST_TO_SET_EQ_EMPTY : thm
    val LIST_TO_SET_FILTER : thm
    val LIST_TO_SET_FLAT : thm
    val LIST_TO_SET_GENLIST : thm
    val LIST_TO_SET_MAP : thm
    val LIST_TO_SET_REVERSE : thm
    val LIST_TO_SET_SNOC : thm
    val LIST_TO_SET_THM : thm
    val LLEX_NIL2 : thm
    val LLEX_THM : thm
    val LLEX_not_WF : thm
    val LLEX_total : thm
    val LLEX_transitive : thm
    val LRC_MEM : thm
    val LRC_MEM_right : thm
    val LUPDATE_LENGTH : thm
    val LUPDATE_MAP : thm
    val LUPDATE_SEM : thm
    val LUPDATE_SNOC : thm
    val LUPDATE_compute : thm
    val MAP2 : thm
    val MAP2_CONG : thm
    val MAP2_MAP : thm
    val MAP2_ZIP : thm
    val MAP2_def : thm
    val MAP2_ind : thm
    val MAP_APPEND : thm
    val MAP_CONG : thm
    val MAP_EQ_EVERY2 : thm
    val MAP_EQ_NIL : thm
    val MAP_EQ_f : thm
    val MAP_FLAT : thm
    val MAP_GENLIST : thm
    val MAP_ID : thm
    val MAP_LIST_BIND : thm
    val MAP_MAP_o : thm
    val MAP_SNOC : thm
    val MAP_TL : thm
    val MAP_ZIP : thm
    val MAP_ZIP_SAME : thm
    val MAP_o : thm
    val MEM : thm
    val MEM_APPEND : thm
    val MEM_APPEND_lemma : thm
    val MEM_DROP : thm
    val MEM_EL : thm
    val MEM_FILTER : thm
    val MEM_FLAT : thm
    val MEM_GENLIST : thm
    val MEM_LUPDATE : thm
    val MEM_LUPDATE_E : thm
    val MEM_MAP : thm
    val MEM_REVERSE : thm
    val MEM_SET_TO_LIST : thm
    val MEM_SNOC : thm
    val MEM_SPLIT : thm
    val MEM_SPLIT_APPEND_first : thm
    val MEM_SPLIT_APPEND_last : thm
    val MEM_ZIP : thm
    val MEM_ZIP_MEM_MAP : thm
    val MEM_dropWhile_IMP : thm
    val MONO_EVERY : thm
    val MONO_EXISTS : thm
    val NOT_CONS_NIL : thm
    val NOT_EQ_LIST : thm
    val NOT_EVERY : thm
    val NOT_EXISTS : thm
    val NOT_NIL_CONS : thm
    val NOT_NULL_MEM : thm
    val NRC_LRC : thm
    val NULL : thm
    val NULL_EQ : thm
    val NULL_FILTER : thm
    val NULL_GENLIST : thm
    val NULL_LENGTH : thm
    val REVERSE_11 : thm
    val REVERSE_APPEND : thm
    val REVERSE_EQ_NIL : thm
    val REVERSE_EQ_SING : thm
    val REVERSE_GENLIST : thm
    val REVERSE_REV : thm
    val REVERSE_REVERSE : thm
    val REVERSE_SNOC : thm
    val REVERSE_SNOC_DEF : thm
    val REVERSE_o_REVERSE : thm
    val REV_REVERSE_LEM : thm
    val SET_TO_LIST_CARD : thm
    val SET_TO_LIST_EMPTY : thm
    val SET_TO_LIST_IND : thm
    val SET_TO_LIST_INV : thm
    val SET_TO_LIST_IN_MEM : thm
    val SET_TO_LIST_SING : thm
    val SET_TO_LIST_THM : thm
    val SINGL_APPLY_MAP : thm
    val SINGL_APPLY_PERMUTE : thm
    val SINGL_LIST_APPLY_L : thm
    val SINGL_LIST_APPLY_R : thm
    val SINGL_SINGL_APPLY : thm
    val SNOC_11 : thm
    val SNOC_APPEND : thm
    val SNOC_Axiom : thm
    val SNOC_CASES : thm
    val SNOC_INDUCT : thm
    val SUM_ACC_SUM_LEM : thm
    val SUM_APPEND : thm
    val SUM_IMAGE_LIST_TO_SET_upper_bound : thm
    val SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST : thm
    val SUM_MAP_FOLDL : thm
    val SUM_MAP_MEM_bound : thm
    val SUM_MAP_PLUS : thm
    val SUM_MAP_PLUS_ZIP : thm
    val SUM_SNOC : thm
    val SUM_SUM_ACC : thm
    val SUM_eq_0 : thm
    val SWAP_REVERSE : thm
    val SWAP_REVERSE_SYM : thm
    val TAKE_0 : thm
    val TAKE_APPEND1 : thm
    val TAKE_APPEND2 : thm
    val TAKE_DROP : thm
    val TAKE_LENGTH_ID : thm
    val TAKE_LENGTH_ID_rwt : thm
    val TAKE_LENGTH_TOO_LONG : thm
    val TAKE_SUM : thm
    val TAKE_compute : thm
    val TAKE_splitAtPki : thm
    val TL_GENLIST : thm
    val UNION_APPEND : thm
    val UNZIP_MAP : thm
    val UNZIP_THM : thm
    val UNZIP_ZIP : thm
    val WF_LIST_PRED : thm
    val ZIP_DROP : thm
    val ZIP_GENLIST : thm
    val ZIP_MAP : thm
    val ZIP_UNZIP : thm
    val all_distinct_nub : thm
    val datatype_list : thm
    val dropWhile_APPEND_EVERY : thm
    val dropWhile_APPEND_EXISTS : thm
    val dropWhile_eq_nil : thm
    val dropWhile_splitAtPki : thm
    val el_append3 : thm
    val every_zip_fst : thm
    val every_zip_snd : thm
    val exists_list_GENLIST : thm
    val isPREFIX_THM : thm
    val length_nub_append : thm
    val list_11 : thm
    val list_Axiom : thm
    val list_Axiom_old : thm
    val list_CASES : thm
    val list_INDUCT : thm
    val list_case_compute : thm
    val list_case_cong : thm
    val list_distinct : thm
    val list_induction : thm
    val list_nchotomy : thm
    val list_size_cong : thm
    val list_to_set_diff : thm
    val lupdate_append : thm
    val lupdate_append2 : thm
    val mem_exists_set : thm
    val nub_append : thm
    val nub_set : thm
    val splitAtPki_APPEND : thm
    val splitAtPki_EQN : thm

  val list_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ind_type] Parent theory of "list"

   [operator] Parent theory of "list"

   [pred_set] Parent theory of "list"

   [ALL_DISTINCT]  Definition

      |- (ALL_DISTINCT [] ⇔ T) ∧
         ∀h t. ALL_DISTINCT (h::t) ⇔ ¬MEM h t ∧ ALL_DISTINCT t

   [APPEND]  Definition

      |- (∀l. [] ++ l = l) ∧ ∀l1 l2 h. h::l1 ++ l2 = h::(l1 ++ l2)

   [DROP_def]  Definition

      |- (∀n. DROP n [] = []) ∧
         ∀n x xs. DROP n (x::xs) = if n = 0 then x::xs else DROP (n − 1) xs

   [EL]  Definition

      |- (∀l. EL 0 l = HD l) ∧ ∀l n. EL (SUC n) l = EL n (TL l)

   [EVERY_DEF]  Definition

      |- (∀P. EVERY P [] ⇔ T) ∧ ∀P h t. EVERY P (h::t) ⇔ P h ∧ EVERY P t

   [EVERYi_DEF]  Definition

      |- (∀P. EVERYi P [] ⇔ T) ∧
         ∀P h t. EVERYi P (h::t) ⇔ P 0 h ∧ EVERYi (P o SUC) t

   [EXISTS_DEF]  Definition

      |- (∀P. EXISTS P [] ⇔ F) ∧ ∀P h t. EXISTS P (h::t) ⇔ P h ∨ EXISTS P t

   [FILTER]  Definition

      |- (∀P. FILTER P [] = []) ∧
         ∀P h t.
           FILTER P (h::t) = if P h then h::FILTER P t else FILTER P t

   [FIND_def]  Definition

      |- ∀P. FIND P = OPTION_MAP SND o INDEX_FIND 0 P

   [FLAT]  Definition

      |- (FLAT [] = []) ∧ ∀h t. FLAT (h::t) = h ++ FLAT t

   [FOLDL]  Definition

      |- (∀f e. FOLDL f e [] = e) ∧
         ∀f e x l. FOLDL f e (x::l) = FOLDL f (f e x) l

   [FOLDR]  Definition

      |- (∀f e. FOLDR f e [] = e) ∧
         ∀f e x l. FOLDR f e (x::l) = f x (FOLDR f e l)

   [FRONT_DEF]  Definition

      |- ∀h t. FRONT (h::t) = if t = [] then [] else h::FRONT t

   [GENLIST]  Definition

      |- (∀f. GENLIST f 0 = []) ∧
         ∀f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n)

   [GENLIST_AUX]  Definition

      |- (∀f l. GENLIST_AUX f 0 l = l) ∧
         ∀f n l. GENLIST_AUX f (SUC n) l = GENLIST_AUX f n (f n::l)

   [HD]  Definition

      |- ∀h t. HD (h::t) = h

   [INDEX_FIND_def]  Definition

      |- (∀i P. INDEX_FIND i P [] = NONE) ∧
         ∀i P h t.
           INDEX_FIND i P (h::t) =
           if P h then SOME (i,h) else INDEX_FIND (SUC i) P t

   [INDEX_OF_def]  Definition

      |- ∀x. INDEX_OF x = OPTION_MAP FST o INDEX_FIND 0 ($= x)

   [LAST_DEF]  Definition

      |- ∀h t. LAST (h::t) = if t = [] then h else LAST t

   [LENGTH]  Definition

      |- (LENGTH [] = 0) ∧ ∀h t. LENGTH (h::t) = SUC (LENGTH t)

   [LEN_DEF]  Definition

      |- (∀n. LEN [] n = n) ∧ ∀h t n. LEN (h::t) n = LEN t (n + 1)

   [LIST_APPLY_DEF]  Definition

      |- ∀fs xs. fs <*> xs = LIST_BIND fs (combin$C MAP xs)

   [LIST_BIND_DEF]  Definition

      |- ∀l f. LIST_BIND l f = FLAT (MAP f l)

   [LIST_IGNORE_BIND_DEF]  Definition

      |- ∀m1 m2. LIST_IGNORE_BIND m1 m2 = LIST_BIND m1 (K m2)

   [LIST_LIFT2_DEF]  Definition

      |- ∀f xs ys. LIST_LIFT2 f xs ys = MAP f xs <*> ys

   [LIST_TO_SET_DEF]  Definition

      |- (∀x. set [] x ⇔ F) ∧ ∀h t x. set (h::t) x ⇔ (x = h) ∨ set t x

   [LLEX_DEF]  Definition

      |- (∀R l2. LLEX R [] l2 ⇔ l2 ≠ []) ∧
         ∀R h1 t1 l2.
           LLEX R (h1::t1) l2 ⇔
           case l2 of
             [] => F
           | h2::t2 =>
               if R h1 h2 then T else if h1 = h2 then LLEX R t1 t2 else F

   [LRC_def]  Definition

      |- (∀R x y. LRC R [] x y ⇔ (x = y)) ∧
         ∀R h t x y. LRC R (h::t) x y ⇔ (x = h) ∧ ∃z. R x z ∧ LRC R t z y

   [LUPDATE_def]  Definition

      |- (∀e n. LUPDATE e n [] = []) ∧
         (∀e x l. LUPDATE e 0 (x::l) = e::l) ∧
         ∀e n x l. LUPDATE e (SUC n) (x::l) = x::LUPDATE e n l

   [MAP]  Definition

      |- (∀f. MAP f [] = []) ∧ ∀f h t. MAP f (h::t) = f h::MAP f t

   [NULL_DEF]  Definition

      |- (NULL [] ⇔ T) ∧ ∀h t. NULL (h::t) ⇔ F

   [PAD_LEFT]  Definition

      |- ∀c n s. PAD_LEFT c n s = GENLIST (K c) (n − LENGTH s) ++ s

   [PAD_RIGHT]  Definition

      |- ∀c n s. PAD_RIGHT c n s = s ++ GENLIST (K c) (n − LENGTH s)

   [REVERSE_DEF]  Definition

      |- (REVERSE [] = []) ∧ ∀h t. REVERSE (h::t) = REVERSE t ++ [h]

   [REV_DEF]  Definition

      |- (∀acc. REV [] acc = acc) ∧
         ∀h t acc. REV (h::t) acc = REV t (h::acc)

   [SET_TO_LIST_primitive]  Definition

      |- SET_TO_LIST =
         WFREC (@R. WF R ∧ ∀s. FINITE s ∧ s ≠ ∅ ⇒ R (REST s) s)
           (λSET_TO_LIST s.
              I
                (if FINITE s then
                   if s = ∅ then [] else CHOICE s::SET_TO_LIST (REST s)
                 else ARB))

   [SNOC]  Definition

      |- (∀x. SNOC x [] = [x]) ∧ ∀x x' l. SNOC x (x'::l) = x'::SNOC x l

   [SUM]  Definition

      |- (SUM [] = 0) ∧ ∀h t. SUM (h::t) = h + SUM t

   [SUM_ACC_DEF]  Definition

      |- (∀acc. SUM_ACC [] acc = acc) ∧
         ∀h t acc. SUM_ACC (h::t) acc = SUM_ACC t (h + acc)

   [TAKE_def]  Definition

      |- (∀n. TAKE n [] = []) ∧
         ∀n x xs. TAKE n (x::xs) = if n = 0 then [] else x::TAKE (n − 1) xs

   [TL]  Definition

      |- ∀h t. TL (h::t) = t

   [UNZIP]  Definition

      |- (UNZIP [] = ([],[])) ∧
         ∀x l. UNZIP (x::l) = (FST x::FST (UNZIP l),SND x::SND (UNZIP l))

   [ZIP]  Definition

      |- (ZIP ([],[]) = []) ∧
         ∀x1 l1 x2 l2. ZIP (x1::l1,x2::l2) = (x1,x2)::ZIP (l1,l2)

   [dropWhile_def]  Definition

      |- (∀P. dropWhile P [] = []) ∧
         ∀P h t. dropWhile P (h::t) = if P h then dropWhile P t else h::t

   [isPREFIX]  Definition

      |- (∀l. [] ≼ l ⇔ T) ∧
         ∀h t l. h::t ≼ l ⇔ case l of [] => F | h'::t' => (h = h') ∧ t ≼ t'

   [list_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'list' .
                  (∀a0'.
                     (a0' = ind_type$CONSTR 0 ARB (λn. ind_type$BOTTOM)) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC 0) a0
                              (ind_type$FCONS a1 (λn. ind_type$BOTTOM))) a0
                           a1) ∧ 'list' a1) ⇒
                     'list' a0') ⇒
                  'list' a0') rep

   [list_case_def]  Definition

      |- (∀v f. list_CASE [] v f = v) ∧
         ∀a0 a1 v f. list_CASE (a0::a1) v f = f a0 a1

   [list_size_def]  Definition

      |- (∀f. list_size f [] = 0) ∧
         ∀f a0 a1. list_size f (a0::a1) = 1 + (f a0 + list_size f a1)

   [nub_def]  Definition

      |- (nub [] = []) ∧
         ∀x l. nub (x::l) = if MEM x l then nub l else x::nub l

   [splitAtPki_DEF]  Definition

      |- (∀P k. splitAtPki P k [] = k [] []) ∧
         ∀P k h t.
           splitAtPki P k (h::t) =
           if P 0 h then k [] (h::t)
           else splitAtPki (P o SUC) (λp s. k (h::p) s) t

   [ALL_DISTINCT_APPEND]  Theorem

      |- ∀l1 l2.
           ALL_DISTINCT (l1 ++ l2) ⇔
           ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 ∧ ∀e. MEM e l1 ⇒ ¬MEM e l2

   [ALL_DISTINCT_CARD_LIST_TO_SET]  Theorem

      |- ∀ls. ALL_DISTINCT ls ⇒ (CARD (set ls) = LENGTH ls)

   [ALL_DISTINCT_DROP]  Theorem

      |- ∀ls n. ALL_DISTINCT ls ⇒ ALL_DISTINCT (DROP n ls)

   [ALL_DISTINCT_EL_IMP]  Theorem

      |- ∀l n1 n2.
           ALL_DISTINCT l ∧ n1 < LENGTH l ∧ n2 < LENGTH l ⇒
           ((EL n1 l = EL n2 l) ⇔ (n1 = n2))

   [ALL_DISTINCT_FILTER]  Theorem

      |- ∀l. ALL_DISTINCT l ⇔ ∀x. MEM x l ⇒ (FILTER ($= x) l = [x])

   [ALL_DISTINCT_FILTER_EL_IMP]  Theorem

      |- ∀P l n1 n2.
           ALL_DISTINCT (FILTER P l) ∧ n1 < LENGTH l ∧ n2 < LENGTH l ∧
           P (EL n1 l) ∧ (EL n1 l = EL n2 l) ⇒
           (n1 = n2)

   [ALL_DISTINCT_GENLIST]  Theorem

      |- ALL_DISTINCT (GENLIST f n) ⇔
         ∀m1 m2. m1 < n ∧ m2 < n ∧ (f m1 = f m2) ⇒ (m1 = m2)

   [ALL_DISTINCT_MAP]  Theorem

      |- ∀f ls. ALL_DISTINCT (MAP f ls) ⇒ ALL_DISTINCT ls

   [ALL_DISTINCT_MAP_INJ]  Theorem

      |- ∀ls f.
           (∀x y. MEM x ls ∧ MEM y ls ∧ (f x = f y) ⇒ (x = y)) ∧
           ALL_DISTINCT ls ⇒
           ALL_DISTINCT (MAP f ls)

   [ALL_DISTINCT_REVERSE]  Theorem

      |- ∀l. ALL_DISTINCT (REVERSE l) ⇔ ALL_DISTINCT l

   [ALL_DISTINCT_SET_TO_LIST]  Theorem

      |- ∀s. FINITE s ⇒ ALL_DISTINCT (SET_TO_LIST s)

   [ALL_DISTINCT_SING]  Theorem

      |- ∀x. ALL_DISTINCT [x]

   [ALL_DISTINCT_SNOC]  Theorem

      |- ∀x l. ALL_DISTINCT (SNOC x l) ⇔ ¬MEM x l ∧ ALL_DISTINCT l

   [ALL_DISTINCT_ZIP]  Theorem

      |- ∀l1 l2.
           ALL_DISTINCT l1 ∧ (LENGTH l1 = LENGTH l2) ⇒
           ALL_DISTINCT (ZIP (l1,l2))

   [ALL_DISTINCT_ZIP_SWAP]  Theorem

      |- ∀l1 l2.
           ALL_DISTINCT (ZIP (l1,l2)) ∧ (LENGTH l1 = LENGTH l2) ⇒
           ALL_DISTINCT (ZIP (l2,l1))

   [APPEND_11]  Theorem

      |- (∀l1 l2 l3. (l1 ++ l2 = l1 ++ l3) ⇔ (l2 = l3)) ∧
         ∀l1 l2 l3. (l2 ++ l1 = l3 ++ l1) ⇔ (l2 = l3)

   [APPEND_11_LENGTH]  Theorem

      |- (∀l1 l2 l1' l2'.
            (LENGTH l1 = LENGTH l1') ⇒
            ((l1 ++ l2 = l1' ++ l2') ⇔ (l1 = l1') ∧ (l2 = l2'))) ∧
         ∀l1 l2 l1' l2'.
           (LENGTH l2 = LENGTH l2') ⇒
           ((l1 ++ l2 = l1' ++ l2') ⇔ (l1 = l1') ∧ (l2 = l2'))

   [APPEND_ASSOC]  Theorem

      |- ∀l1 l2 l3. l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3

   [APPEND_EQ_APPEND]  Theorem

      |- (l1 ++ l2 = m1 ++ m2) ⇔
         (∃l. (l1 = m1 ++ l) ∧ (m2 = l ++ l2)) ∨
         ∃l. (m1 = l1 ++ l) ∧ (l2 = l ++ m2)

   [APPEND_EQ_APPEND_MID]  Theorem

      |- (l1 ++ [e] ++ l2 = m1 ++ m2) ⇔
         (∃l. (m1 = l1 ++ [e] ++ l) ∧ (l2 = l ++ m2)) ∨
         ∃l. (l1 = m1 ++ l) ∧ (m2 = l ++ [e] ++ l2)

   [APPEND_EQ_CONS]  Theorem

      |- (l1 ++ l2 = h::t) ⇔
         (l1 = []) ∧ (l2 = h::t) ∨ ∃lt. (l1 = h::lt) ∧ (t = lt ++ l2)

   [APPEND_EQ_SELF]  Theorem

      |- (∀l1 l2. (l1 ++ l2 = l1) ⇔ (l2 = [])) ∧
         (∀l1 l2. (l1 ++ l2 = l2) ⇔ (l1 = [])) ∧
         (∀l1 l2. (l1 = l1 ++ l2) ⇔ (l2 = [])) ∧
         ∀l1 l2. (l2 = l1 ++ l2) ⇔ (l1 = [])

   [APPEND_EQ_SING]  Theorem

      |- (l1 ++ l2 = [e]) ⇔ (l1 = [e]) ∧ (l2 = []) ∨ (l1 = []) ∧ (l2 = [e])

   [APPEND_FRONT_LAST]  Theorem

      |- ∀l. l ≠ [] ⇒ (FRONT l ++ [LAST l] = l)

   [APPEND_LENGTH_EQ]  Theorem

      |- ∀l1 l1'.
           (LENGTH l1 = LENGTH l1') ⇒
           ∀l2 l2'.
             (LENGTH l2 = LENGTH l2') ⇒
             ((l1 ++ l2 = l1' ++ l2') ⇔ (l1 = l1') ∧ (l2 = l2'))

   [APPEND_NIL]  Theorem

      |- ∀l. l ++ [] = l

   [APPEND_SNOC]  Theorem

      |- ∀l1 x l2. l1 ++ SNOC x l2 = SNOC x (l1 ++ l2)

   [APPEND_eq_NIL]  Theorem

      |- (∀l1 l2. ([] = l1 ++ l2) ⇔ (l1 = []) ∧ (l2 = [])) ∧
         ∀l1 l2. (l1 ++ l2 = []) ⇔ (l1 = []) ∧ (l2 = [])

   [BIGUNION_IMAGE_set_SUBSET]  Theorem

      |- BIGUNION (IMAGE f (set ls)) ⊆ s ⇔ ∀x. MEM x ls ⇒ f x ⊆ s

   [CARD_LIST_TO_SET]  Theorem

      |- CARD (set ls) ≤ LENGTH ls

   [CONS]  Theorem

      |- ∀l. ¬NULL l ⇒ (HD l::TL l = l)

   [CONS_11]  Theorem

      |- ∀a0 a1 a0' a1'. (a0::a1 = a0'::a1') ⇔ (a0 = a0') ∧ (a1 = a1')

   [CONS_ACYCLIC]  Theorem

      |- ∀l x. l ≠ x::l ∧ x::l ≠ l

   [DISJOINT_GENLIST_PLUS]  Theorem

      |- DISJOINT x (set (GENLIST ($+ n) (a + b))) ⇒
         DISJOINT x (set (GENLIST ($+ n) a)) ∧
         DISJOINT x (set (GENLIST ($+ (n + a)) b))

   [DROP_0]  Theorem

      |- DROP 0 l = l

   [DROP_LENGTH_TOO_LONG]  Theorem

      |- ∀l n. LENGTH l ≤ n ⇒ (DROP n l = [])

   [DROP_NIL]  Theorem

      |- ∀ls n. (DROP n ls = []) ⇔ n ≥ LENGTH ls

   [DROP_compute]  Theorem

      |- (∀l. DROP 0 l = l) ∧ (∀n. DROP (NUMERAL (BIT1 n)) [] = []) ∧
         (∀n. DROP (NUMERAL (BIT2 n)) [] = []) ∧
         (∀n h t.
            DROP (NUMERAL (BIT1 n)) (h::t) =
            DROP (NUMERAL (BIT1 n) − 1) t) ∧
         ∀n h t. DROP (NUMERAL (BIT2 n)) (h::t) = DROP (NUMERAL (BIT1 n)) t

   [DROP_splitAtPki]  Theorem

      |- DROP n l = splitAtPki (K o $= n) (K I) l

   [EL_ALL_DISTINCT_EL_EQ]  Theorem

      |- ∀l.
           ALL_DISTINCT l ⇔
           ∀n1 n2.
             n1 < LENGTH l ∧ n2 < LENGTH l ⇒
             ((EL n1 l = EL n2 l) ⇔ (n1 = n2))

   [EL_GENLIST]  Theorem

      |- ∀f n x. x < n ⇒ (EL x (GENLIST f n) = f x)

   [EL_LENGTH_SNOC]  Theorem

      |- ∀l x. EL (LENGTH l) (SNOC x l) = x

   [EL_LENGTH_dropWhile_REVERSE]  Theorem

      |- ∀P ls k.
           LENGTH (dropWhile P (REVERSE ls)) ≤ k ∧ k < LENGTH ls ⇒
           P (EL k ls)

   [EL_LUPDATE]  Theorem

      |- ∀ys x i k.
           EL i (LUPDATE x k ys) =
           if (i = k) ∧ k < LENGTH ys then x else EL i ys

   [EL_MAP]  Theorem

      |- ∀n l. n < LENGTH l ⇒ ∀f. EL n (MAP f l) = f (EL n l)

   [EL_REVERSE]  Theorem

      |- ∀n l.
           n < LENGTH l ⇒ (EL n (REVERSE l) = EL (PRE (LENGTH l − n)) l)

   [EL_SNOC]  Theorem

      |- ∀n l. n < LENGTH l ⇒ ∀x. EL n (SNOC x l) = EL n l

   [EL_ZIP]  Theorem

      |- ∀l1 l2 n.
           (LENGTH l1 = LENGTH l2) ∧ n < LENGTH l1 ⇒
           (EL n (ZIP (l1,l2)) = (EL n l1,EL n l2))

   [EL_compute]  Theorem

      |- ∀n. EL n l = if n = 0 then HD l else EL (PRE n) (TL l)

   [EL_restricted]  Theorem

      |- (EL 0 = HD) ∧ (EL (SUC n) (l::ls) = EL n ls)

   [EL_simp]  Theorem

      |- (EL (NUMERAL (BIT1 n)) l = EL (PRE (NUMERAL (BIT1 n))) (TL l)) ∧
         (EL (NUMERAL (BIT2 n)) l = EL (NUMERAL (BIT1 n)) (TL l))

   [EL_simp_restricted]  Theorem

      |- (EL (NUMERAL (BIT1 n)) (l::ls) = EL (PRE (NUMERAL (BIT1 n))) ls) ∧
         (EL (NUMERAL (BIT2 n)) (l::ls) = EL (NUMERAL (BIT1 n)) ls)

   [EQ_LIST]  Theorem

      |- ∀h1 h2. (h1 = h2) ⇒ ∀l1 l2. (l1 = l2) ⇒ (h1::l1 = h2::l2)

   [EVERY2_EVERY]  Theorem

      |- ∀l1 l2 f.
           LIST_REL f l1 l2 ⇔
           (LENGTH l1 = LENGTH l2) ∧ EVERY (UNCURRY f) (ZIP (l1,l2))

   [EVERY2_LENGTH]  Theorem

      |- ∀P l1 l2. LIST_REL P l1 l2 ⇒ (LENGTH l1 = LENGTH l2)

   [EVERY2_LUPDATE_same]  Theorem

      |- ∀P l1 l2 v1 v2 n.
           P v1 v2 ∧ LIST_REL P l1 l2 ⇒
           LIST_REL P (LUPDATE v1 n l1) (LUPDATE v2 n l2)

   [EVERY2_MAP]  Theorem

      |- (LIST_REL P (MAP f l1) l2 ⇔ LIST_REL (λx y. P (f x) y) l1 l2) ∧
         (LIST_REL Q l1 (MAP g l2) ⇔ LIST_REL (λx y. Q x (g y)) l1 l2)

   [EVERY2_MEM_MONO]  Theorem

      |- ∀P Q l1 l2.
           (∀x. MEM x (ZIP (l1,l2)) ∧ UNCURRY P x ⇒ UNCURRY Q x) ∧
           LIST_REL P l1 l2 ⇒
           LIST_REL Q l1 l2

   [EVERY2_REVERSE]  Theorem

      |- ∀R l1 l2. LIST_REL R l1 l2 ⇒ LIST_REL R (REVERSE l1) (REVERSE l2)

   [EVERY2_THM]  Theorem

      |- (∀P ys. LIST_REL P [] ys ⇔ (ys = [])) ∧
         (∀P yys x xs.
            LIST_REL P (x::xs) yys ⇔
            ∃y ys. (yys = y::ys) ∧ P x y ∧ LIST_REL P xs ys) ∧
         (∀P xs. LIST_REL P xs [] ⇔ (xs = [])) ∧
         ∀P xxs y ys.
           LIST_REL P xxs (y::ys) ⇔
           ∃x xs. (xxs = x::xs) ∧ P x y ∧ LIST_REL P xs ys

   [EVERY2_cong]  Theorem

      |- ∀l1 l1' l2 l2' P P'.
           (l1 = l1') ∧ (l2 = l2') ∧
           (∀x y. MEM x l1' ∧ MEM y l2' ⇒ (P x y ⇔ P' x y)) ⇒
           (LIST_REL P l1 l2 ⇔ LIST_REL P' l1' l2')

   [EVERY2_mono]  Theorem

      |- (∀x y. R1 x y ⇒ R2 x y) ⇒ LIST_REL R1 l1 l2 ⇒ LIST_REL R2 l1 l2

   [EVERY2_refl]  Theorem

      |- (∀x. MEM x ls ⇒ R x x) ⇒ LIST_REL R ls ls

   [EVERY2_sym]  Theorem

      |- (∀x y. R1 x y ⇒ R2 y x) ⇒ ∀x y. LIST_REL R1 x y ⇒ LIST_REL R2 y x

   [EVERY2_trans]  Theorem

      |- (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒
         ∀x y z. LIST_REL R x y ∧ LIST_REL R y z ⇒ LIST_REL R x z

   [EVERY_APPEND]  Theorem

      |- ∀P l1 l2. EVERY P (l1 ++ l2) ⇔ EVERY P l1 ∧ EVERY P l2

   [EVERY_CONG]  Theorem

      |- ∀l1 l2 P P'.
           (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (P x ⇔ P' x)) ⇒
           (EVERY P l1 ⇔ EVERY P' l2)

   [EVERY_CONJ]  Theorem

      |- ∀P Q l. EVERY (λx. P x ∧ Q x) l ⇔ EVERY P l ∧ EVERY Q l

   [EVERY_EL]  Theorem

      |- ∀l P. EVERY P l ⇔ ∀n. n < LENGTH l ⇒ P (EL n l)

   [EVERY_FILTER]  Theorem

      |- ∀P1 P2 l. EVERY P1 (FILTER P2 l) ⇔ EVERY (λx. P2 x ⇒ P1 x) l

   [EVERY_FILTER_IMP]  Theorem

      |- ∀P1 P2 l. EVERY P1 l ⇒ EVERY P1 (FILTER P2 l)

   [EVERY_GENLIST]  Theorem

      |- ∀n. EVERY P (GENLIST f n) ⇔ ∀i. i < n ⇒ P (f i)

   [EVERY_MAP]  Theorem

      |- ∀P f l. EVERY P (MAP f l) ⇔ EVERY (λx. P (f x)) l

   [EVERY_MEM]  Theorem

      |- ∀P l. EVERY P l ⇔ ∀e. MEM e l ⇒ P e

   [EVERY_MEM_MONO]  Theorem

      |- ∀P Q l. (∀x. MEM x l ∧ P x ⇒ Q x) ∧ EVERY P l ⇒ EVERY Q l

   [EVERY_MONOTONIC]  Theorem

      |- ∀P Q. (∀x. P x ⇒ Q x) ⇒ ∀l. EVERY P l ⇒ EVERY Q l

   [EVERY_NOT_EXISTS]  Theorem

      |- ∀P l. EVERY P l ⇔ ¬EXISTS (λx. ¬P x) l

   [EVERY_SIMP]  Theorem

      |- ∀c l. EVERY (λx. c) l ⇔ (l = []) ∨ c

   [EVERY_SNOC]  Theorem

      |- ∀P x l. EVERY P (SNOC x l) ⇔ EVERY P l ∧ P x

   [EXISTS_APPEND]  Theorem

      |- ∀P l1 l2. EXISTS P (l1 ++ l2) ⇔ EXISTS P l1 ∨ EXISTS P l2

   [EXISTS_CONG]  Theorem

      |- ∀l1 l2 P P'.
           (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (P x ⇔ P' x)) ⇒
           (EXISTS P l1 ⇔ EXISTS P' l2)

   [EXISTS_GENLIST]  Theorem

      |- ∀n. EXISTS P (GENLIST f n) ⇔ ∃i. i < n ∧ P (f i)

   [EXISTS_LIST]  Theorem

      |- (∃l. P l) ⇔ P [] ∨ ∃h t. P (h::t)

   [EXISTS_LIST_EQ_MAP]  Theorem

      |- ∀ls f. EVERY (λx. ∃y. x = f y) ls ⇒ ∃l. ls = MAP f l

   [EXISTS_MAP]  Theorem

      |- ∀P f l. EXISTS P (MAP f l) ⇔ EXISTS (λx. P (f x)) l

   [EXISTS_MEM]  Theorem

      |- ∀P l. EXISTS P l ⇔ ∃e. MEM e l ∧ P e

   [EXISTS_NOT_EVERY]  Theorem

      |- ∀P l. EXISTS P l ⇔ ¬EVERY (λx. ¬P x) l

   [EXISTS_SIMP]  Theorem

      |- ∀c l. EXISTS (λx. c) l ⇔ l ≠ [] ∧ c

   [EXISTS_SNOC]  Theorem

      |- ∀P x l. EXISTS P (SNOC x l) ⇔ P x ∨ EXISTS P l

   [FILTER_ALL_DISTINCT]  Theorem

      |- ∀P l. ALL_DISTINCT l ⇒ ALL_DISTINCT (FILTER P l)

   [FILTER_APPEND_DISTRIB]  Theorem

      |- ∀P L M. FILTER P (L ++ M) = FILTER P L ++ FILTER P M

   [FILTER_COND_REWRITE]  Theorem

      |- (FILTER P [] = []) ∧
         (∀h. P h ⇒ (FILTER P (h::l) = h::FILTER P l)) ∧
         ∀h. ¬P h ⇒ (FILTER P (h::l) = FILTER P l)

   [FILTER_EQ_APPEND]  Theorem

      |- ∀P l l1 l2.
           (FILTER P l = l1 ++ l2) ⇔
           ∃l3 l4. (l = l3 ++ l4) ∧ (FILTER P l3 = l1) ∧ (FILTER P l4 = l2)

   [FILTER_EQ_CONS]  Theorem

      |- ∀P l h lr.
           (FILTER P l = h::lr) ⇔
           ∃l1 l2.
             (l = l1 ++ [h] ++ l2) ∧ (FILTER P l1 = []) ∧
             (FILTER P l2 = lr) ∧ P h

   [FILTER_EQ_ID]  Theorem

      |- ∀P l. (FILTER P l = l) ⇔ EVERY P l

   [FILTER_EQ_NIL]  Theorem

      |- ∀P l. (FILTER P l = []) ⇔ EVERY (λx. ¬P x) l

   [FILTER_NEQ_ID]  Theorem

      |- ∀P l. FILTER P l ≠ l ⇔ ∃x. MEM x l ∧ ¬P x

   [FILTER_NEQ_NIL]  Theorem

      |- ∀P l. FILTER P l ≠ [] ⇔ ∃x. MEM x l ∧ P x

   [FILTER_REVERSE]  Theorem

      |- ∀l P. FILTER P (REVERSE l) = REVERSE (FILTER P l)

   [FINITE_LIST_TO_SET]  Theorem

      |- ∀l. FINITE (set l)

   [FLAT_APPEND]  Theorem

      |- ∀l1 l2. FLAT (l1 ++ l2) = FLAT l1 ++ FLAT l2

   [FLAT_EQ_NIL]  Theorem

      |- ∀ls. (FLAT ls = []) ⇔ EVERY ($= []) ls

   [FOLDL2_FOLDL]  Theorem

      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ⇒
           ∀f a.
             FOLDL2 f a l1 l2 = FOLDL (λa. UNCURRY (f a)) a (ZIP (l1,l2))

   [FOLDL2_cong]  Theorem

      |- ∀l1 l1' l2 l2' a a' f f'.
           (l1 = l1') ∧ (l2 = l2') ∧ (a = a') ∧
           (∀z b c. MEM b l1' ∧ MEM c l2' ⇒ (f z b c = f' z b c)) ⇒
           (FOLDL2 f a l1 l2 = FOLDL2 f' a' l1' l2')

   [FOLDL2_def]  Theorem

      |- (∀f cs c bs b a.
            FOLDL2 f a (b::bs) (c::cs) = FOLDL2 f (f a b c) bs cs) ∧
         (∀f cs a. FOLDL2 f a [] cs = a) ∧
         ∀v7 v6 f a. FOLDL2 f a (v6::v7) [] = a

   [FOLDL2_ind]  Theorem

      |- ∀P.
           (∀f a b bs c cs. P f (f a b c) bs cs ⇒ P f a (b::bs) (c::cs)) ∧
           (∀f a cs. P f a [] cs) ∧ (∀f a v6 v7. P f a (v6::v7) []) ⇒
           ∀v v1 v2 v3. P v v1 v2 v3

   [FOLDL_CONG]  Theorem

      |- ∀l l' b b' f f'.
           (l = l') ∧ (b = b') ∧ (∀x a. MEM x l' ⇒ (f a x = f' a x)) ⇒
           (FOLDL f b l = FOLDL f' b' l')

   [FOLDL_EQ_FOLDR]  Theorem

      |- ∀f l e. ASSOC f ∧ COMM f ⇒ (FOLDL f e l = FOLDR f e l)

   [FOLDL_SNOC]  Theorem

      |- ∀f e x l. FOLDL f e (SNOC x l) = f (FOLDL f e l) x

   [FOLDL_UNION_BIGUNION]  Theorem

      |- ∀f ls s.
           FOLDL (λs x. s ∪ f x) s ls = s ∪ BIGUNION (IMAGE f (set ls))

   [FOLDL_UNION_BIGUNION_paired]  Theorem

      |- ∀f ls s.
           FOLDL (λs (x,y). s ∪ f x y) s ls =
           s ∪ BIGUNION (IMAGE (UNCURRY f) (set ls))

   [FOLDL_ZIP_SAME]  Theorem

      |- ∀ls f e. FOLDL f e (ZIP (ls,ls)) = FOLDL (λx y. f x (y,y)) e ls

   [FOLDR_CONG]  Theorem

      |- ∀l l' b b' f f'.
           (l = l') ∧ (b = b') ∧ (∀x a. MEM x l' ⇒ (f x a = f' x a)) ⇒
           (FOLDR f b l = FOLDR f' b' l')

   [FOLDR_CONS]  Theorem

      |- ∀f ls a. FOLDR (λx y. f x::y) a ls = MAP f ls ++ a

   [FORALL_LIST]  Theorem

      |- (∀l. P l) ⇔ P [] ∧ ∀h t. P (h::t)

   [FRONT_CONS]  Theorem

      |- (∀x. FRONT [x] = []) ∧ ∀x y z. FRONT (x::y::z) = x::FRONT (y::z)

   [FRONT_CONS_EQ_NIL]  Theorem

      |- (∀x xs. (FRONT (x::xs) = []) ⇔ (xs = [])) ∧
         (∀x xs. ([] = FRONT (x::xs)) ⇔ (xs = [])) ∧
         ∀x xs. NULL (FRONT (x::xs)) ⇔ NULL xs

   [FRONT_SNOC]  Theorem

      |- ∀x l. FRONT (SNOC x l) = l

   [GENLIST_APPEND]  Theorem

      |- ∀f a b.
           GENLIST f (a + b) = GENLIST f b ++ GENLIST (λt. f (t + b)) a

   [GENLIST_AUX_compute]  Theorem

      |- (∀f l. GENLIST_AUX f 0 l = l) ∧
         (∀f n l.
            GENLIST_AUX f (NUMERAL (BIT1 n)) l =
            GENLIST_AUX f (NUMERAL (BIT1 n) − 1)
              (f (NUMERAL (BIT1 n) − 1)::l)) ∧
         ∀f n l.
           GENLIST_AUX f (NUMERAL (BIT2 n)) l =
           GENLIST_AUX f (NUMERAL (BIT1 n)) (f (NUMERAL (BIT1 n))::l)

   [GENLIST_CONS]  Theorem

      |- GENLIST f (SUC n) = f 0::GENLIST (f o SUC) n

   [GENLIST_EL]  Theorem

      |- ∀ls f n.
           (n = LENGTH ls) ∧ (∀i. i < n ⇒ (f i = EL i ls)) ⇒
           (GENLIST f n = ls)

   [GENLIST_EL_MAP]  Theorem

      |- ∀f ls. GENLIST (λn. f (EL n ls)) (LENGTH ls) = MAP f ls

   [GENLIST_FUN_EQ]  Theorem

      |- ∀n f g. (GENLIST f n = GENLIST g n) ⇔ ∀x. x < n ⇒ (f x = g x)

   [GENLIST_GENLIST_AUX]  Theorem

      |- ∀n. GENLIST f n = GENLIST_AUX f n []

   [GENLIST_NUMERALS]  Theorem

      |- (GENLIST f 0 = []) ∧
         (GENLIST f (NUMERAL n) = GENLIST_AUX f (NUMERAL n) [])

   [GENLIST_PLUS_APPEND]  Theorem

      |- GENLIST ($+ a) n1 ++ GENLIST ($+ (n1 + a)) n2 =
         GENLIST ($+ a) (n1 + n2)

   [HD_GENLIST]  Theorem

      |- HD (GENLIST f (SUC n)) = f 0

   [HD_GENLIST_COR]  Theorem

      |- ∀n f. 0 < n ⇒ (HD (GENLIST f n) = f 0)

   [HD_dropWhile]  Theorem

      |- ∀P ls. EXISTS ($~ o P) ls ⇒ ¬P (HD (dropWhile P ls))

   [IMAGE_EL_count_LENGTH]  Theorem

      |- ∀f ls.
           IMAGE (λn. f (EL n ls)) (count (LENGTH ls)) = IMAGE f (set ls)

   [INFINITE_LIST_UNIV]  Theorem

      |- INFINITE pred_set$UNIV

   [INJ_MAP_EQ]  Theorem

      |- ∀f l1 l2.
           INJ f (set l1 ∪ set l2) pred_set$UNIV ∧ (MAP f l1 = MAP f l2) ⇒
           (l1 = l2)

   [IN_LIST_TO_SET]  Theorem

      |- T

   [ITSET_eq_FOLDL_SET_TO_LIST]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f a. ITSET f s a = FOLDL (combin$C f) a (SET_TO_LIST s)

   [LAST_APPEND_CONS]  Theorem

      |- ∀h l1 l2. LAST (l1 ++ h::l2) = LAST (h::l2)

   [LAST_CONS]  Theorem

      |- (∀x. LAST [x] = x) ∧ ∀x y z. LAST (x::y::z) = LAST (y::z)

   [LAST_CONS_cond]  Theorem

      |- LAST (h::t) = if t = [] then h else LAST t

   [LAST_EL]  Theorem

      |- ∀ls. ls ≠ [] ⇒ (LAST ls = EL (PRE (LENGTH ls)) ls)

   [LAST_REVERSE]  Theorem

      |- ∀ls. ls ≠ [] ⇒ (LAST (REVERSE ls) = HD ls)

   [LAST_SNOC]  Theorem

      |- ∀x l. LAST (SNOC x l) = x

   [LAST_compute]  Theorem

      |- (∀x. LAST [x] = x) ∧ ∀h1 h2 t. LAST (h1::h2::t) = LAST (h2::t)

   [LENGTH_APPEND]  Theorem

      |- ∀l1 l2. LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2

   [LENGTH_CONS]  Theorem

      |- ∀l n. (LENGTH l = SUC n) ⇔ ∃h l'. (LENGTH l' = n) ∧ (l = h::l')

   [LENGTH_DROP]  Theorem

      |- ∀n l. LENGTH (DROP n l) = LENGTH l − n

   [LENGTH_EQ_CONS]  Theorem

      |- ∀P n.
           (∀l. (LENGTH l = SUC n) ⇒ P l) ⇔
           ∀l. (LENGTH l = n) ⇒ (λl. ∀x. P (x::l)) l

   [LENGTH_EQ_NIL]  Theorem

      |- ∀P. (∀l. (LENGTH l = 0) ⇒ P l) ⇔ P []

   [LENGTH_EQ_NUM]  Theorem

      |- (∀l. (LENGTH l = 0) ⇔ (l = [])) ∧
         (∀l n.
            (LENGTH l = SUC n) ⇔ ∃h l'. (LENGTH l' = n) ∧ (l = h::l')) ∧
         ∀l n1 n2.
           (LENGTH l = n1 + n2) ⇔
           ∃l1 l2. (LENGTH l1 = n1) ∧ (LENGTH l2 = n2) ∧ (l = l1 ++ l2)

   [LENGTH_EQ_NUM_compute]  Theorem

      |- (∀l. (LENGTH l = 0) ⇔ (l = [])) ∧
         (∀l n.
            (LENGTH l = NUMERAL (BIT1 n)) ⇔
            ∃h l'. (LENGTH l' = NUMERAL (BIT1 n) − 1) ∧ (l = h::l')) ∧
         (∀l n.
            (LENGTH l = NUMERAL (BIT2 n)) ⇔
            ∃h l'. (LENGTH l' = NUMERAL (BIT1 n)) ∧ (l = h::l')) ∧
         ∀l n1 n2.
           (LENGTH l = n1 + n2) ⇔
           ∃l1 l2. (LENGTH l1 = n1) ∧ (LENGTH l2 = n2) ∧ (l = l1 ++ l2)

   [LENGTH_EQ_SUM]  Theorem

      |- ∀l n1 n2.
           (LENGTH l = n1 + n2) ⇔
           ∃l1 l2. (LENGTH l1 = n1) ∧ (LENGTH l2 = n2) ∧ (l = l1 ++ l2)

   [LENGTH_FILTER_LEQ_MONO]  Theorem

      |- ∀P Q.
           (∀x. P x ⇒ Q x) ⇒
           ∀ls. LENGTH (FILTER P ls) ≤ LENGTH (FILTER Q ls)

   [LENGTH_FRONT_CONS]  Theorem

      |- ∀x xs. LENGTH (FRONT (x::xs)) = LENGTH xs

   [LENGTH_GENLIST]  Theorem

      |- ∀f n. LENGTH (GENLIST f n) = n

   [LENGTH_LEN]  Theorem

      |- ∀L. LENGTH L = LEN L 0

   [LENGTH_LUPDATE]  Theorem

      |- ∀x n ys. LENGTH (LUPDATE x n ys) = LENGTH ys

   [LENGTH_MAP]  Theorem

      |- ∀l f. LENGTH (MAP f l) = LENGTH l

   [LENGTH_NIL]  Theorem

      |- ∀l. (LENGTH l = 0) ⇔ (l = [])

   [LENGTH_NIL_SYM]  Theorem

      |- (0 = LENGTH l) ⇔ (l = [])

   [LENGTH_REVERSE]  Theorem

      |- ∀l. LENGTH (REVERSE l) = LENGTH l

   [LENGTH_SNOC]  Theorem

      |- ∀x l. LENGTH (SNOC x l) = SUC (LENGTH l)

   [LENGTH_TAKE]  Theorem

      |- ∀n l. n ≤ LENGTH l ⇒ (LENGTH (TAKE n l) = n)

   [LENGTH_TL]  Theorem

      |- ∀l. 0 < LENGTH l ⇒ (LENGTH (TL l) = LENGTH l − 1)

   [LENGTH_UNZIP]  Theorem

      |- ∀pl.
           (LENGTH (FST (UNZIP pl)) = LENGTH pl) ∧
           (LENGTH (SND (UNZIP pl)) = LENGTH pl)

   [LENGTH_ZIP]  Theorem

      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ⇒
           (LENGTH (ZIP (l1,l2)) = LENGTH l1) ∧
           (LENGTH (ZIP (l1,l2)) = LENGTH l2)

   [LENGTH_dropWhile_LESS_EQ]  Theorem

      |- ∀P ls. LENGTH (dropWhile P ls) ≤ LENGTH ls

   [LENGTH_o_REVERSE]  Theorem

      |- (LENGTH o REVERSE = LENGTH) ∧ (LENGTH o REVERSE o f = LENGTH o f)

   [LEN_LENGTH_LEM]  Theorem

      |- ∀L n. LEN L n = LENGTH L + n

   [LIST_APPLY_o]  Theorem

      |- [$o] <*> fs <*> gs <*> xs = fs <*> (gs <*> xs)

   [LIST_BIND_APPEND]  Theorem

      |- LIST_BIND (l1 ++ l2) f = LIST_BIND l1 f ++ LIST_BIND l2 f

   [LIST_BIND_ID]  Theorem

      |- (LIST_BIND l (λx. x) = FLAT l) ∧ (LIST_BIND l I = FLAT l)

   [LIST_BIND_LIST_BIND]  Theorem

      |- LIST_BIND (LIST_BIND l g) f =
         LIST_BIND l (combin$C LIST_BIND f o g)

   [LIST_BIND_MAP]  Theorem

      |- LIST_BIND (MAP f l) g = LIST_BIND l (g o f)

   [LIST_BIND_THM]  Theorem

      |- (LIST_BIND [] f = []) ∧
         (LIST_BIND (h::t) f = f h ++ LIST_BIND t f)

   [LIST_EQ]  Theorem

      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ∧
           (∀x. x < LENGTH l1 ⇒ (EL x l1 = EL x l2)) ⇒
           (l1 = l2)

   [LIST_EQ_MAP_PAIR]  Theorem

      |- ∀l1 l2.
           (MAP FST l1 = MAP FST l2) ∧ (MAP SND l1 = MAP SND l2) ⇒
           (l1 = l2)

   [LIST_EQ_REWRITE]  Theorem

      |- ∀l1 l2.
           (l1 = l2) ⇔
           (LENGTH l1 = LENGTH l2) ∧
           ∀x. x < LENGTH l1 ⇒ (EL x l1 = EL x l2)

   [LIST_NOT_EQ]  Theorem

      |- ∀l1 l2. l1 ≠ l2 ⇒ ∀h1 h2. h1::l1 ≠ h2::l2

   [LIST_REL_CONJ]  Theorem

      |- LIST_REL (λa b. P a b ∧ Q a b) l1 l2 ⇔
         LIST_REL (λa b. P a b) l1 l2 ∧ LIST_REL (λa b. Q a b) l1 l2

   [LIST_REL_CONS1]  Theorem

      |- LIST_REL R (h::t) xs ⇔
         ∃h' t'. (xs = h'::t') ∧ R h h' ∧ LIST_REL R t t'

   [LIST_REL_CONS2]  Theorem

      |- LIST_REL R xs (h::t) ⇔
         ∃h' t'. (xs = h'::t') ∧ R h' h ∧ LIST_REL R t' t

   [LIST_REL_EL_EQN]  Theorem

      |- ∀R l1 l2.
           LIST_REL R l1 l2 ⇔
           (LENGTH l1 = LENGTH l2) ∧
           ∀n. n < LENGTH l1 ⇒ R (EL n l1) (EL n l2)

   [LIST_REL_EVERY_ZIP]  Theorem

      |- ∀R l1 l2.
           LIST_REL R l1 l2 ⇔
           (LENGTH l1 = LENGTH l2) ∧ EVERY (UNCURRY R) (ZIP (l1,l2))

   [LIST_REL_LENGTH]  Theorem

      |- ∀x y. LIST_REL R x y ⇒ (LENGTH x = LENGTH y)

   [LIST_REL_MAP1]  Theorem

      |- LIST_REL R (MAP f l1) l2 ⇔ LIST_REL (R o f) l1 l2

   [LIST_REL_MAP2]  Theorem

      |- LIST_REL (λa b. R a b) l1 (MAP f l2) ⇔
         LIST_REL (λa b. R a (f b)) l1 l2

   [LIST_REL_NIL]  Theorem

      |- (LIST_REL R [] x ⇔ (x = [])) ∧ (LIST_REL R [] y ⇔ (y = []))

   [LIST_REL_cases]  Theorem

      |- ∀R a0 a1.
           LIST_REL R a0 a1 ⇔
           (a0 = []) ∧ (a1 = []) ∨
           ∃h1 h2 t1 t2.
             (a0 = h1::t1) ∧ (a1 = h2::t2) ∧ R h1 h2 ∧ LIST_REL R t1 t2

   [LIST_REL_def]  Theorem

      |- (LIST_REL R [] [] ⇔ T) ∧ (LIST_REL R (a::as) [] ⇔ F) ∧
         (LIST_REL R [] (b::bs) ⇔ F) ∧
         (LIST_REL R (a::as) (b::bs) ⇔ R a b ∧ LIST_REL R as bs)

   [LIST_REL_ind]  Theorem

      |- ∀R LIST_REL'.
           LIST_REL' [] [] ∧
           (∀h1 h2 t1 t2.
              R h1 h2 ∧ LIST_REL' t1 t2 ⇒ LIST_REL' (h1::t1) (h2::t2)) ⇒
           ∀a0 a1. LIST_REL R a0 a1 ⇒ LIST_REL' a0 a1

   [LIST_REL_mono]  Theorem

      |- (∀x y. R1 x y ⇒ R2 x y) ⇒ LIST_REL R1 l1 l2 ⇒ LIST_REL R2 l1 l2

   [LIST_REL_rules]  Theorem

      |- ∀R.
           LIST_REL R [] [] ∧
           ∀h1 h2 t1 t2.
             R h1 h2 ∧ LIST_REL R t1 t2 ⇒ LIST_REL R (h1::t1) (h2::t2)

   [LIST_REL_strongind]  Theorem

      |- ∀R LIST_REL'.
           LIST_REL' [] [] ∧
           (∀h1 h2 t1 t2.
              R h1 h2 ∧ LIST_REL R t1 t2 ∧ LIST_REL' t1 t2 ⇒
              LIST_REL' (h1::t1) (h2::t2)) ⇒
           ∀a0 a1. LIST_REL R a0 a1 ⇒ LIST_REL' a0 a1

   [LIST_REL_trans]  Theorem

      |- ∀l1 l2 l3.
           (∀n.
              n < LENGTH l1 ∧ R (EL n l1) (EL n l2) ∧
              R (EL n l2) (EL n l3) ⇒
              R (EL n l1) (EL n l3)) ∧ LIST_REL R l1 l2 ∧
           LIST_REL R l2 l3 ⇒
           LIST_REL R l1 l3

   [LIST_TO_SET]  Theorem

      |- (set [] = ∅) ∧ (set (h::t) = h INSERT set t)

   [LIST_TO_SET_APPEND]  Theorem

      |- ∀l1 l2. set (l1 ++ l2) = set l1 ∪ set l2

   [LIST_TO_SET_EQ_EMPTY]  Theorem

      |- ((set l = ∅) ⇔ (l = [])) ∧ ((∅ = set l) ⇔ (l = []))

   [LIST_TO_SET_FILTER]  Theorem

      |- set (FILTER P l) = {x | P x} ∩ set l

   [LIST_TO_SET_FLAT]  Theorem

      |- ∀ls. set (FLAT ls) = BIGUNION (set (MAP set ls))

   [LIST_TO_SET_GENLIST]  Theorem

      |- ∀f n. set (GENLIST f n) = IMAGE f (count n)

   [LIST_TO_SET_MAP]  Theorem

      |- ∀f l. set (MAP f l) = IMAGE f (set l)

   [LIST_TO_SET_REVERSE]  Theorem

      |- ∀ls. set (REVERSE ls) = set ls

   [LIST_TO_SET_SNOC]  Theorem

      |- set (SNOC x ls) = x INSERT set ls

   [LIST_TO_SET_THM]  Theorem

      |- (set [] = ∅) ∧ (set (h::t) = h INSERT set t)

   [LLEX_NIL2]  Theorem

      |- ¬LLEX R l []

   [LLEX_THM]  Theorem

      |- (¬LLEX R [] [] ∧ ¬LLEX R (h1::t1) []) ∧ LLEX R [] (h2::t2) ∧
         (LLEX R (h1::t1) (h2::t2) ⇔ R h1 h2 ∨ (h1 = h2) ∧ LLEX R t1 t2)

   [LLEX_not_WF]  Theorem

      |- (∃a b. R a b) ⇒ ¬WF (LLEX R)

   [LLEX_total]  Theorem

      |- total (RC R) ⇒ total (RC (LLEX R))

   [LLEX_transitive]  Theorem

      |- transitive R ⇒ transitive (LLEX R)

   [LRC_MEM]  Theorem

      |- LRC R ls x y ∧ MEM e ls ⇒ ∃z t. R e z ∧ LRC R t z y

   [LRC_MEM_right]  Theorem

      |- LRC R (h::t) x y ∧ MEM e t ⇒ ∃z p. R z e ∧ LRC R p x z

   [LUPDATE_LENGTH]  Theorem

      |- ∀xs x y ys. LUPDATE x (LENGTH xs) (xs ++ y::ys) = xs ++ x::ys

   [LUPDATE_MAP]  Theorem

      |- ∀x n l f. MAP f (LUPDATE x n l) = LUPDATE (f x) n (MAP f l)

   [LUPDATE_SEM]  Theorem

      |- (∀e n l. LENGTH (LUPDATE e n l) = LENGTH l) ∧
         ∀e n l p.
           p < LENGTH l ⇒
           (EL p (LUPDATE e n l) = if p = n then e else EL p l)

   [LUPDATE_SNOC]  Theorem

      |- ∀ys k x y.
           LUPDATE x k (SNOC y ys) =
           if k = LENGTH ys then SNOC x ys else SNOC y (LUPDATE x k ys)

   [LUPDATE_compute]  Theorem

      |- (∀e n. LUPDATE e n [] = []) ∧
         (∀e x l. LUPDATE e 0 (x::l) = e::l) ∧
         (∀e n x l.
            LUPDATE e (NUMERAL (BIT1 n)) (x::l) =
            x::LUPDATE e (NUMERAL (BIT1 n) − 1) l) ∧
         ∀e n x l.
           LUPDATE e (NUMERAL (BIT2 n)) (x::l) =
           x::LUPDATE e (NUMERAL (BIT1 n)) l

   [MAP2]  Theorem

      |- (∀f. MAP2 f [] [] = []) ∧
         ∀f h1 t1 h2 t2. MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2

   [MAP2_CONG]  Theorem

      |- ∀l1 l1' l2 l2' f f'.
           (l1 = l1') ∧ (l2 = l2') ∧
           (∀x y. MEM x l1' ∧ MEM y l2' ⇒ (f x y = f' x y)) ⇒
           (MAP2 f l1 l2 = MAP2 f' l1' l2')

   [MAP2_MAP]  Theorem

      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ⇒
           ∀f. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))

   [MAP2_ZIP]  Theorem

      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ⇒
           ∀f. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))

   [MAP2_def]  Theorem

      |- (∀t2 t1 h2 h1 f.
            MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2) ∧
         (∀y f. MAP2 f [] y = []) ∧ ∀v5 v4 f. MAP2 f (v4::v5) [] = []

   [MAP2_ind]  Theorem

      |- ∀P.
           (∀f h1 t1 h2 t2. P f t1 t2 ⇒ P f (h1::t1) (h2::t2)) ∧
           (∀f y. P f [] y) ∧ (∀f v4 v5. P f (v4::v5) []) ⇒
           ∀v v1 v2. P v v1 v2

   [MAP_APPEND]  Theorem

      |- ∀f l1 l2. MAP f (l1 ++ l2) = MAP f l1 ++ MAP f l2

   [MAP_CONG]  Theorem

      |- ∀l1 l2 f f'.
           (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (f x = f' x)) ⇒
           (MAP f l1 = MAP f' l2)

   [MAP_EQ_EVERY2]  Theorem

      |- ∀f1 f2 l1 l2.
           (MAP f1 l1 = MAP f2 l2) ⇔
           (LENGTH l1 = LENGTH l2) ∧ LIST_REL (λx y. f1 x = f2 y) l1 l2

   [MAP_EQ_NIL]  Theorem

      |- ∀l f. ((MAP f l = []) ⇔ (l = [])) ∧ (([] = MAP f l) ⇔ (l = []))

   [MAP_EQ_f]  Theorem

      |- ∀f1 f2 l. (MAP f1 l = MAP f2 l) ⇔ ∀e. MEM e l ⇒ (f1 e = f2 e)

   [MAP_FLAT]  Theorem

      |- MAP f (FLAT l) = FLAT (MAP (MAP f) l)

   [MAP_GENLIST]  Theorem

      |- ∀f g n. MAP f (GENLIST g n) = GENLIST (f o g) n

   [MAP_ID]  Theorem

      |- (MAP (λx. x) l = l) ∧ (MAP I l = l)

   [MAP_LIST_BIND]  Theorem

      |- MAP f (LIST_BIND l g) = LIST_BIND l (MAP f o g)

   [MAP_MAP_o]  Theorem

      |- ∀f g l. MAP f (MAP g l) = MAP (f o g) l

   [MAP_SNOC]  Theorem

      |- ∀f x l. MAP f (SNOC x l) = SNOC (f x) (MAP f l)

   [MAP_TL]  Theorem

      |- ∀l f. ¬NULL l ⇒ (MAP f (TL l) = TL (MAP f l))

   [MAP_ZIP]  Theorem

      |- (LENGTH l1 = LENGTH l2) ⇒
         (MAP FST (ZIP (l1,l2)) = l1) ∧ (MAP SND (ZIP (l1,l2)) = l2) ∧
         (MAP (f o FST) (ZIP (l1,l2)) = MAP f l1) ∧
         (MAP (g o SND) (ZIP (l1,l2)) = MAP g l2)

   [MAP_ZIP_SAME]  Theorem

      |- ∀ls f. MAP f (ZIP (ls,ls)) = MAP (λx. f (x,x)) ls

   [MAP_o]  Theorem

      |- ∀f g. MAP (f o g) = MAP f o MAP g

   [MEM]  Theorem

      |- (∀x. MEM x [] ⇔ F) ∧ ∀x h t. MEM x (h::t) ⇔ (x = h) ∨ MEM x t

   [MEM_APPEND]  Theorem

      |- ∀e l1 l2. MEM e (l1 ++ l2) ⇔ MEM e l1 ∨ MEM e l2

   [MEM_APPEND_lemma]  Theorem

      |- ∀a b c d x.
           (a ++ [x] ++ b = c ++ [x] ++ d) ∧ ¬MEM x b ∧ ¬MEM x a ⇒
           (a = c) ∧ (b = d)

   [MEM_DROP]  Theorem

      |- ∀x ls n.
           MEM x (DROP n ls) ⇔
           n < LENGTH ls ∧ (x = EL n ls) ∨ MEM x (DROP (SUC n) ls)

   [MEM_EL]  Theorem

      |- ∀l x. MEM x l ⇔ ∃n. n < LENGTH l ∧ (x = EL n l)

   [MEM_FILTER]  Theorem

      |- ∀P L x. MEM x (FILTER P L) ⇔ P x ∧ MEM x L

   [MEM_FLAT]  Theorem

      |- ∀x L. MEM x (FLAT L) ⇔ ∃l. MEM l L ∧ MEM x l

   [MEM_GENLIST]  Theorem

      |- MEM x (GENLIST f n) ⇔ ∃m. m < n ∧ (x = f m)

   [MEM_LUPDATE]  Theorem

      |- ∀l x y i.
           MEM x (LUPDATE y i l) ⇔
           i < LENGTH l ∧ (x = y) ∨ ∃j. j < LENGTH l ∧ i ≠ j ∧ (EL j l = x)

   [MEM_LUPDATE_E]  Theorem

      |- ∀l x y i. MEM x (LUPDATE y i l) ⇒ (x = y) ∨ MEM x l

   [MEM_MAP]  Theorem

      |- ∀l f x. MEM x (MAP f l) ⇔ ∃y. (x = f y) ∧ MEM y l

   [MEM_REVERSE]  Theorem

      |- ∀l x. MEM x (REVERSE l) ⇔ MEM x l

   [MEM_SET_TO_LIST]  Theorem

      |- ∀s. FINITE s ⇒ ∀x. MEM x (SET_TO_LIST s) ⇔ x ∈ s

   [MEM_SNOC]  Theorem

      |- ∀y x l. MEM y (SNOC x l) ⇔ (y = x) ∨ MEM y l

   [MEM_SPLIT]  Theorem

      |- ∀x l. MEM x l ⇔ ∃l1 l2. l = l1 ++ x::l2

   [MEM_SPLIT_APPEND_first]  Theorem

      |- MEM e l ⇔ ∃pfx sfx. (l = pfx ++ [e] ++ sfx) ∧ ¬MEM e pfx

   [MEM_SPLIT_APPEND_last]  Theorem

      |- MEM e l ⇔ ∃pfx sfx. (l = pfx ++ [e] ++ sfx) ∧ ¬MEM e sfx

   [MEM_ZIP]  Theorem

      |- ∀l1 l2 p.
           (LENGTH l1 = LENGTH l2) ⇒
           (MEM p (ZIP (l1,l2)) ⇔
            ∃n. n < LENGTH l1 ∧ (p = (EL n l1,EL n l2)))

   [MEM_ZIP_MEM_MAP]  Theorem

      |- (LENGTH (FST ps) = LENGTH (SND ps)) ∧ MEM p (ZIP ps) ⇒
         MEM (FST p) (FST ps) ∧ MEM (SND p) (SND ps)

   [MEM_dropWhile_IMP]  Theorem

      |- ∀P ls x. MEM x (dropWhile P ls) ⇒ MEM x ls

   [MONO_EVERY]  Theorem

      |- (∀x. P x ⇒ Q x) ⇒ EVERY P l ⇒ EVERY Q l

   [MONO_EXISTS]  Theorem

      |- (∀x. P x ⇒ Q x) ⇒ EXISTS P l ⇒ EXISTS Q l

   [NOT_CONS_NIL]  Theorem

      |- ∀a1 a0. a0::a1 ≠ []

   [NOT_EQ_LIST]  Theorem

      |- ∀h1 h2. h1 ≠ h2 ⇒ ∀l1 l2. h1::l1 ≠ h2::l2

   [NOT_EVERY]  Theorem

      |- ∀P l. ¬EVERY P l ⇔ EXISTS ($~ o P) l

   [NOT_EXISTS]  Theorem

      |- ∀P l. ¬EXISTS P l ⇔ EVERY ($~ o P) l

   [NOT_NIL_CONS]  Theorem

      |- ∀a1 a0. [] ≠ a0::a1

   [NOT_NULL_MEM]  Theorem

      |- ∀l. ¬NULL l ⇔ ∃e. MEM e l

   [NRC_LRC]  Theorem

      |- NRC R n x y ⇔ ∃ls. LRC R ls x y ∧ (LENGTH ls = n)

   [NULL]  Theorem

      |- NULL [] ∧ ∀h t. ¬NULL (h::t)

   [NULL_EQ]  Theorem

      |- ∀l. NULL l ⇔ (l = [])

   [NULL_FILTER]  Theorem

      |- ∀P ls. NULL (FILTER P ls) ⇔ ∀x. MEM x ls ⇒ ¬P x

   [NULL_GENLIST]  Theorem

      |- ∀n f. NULL (GENLIST f n) ⇔ (n = 0)

   [NULL_LENGTH]  Theorem

      |- ∀l. NULL l ⇔ (LENGTH l = 0)

   [REVERSE_11]  Theorem

      |- ∀l1 l2. (REVERSE l1 = REVERSE l2) ⇔ (l1 = l2)

   [REVERSE_APPEND]  Theorem

      |- ∀l1 l2. REVERSE (l1 ++ l2) = REVERSE l2 ++ REVERSE l1

   [REVERSE_EQ_NIL]  Theorem

      |- (REVERSE l = []) ⇔ (l = [])

   [REVERSE_EQ_SING]  Theorem

      |- (REVERSE l = [e]) ⇔ (l = [e])

   [REVERSE_GENLIST]  Theorem

      |- REVERSE (GENLIST f n) = GENLIST (λm. f (PRE n − m)) n

   [REVERSE_REV]  Theorem

      |- ∀L. REVERSE L = REV L []

   [REVERSE_REVERSE]  Theorem

      |- ∀l. REVERSE (REVERSE l) = l

   [REVERSE_SNOC]  Theorem

      |- ∀x l. REVERSE (SNOC x l) = x::REVERSE l

   [REVERSE_SNOC_DEF]  Theorem

      |- (REVERSE [] = []) ∧ ∀x l. REVERSE (x::l) = SNOC x (REVERSE l)

   [REVERSE_o_REVERSE]  Theorem

      |- REVERSE o REVERSE o f = f

   [REV_REVERSE_LEM]  Theorem

      |- ∀L1 L2. REV L1 L2 = REVERSE L1 ++ L2

   [SET_TO_LIST_CARD]  Theorem

      |- ∀s. FINITE s ⇒ (LENGTH (SET_TO_LIST s) = CARD s)

   [SET_TO_LIST_EMPTY]  Theorem

      |- SET_TO_LIST ∅ = []

   [SET_TO_LIST_IND]  Theorem

      |- ∀P. (∀s. (FINITE s ∧ s ≠ ∅ ⇒ P (REST s)) ⇒ P s) ⇒ ∀v. P v

   [SET_TO_LIST_INV]  Theorem

      |- ∀s. FINITE s ⇒ (set (SET_TO_LIST s) = s)

   [SET_TO_LIST_IN_MEM]  Theorem

      |- ∀s. FINITE s ⇒ ∀x. x ∈ s ⇔ MEM x (SET_TO_LIST s)

   [SET_TO_LIST_SING]  Theorem

      |- SET_TO_LIST {x} = [x]

   [SET_TO_LIST_THM]  Theorem

      |- FINITE s ⇒
         (SET_TO_LIST s =
          if s = ∅ then [] else CHOICE s::SET_TO_LIST (REST s))

   [SINGL_APPLY_MAP]  Theorem

      |- [f] <*> l = MAP f l

   [SINGL_APPLY_PERMUTE]  Theorem

      |- fs <*> [x] = [(λf. f x)] <*> fs

   [SINGL_LIST_APPLY_L]  Theorem

      |- LIST_BIND [x] f = f x

   [SINGL_LIST_APPLY_R]  Theorem

      |- LIST_BIND l (λx. [x]) = l

   [SINGL_SINGL_APPLY]  Theorem

      |- [f] <*> [x] = [f x]

   [SNOC_11]  Theorem

      |- ∀x y a b. (SNOC x y = SNOC a b) ⇔ (x = a) ∧ (y = b)

   [SNOC_APPEND]  Theorem

      |- ∀x l. SNOC x l = l ++ [x]

   [SNOC_Axiom]  Theorem

      |- ∀e f. ∃fn. (fn [] = e) ∧ ∀x l. fn (SNOC x l) = f x l (fn l)

   [SNOC_CASES]  Theorem

      |- ∀ll. (ll = []) ∨ ∃x l. ll = SNOC x l

   [SNOC_INDUCT]  Theorem

      |- ∀P. P [] ∧ (∀l. P l ⇒ ∀x. P (SNOC x l)) ⇒ ∀l. P l

   [SUM_ACC_SUM_LEM]  Theorem

      |- ∀L n. SUM_ACC L n = SUM L + n

   [SUM_APPEND]  Theorem

      |- ∀l1 l2. SUM (l1 ++ l2) = SUM l1 + SUM l2

   [SUM_IMAGE_LIST_TO_SET_upper_bound]  Theorem

      |- ∀ls. ∑ f (set ls) ≤ SUM (MAP f ls)

   [SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST]  Theorem

      |- FINITE s ⇒ (∑ f s = SUM (MAP f (SET_TO_LIST s)))

   [SUM_MAP_FOLDL]  Theorem

      |- ∀ls. SUM (MAP f ls) = FOLDL (λa e. a + f e) 0 ls

   [SUM_MAP_MEM_bound]  Theorem

      |- ∀f x ls. MEM x ls ⇒ f x ≤ SUM (MAP f ls)

   [SUM_MAP_PLUS]  Theorem

      |- ∀f g ls.
           SUM (MAP (λx. f x + g x) ls) = SUM (MAP f ls) + SUM (MAP g ls)

   [SUM_MAP_PLUS_ZIP]  Theorem

      |- ∀ls1 ls2.
           (LENGTH ls1 = LENGTH ls2) ∧ (∀x y. f (x,y) = g x + h y) ⇒
           (SUM (MAP f (ZIP (ls1,ls2))) =
            SUM (MAP g ls1) + SUM (MAP h ls2))

   [SUM_SNOC]  Theorem

      |- ∀x l. SUM (SNOC x l) = SUM l + x

   [SUM_SUM_ACC]  Theorem

      |- ∀L. SUM L = SUM_ACC L 0

   [SUM_eq_0]  Theorem

      |- ∀ls. (SUM ls = 0) ⇔ ∀x. MEM x ls ⇒ (x = 0)

   [SWAP_REVERSE]  Theorem

      |- ∀l1 l2. (l1 = REVERSE l2) ⇔ (l2 = REVERSE l1)

   [SWAP_REVERSE_SYM]  Theorem

      |- ∀l1 l2. (REVERSE l1 = l2) ⇔ (l1 = REVERSE l2)

   [TAKE_0]  Theorem

      |- TAKE 0 l = []

   [TAKE_APPEND1]  Theorem

      |- ∀n. n ≤ LENGTH l1 ⇒ (TAKE n (l1 ++ l2) = TAKE n l1)

   [TAKE_APPEND2]  Theorem

      |- ∀n.
           LENGTH l1 < n ⇒
           (TAKE n (l1 ++ l2) = l1 ++ TAKE (n − LENGTH l1) l2)

   [TAKE_DROP]  Theorem

      |- ∀n l. TAKE n l ++ DROP n l = l

   [TAKE_LENGTH_ID]  Theorem

      |- ∀l. TAKE (LENGTH l) l = l

   [TAKE_LENGTH_ID_rwt]  Theorem

      |- ∀l m. (m = LENGTH l) ⇒ (TAKE m l = l)

   [TAKE_LENGTH_TOO_LONG]  Theorem

      |- ∀l n. LENGTH l ≤ n ⇒ (TAKE n l = l)

   [TAKE_SUM]  Theorem

      |- ∀n m l.
           n + m ≤ LENGTH l ⇒
           (TAKE (n + m) l = TAKE n l ++ TAKE m (DROP n l))

   [TAKE_compute]  Theorem

      |- (∀l. TAKE 0 l = []) ∧ (∀n. TAKE (NUMERAL (BIT1 n)) [] = []) ∧
         (∀n. TAKE (NUMERAL (BIT2 n)) [] = []) ∧
         (∀n h t.
            TAKE (NUMERAL (BIT1 n)) (h::t) =
            h::TAKE (NUMERAL (BIT1 n) − 1) t) ∧
         ∀n h t.
           TAKE (NUMERAL (BIT2 n)) (h::t) = h::TAKE (NUMERAL (BIT1 n)) t

   [TAKE_splitAtPki]  Theorem

      |- TAKE n l = splitAtPki (K o $= n) K l

   [TL_GENLIST]  Theorem

      |- ∀f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n

   [UNION_APPEND]  Theorem

      |- ∀l1 l2. set l1 ∪ set l2 = set (l1 ++ l2)

   [UNZIP_MAP]  Theorem

      |- ∀L. UNZIP L = (MAP FST L,MAP SND L)

   [UNZIP_THM]  Theorem

      |- (UNZIP [] = ([],[])) ∧
         (UNZIP ((x,y)::t) = (let (L1,L2) = UNZIP t in (x::L1,y::L2)))

   [UNZIP_ZIP]  Theorem

      |- ∀l1 l2. (LENGTH l1 = LENGTH l2) ⇒ (UNZIP (ZIP (l1,l2)) = (l1,l2))

   [WF_LIST_PRED]  Theorem

      |- WF (λL1 L2. ∃h. L2 = h::L1)

   [ZIP_DROP]  Theorem

      |- ∀a b n.
           n ≤ LENGTH a ∧ (LENGTH a = LENGTH b) ⇒
           (ZIP (DROP n a,DROP n b) = DROP n (ZIP (a,b)))

   [ZIP_GENLIST]  Theorem

      |- ∀l f n.
           (LENGTH l = n) ⇒
           (ZIP (l,GENLIST f n) = GENLIST (λx. (EL x l,f x)) n)

   [ZIP_MAP]  Theorem

      |- ∀l1 l2 f1 f2.
           (LENGTH l1 = LENGTH l2) ⇒
           (ZIP (MAP f1 l1,l2) =
            MAP (λp. (f1 (FST p),SND p)) (ZIP (l1,l2))) ∧
           (ZIP (l1,MAP f2 l2) =
            MAP (λp. (FST p,f2 (SND p))) (ZIP (l1,l2)))

   [ZIP_UNZIP]  Theorem

      |- ∀l. ZIP (UNZIP l) = l

   [all_distinct_nub]  Theorem

      |- ∀l. ALL_DISTINCT (nub l)

   [datatype_list]  Theorem

      |- DATATYPE (list [] CONS)

   [dropWhile_APPEND_EVERY]  Theorem

      |- ∀P l1 l2. EVERY P l1 ⇒ (dropWhile P (l1 ++ l2) = dropWhile P l2)

   [dropWhile_APPEND_EXISTS]  Theorem

      |- ∀P l1 l2.
           EXISTS ($~ o P) l1 ⇒
           (dropWhile P (l1 ++ l2) = dropWhile P l1 ++ l2)

   [dropWhile_eq_nil]  Theorem

      |- ∀P ls. (dropWhile P ls = []) ⇔ EVERY P ls

   [dropWhile_splitAtPki]  Theorem

      |- ∀P. dropWhile P = splitAtPki (combin$C (K o $~ o P)) (K I)

   [el_append3]  Theorem

      |- ∀l1 x l2. EL (LENGTH l1) (l1 ++ [x] ++ l2) = x

   [every_zip_fst]  Theorem

      |- ∀l1 l2 P.
           (LENGTH l1 = LENGTH l2) ⇒
           (EVERY (λx. P (FST x)) (ZIP (l1,l2)) ⇔ EVERY P l1)

   [every_zip_snd]  Theorem

      |- ∀l1 l2 P.
           (LENGTH l1 = LENGTH l2) ⇒
           (EVERY (λx. P (SND x)) (ZIP (l1,l2)) ⇔ EVERY P l2)

   [exists_list_GENLIST]  Theorem

      |- (∃ls. P ls) ⇔ ∃n f. P (GENLIST f n)

   [isPREFIX_THM]  Theorem

      |- ([] ≼ l ⇔ T) ∧ (h::t ≼ [] ⇔ F) ∧
         (h1::t1 ≼ h2::t2 ⇔ (h1 = h2) ∧ t1 ≼ t2)

   [length_nub_append]  Theorem

      |- ∀l1 l2.
           LENGTH (nub (l1 ++ l2)) =
           LENGTH (nub l1) + LENGTH (nub (FILTER (λx. ¬MEM x l1) l2))

   [list_11]  Theorem

      |- ∀a0 a1 a0' a1'. (a0::a1 = a0'::a1') ⇔ (a0 = a0') ∧ (a1 = a1')

   [list_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (fn [] = f0) ∧ ∀a0 a1. fn (a0::a1) = f1 a0 a1 (fn a1)

   [list_Axiom_old]  Theorem

      |- ∀x f. ∃!fn1. (fn1 [] = x) ∧ ∀h t. fn1 (h::t) = f (fn1 t) h t

   [list_CASES]  Theorem

      |- ∀l. (l = []) ∨ ∃h t. l = h::t

   [list_INDUCT]  Theorem

      |- ∀P. P [] ∧ (∀t. P t ⇒ ∀h. P (h::t)) ⇒ ∀l. P l

   [list_case_compute]  Theorem

      |- ∀l. list_CASE l b f = if NULL l then b else f (HD l) (TL l)

   [list_case_cong]  Theorem

      |- ∀M M' v f.
           (M = M') ∧ ((M' = []) ⇒ (v = v')) ∧
           (∀a0 a1. (M' = a0::a1) ⇒ (f a0 a1 = f' a0 a1)) ⇒
           (list_CASE M v f = list_CASE M' v' f')

   [list_distinct]  Theorem

      |- ∀a1 a0. [] ≠ a0::a1

   [list_induction]  Theorem

      |- ∀P. P [] ∧ (∀t. P t ⇒ ∀h. P (h::t)) ⇒ ∀l. P l

   [list_nchotomy]  Theorem

      |- ∀l. (l = []) ∨ ∃h t. l = h::t

   [list_size_cong]  Theorem

      |- ∀M N f f'.
           (M = N) ∧ (∀x. MEM x N ⇒ (f x = f' x)) ⇒
           (list_size f M = list_size f' N)

   [list_to_set_diff]  Theorem

      |- ∀l1 l2. set l2 DIFF set l1 = set (FILTER (λx. ¬MEM x l1) l2)

   [lupdate_append]  Theorem

      |- ∀x n l1 l2.
           n < LENGTH l1 ⇒ (LUPDATE x n (l1 ++ l2) = LUPDATE x n l1 ++ l2)

   [lupdate_append2]  Theorem

      |- ∀v l1 x l2 l3.
           LUPDATE v (LENGTH l1) (l1 ++ [x] ++ l2) = l1 ++ [v] ++ l2

   [mem_exists_set]  Theorem

      |- ∀x y l. MEM (x,y) l ⇒ ∃z. (x = FST z) ∧ MEM z l

   [nub_append]  Theorem

      |- ∀l1 l2. nub (l1 ++ l2) = nub (FILTER (λx. ¬MEM x l2) l1) ++ nub l2

   [nub_set]  Theorem

      |- ∀l. set (nub l) = set l

   [splitAtPki_APPEND]  Theorem

      |- ∀l1 l2 P k.
           EVERYi (λi. $~ o P i) l1 ∧
           (0 < LENGTH l2 ⇒ P (LENGTH l1) (HD l2)) ⇒
           (splitAtPki P k (l1 ++ l2) = k l1 l2)

   [splitAtPki_EQN]  Theorem

      |- splitAtPki P k l =
         case OLEAST i. i < LENGTH l ∧ P i (EL i l) of
           NONE => k l []
         | SOME i => k (TAKE i l) (DROP i l)


*)
end
