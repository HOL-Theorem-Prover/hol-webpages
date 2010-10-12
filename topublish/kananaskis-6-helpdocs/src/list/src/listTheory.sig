signature listTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ALL_DISTINCT : thm
    val APPEND : thm
    val DROP_def : thm
    val EL : thm
    val EVERY_DEF : thm
    val EXISTS_DEF : thm
    val FILTER : thm
    val FLAT : thm
    val FOLDL : thm
    val FOLDR : thm
    val FRONT_DEF : thm
    val HD : thm
    val LAST_DEF : thm
    val LENGTH : thm
    val LEN_DEF : thm
    val LIST_TO_SET : thm
    val LRC_def : thm
    val MAP : thm
    val MAP2 : thm
    val MEM : thm
    val NULL_DEF : thm
    val REVERSE_DEF : thm
    val REV_DEF : thm
    val SET_TO_LIST_primitive : thm
    val SNOC : thm
    val SUM : thm
    val TAKE_def : thm
    val TL : thm
    val UNZIP : thm
    val ZIP : thm
    val isPREFIX : thm
    val listRel : thm
    val list_TY_DEF : thm
    val list_case_def : thm
    val list_repfns : thm
    val list_size_def : thm
  
  (*  Theorems  *)
    val ALL_DISTINCT_APPEND : thm
    val ALL_DISTINCT_CARD_LIST_TO_SET : thm
    val ALL_DISTINCT_EL_IMP : thm
    val ALL_DISTINCT_FILTER : thm
    val ALL_DISTINCT_REVERSE : thm
    val ALL_DISTINCT_SET_TO_LIST : thm
    val ALL_DISTINCT_SING : thm
    val ALL_DISTINCT_ZIP : thm
    val ALL_DISTINCT_ZIP_SWAP : thm
    val APPEND_11 : thm
    val APPEND_11_LENGTH : thm
    val APPEND_ASSOC : thm
    val APPEND_EQ_SELF : thm
    val APPEND_EQ_SING : thm
    val APPEND_FRONT_LAST : thm
    val APPEND_LENGTH_EQ : thm
    val APPEND_NIL : thm
    val APPEND_eq_NIL : thm
    val CARD_LIST_TO_SET : thm
    val CONS : thm
    val CONS_11 : thm
    val CONS_ACYCLIC : thm
    val DROP_0 : thm
    val EL_ALL_DISTINCT_EL_EQ : thm
    val EL_ZIP : thm
    val EL_compute : thm
    val EL_restricted : thm
    val EL_simp : thm
    val EL_simp_restricted : thm
    val EQ_LIST : thm
    val EVERY_APPEND : thm
    val EVERY_CONG : thm
    val EVERY_CONJ : thm
    val EVERY_EL : thm
    val EVERY_FILTER : thm
    val EVERY_FILTER_IMP : thm
    val EVERY_MAP : thm
    val EVERY_MEM : thm
    val EVERY_MONOTONIC : thm
    val EVERY_NOT_EXISTS : thm
    val EVERY_SIMP : thm
    val EXISTS_APPEND : thm
    val EXISTS_CONG : thm
    val EXISTS_MAP : thm
    val EXISTS_MEM : thm
    val EXISTS_NOT_EVERY : thm
    val EXISTS_SIMP : thm
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
    val FOLDL_CONG : thm
    val FOLDL_EQ_FOLDR : thm
    val FOLDR_CONG : thm
    val FORALL_LIST : thm
    val FRONT_CONS : thm
    val FRONT_CONS_EQ_NIL : thm
    val FRONT_SNOC : thm
    val INFINITE_LIST_UNIV : thm
    val IN_LIST_TO_SET : thm
    val LAST_APPEND_CONS : thm
    val LAST_CONS : thm
    val LAST_CONS_cond : thm
    val LAST_SNOC : thm
    val LENGTH_APPEND : thm
    val LENGTH_CONS : thm
    val LENGTH_DROP : thm
    val LENGTH_EQ_CONS : thm
    val LENGTH_EQ_NIL : thm
    val LENGTH_EQ_NUM : thm
    val LENGTH_EQ_NUM_compute : thm
    val LENGTH_EQ_SUM : thm
    val LENGTH_FRONT_CONS : thm
    val LENGTH_LEN : thm
    val LENGTH_MAP : thm
    val LENGTH_NIL : thm
    val LENGTH_NIL_SYM : thm
    val LENGTH_REVERSE : thm
    val LENGTH_SNOC : thm
    val LENGTH_TAKE : thm
    val LENGTH_TL : thm
    val LENGTH_UNZIP : thm
    val LENGTH_ZIP : thm
    val LEN_LENGTH_LEM : thm
    val LIST_EQ : thm
    val LIST_EQ_REWRITE : thm
    val LIST_NOT_EQ : thm
    val LIST_TO_SET_APPEND : thm
    val LIST_TO_SET_EQ_EMPTY : thm
    val LIST_TO_SET_MAP : thm
    val LIST_TO_SET_REVERSE : thm
    val LIST_TO_SET_SNOC : thm
    val LIST_TO_SET_THM : thm
    val LRC_MEM : thm
    val LRC_MEM_right : thm
    val MAP2_ZIP : thm
    val MAP_APPEND : thm
    val MAP_CONG : thm
    val MAP_EQ_NIL : thm
    val MAP_ID : thm
    val MAP_ZIP : thm
    val MEM_APPEND : thm
    val MEM_EL : thm
    val MEM_FILTER : thm
    val MEM_FLAT : thm
    val MEM_MAP : thm
    val MEM_REVERSE : thm
    val MEM_SET_TO_LIST : thm
    val MEM_SPLIT : thm
    val MEM_ZIP : thm
    val MONO_EVERY : thm
    val MONO_EXISTS : thm
    val MONO_listRel : thm
    val NOT_CONS_NIL : thm
    val NOT_EQ_LIST : thm
    val NOT_EVERY : thm
    val NOT_EXISTS : thm
    val NOT_NIL_CONS : thm
    val NOT_NULL_MEM : thm
    val NRC_LRC : thm
    val NULL : thm
    val NULL_EQ : thm
    val NULL_LENGTH : thm
    val REVERSE_APPEND : thm
    val REVERSE_EQ_NIL : thm
    val REVERSE_EQ_SING : thm
    val REVERSE_REV : thm
    val REVERSE_REVERSE : thm
    val REV_REVERSE_LEM : thm
    val SET_TO_LIST_CARD : thm
    val SET_TO_LIST_IND : thm
    val SET_TO_LIST_INV : thm
    val SET_TO_LIST_IN_MEM : thm
    val SET_TO_LIST_SING : thm
    val SET_TO_LIST_THM : thm
    val SNOC_APPEND : thm
    val TAKE_0 : thm
    val TAKE_APPEND1 : thm
    val TAKE_APPEND2 : thm
    val TAKE_DROP : thm
    val TAKE_LENGTH_ID : thm
    val UNION_APPEND : thm
    val UNZIP_MAP : thm
    val UNZIP_THM : thm
    val UNZIP_ZIP : thm
    val WF_LIST_PRED : thm
    val ZIP_MAP : thm
    val ZIP_UNZIP : thm
    val datatype_list : thm
    val isPREFIX_THM : thm
    val listRel_CONS : thm
    val listRel_LENGTH : thm
    val listRel_NIL : thm
    val listRel_cases : thm
    val listRel_ind : thm
    val listRel_rules : thm
    val listRel_strong_ind : thm
    val listRel_strongind : thm
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
   
   [EXISTS_DEF]  Definition
      
      |- (∀P. EXISTS P [] ⇔ F) ∧ ∀P h t. EXISTS P (h::t) ⇔ P h ∨ EXISTS P t
   
   [FILTER]  Definition
      
      |- (∀P. FILTER P [] = []) ∧
         ∀P h t. FILTER P (h::t) = if P h then h::FILTER P t else FILTER P t
   
   [FLAT]  Definition
      
      |- (FLAT [] = []) ∧ ∀h t. FLAT (h::t) = h ++ FLAT t
   
   [FOLDL]  Definition
      
      |- (∀f e. FOLDL f e [] = e) ∧ ∀f e x l. FOLDL f e (x::l) = FOLDL f (f e x) l
   
   [FOLDR]  Definition
      
      |- (∀f e. FOLDR f e [] = e) ∧ ∀f e x l. FOLDR f e (x::l) = f x (FOLDR f e l)
   
   [FRONT_DEF]  Definition
      
      |- ∀h t. FRONT (h::t) = if t = [] then [] else h::FRONT t
   
   [HD]  Definition
      
      |- ∀h t. HD (h::t) = h
   
   [LAST_DEF]  Definition
      
      |- ∀h t. LAST (h::t) = if t = [] then h else LAST t
   
   [LENGTH]  Definition
      
      |- (LENGTH [] = 0) ∧ ∀h t. LENGTH (h::t) = SUC (LENGTH t)
   
   [LEN_DEF]  Definition
      
      |- (∀n. LEN [] n = n) ∧ ∀h t n. LEN (h::t) n = LEN t (n + 1)
   
   [LIST_TO_SET]  Definition
      
      |- set = combin$C MEM
   
   [LRC_def]  Definition
      
      |- (∀R x y. LRC R [] x y ⇔ (x = y)) ∧
         ∀R h t x y. LRC R (h::t) x y ⇔ (x = h) ∧ ∃z. R x z ∧ LRC R t z y
   
   [MAP]  Definition
      
      |- (∀f. MAP f [] = []) ∧ ∀f h t. MAP f (h::t) = f h::MAP f t
   
   [MAP2]  Definition
      
      |- (∀f. MAP2 f [] [] = []) ∧
         ∀f h1 t1 h2 t2. MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2
   
   [MEM]  Definition
      
      |- (∀x. MEM x [] ⇔ F) ∧ ∀x h t. MEM x (h::t) ⇔ (x = h) ∨ MEM x t
   
   [NULL_DEF]  Definition
      
      |- (NULL [] ⇔ T) ∧ ∀h t. NULL (h::t) ⇔ F
   
   [REVERSE_DEF]  Definition
      
      |- (REVERSE [] = []) ∧ ∀h t. REVERSE (h::t) = REVERSE t ++ [h]
   
   [REV_DEF]  Definition
      
      |- (∀acc. REV [] acc = acc) ∧ ∀h t acc. REV (h::t) acc = REV t (h::acc)
   
   [SET_TO_LIST_primitive]  Definition
      
      |- SET_TO_LIST =
         WFREC (@R. WF R ∧ ∀s. FINITE s ∧ s ≠ ∅ ⇒ R (REST s) s)
           (λSET_TO_LIST s.
              I
                (if FINITE s then
                   if s = ∅ then [] else CHOICE s::SET_TO_LIST (REST s)
                 else
                   ARB))
   
   [SNOC]  Definition
      
      |- (∀x. SNOC x [] = [x]) ∧ ∀x x' l. SNOC x (x'::l) = x'::SNOC x l
   
   [SUM]  Definition
      
      |- (SUM [] = 0) ∧ ∀h t. SUM (h::t) = h + SUM t
   
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
   
   [isPREFIX]  Definition
      
      |- (∀l. [] ≼ l ⇔ T) ∧
         ∀h t l. h::t ≼ l ⇔ case l of [] -> F || h'::t' -> (h = h') ∧ t ≼ t'
   
   [listRel]  Definition
      
      |- listRel =
         (λR a0 a1.
            ∀listRel'.
              (∀a0 a1.
                 (a0 = []) ∧ (a1 = []) ∨
                 (∃h1 h2 t1 t2.
                    (a0 = h1::t1) ∧ (a1 = h2::t2) ∧ R h1 h2 ∧ listRel' t1 t2) ⇒
                 listRel' a0 a1) ⇒
              listRel' a0 a1)
   
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
                              (ind_type$FCONS a1 (λn. ind_type$BOTTOM))) a0 a1) ∧
                        'list' a1) ⇒
                     'list' a0') ⇒
                  'list' a0') rep
   
   [list_case_def]  Definition
      
      |- (∀v f. list_case v f [] = v) ∧ ∀v f a0 a1. list_case v f (a0::a1) = f a0 a1
   
   [list_repfns]  Definition
      
      |- (∀a. mk_list (dest_list a) = a) ∧
         ∀r.
           (λa0'.
              ∀'list' .
                (∀a0'.
                   (a0' = ind_type$CONSTR 0 ARB (λn. ind_type$BOTTOM)) ∨
                   (∃a0 a1.
                      (a0' =
                       (λa0 a1.
                          ind_type$CONSTR (SUC 0) a0
                            (ind_type$FCONS a1 (λn. ind_type$BOTTOM))) a0 a1) ∧
                      'list' a1) ⇒
                   'list' a0') ⇒
                'list' a0') r ⇔ (dest_list (mk_list r) = r)
   
   [list_size_def]  Definition
      
      |- (∀f. list_size f [] = 0) ∧
         ∀f a0 a1. list_size f (a0::a1) = 1 + (f a0 + list_size f a1)
   
   [ALL_DISTINCT_APPEND]  Theorem
      
      |- ∀l1 l2.
           ALL_DISTINCT (l1 ++ l2) ⇔
           ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 ∧ ∀e. MEM e l1 ⇒ ¬MEM e l2
   
   [ALL_DISTINCT_CARD_LIST_TO_SET]  Theorem
      
      |- ∀ls. ALL_DISTINCT ls ⇒ (CARD (set ls) = LENGTH ls)
   
   [ALL_DISTINCT_EL_IMP]  Theorem
      
      |- ∀l n1 n2.
           ALL_DISTINCT l ∧ n1 < LENGTH l ∧ n2 < LENGTH l ⇒
           ((EL n1 l = EL n2 l) ⇔ (n1 = n2))
   
   [ALL_DISTINCT_FILTER]  Theorem
      
      |- ∀l. ALL_DISTINCT l ⇔ ∀x. MEM x l ⇒ (FILTER ($= x) l = [x])
   
   [ALL_DISTINCT_REVERSE]  Theorem
      
      |- ∀l. ALL_DISTINCT (REVERSE l) ⇔ ALL_DISTINCT l
   
   [ALL_DISTINCT_SET_TO_LIST]  Theorem
      
      |- ∀s. FINITE s ⇒ ALL_DISTINCT (SET_TO_LIST s)
   
   [ALL_DISTINCT_SING]  Theorem
      
      |- ∀x. ALL_DISTINCT [x]
   
   [ALL_DISTINCT_ZIP]  Theorem
      
      |- ∀l1 l2.
           ALL_DISTINCT l1 ∧ (LENGTH l1 = LENGTH l2) ⇒ ALL_DISTINCT (ZIP (l1,l2))
   
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
   
   [APPEND_EQ_SELF]  Theorem
      
      |- (∀l1 l2. (l1 ++ l2 = l1) ⇔ (l2 = [])) ∧
         (∀l1 l2. (l1 ++ l2 = l2) ⇔ (l1 = [])) ∧
         (∀l1 l2. (l1 = l1 ++ l2) ⇔ (l2 = [])) ∧ ∀l1 l2. (l2 = l1 ++ l2) ⇔ (l1 = [])
   
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
   
   [APPEND_eq_NIL]  Theorem
      
      |- (∀l1 l2. ([] = l1 ++ l2) ⇔ (l1 = []) ∧ (l2 = [])) ∧
         ∀l1 l2. (l1 ++ l2 = []) ⇔ (l1 = []) ∧ (l2 = [])
   
   [CARD_LIST_TO_SET]  Theorem
      
      |- CARD (set ls) ≤ LENGTH ls
   
   [CONS]  Theorem
      
      |- ∀l. ¬NULL l ⇒ (HD l::TL l = l)
   
   [CONS_11]  Theorem
      
      |- ∀a0 a1 a0' a1'. (a0::a1 = a0'::a1') ⇔ (a0 = a0') ∧ (a1 = a1')
   
   [CONS_ACYCLIC]  Theorem
      
      |- ∀l x. l ≠ x::l ∧ x::l ≠ l
   
   [DROP_0]  Theorem
      
      |- DROP 0 l = l
   
   [EL_ALL_DISTINCT_EL_EQ]  Theorem
      
      |- ∀l.
           ALL_DISTINCT l ⇔
           ∀n1 n2. n1 < LENGTH l ∧ n2 < LENGTH l ⇒ ((EL n1 l = EL n2 l) ⇔ (n1 = n2))
   
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
   
   [EVERY_APPEND]  Theorem
      
      |- ∀P l1 l2. EVERY P (l1 ++ l2) ⇔ EVERY P l1 ∧ EVERY P l2
   
   [EVERY_CONG]  Theorem
      
      |- ∀l1 l2 P P'.
           (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (P x ⇔ P' x)) ⇒ (EVERY P l1 ⇔ EVERY P' l2)
   
   [EVERY_CONJ]  Theorem
      
      |- ∀l. EVERY (λx. P x ∧ Q x) l ⇔ EVERY P l ∧ EVERY Q l
   
   [EVERY_EL]  Theorem
      
      |- ∀l P. EVERY P l ⇔ ∀n. n < LENGTH l ⇒ P (EL n l)
   
   [EVERY_FILTER]  Theorem
      
      |- ∀P1 P2 l. EVERY P1 (FILTER P2 l) ⇔ EVERY (λx. P2 x ⇒ P1 x) l
   
   [EVERY_FILTER_IMP]  Theorem
      
      |- ∀P1 P2 l. EVERY P1 l ⇒ EVERY P1 (FILTER P2 l)
   
   [EVERY_MAP]  Theorem
      
      |- ∀P f l. EVERY P (MAP f l) ⇔ EVERY (λx. P (f x)) l
   
   [EVERY_MEM]  Theorem
      
      |- ∀P l. EVERY P l ⇔ ∀e. MEM e l ⇒ P e
   
   [EVERY_MONOTONIC]  Theorem
      
      |- ∀P Q. (∀x. P x ⇒ Q x) ⇒ ∀l. EVERY P l ⇒ EVERY Q l
   
   [EVERY_NOT_EXISTS]  Theorem
      
      |- ∀P l. EVERY P l ⇔ ¬EXISTS (λx. ¬P x) l
   
   [EVERY_SIMP]  Theorem
      
      |- ∀c l. EVERY (λx. c) l ⇔ (l = []) ∨ c
   
   [EXISTS_APPEND]  Theorem
      
      |- ∀P l1 l2. EXISTS P (l1 ++ l2) ⇔ EXISTS P l1 ∨ EXISTS P l2
   
   [EXISTS_CONG]  Theorem
      
      |- ∀l1 l2 P P'.
           (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (P x ⇔ P' x)) ⇒ (EXISTS P l1 ⇔ EXISTS P' l2)
   
   [EXISTS_MAP]  Theorem
      
      |- ∀P f l. EXISTS P (MAP f l) ⇔ EXISTS (λx. P (f x)) l
   
   [EXISTS_MEM]  Theorem
      
      |- ∀P l. EXISTS P l ⇔ ∃e. MEM e l ∧ P e
   
   [EXISTS_NOT_EVERY]  Theorem
      
      |- ∀P l. EXISTS P l ⇔ ¬EVERY (λx. ¬P x) l
   
   [EXISTS_SIMP]  Theorem
      
      |- ∀c l. EXISTS (λx. c) l ⇔ l ≠ [] ∧ c
   
   [FILTER_ALL_DISTINCT]  Theorem
      
      |- ∀P l. ALL_DISTINCT l ⇒ ALL_DISTINCT (FILTER P l)
   
   [FILTER_APPEND_DISTRIB]  Theorem
      
      |- ∀P L M. FILTER P (L ++ M) = FILTER P L ++ FILTER P M
   
   [FILTER_COND_REWRITE]  Theorem
      
      |- (FILTER P [] = []) ∧ (∀h. P h ⇒ (FILTER P (h::l) = h::FILTER P l)) ∧
         ∀h. ¬P h ⇒ (FILTER P (h::l) = FILTER P l)
   
   [FILTER_EQ_APPEND]  Theorem
      
      |- ∀P l l1 l2.
           (FILTER P l = l1 ++ l2) ⇔
           ∃l3 l4. (l = l3 ++ l4) ∧ (FILTER P l3 = l1) ∧ (FILTER P l4 = l2)
   
   [FILTER_EQ_CONS]  Theorem
      
      |- ∀P l h lr.
           (FILTER P l = h::lr) ⇔
           ∃l1 l2.
             (l = l1 ++ [h] ++ l2) ∧ (FILTER P l1 = []) ∧ (FILTER P l2 = lr) ∧ P h
   
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
   
   [FOLDL_CONG]  Theorem
      
      |- ∀l l' b b' f f'.
           (l = l') ∧ (b = b') ∧ (∀x a. MEM x l' ⇒ (f a x = f' a x)) ⇒
           (FOLDL f b l = FOLDL f' b' l')
   
   [FOLDL_EQ_FOLDR]  Theorem
      
      |- ∀f l e. ASSOC f ∧ COMM f ⇒ (FOLDL f e l = FOLDR f e l)
   
   [FOLDR_CONG]  Theorem
      
      |- ∀l l' b b' f f'.
           (l = l') ∧ (b = b') ∧ (∀x a. MEM x l' ⇒ (f x a = f' x a)) ⇒
           (FOLDR f b l = FOLDR f' b' l')
   
   [FORALL_LIST]  Theorem
      
      |- (∀l. P l) ⇔ P [] ∧ ∀h t. P t ⇒ P (h::t)
   
   [FRONT_CONS]  Theorem
      
      |- (∀x. FRONT [x] = []) ∧ ∀x y z. FRONT (x::y::z) = x::FRONT (y::z)
   
   [FRONT_CONS_EQ_NIL]  Theorem
      
      |- (∀x xs. (FRONT (x::xs) = []) ⇔ (xs = [])) ∧
         (∀x xs. ([] = FRONT (x::xs)) ⇔ (xs = [])) ∧
         ∀x xs. NULL (FRONT (x::xs)) ⇔ NULL xs
   
   [FRONT_SNOC]  Theorem
      
      |- ∀x l. FRONT (SNOC x l) = l
   
   [INFINITE_LIST_UNIV]  Theorem
      
      |- INFINITE pred_set$UNIV
   
   [IN_LIST_TO_SET]  Theorem
      
      |- x ∈ set l ⇔ MEM x l
   
   [LAST_APPEND_CONS]  Theorem
      
      |- LAST (l1 ++ h::l2) = LAST (h::l2)
   
   [LAST_CONS]  Theorem
      
      |- (∀x. LAST [x] = x) ∧ ∀x y z. LAST (x::y::z) = LAST (y::z)
   
   [LAST_CONS_cond]  Theorem
      
      |- LAST (h::t) = if t = [] then h else LAST t
   
   [LAST_SNOC]  Theorem
      
      |- ∀x l. LAST (SNOC x l) = x
   
   [LENGTH_APPEND]  Theorem
      
      |- ∀l1 l2. LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2
   
   [LENGTH_CONS]  Theorem
      
      |- ∀l n. (LENGTH l = SUC n) ⇔ ∃h l'. (LENGTH l' = n) ∧ (l = h::l')
   
   [LENGTH_DROP]  Theorem
      
      |- ∀n. LENGTH (DROP n l) = LENGTH l − n
   
   [LENGTH_EQ_CONS]  Theorem
      
      |- ∀P n.
           (∀l. (LENGTH l = SUC n) ⇒ P l) ⇔ ∀l. (LENGTH l = n) ⇒ (λl. ∀x. P (x::l)) l
   
   [LENGTH_EQ_NIL]  Theorem
      
      |- ∀P. (∀l. (LENGTH l = 0) ⇒ P l) ⇔ P []
   
   [LENGTH_EQ_NUM]  Theorem
      
      |- (∀l. (LENGTH l = 0) ⇔ (l = [])) ∧
         (∀l n. (LENGTH l = SUC n) ⇔ ∃h l'. (LENGTH l' = n) ∧ (l = h::l')) ∧
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
   
   [LENGTH_FRONT_CONS]  Theorem
      
      |- ∀x xs. LENGTH (FRONT (x::xs)) = LENGTH xs
   
   [LENGTH_LEN]  Theorem
      
      |- ∀L. LENGTH L = LEN L 0
   
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
      
      |- ∀n. n ≤ LENGTH l ⇒ (LENGTH (TAKE n l) = n)
   
   [LENGTH_TL]  Theorem
      
      |- ∀l. 0 < LENGTH l ⇒ (LENGTH (TL l) = LENGTH l − 1)
   
   [LENGTH_UNZIP]  Theorem
      
      |- ∀pl.
           (LENGTH (FST (UNZIP pl)) = LENGTH pl) ∧
           (LENGTH (SND (UNZIP pl)) = LENGTH pl)
   
   [LENGTH_ZIP]  Theorem
      
      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ⇒
           (LENGTH (ZIP (l1,l2)) = LENGTH l1) ∧ (LENGTH (ZIP (l1,l2)) = LENGTH l2)
   
   [LEN_LENGTH_LEM]  Theorem
      
      |- ∀L n. LEN L n = LENGTH L + n
   
   [LIST_EQ]  Theorem
      
      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ∧ (∀x. x < LENGTH l1 ⇒ (EL x l1 = EL x l2)) ⇒
           (l1 = l2)
   
   [LIST_EQ_REWRITE]  Theorem
      
      |- ∀l1 l2.
           (l1 = l2) ⇔
           (LENGTH l1 = LENGTH l2) ∧ ∀x. x < LENGTH l1 ⇒ (EL x l1 = EL x l2)
   
   [LIST_NOT_EQ]  Theorem
      
      |- ∀l1 l2. l1 ≠ l2 ⇒ ∀h1 h2. h1::l1 ≠ h2::l2
   
   [LIST_TO_SET_APPEND]  Theorem
      
      |- ∀l1 l2. set (l1 ++ l2) = set l1 ∪ set l2
   
   [LIST_TO_SET_EQ_EMPTY]  Theorem
      
      |- ((set l = ∅) ⇔ (l = [])) ∧ ((∅ = set l) ⇔ (l = []))
   
   [LIST_TO_SET_MAP]  Theorem
      
      |- ∀f l. set (MAP f l) = IMAGE f (set l)
   
   [LIST_TO_SET_REVERSE]  Theorem
      
      |- ∀ls. set (REVERSE ls) = set ls
   
   [LIST_TO_SET_SNOC]  Theorem
      
      |- set (SNOC x ls) = x INSERT set ls
   
   [LIST_TO_SET_THM]  Theorem
      
      |- (set [] = ∅) ∧ (set (h::t) = h INSERT set t)
   
   [LRC_MEM]  Theorem
      
      |- LRC R ls x y ∧ MEM e ls ⇒ ∃z t. R e z ∧ LRC R t z y
   
   [LRC_MEM_right]  Theorem
      
      |- LRC R (h::t) x y ∧ MEM e t ⇒ ∃z p. R z e ∧ LRC R p x z
   
   [MAP2_ZIP]  Theorem
      
      |- ∀l1 l2.
           (LENGTH l1 = LENGTH l2) ⇒ ∀f. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))
   
   [MAP_APPEND]  Theorem
      
      |- ∀f l1 l2. MAP f (l1 ++ l2) = MAP f l1 ++ MAP f l2
   
   [MAP_CONG]  Theorem
      
      |- ∀l1 l2 f f'.
           (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (f x = f' x)) ⇒ (MAP f l1 = MAP f' l2)
   
   [MAP_EQ_NIL]  Theorem
      
      |- ∀l f. ((MAP f l = []) ⇔ (l = [])) ∧ (([] = MAP f l) ⇔ (l = []))
   
   [MAP_ID]  Theorem
      
      |- (MAP (λx. x) l = l) ∧ (MAP I l = l)
   
   [MAP_ZIP]  Theorem
      
      |- (LENGTH l1 = LENGTH l2) ⇒
         (MAP FST (ZIP (l1,l2)) = l1) ∧ (MAP SND (ZIP (l1,l2)) = l2) ∧
         (MAP (f o FST) (ZIP (l1,l2)) = MAP f l1) ∧
         (MAP (g o SND) (ZIP (l1,l2)) = MAP g l2)
   
   [MEM_APPEND]  Theorem
      
      |- ∀e l1 l2. MEM e (l1 ++ l2) ⇔ MEM e l1 ∨ MEM e l2
   
   [MEM_EL]  Theorem
      
      |- ∀l x. MEM x l ⇔ ∃n. n < LENGTH l ∧ (x = EL n l)
   
   [MEM_FILTER]  Theorem
      
      |- ∀P L x. MEM x (FILTER P L) ⇔ P x ∧ MEM x L
   
   [MEM_FLAT]  Theorem
      
      |- ∀x L. MEM x (FLAT L) ⇔ ∃l. MEM l L ∧ MEM x l
   
   [MEM_MAP]  Theorem
      
      |- ∀l f x. MEM x (MAP f l) ⇔ ∃y. (x = f y) ∧ MEM y l
   
   [MEM_REVERSE]  Theorem
      
      |- ∀l x. MEM x (REVERSE l) ⇔ MEM x l
   
   [MEM_SET_TO_LIST]  Theorem
      
      |- ∀s. FINITE s ⇒ ∀x. MEM x (SET_TO_LIST s) ⇔ x ∈ s
   
   [MEM_SPLIT]  Theorem
      
      |- ∀x l. MEM x l ⇔ ∃l1 l2. l = l1 ++ x::l2
   
   [MEM_ZIP]  Theorem
      
      |- ∀l1 l2 p.
           (LENGTH l1 = LENGTH l2) ⇒
           (MEM p (ZIP (l1,l2)) ⇔ ∃n. n < LENGTH l1 ∧ (p = (EL n l1,EL n l2)))
   
   [MONO_EVERY]  Theorem
      
      |- (∀x. P x ⇒ Q x) ⇒ EVERY P l ⇒ EVERY Q l
   
   [MONO_EXISTS]  Theorem
      
      |- (∀x. P x ⇒ Q x) ⇒ EXISTS P l ⇒ EXISTS Q l
   
   [MONO_listRel]  Theorem
      
      |- (∀x y. R x y ⇒ R' x y) ⇒ listRel R x y ⇒ listRel R' x y
   
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
   
   [NULL_LENGTH]  Theorem
      
      |- ∀l. NULL l ⇔ (LENGTH l = 0)
   
   [REVERSE_APPEND]  Theorem
      
      |- ∀l1 l2. REVERSE (l1 ++ l2) = REVERSE l2 ++ REVERSE l1
   
   [REVERSE_EQ_NIL]  Theorem
      
      |- (REVERSE l = []) ⇔ (l = [])
   
   [REVERSE_EQ_SING]  Theorem
      
      |- (REVERSE l = [e]) ⇔ (l = [e])
   
   [REVERSE_REV]  Theorem
      
      |- ∀L. REVERSE L = REV L []
   
   [REVERSE_REVERSE]  Theorem
      
      |- ∀l. REVERSE (REVERSE l) = l
   
   [REV_REVERSE_LEM]  Theorem
      
      |- ∀L1 L2. REV L1 L2 = REVERSE L1 ++ L2
   
   [SET_TO_LIST_CARD]  Theorem
      
      |- ∀s. FINITE s ⇒ (LENGTH (SET_TO_LIST s) = CARD s)
   
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
         (SET_TO_LIST s = if s = ∅ then [] else CHOICE s::SET_TO_LIST (REST s))
   
   [SNOC_APPEND]  Theorem
      
      |- ∀x l. SNOC x l = l ++ [x]
   
   [TAKE_0]  Theorem
      
      |- TAKE 0 l = []
   
   [TAKE_APPEND1]  Theorem
      
      |- ∀n. n ≤ LENGTH l1 ⇒ (TAKE n (l1 ++ l2) = TAKE n l1)
   
   [TAKE_APPEND2]  Theorem
      
      |- ∀n. LENGTH l1 < n ⇒ (TAKE n (l1 ++ l2) = l1 ++ TAKE (n − LENGTH l1) l2)
   
   [TAKE_DROP]  Theorem
      
      |- ∀n. TAKE n l ++ DROP n l = l
   
   [TAKE_LENGTH_ID]  Theorem
      
      |- TAKE (LENGTH l) l = l
   
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
   
   [ZIP_MAP]  Theorem
      
      |- ∀l1 l2 f1 f2.
           (LENGTH l1 = LENGTH l2) ⇒
           (ZIP (MAP f1 l1,l2) = MAP (λp. (f1 (FST p),SND p)) (ZIP (l1,l2))) ∧
           (ZIP (l1,MAP f2 l2) = MAP (λp. (FST p,f2 (SND p))) (ZIP (l1,l2)))
   
   [ZIP_UNZIP]  Theorem
      
      |- ∀l. ZIP (UNZIP l) = l
   
   [datatype_list]  Theorem
      
      |- DATATYPE (list [] CONS)
   
   [isPREFIX_THM]  Theorem
      
      |- ([] ≼ l ⇔ T) ∧ (h::t ≼ [] ⇔ F) ∧ (h1::t1 ≼ h2::t2 ⇔ (h1 = h2) ∧ t1 ≼ t2)
   
   [listRel_CONS]  Theorem
      
      |- (listRel R (h::t) y ⇔ ∃h' t'. (y = h'::t') ∧ R h h' ∧ listRel R t t') ∧
         (listRel R x (h'::t') ⇔ ∃h t. (x = h::t) ∧ R h h' ∧ listRel R t t')
   
   [listRel_LENGTH]  Theorem
      
      |- ∀x y. listRel R x y ⇒ (LENGTH x = LENGTH y)
   
   [listRel_NIL]  Theorem
      
      |- (listRel R [] y ⇔ (y = [])) ∧ (listRel R x [] ⇔ (x = []))
   
   [listRel_cases]  Theorem
      
      |- ∀R a0 a1.
           listRel R a0 a1 ⇔
           (a0 = []) ∧ (a1 = []) ∨
           ∃h1 h2 t1 t2. (a0 = h1::t1) ∧ (a1 = h2::t2) ∧ R h1 h2 ∧ listRel R t1 t2
   
   [listRel_ind]  Theorem
      
      |- ∀R listRel'.
           listRel' [] [] ∧
           (∀h1 h2 t1 t2. R h1 h2 ∧ listRel' t1 t2 ⇒ listRel' (h1::t1) (h2::t2)) ⇒
           ∀a0 a1. listRel R a0 a1 ⇒ listRel' a0 a1
   
   [listRel_rules]  Theorem
      
      |- ∀R.
           listRel R [] [] ∧
           ∀h1 h2 t1 t2. R h1 h2 ∧ listRel R t1 t2 ⇒ listRel R (h1::t1) (h2::t2)
   
   [listRel_strong_ind]  Theorem
      
      |- ∀R listRel'.
           listRel' [] [] ∧
           (∀h1 h2 t1 t2.
              R h1 h2 ∧ listRel R t1 t2 ∧ listRel' t1 t2 ⇒
              listRel' (h1::t1) (h2::t2)) ⇒
           ∀a0 a1. listRel R a0 a1 ⇒ listRel' a0 a1
   
   [listRel_strongind]  Theorem
      
      |- ∀R listRel'.
           listRel' [] [] ∧
           (∀h1 h2 t1 t2.
              R h1 h2 ∧ listRel R t1 t2 ∧ listRel' t1 t2 ⇒
              listRel' (h1::t1) (h2::t2)) ⇒
           ∀a0 a1. listRel R a0 a1 ⇒ listRel' a0 a1
   
   [list_11]  Theorem
      
      |- ∀a0 a1 a0' a1'. (a0::a1 = a0'::a1') ⇔ (a0 = a0') ∧ (a1 = a1')
   
   [list_Axiom]  Theorem
      
      |- ∀f0 f1. ∃fn. (fn [] = f0) ∧ ∀a0 a1. fn (a0::a1) = f1 a0 a1 (fn a1)
   
   [list_Axiom_old]  Theorem
      
      |- ∀x f. ∃!fn1. (fn1 [] = x) ∧ ∀h t. fn1 (h::t) = f (fn1 t) h t
   
   [list_CASES]  Theorem
      
      |- ∀l. (l = []) ∨ ∃t h. l = h::t
   
   [list_INDUCT]  Theorem
      
      |- ∀P. P [] ∧ (∀t. P t ⇒ ∀h. P (h::t)) ⇒ ∀l. P l
   
   [list_case_compute]  Theorem
      
      |- ∀l. list_case b f l = if NULL l then b else f (HD l) (TL l)
   
   [list_case_cong]  Theorem
      
      |- ∀M M' v f.
           (M = M') ∧ ((M' = []) ⇒ (v = v')) ∧
           (∀a0 a1. (M' = a0::a1) ⇒ (f a0 a1 = f' a0 a1)) ⇒
           (list_case v f M = list_case v' f' M')
   
   [list_distinct]  Theorem
      
      |- ∀a1 a0. [] ≠ a0::a1
   
   [list_induction]  Theorem
      
      |- ∀P. P [] ∧ (∀t. P t ⇒ ∀h. P (h::t)) ⇒ ∀l. P l
   
   [list_nchotomy]  Theorem
      
      |- ∀l. (l = []) ∨ ∃t h. l = h::t
   
   [list_size_cong]  Theorem
      
      |- ∀M N f f'.
           (M = N) ∧ (∀x. MEM x N ⇒ (f x = f' x)) ⇒ (list_size f M = list_size f' N)
   
   
*)
end
