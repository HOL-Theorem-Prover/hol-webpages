signature sortingTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val PART3_DEF : thm
    val PARTITION_DEF : thm
    val PART_DEF : thm
    val PERM_DEF : thm
    val PERM_SINGLE_SWAP_DEF : thm
    val QSORT3_curried_DEF : thm
    val QSORT3_tupled_primitive_DEF : thm
    val QSORT_curried_DEF : thm
    val QSORT_tupled_primitive_DEF : thm
    val SORTED_curried_DEF : thm
    val SORTED_tupled_primitive_DEF : thm
    val SORTS_DEF : thm
    val STABLE_DEF : thm

  (*  Theorems  *)
    val ALL_DISTINCT_PERM : thm
    val ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST : thm
    val APPEND_PERM_SYM : thm
    val CONS_PERM : thm
    val FOLDR_PERM : thm
    val MEM_PERM : thm
    val PART3_FILTER : thm
    val PART_LENGTH : thm
    val PART_LENGTH_LEM : thm
    val PART_MEM : thm
    val PARTs_HAVE_PROP : thm
    val PERM3 : thm
    val PERM3_FILTER : thm
    val PERM_ALL_DISTINCT : thm
    val PERM_APPEND : thm
    val PERM_APPEND_IFF : thm
    val PERM_CONG : thm
    val PERM_CONG_2 : thm
    val PERM_CONG_APPEND_IFF : thm
    val PERM_CONS_EQ_APPEND : thm
    val PERM_CONS_IFF : thm
    val PERM_EQC : thm
    val PERM_EQUIVALENCE : thm
    val PERM_EQUIVALENCE_ALT_DEF : thm
    val PERM_FILTER : thm
    val PERM_FUN_APPEND : thm
    val PERM_FUN_APPEND_APPEND_1 : thm
    val PERM_FUN_APPEND_APPEND_2 : thm
    val PERM_FUN_APPEND_CONS : thm
    val PERM_FUN_APPEND_IFF : thm
    val PERM_FUN_CONG : thm
    val PERM_FUN_CONS : thm
    val PERM_FUN_CONS_11_APPEND : thm
    val PERM_FUN_CONS_11_SWAP_AT_FRONT : thm
    val PERM_FUN_CONS_APPEND_1 : thm
    val PERM_FUN_CONS_APPEND_2 : thm
    val PERM_FUN_CONS_IFF : thm
    val PERM_FUN_SPLIT : thm
    val PERM_FUN_SWAP_AT_FRONT : thm
    val PERM_IND : thm
    val PERM_INTRO : thm
    val PERM_LENGTH : thm
    val PERM_LIST_TO_SET : thm
    val PERM_MAP : thm
    val PERM_MEM_EQ : thm
    val PERM_MONO : thm
    val PERM_NIL : thm
    val PERM_QSORT3 : thm
    val PERM_REFL : thm
    val PERM_REVERSE : thm
    val PERM_REVERSE_EQ : thm
    val PERM_REWR : thm
    val PERM_RTC : thm
    val PERM_SET_TO_LIST_count_COUNT_LIST : thm
    val PERM_SING : thm
    val PERM_SINGLE_SWAP_REFL : thm
    val PERM_SINGLE_SWAP_SYM : thm
    val PERM_SPLIT : thm
    val PERM_SUM : thm
    val PERM_SWAP_AT_FRONT : thm
    val PERM_SYM : thm
    val PERM_TC : thm
    val PERM_TRANS : thm
    val PERM_lifts_equalities : thm
    val PERM_lifts_invariants : thm
    val PERM_lifts_monotonicities : thm
    val PERM_lifts_transitive_relations : thm
    val PERM_transitive : thm
    val QSORT3_DEF : thm
    val QSORT3_IND : thm
    val QSORT3_SORTS : thm
    val QSORT3_SPLIT : thm
    val QSORT3_STABLE : thm
    val QSORT_DEF : thm
    val QSORT_IND : thm
    val QSORT_MEM : thm
    val QSORT_PERM : thm
    val QSORT_SORTED : thm
    val QSORT_SORTS : thm
    val QSORT_eq_if_PERM : thm
    val SORTED_APPEND : thm
    val SORTED_DEF : thm
    val SORTED_EL_LESS : thm
    val SORTED_EL_SUC : thm
    val SORTED_EQ : thm
    val SORTED_EQ_PART : thm
    val SORTED_IND : thm
    val SORTED_NIL : thm
    val SORTED_PERM_EQ : thm
    val SORTED_SING : thm
    val SORTED_transitive_APPEND_IFF : thm
    val SUM_IMAGE_count_MULT : thm
    val SUM_IMAGE_count_SUM_GENLIST : thm
    val sum_of_sums : thm

  val sorting_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [rich_list] Parent theory of "sorting"

   [PART3_DEF]  Definition

      |- (∀R h. PART3 R h [] = ([],[],[])) ∧
         ∀R h hd tl.
           PART3 R h (hd::tl) =
           if R h hd ∧ R hd h then (I ## CONS hd ## I) (PART3 R h tl)
           else if R hd h then (CONS hd ## I ## I) (PART3 R h tl)
           else (I ## I ## CONS hd) (PART3 R h tl)

   [PARTITION_DEF]  Definition

      |- ∀P l. PARTITION P l = PART P l [] []

   [PART_DEF]  Definition

      |- (∀P l1 l2. PART P [] l1 l2 = (l1,l2)) ∧
         ∀P h rst l1 l2.
           PART P (h::rst) l1 l2 =
           if P h then PART P rst (h::l1) l2 else PART P rst l1 (h::l2)

   [PERM_DEF]  Definition

      |- ∀L1 L2. PERM L1 L2 ⇔ ∀x. FILTER ($= x) L1 = FILTER ($= x) L2

   [PERM_SINGLE_SWAP_DEF]  Definition

      |- ∀l1 l2.
           PERM_SINGLE_SWAP l1 l2 ⇔
           ∃x1 x2 x3. (l1 = x1 ++ x2 ++ x3) ∧ (l2 = x1 ++ x3 ++ x2)

   [QSORT3_curried_DEF]  Definition

      |- ∀x x1. QSORT3 x x1 = QSORT3_tupled (x,x1)

   [QSORT3_tupled_primitive_DEF]  Definition

      |- QSORT3_tupled =
         WFREC
           (@R'.
              WF R' ∧
              (∀tl hd R lo eq hi.
                 ((lo,eq,hi) = PART3 R hd tl) ⇒ R' (R,hi) (R,hd::tl)) ∧
              ∀tl hd R lo eq hi.
                ((lo,eq,hi) = PART3 R hd tl) ⇒ R' (R,lo) (R,hd::tl))
           (λQSORT3_tupled a.
              case a of
                (R,[]) => I []
              | (R,hd::tl) =>
                  I
                    (let (lo,eq,hi) = PART3 R hd tl
                     in
                       QSORT3_tupled (R,lo) ++ hd::eq ++
                       QSORT3_tupled (R,hi)))

   [QSORT_curried_DEF]  Definition

      |- ∀x x1. QSORT x x1 = QSORT_tupled (x,x1)

   [QSORT_tupled_primitive_DEF]  Definition

      |- QSORT_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀t h ord l1 l2.
                 ((l1,l2) = PARTITION (λy. ord y h) t) ⇒
                 R (ord,l2) (ord,h::t)) ∧
              ∀t h ord l1 l2.
                ((l1,l2) = PARTITION (λy. ord y h) t) ⇒
                R (ord,l1) (ord,h::t))
           (λQSORT_tupled a.
              case a of
                (ord,[]) => I []
              | (ord,h::t) =>
                  I
                    (let (l1,l2) = PARTITION (λy. ord y h) t
                     in
                       QSORT_tupled (ord,l1) ++ [h] ++
                       QSORT_tupled (ord,l2)))

   [SORTED_curried_DEF]  Definition

      |- ∀x x1. SORTED x x1 ⇔ SORTED_tupled (x,x1)

   [SORTED_tupled_primitive_DEF]  Definition

      |- SORTED_tupled =
         WFREC (@R'. WF R' ∧ ∀x rst y R. R' (R,y::rst) (R,x::y::rst))
           (λSORTED_tupled a.
              case a of
                (R,[]) => I T
              | (R,[x]) => I T
              | (R,x::y::rst) => I (R x y ∧ SORTED_tupled (R,y::rst)))

   [SORTS_DEF]  Definition

      |- ∀f R. SORTS f R ⇔ ∀l. PERM l (f R l) ∧ SORTED R (f R l)

   [STABLE_DEF]  Definition

      |- ∀sort r.
           STABLE sort r ⇔
           SORTS sort r ∧
           ∀p.
             (∀x y. p x ∧ p y ⇒ r x y) ⇒
             ∀l. FILTER p l = FILTER p (sort r l)

   [ALL_DISTINCT_PERM]  Theorem

      |- ∀l1 l2. PERM l1 l2 ⇒ (ALL_DISTINCT l1 ⇔ ALL_DISTINCT l2)

   [ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST]  Theorem

      |- ∀ls. ALL_DISTINCT ls ⇔ PERM ls (SET_TO_LIST (set ls))

   [APPEND_PERM_SYM]  Theorem

      |- ∀A B C. PERM (A ++ B) C ⇒ PERM (B ++ A) C

   [CONS_PERM]  Theorem

      |- ∀x L M N. PERM L (M ++ N) ⇒ PERM (x::L) (M ++ x::N)

   [FOLDR_PERM]  Theorem

      |- ∀f l1 l2 e.
           ASSOC f ∧ COMM f ⇒ PERM l1 l2 ⇒ (FOLDR f e l1 = FOLDR f e l2)

   [MEM_PERM]  Theorem

      |- ∀l1 l2. PERM l1 l2 ⇒ ∀a. MEM a l1 ⇔ MEM a l2

   [PART3_FILTER]  Theorem

      |- ∀tl hd.
           PART3 R hd tl =
           (FILTER (λx. R x hd ∧ ¬R hd x) tl,
            FILTER (λx. R x hd ∧ R hd x) tl,FILTER (λx. ¬R x hd) tl)

   [PART_LENGTH]  Theorem

      |- ∀P L l1 l2 p q.
           ((p,q) = PART P L l1 l2) ⇒
           (LENGTH L + LENGTH l1 + LENGTH l2 = LENGTH p + LENGTH q)

   [PART_LENGTH_LEM]  Theorem

      |- ∀P L l1 l2 p q.
           ((p,q) = PART P L l1 l2) ⇒
           LENGTH p ≤ LENGTH L + LENGTH l1 + LENGTH l2 ∧
           LENGTH q ≤ LENGTH L + LENGTH l1 + LENGTH l2

   [PART_MEM]  Theorem

      |- ∀P L a1 a2 l1 l2.
           ((a1,a2) = PART P L l1 l2) ⇒
           ∀x. MEM x (L ++ (l1 ++ l2)) ⇔ MEM x (a1 ++ a2)

   [PARTs_HAVE_PROP]  Theorem

      |- ∀P L A B l1 l2.
           ((A,B) = PART P L l1 l2) ∧ (∀x. MEM x l1 ⇒ P x) ∧
           (∀x. MEM x l2 ⇒ ¬P x) ⇒
           (∀z. MEM z A ⇒ P z) ∧ ∀z. MEM z B ⇒ ¬P z

   [PERM3]  Theorem

      |- ∀x a a' b b' c c'.
           (PERM a a' ∧ PERM b b' ∧ PERM c c') ∧ PERM x (a ++ b ++ c) ⇒
           PERM x (a' ++ b' ++ c')

   [PERM3_FILTER]  Theorem

      |- ∀l h.
           PERM l
             (FILTER (λx. R x h ∧ ¬R h x) l ++
              FILTER (λx. R x h ∧ R h x) l ++ FILTER (λx. ¬R x h) l)

   [PERM_ALL_DISTINCT]  Theorem

      |- ∀l1 l2.
           ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 ∧ (∀x. MEM x l1 ⇔ MEM x l2) ⇒
           PERM l1 l2

   [PERM_APPEND]  Theorem

      |- ∀l1 l2. PERM (l1 ++ l2) (l2 ++ l1)

   [PERM_APPEND_IFF]  Theorem

      |- (∀l l1 l2. PERM (l ++ l1) (l ++ l2) ⇔ PERM l1 l2) ∧
         ∀l l1 l2. PERM (l1 ++ l) (l2 ++ l) ⇔ PERM l1 l2

   [PERM_CONG]  Theorem

      |- ∀L1 L2 L3 L4. PERM L1 L3 ∧ PERM L2 L4 ⇒ PERM (L1 ++ L2) (L3 ++ L4)

   [PERM_CONG_2]  Theorem

      |- ∀l1 l1' l2 l2'.
           PERM l1 l1' ⇒ PERM l2 l2' ⇒ (PERM l1 l2 ⇔ PERM l1' l2')

   [PERM_CONG_APPEND_IFF]  Theorem

      |- ∀l l1 l1' l2 l2'.
           PERM l1 (l ++ l1') ⇒
           PERM l2 (l ++ l2') ⇒
           (PERM l1 l2 ⇔ PERM l1' l2')

   [PERM_CONS_EQ_APPEND]  Theorem

      |- ∀L h. PERM (h::t) L ⇔ ∃M N. (L = M ++ h::N) ∧ PERM t (M ++ N)

   [PERM_CONS_IFF]  Theorem

      |- ∀x l2 l1. PERM (x::l1) (x::l2) ⇔ PERM l1 l2

   [PERM_EQC]  Theorem

      |- PERM = PERM_SINGLE_SWAP^=

   [PERM_EQUIVALENCE]  Theorem

      |- equivalence PERM

   [PERM_EQUIVALENCE_ALT_DEF]  Theorem

      |- ∀x y. PERM x y ⇔ (PERM x = PERM y)

   [PERM_FILTER]  Theorem

      |- ∀P l1 l2. PERM l1 l2 ⇒ PERM (FILTER P l1) (FILTER P l2)

   [PERM_FUN_APPEND]  Theorem

      |- ∀l1 l2. PERM (l1 ++ l2) = PERM (l2 ++ l1)

   [PERM_FUN_APPEND_APPEND_1]  Theorem

      |- ∀l1 l2 l3 l4.
           (PERM l1 = PERM (l2 ++ l3)) ⇒
           (PERM (l1 ++ l4) = PERM (l2 ++ (l3 ++ l4)))

   [PERM_FUN_APPEND_APPEND_2]  Theorem

      |- ∀l1 l2 l3 l4.
           (PERM l1 = PERM (l2 ++ l3)) ⇒
           (PERM (l4 ++ l1) = PERM (l2 ++ (l4 ++ l3)))

   [PERM_FUN_APPEND_CONS]  Theorem

      |- ∀x l1 l2. PERM (l1 ++ x::l2) = PERM (x::l1 ++ l2)

   [PERM_FUN_APPEND_IFF]  Theorem

      |- ∀l l1 l2. (PERM l1 = PERM l2) ⇒ (PERM (l ++ l1) = PERM (l ++ l2))

   [PERM_FUN_CONG]  Theorem

      |- ∀l1 l1' l2 l2'.
           (PERM l1 = PERM l1') ⇒
           (PERM l2 = PERM l2') ⇒
           (PERM l1 l2 ⇔ PERM l1' l2')

   [PERM_FUN_CONS]  Theorem

      |- ∀x l1 l1'. (PERM l1 = PERM l1') ⇒ (PERM (x::l1) = PERM (x::l1'))

   [PERM_FUN_CONS_11_APPEND]  Theorem

      |- ∀y l1 l2 l3.
           (PERM l1 = PERM (l2 ++ l3)) ⇒
           (PERM (y::l1) = PERM (l2 ++ y::l3))

   [PERM_FUN_CONS_11_SWAP_AT_FRONT]  Theorem

      |- ∀y l1 x l2.
           (PERM l1 = PERM (x::l2)) ⇒ (PERM (y::l1) = PERM (x::y::l2))

   [PERM_FUN_CONS_APPEND_1]  Theorem

      |- ∀l l1 x l2.
           (PERM l1 = PERM (x::l2)) ⇒
           (PERM (l1 ++ l) = PERM (x::(l2 ++ l)))

   [PERM_FUN_CONS_APPEND_2]  Theorem

      |- ∀l l1 x l2.
           (PERM l1 = PERM (x::l2)) ⇒
           (PERM (l ++ l1) = PERM (x::(l ++ l2)))

   [PERM_FUN_CONS_IFF]  Theorem

      |- ∀x l1 l2. (PERM l1 = PERM l2) ⇒ (PERM (x::l1) = PERM (x::l2))

   [PERM_FUN_SPLIT]  Theorem

      |- ∀l l1 l1' l2. PERM l (l1 ++ l2) ⇒ PERM l1' l1 ⇒ PERM l (l1' ++ l2)

   [PERM_FUN_SWAP_AT_FRONT]  Theorem

      |- ∀x y l. PERM (x::y::l) = PERM (y::x::l)

   [PERM_IND]  Theorem

      |- ∀P.
           P [] [] ∧ (∀x l1 l2. P l1 l2 ⇒ P (x::l1) (x::l2)) ∧
           (∀x y l1 l2. P l1 l2 ⇒ P (x::y::l1) (y::x::l2)) ∧
           (∀l1 l2 l3. P l1 l2 ∧ P l2 l3 ⇒ P l1 l3) ⇒
           ∀l1 l2. PERM l1 l2 ⇒ P l1 l2

   [PERM_INTRO]  Theorem

      |- ∀x y. (x = y) ⇒ PERM x y

   [PERM_LENGTH]  Theorem

      |- ∀l1 l2. PERM l1 l2 ⇒ (LENGTH l1 = LENGTH l2)

   [PERM_LIST_TO_SET]  Theorem

      |- ∀l1 l2. PERM l1 l2 ⇒ (set l1 = set l2)

   [PERM_MAP]  Theorem

      |- ∀f l1 l2. PERM l1 l2 ⇒ PERM (MAP f l1) (MAP f l2)

   [PERM_MEM_EQ]  Theorem

      |- ∀l1 l2. PERM l1 l2 ⇒ ∀x. MEM x l1 ⇔ MEM x l2

   [PERM_MONO]  Theorem

      |- ∀l1 l2 x. PERM l1 l2 ⇒ PERM (x::l1) (x::l2)

   [PERM_NIL]  Theorem

      |- ∀L. (PERM L [] ⇔ (L = [])) ∧ (PERM [] L ⇔ (L = []))

   [PERM_QSORT3]  Theorem

      |- ∀l R. PERM l (QSORT3 R l)

   [PERM_REFL]  Theorem

      |- ∀L. PERM L L

   [PERM_REVERSE]  Theorem

      |- PERM ls (REVERSE ls)

   [PERM_REVERSE_EQ]  Theorem

      |- (PERM (REVERSE l1) l2 ⇔ PERM l1 l2) ∧
         (PERM l1 (REVERSE l2) ⇔ PERM l1 l2)

   [PERM_REWR]  Theorem

      |- ∀l r l1 l2. PERM l r ⇒ (PERM (l ++ l1) l2 ⇔ PERM (r ++ l1) l2)

   [PERM_RTC]  Theorem

      |- PERM = PERM_SINGLE_SWAP^*

   [PERM_SET_TO_LIST_count_COUNT_LIST]  Theorem

      |- PERM (SET_TO_LIST (count n)) (COUNT_LIST n)

   [PERM_SING]  Theorem

      |- (PERM L [x] ⇔ (L = [x])) ∧ (PERM [x] L ⇔ (L = [x]))

   [PERM_SINGLE_SWAP_REFL]  Theorem

      |- ∀l. PERM_SINGLE_SWAP l l

   [PERM_SINGLE_SWAP_SYM]  Theorem

      |- ∀l1 l2. PERM_SINGLE_SWAP l1 l2 ⇔ PERM_SINGLE_SWAP l2 l1

   [PERM_SPLIT]  Theorem

      |- ∀P l. PERM l (FILTER P l ++ FILTER ($~ o P) l)

   [PERM_SUM]  Theorem

      |- ∀l1 l2. PERM l1 l2 ⇒ (SUM l1 = SUM l2)

   [PERM_SWAP_AT_FRONT]  Theorem

      |- PERM (x::y::l1) (y::x::l2) ⇔ PERM l1 l2

   [PERM_SYM]  Theorem

      |- ∀l1 l2. PERM l1 l2 ⇔ PERM l2 l1

   [PERM_TC]  Theorem

      |- PERM = PERM_SINGLE_SWAP⁺

   [PERM_TRANS]  Theorem

      |- ∀x y z. PERM x y ∧ PERM y z ⇒ PERM x z

   [PERM_lifts_equalities]  Theorem

      |- ∀f.
           (∀x1 x2 x3. f (x1 ++ x2 ++ x3) = f (x1 ++ x3 ++ x2)) ⇒
           ∀x y. PERM x y ⇒ (f x = f y)

   [PERM_lifts_invariants]  Theorem

      |- ∀P.
           (∀x1 x2 x3. P (x1 ++ x2 ++ x3) ⇒ P (x1 ++ x3 ++ x2)) ⇒
           ∀x y. P x ∧ PERM x y ⇒ P y

   [PERM_lifts_monotonicities]  Theorem

      |- ∀f.
           (∀x1 x2 x3.
              ∃x1' x2' x3'.
                (f (x1 ++ x2 ++ x3) = x1' ++ x2' ++ x3') ∧
                (f (x1 ++ x3 ++ x2) = x1' ++ x3' ++ x2')) ⇒
           ∀x y. PERM x y ⇒ PERM (f x) (f y)

   [PERM_lifts_transitive_relations]  Theorem

      |- ∀f Q.
           (∀x1 x2 x3. Q (f (x1 ++ x2 ++ x3)) (f (x1 ++ x3 ++ x2))) ∧
           transitive Q ⇒
           ∀x y. PERM x y ⇒ Q (f x) (f y)

   [PERM_transitive]  Theorem

      |- transitive PERM

   [QSORT3_DEF]  Theorem

      |- (∀R. QSORT3 R [] = []) ∧
         ∀tl hd R.
           QSORT3 R (hd::tl) =
           (let (lo,eq,hi) = PART3 R hd tl
            in
              QSORT3 R lo ++ hd::eq ++ QSORT3 R hi)

   [QSORT3_IND]  Theorem

      |- ∀P.
           (∀R. P R []) ∧
           (∀R hd tl.
              (∀lo eq hi. ((lo,eq,hi) = PART3 R hd tl) ⇒ P R hi) ∧
              (∀lo eq hi. ((lo,eq,hi) = PART3 R hd tl) ⇒ P R lo) ⇒
              P R (hd::tl)) ⇒
           ∀v v1. P v v1

   [QSORT3_SORTS]  Theorem

      |- ∀R. transitive R ∧ total R ⇒ SORTS QSORT3 R

   [QSORT3_SPLIT]  Theorem

      |- ∀R.
           transitive R ∧ total R ⇒
           ∀l e.
             QSORT3 R l =
             QSORT3 R (FILTER (λx. R x e ∧ ¬R e x) l) ++
             FILTER (λx. R x e ∧ R e x) l ++
             QSORT3 R (FILTER (λx. ¬R x e) l)

   [QSORT3_STABLE]  Theorem

      |- ∀R. transitive R ∧ total R ⇒ STABLE QSORT3 R

   [QSORT_DEF]  Theorem

      |- (∀ord. QSORT ord [] = []) ∧
         ∀t ord h.
           QSORT ord (h::t) =
           (let (l1,l2) = PARTITION (λy. ord y h) t
            in
              QSORT ord l1 ++ [h] ++ QSORT ord l2)

   [QSORT_IND]  Theorem

      |- ∀P.
           (∀ord. P ord []) ∧
           (∀ord h t.
              (∀l1 l2. ((l1,l2) = PARTITION (λy. ord y h) t) ⇒ P ord l2) ∧
              (∀l1 l2. ((l1,l2) = PARTITION (λy. ord y h) t) ⇒ P ord l1) ⇒
              P ord (h::t)) ⇒
           ∀v v1. P v v1

   [QSORT_MEM]  Theorem

      |- ∀R L x. MEM x (QSORT R L) ⇔ MEM x L

   [QSORT_PERM]  Theorem

      |- ∀R L. PERM L (QSORT R L)

   [QSORT_SORTED]  Theorem

      |- ∀R L. transitive R ∧ total R ⇒ SORTED R (QSORT R L)

   [QSORT_SORTS]  Theorem

      |- ∀R. transitive R ∧ total R ⇒ SORTS QSORT R

   [QSORT_eq_if_PERM]  Theorem

      |- ∀R.
           total R ∧ transitive R ∧ antisymmetric R ⇒
           ∀l1 l2. (QSORT R l1 = QSORT R l2) ⇔ PERM l1 l2

   [SORTED_APPEND]  Theorem

      |- ∀R L1 L2.
           transitive R ∧ SORTED R L1 ∧ SORTED R L2 ∧
           (∀x y. MEM x L1 ∧ MEM y L2 ⇒ R x y) ⇒
           SORTED R (L1 ++ L2)

   [SORTED_DEF]  Theorem

      |- (∀R. SORTED R [] ⇔ T) ∧ (∀x R. SORTED R [x] ⇔ T) ∧
         ∀y x rst R. SORTED R (x::y::rst) ⇔ R x y ∧ SORTED R (y::rst)

   [SORTED_EL_LESS]  Theorem

      |- ∀R.
           transitive R ⇒
           ∀ls.
             SORTED R ls ⇔
             ∀m n. m < n ∧ n < LENGTH ls ⇒ R (EL m ls) (EL n ls)

   [SORTED_EL_SUC]  Theorem

      |- ∀R ls.
           SORTED R ls ⇔
           ∀n. SUC n < LENGTH ls ⇒ R (EL n ls) (EL (SUC n) ls)

   [SORTED_EQ]  Theorem

      |- ∀R L x.
           transitive R ⇒
           (SORTED R (x::L) ⇔ SORTED R L ∧ ∀y. MEM y L ⇒ R x y)

   [SORTED_EQ_PART]  Theorem

      |- ∀l R. transitive R ⇒ SORTED R (FILTER (λx. R x hd ∧ R hd x) l)

   [SORTED_IND]  Theorem

      |- ∀P.
           (∀R. P R []) ∧ (∀R x. P R [x]) ∧
           (∀R x y rst. P R (y::rst) ⇒ P R (x::y::rst)) ⇒
           ∀v v1. P v v1

   [SORTED_NIL]  Theorem

      |- ∀R. SORTED R []

   [SORTED_PERM_EQ]  Theorem

      |- ∀R.
           transitive R ∧ antisymmetric R ⇒
           ∀l1 l2. SORTED R l1 ∧ SORTED R l2 ∧ PERM l1 l2 ⇒ (l1 = l2)

   [SORTED_SING]  Theorem

      |- ∀R x. SORTED R [x]

   [SORTED_transitive_APPEND_IFF]  Theorem

      |- ∀R.
           transitive R ⇒
           ∀L1 L2.
             SORTED R (L1 ++ L2) ⇔
             SORTED R L1 ∧ SORTED R L2 ∧
             ((L1 = []) ∨ (L2 = []) ∨ R (LAST L1) (HD L2))

   [SUM_IMAGE_count_MULT]  Theorem

      |- (∀m. m < n ⇒ (g m = ∑ (λx. f (x + k * m)) (count k))) ⇒
         (∑ f (count (k * n)) = ∑ g (count n))

   [SUM_IMAGE_count_SUM_GENLIST]  Theorem

      |- ∑ f (count n) = SUM (GENLIST f n)

   [sum_of_sums]  Theorem

      |- ∑ (λm. ∑ (f m) (count a)) (count b) =
         ∑ (λm. f (m DIV a) (m MOD a)) (count (a * b))


*)
end
