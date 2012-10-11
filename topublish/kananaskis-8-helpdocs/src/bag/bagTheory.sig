signature bagTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BAG_ALL_DISTINCT : thm
    val BAG_CARD : thm
    val BAG_CARD_RELn : thm
    val BAG_CHOICE_DEF : thm
    val BAG_DELETE : thm
    val BAG_DIFF : thm
    val BAG_DISJOINT : thm
    val BAG_EVERY : thm
    val BAG_FILTER_DEF : thm
    val BAG_GEN_PROD_def : thm
    val BAG_GEN_SUM_def : thm
    val BAG_IMAGE_DEF : thm
    val BAG_IN : thm
    val BAG_INN : thm
    val BAG_INSERT : thm
    val BAG_INTER : thm
    val BAG_MERGE : thm
    val BAG_OF_SET : thm
    val BAG_REST_DEF : thm
    val BAG_UNION : thm
    val BIG_BAG_UNION_def : thm
    val EL_BAG : thm
    val EMPTY_BAG : thm
    val FINITE_BAG : thm
    val ITBAG_curried_def : thm
    val ITBAG_tupled_primitive_def : thm
    val PSUB_BAG : thm
    val SET_OF_BAG : thm
    val SING_BAG : thm
    val SUB_BAG : thm
    val bag_size_def : thm
    val mlt1_def : thm

  (*  Theorems  *)
    val ASSOC_BAG_UNION : thm
    val BAG_ALL_DISTINCT_BAG_INN : thm
    val BAG_ALL_DISTINCT_BAG_MERGE : thm
    val BAG_ALL_DISTINCT_BAG_OF_SET : thm
    val BAG_ALL_DISTINCT_BAG_UNION : thm
    val BAG_ALL_DISTINCT_DELETE : thm
    val BAG_ALL_DISTINCT_DIFF : thm
    val BAG_ALL_DISTINCT_EXTENSION : thm
    val BAG_ALL_DISTINCT_SET : thm
    val BAG_ALL_DISTINCT_THM : thm
    val BAG_CARD_BAG_INN : thm
    val BAG_CARD_EMPTY : thm
    val BAG_CARD_THM : thm
    val BAG_CARD_UNION : thm
    val BAG_CHOICE_SING : thm
    val BAG_DECOMPOSE : thm
    val BAG_DELETE_11 : thm
    val BAG_DELETE_BAG_IN : thm
    val BAG_DELETE_BAG_IN_down : thm
    val BAG_DELETE_BAG_IN_up : thm
    val BAG_DELETE_EMPTY : thm
    val BAG_DELETE_INSERT : thm
    val BAG_DELETE_PSUB_BAG : thm
    val BAG_DELETE_SING : thm
    val BAG_DELETE_TWICE : thm
    val BAG_DELETE_commutes : thm
    val BAG_DELETE_concrete : thm
    val BAG_DIFF_2L : thm
    val BAG_DIFF_2R : thm
    val BAG_DIFF_EMPTY : thm
    val BAG_DIFF_EMPTY_simple : thm
    val BAG_DIFF_INSERT : thm
    val BAG_DIFF_INSERT_same : thm
    val BAG_DIFF_UNION_eliminate : thm
    val BAG_DISJOINT_BAG_IN : thm
    val BAG_DISJOINT_BAG_INSERT : thm
    val BAG_DISJOINT_DIFF : thm
    val BAG_DISJOINT_EMPTY : thm
    val BAG_EVERY_MERGE : thm
    val BAG_EVERY_SET : thm
    val BAG_EVERY_THM : thm
    val BAG_EVERY_UNION : thm
    val BAG_EXTENSION : thm
    val BAG_FILTER_BAG_INSERT : thm
    val BAG_FILTER_EMPTY : thm
    val BAG_FILTER_EQ_EMPTY : thm
    val BAG_GEN_PROD_ALL_ONES : thm
    val BAG_GEN_PROD_EMPTY : thm
    val BAG_GEN_PROD_EQ_1 : thm
    val BAG_GEN_PROD_POSITIVE : thm
    val BAG_GEN_PROD_REC : thm
    val BAG_GEN_PROD_TAILREC : thm
    val BAG_GEN_PROD_UNION : thm
    val BAG_GEN_PROD_UNION_LEM : thm
    val BAG_GEN_SUM_EMPTY : thm
    val BAG_GEN_SUM_REC : thm
    val BAG_GEN_SUM_TAILREC : thm
    val BAG_IMAGE_COMPOSE : thm
    val BAG_IMAGE_EMPTY : thm
    val BAG_IMAGE_FINITE : thm
    val BAG_IMAGE_FINITE_I : thm
    val BAG_IMAGE_FINITE_INSERT : thm
    val BAG_IMAGE_FINITE_RESTRICTED_I : thm
    val BAG_IMAGE_FINITE_UNION : thm
    val BAG_INN_0 : thm
    val BAG_INN_BAG_DELETE : thm
    val BAG_INN_BAG_FILTER : thm
    val BAG_INN_BAG_INSERT : thm
    val BAG_INN_BAG_INSERT_STRONG : thm
    val BAG_INN_BAG_MERGE : thm
    val BAG_INN_BAG_UNION : thm
    val BAG_INN_EMPTY_BAG : thm
    val BAG_INN_LESS : thm
    val BAG_INSERT_CHOICE_REST : thm
    val BAG_INSERT_DIFF : thm
    val BAG_INSERT_EQUAL : thm
    val BAG_INSERT_EQ_UNION : thm
    val BAG_INSERT_NOT_EMPTY : thm
    val BAG_INSERT_ONE_ONE : thm
    val BAG_INSERT_UNION : thm
    val BAG_INSERT_commutes : thm
    val BAG_IN_BAG_DELETE : thm
    val BAG_IN_BAG_DIFF_ALL_DISTINCT : thm
    val BAG_IN_BAG_FILTER : thm
    val BAG_IN_BAG_INSERT : thm
    val BAG_IN_BAG_MERGE : thm
    val BAG_IN_BAG_OF_SET : thm
    val BAG_IN_BAG_UNION : thm
    val BAG_IN_BIG_BAG_UNION : thm
    val BAG_IN_DIFF_E : thm
    val BAG_IN_DIFF_I : thm
    val BAG_IN_DIVIDES : thm
    val BAG_IN_FINITE_BAG_IMAGE : thm
    val BAG_LESS_ADD : thm
    val BAG_MERGE_IDEM : thm
    val BAG_NOT_LESS_EMPTY : thm
    val BAG_OF_EMPTY : thm
    val BAG_REST_SING : thm
    val BAG_SIZE_EMPTY : thm
    val BAG_SIZE_INSERT : thm
    val BAG_UNION_DIFF : thm
    val BAG_UNION_DIFF_eliminate : thm
    val BAG_UNION_EMPTY : thm
    val BAG_UNION_EQ_LEFT : thm
    val BAG_UNION_INSERT : thm
    val BAG_UNION_LEFT_CANCEL : thm
    val BAG_UNION_RIGHT_CANCEL : thm
    val BAG_cases : thm
    val BCARD_0 : thm
    val BCARD_SUC : thm
    val BIG_BAG_UNION_DELETE : thm
    val BIG_BAG_UNION_EMPTY : thm
    val BIG_BAG_UNION_EQ_ELEMENT : thm
    val BIG_BAG_UNION_EQ_EMPTY_BAG : thm
    val BIG_BAG_UNION_INSERT : thm
    val BIG_BAG_UNION_ITSET_BAG_UNION : thm
    val BIG_BAG_UNION_UNION : thm
    val COMMUTING_ITBAG_INSERT : thm
    val COMMUTING_ITBAG_RECURSES : thm
    val COMM_BAG_UNION : thm
    val C_BAG_INSERT_ONE_ONE : thm
    val EL_BAG_11 : thm
    val EL_BAG_INSERT_squeeze : thm
    val EMPTY_BAG_alt : thm
    val FINITE_BAG_DIFF : thm
    val FINITE_BAG_DIFF_dual : thm
    val FINITE_BAG_FILTER : thm
    val FINITE_BAG_INDUCT : thm
    val FINITE_BAG_INSERT : thm
    val FINITE_BAG_THM : thm
    val FINITE_BAG_UNION : thm
    val FINITE_BIG_BAG_UNION : thm
    val FINITE_EMPTY_BAG : thm
    val FINITE_SET_OF_BAG : thm
    val FINITE_SUB_BAG : thm
    val IN_SET_OF_BAG : thm
    val ITBAG_EMPTY : thm
    val ITBAG_IND : thm
    val ITBAG_INSERT : thm
    val ITBAG_THM : thm
    val MEMBER_NOT_EMPTY : thm
    val NOT_BAG_IN : thm
    val NOT_IN_BAG_DIFF : thm
    val NOT_IN_EMPTY_BAG : thm
    val NOT_IN_SUB_BAG_INSERT : thm
    val PSUB_BAG_ANTISYM : thm
    val PSUB_BAG_CARD : thm
    val PSUB_BAG_IRREFL : thm
    val PSUB_BAG_NOT_EQ : thm
    val PSUB_BAG_REST : thm
    val PSUB_BAG_SUB_BAG : thm
    val PSUB_BAG_TRANS : thm
    val SET_BAG_I : thm
    val SET_OF_BAG_DIFF_SUBSET_down : thm
    val SET_OF_BAG_DIFF_SUBSET_up : thm
    val SET_OF_BAG_EQ_EMPTY : thm
    val SET_OF_BAG_EQ_INSERT : thm
    val SET_OF_BAG_IMAGE : thm
    val SET_OF_BAG_INSERT : thm
    val SET_OF_BAG_MERGE : thm
    val SET_OF_BAG_UNION : thm
    val SET_OF_EL_BAG : thm
    val SET_OF_EMPTY : thm
    val SING_BAG_THM : thm
    val SING_EL_BAG : thm
    val STRONG_FINITE_BAG_INDUCT : thm
    val SUB_BAG_ALL_DISTINCT : thm
    val SUB_BAG_ANTISYM : thm
    val SUB_BAG_BAG_DIFF : thm
    val SUB_BAG_BAG_IN : thm
    val SUB_BAG_CARD : thm
    val SUB_BAG_DIFF : thm
    val SUB_BAG_DIFF_EQ : thm
    val SUB_BAG_EL_BAG : thm
    val SUB_BAG_EMPTY : thm
    val SUB_BAG_EXISTS : thm
    val SUB_BAG_INSERT : thm
    val SUB_BAG_LEQ : thm
    val SUB_BAG_PSUB_BAG : thm
    val SUB_BAG_REFL : thm
    val SUB_BAG_REST : thm
    val SUB_BAG_SET : thm
    val SUB_BAG_TRANS : thm
    val SUB_BAG_UNION : thm
    val SUB_BAG_UNION_DIFF : thm
    val SUB_BAG_UNION_MONO : thm
    val SUB_BAG_UNION_down : thm
    val SUB_BAG_UNION_eliminate : thm
    val TC_mlt1_FINITE_BAG : thm
    val TC_mlt1_UNION1_I : thm
    val TC_mlt1_UNION2_I : thm
    val WF_mlt1 : thm
    val mlt1_all_accessible : thm
    val mlt_TO_EMPTY_BAG : thm
    val move_BAG_UNION_over_eq : thm

  val bag_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divides] Parent theory of "bag"

   [list] Parent theory of "bag"

   [BAG_ALL_DISTINCT]  Definition

      |- ∀b. BAG_ALL_DISTINCT b ⇔ ∀e. b e ≤ 1

   [BAG_CARD]  Definition

      |- ∀b. FINITE_BAG b ⇒ BAG_CARD_RELn b (BAG_CARD b)

   [BAG_CARD_RELn]  Definition

      |- ∀b n.
           BAG_CARD_RELn b n ⇔
           ∀P.
             P {||} 0 ∧ (∀b n. P b n ⇒ ∀e. P (BAG_INSERT e b) (SUC n)) ⇒
             P b n

   [BAG_CHOICE_DEF]  Definition

      |- ∀b. b ≠ {||} ⇒ BAG_CHOICE b ⋲ b

   [BAG_DELETE]  Definition

      |- ∀b0 e b. BAG_DELETE b0 e b ⇔ (b0 = BAG_INSERT e b)

   [BAG_DIFF]  Definition

      |- ∀b1 b2. b1 − b2 = (λx. b1 x − b2 x)

   [BAG_DISJOINT]  Definition

      |- ∀b1 b2.
           BAG_DISJOINT b1 b2 ⇔ DISJOINT (SET_OF_BAG b1) (SET_OF_BAG b2)

   [BAG_EVERY]  Definition

      |- ∀P b. BAG_EVERY P b ⇔ ∀e. e ⋲ b ⇒ P e

   [BAG_FILTER_DEF]  Definition

      |- ∀P b. BAG_FILTER P b = (λe. if P e then b e else 0)

   [BAG_GEN_PROD_def]  Definition

      |- ∀bag n. BAG_GEN_PROD bag n = ITBAG $* bag n

   [BAG_GEN_SUM_def]  Definition

      |- ∀bag n. BAG_GEN_SUM bag n = ITBAG $+ bag n

   [BAG_IMAGE_DEF]  Definition

      |- ∀f b.
           BAG_IMAGE f b =
           (λe.
              (let sb = BAG_FILTER (λe0. f e0 = e) b
               in
                 if FINITE_BAG sb then BAG_CARD sb else 1))

   [BAG_IN]  Definition

      |- ∀e b. e ⋲ b ⇔ BAG_INN e 1 b

   [BAG_INN]  Definition

      |- ∀e n b. BAG_INN e n b ⇔ b e ≥ n

   [BAG_INSERT]  Definition

      |- ∀e b. BAG_INSERT e b = (λx. if x = e then b e + 1 else b x)

   [BAG_INTER]  Definition

      |- ∀b1 b2. BAG_INTER b1 b2 = (λx. if b1 x < b2 x then b1 x else b2 x)

   [BAG_MERGE]  Definition

      |- ∀b1 b2. BAG_MERGE b1 b2 = (λx. if b1 x < b2 x then b2 x else b1 x)

   [BAG_OF_SET]  Definition

      |- ∀P. BAG_OF_SET P = (λx. if x ∈ P then 1 else 0)

   [BAG_REST_DEF]  Definition

      |- ∀b. BAG_REST b = b − EL_BAG (BAG_CHOICE b)

   [BAG_UNION]  Definition

      |- ∀b c. b ⊎ c = (λx. b x + c x)

   [BIG_BAG_UNION_def]  Definition

      |- ∀sob. BIG_BAG_UNION sob = (λx. ∑ (λb. b x) sob)

   [EL_BAG]  Definition

      |- ∀e. EL_BAG e = {|e|}

   [EMPTY_BAG]  Definition

      |- {||} = K 0

   [FINITE_BAG]  Definition

      |- ∀b.
           FINITE_BAG b ⇔
           ∀P. P {||} ∧ (∀b. P b ⇒ ∀e. P (BAG_INSERT e b)) ⇒ P b

   [ITBAG_curried_def]  Definition

      |- ∀f x x1. ITBAG f x x1 = ITBAG_tupled f (x,x1)

   [ITBAG_tupled_primitive_def]  Definition

      |- ∀f.
           ITBAG_tupled f =
           WFREC
             (@R.
                WF R ∧
                ∀acc b.
                  FINITE_BAG b ∧ b ≠ {||} ⇒
                  R (BAG_REST b,f (BAG_CHOICE b) acc) (b,acc))
             (λITBAG_tupled a.
                case a of
                  (b,acc) =>
                    I
                      (if FINITE_BAG b then
                         if b = {||} then
                           acc
                         else
                           ITBAG_tupled (BAG_REST b,f (BAG_CHOICE b) acc)
                       else
                         ARB))

   [PSUB_BAG]  Definition

      |- ∀b1 b2. b1 < b2 ⇔ b1 ≤ b2 ∧ b1 ≠ b2

   [SET_OF_BAG]  Definition

      |- ∀b. SET_OF_BAG b = (λx. x ⋲ b)

   [SING_BAG]  Definition

      |- ∀b. SING_BAG b ⇔ ∃x. b = {|x|}

   [SUB_BAG]  Definition

      |- ∀b1 b2. b1 ≤ b2 ⇔ ∀x n. BAG_INN x n b1 ⇒ BAG_INN x n b2

   [bag_size_def]  Definition

      |- ∀eltsize b.
           bag_size eltsize b = ITBAG (λe acc. 1 + eltsize e + acc) b 0

   [mlt1_def]  Definition

      |- ∀r b1 b2.
           mlt1 r b1 b2 ⇔
           FINITE_BAG b1 ∧ FINITE_BAG b2 ∧
           ∃e rep res.
             (b1 = rep ⊎ res) ∧ (b2 = res ⊎ {|e|}) ∧ ∀e'. e' ⋲ rep ⇒ r e' e

   [ASSOC_BAG_UNION]  Theorem

      |- ∀b1 b2 b3. b1 ⊎ (b2 ⊎ b3) = b1 ⊎ b2 ⊎ b3

   [BAG_ALL_DISTINCT_BAG_INN]  Theorem

      |- ∀b n e.
           BAG_ALL_DISTINCT b ⇒ (BAG_INN e n b ⇔ (n = 0) ∨ (n = 1) ∧ e ⋲ b)

   [BAG_ALL_DISTINCT_BAG_MERGE]  Theorem

      |- ∀b1 b2.
           BAG_ALL_DISTINCT (BAG_MERGE b1 b2) ⇔
           BAG_ALL_DISTINCT b1 ∧ BAG_ALL_DISTINCT b2

   [BAG_ALL_DISTINCT_BAG_OF_SET]  Theorem

      |- BAG_ALL_DISTINCT (BAG_OF_SET s)

   [BAG_ALL_DISTINCT_BAG_UNION]  Theorem

      |- ∀b1 b2.
           BAG_ALL_DISTINCT (b1 ⊎ b2) ⇔
           BAG_ALL_DISTINCT b1 ∧ BAG_ALL_DISTINCT b2 ∧ BAG_DISJOINT b1 b2

   [BAG_ALL_DISTINCT_DELETE]  Theorem

      |- BAG_ALL_DISTINCT b ⇔ ∀e. e ⋲ b ⇒ ¬(e ⋲ b − {|e|})

   [BAG_ALL_DISTINCT_DIFF]  Theorem

      |- ∀b1 b2. BAG_ALL_DISTINCT b1 ⇒ BAG_ALL_DISTINCT (b1 − b2)

   [BAG_ALL_DISTINCT_EXTENSION]  Theorem

      |- ∀b1 b2.
           BAG_ALL_DISTINCT b1 ∧ BAG_ALL_DISTINCT b2 ⇒
           ((b1 = b2) ⇔ ∀x. x ⋲ b1 ⇔ x ⋲ b2)

   [BAG_ALL_DISTINCT_SET]  Theorem

      |- BAG_ALL_DISTINCT b ⇔ (BAG_OF_SET (SET_OF_BAG b) = b)

   [BAG_ALL_DISTINCT_THM]  Theorem

      |- BAG_ALL_DISTINCT {||} ∧
         ∀e b.
           BAG_ALL_DISTINCT (BAG_INSERT e b) ⇔
           ¬(e ⋲ b) ∧ BAG_ALL_DISTINCT b

   [BAG_CARD_BAG_INN]  Theorem

      |- ∀b. FINITE_BAG b ⇒ ∀n e. BAG_INN e n b ⇒ n ≤ BAG_CARD b

   [BAG_CARD_EMPTY]  Theorem

      |- BAG_CARD {||} = 0

   [BAG_CARD_THM]  Theorem

      |- (BAG_CARD {||} = 0) ∧
         ∀b. FINITE_BAG b ⇒ ∀e. BAG_CARD (BAG_INSERT e b) = BAG_CARD b + 1

   [BAG_CARD_UNION]  Theorem

      |- ∀b1 b2.
           FINITE_BAG b1 ∧ FINITE_BAG b2 ⇒
           (BAG_CARD (b1 ⊎ b2) = BAG_CARD b1 + BAG_CARD b2)

   [BAG_CHOICE_SING]  Theorem

      |- BAG_CHOICE {|x|} = x

   [BAG_DECOMPOSE]  Theorem

      |- ∀e b. e ⋲ b ⇒ ∃b'. b = BAG_INSERT e b'

   [BAG_DELETE_11]  Theorem

      |- ∀b0 e1 e2 b1 b2.
           BAG_DELETE b0 e1 b1 ∧ BAG_DELETE b0 e2 b2 ⇒
           ((e1 = e2) ⇔ (b1 = b2))

   [BAG_DELETE_BAG_IN]  Theorem

      |- ∀b0 b e. BAG_DELETE b0 e b ⇒ e ⋲ b0

   [BAG_DELETE_BAG_IN_down]  Theorem

      |- ∀b0 b e1 e2. BAG_DELETE b0 e1 b ∧ e1 ≠ e2 ∧ e2 ⋲ b0 ⇒ e2 ⋲ b

   [BAG_DELETE_BAG_IN_up]  Theorem

      |- ∀b0 b e. BAG_DELETE b0 e b ⇒ ∀e'. e' ⋲ b ⇒ e' ⋲ b0

   [BAG_DELETE_EMPTY]  Theorem

      |- ∀e b. ¬BAG_DELETE {||} e b

   [BAG_DELETE_INSERT]  Theorem

      |- ∀x y b1 b2.
           BAG_DELETE (BAG_INSERT x b1) y b2 ⇒
           (x = y) ∧ (b1 = b2) ∨ (∃b3. BAG_DELETE b1 y b3) ∧ x ≠ y

   [BAG_DELETE_PSUB_BAG]  Theorem

      |- ∀b0 e b. BAG_DELETE b0 e b ⇒ b < b0

   [BAG_DELETE_SING]  Theorem

      |- ∀b e. BAG_DELETE b e {||} ⇒ SING_BAG b

   [BAG_DELETE_TWICE]  Theorem

      |- ∀b0 e1 e2 b1 b2.
           BAG_DELETE b0 e1 b1 ∧ BAG_DELETE b0 e2 b2 ∧ b1 ≠ b2 ⇒
           ∃b. BAG_DELETE b1 e2 b ∧ BAG_DELETE b2 e1 b

   [BAG_DELETE_commutes]  Theorem

      |- ∀b0 b1 b2 e1 e2.
           BAG_DELETE b0 e1 b1 ∧ BAG_DELETE b1 e2 b2 ⇒
           ∃b'. BAG_DELETE b0 e2 b' ∧ BAG_DELETE b' e1 b2

   [BAG_DELETE_concrete]  Theorem

      |- ∀b0 b e.
           BAG_DELETE b0 e b ⇔
           b0 e > 0 ∧ (b = (λx. if x = e then b0 e − 1 else b0 x))

   [BAG_DIFF_2L]  Theorem

      |- ∀X Y Z. X − Y − Z = X − (Y ⊎ Z)

   [BAG_DIFF_2R]  Theorem

      |- ∀A B C. C ≤ B ⇒ (A − (B − C) = A ⊎ C − B)

   [BAG_DIFF_EMPTY]  Theorem

      |- (∀b. b − b = {||}) ∧ (∀b. b − {||} = b) ∧ (∀b. {||} − b = {||}) ∧
         ∀b1 b2. b1 ≤ b2 ⇒ (b1 − b2 = {||})

   [BAG_DIFF_EMPTY_simple]  Theorem

      |- (∀b. b − b = {||}) ∧ (∀b. b − {||} = b) ∧ ∀b. {||} − b = {||}

   [BAG_DIFF_INSERT]  Theorem

      |- ∀x b1 b2.
           ¬(x ⋲ b1) ⇒ (BAG_INSERT x b2 − b1 = BAG_INSERT x (b2 − b1))

   [BAG_DIFF_INSERT_same]  Theorem

      |- ∀x b1 b2. BAG_INSERT x b1 − BAG_INSERT x b2 = b1 − b2

   [BAG_DIFF_UNION_eliminate]  Theorem

      |- ∀b1 b2 b3.
           (b1 ⊎ b2 − (b1 ⊎ b3) = b2 − b3) ∧
           (b1 ⊎ b2 − (b3 ⊎ b1) = b2 − b3) ∧
           (b2 ⊎ b1 − (b1 ⊎ b3) = b2 − b3) ∧
           (b2 ⊎ b1 − (b3 ⊎ b1) = b2 − b3)

   [BAG_DISJOINT_BAG_IN]  Theorem

      |- ∀b1 b2. BAG_DISJOINT b1 b2 ⇔ ∀e. ¬(e ⋲ b1) ∨ ¬(e ⋲ b2)

   [BAG_DISJOINT_BAG_INSERT]  Theorem

      |- (∀b1 b2 e1.
            BAG_DISJOINT (BAG_INSERT e1 b1) b2 ⇔
            ¬(e1 ⋲ b2) ∧ BAG_DISJOINT b1 b2) ∧
         ∀b1 b2 e2.
           BAG_DISJOINT b1 (BAG_INSERT e2 b2) ⇔
           ¬(e2 ⋲ b1) ∧ BAG_DISJOINT b1 b2

   [BAG_DISJOINT_DIFF]  Theorem

      |- ∀B1 B2. BAG_DISJOINT (B1 − B2) (B2 − B1)

   [BAG_DISJOINT_EMPTY]  Theorem

      |- ∀b. BAG_DISJOINT b {||} ∧ BAG_DISJOINT {||} b

   [BAG_EVERY_MERGE]  Theorem

      |- BAG_EVERY P (BAG_MERGE b1 b2) ⇔ BAG_EVERY P b1 ∧ BAG_EVERY P b2

   [BAG_EVERY_SET]  Theorem

      |- BAG_EVERY P b ⇔ SET_OF_BAG b ⊆ {x | P x}

   [BAG_EVERY_THM]  Theorem

      |- (∀P. BAG_EVERY P {||}) ∧
         ∀P e b. BAG_EVERY P (BAG_INSERT e b) ⇔ P e ∧ BAG_EVERY P b

   [BAG_EVERY_UNION]  Theorem

      |- BAG_EVERY P (b1 ⊎ b2) ⇔ BAG_EVERY P b1 ∧ BAG_EVERY P b2

   [BAG_EXTENSION]  Theorem

      |- ∀b1 b2. (b1 = b2) ⇔ ∀n e. BAG_INN e n b1 ⇔ BAG_INN e n b2

   [BAG_FILTER_BAG_INSERT]  Theorem

      |- BAG_FILTER P (BAG_INSERT e b) =
         if P e then BAG_INSERT e (BAG_FILTER P b) else BAG_FILTER P b

   [BAG_FILTER_EMPTY]  Theorem

      |- BAG_FILTER P {||} = {||}

   [BAG_FILTER_EQ_EMPTY]  Theorem

      |- (BAG_FILTER P b = {||}) ⇔ BAG_EVERY ($~ o P) b

   [BAG_GEN_PROD_ALL_ONES]  Theorem

      |- ∀b. FINITE_BAG b ⇒ (BAG_GEN_PROD b 1 = 1) ⇒ ∀x. x ⋲ b ⇒ (x = 1)

   [BAG_GEN_PROD_EMPTY]  Theorem

      |- ∀n. BAG_GEN_PROD {||} n = n

   [BAG_GEN_PROD_EQ_1]  Theorem

      |- ∀b. FINITE_BAG b ⇒ ∀e. (BAG_GEN_PROD b e = 1) ⇒ (e = 1)

   [BAG_GEN_PROD_POSITIVE]  Theorem

      |- ∀b. FINITE_BAG b ⇒ (∀x. x ⋲ b ⇒ 0 < x) ⇒ 0 < BAG_GEN_PROD b 1

   [BAG_GEN_PROD_REC]  Theorem

      |- ∀b.
           FINITE_BAG b ⇒
           ∀x a. BAG_GEN_PROD (BAG_INSERT x b) a = x * BAG_GEN_PROD b a

   [BAG_GEN_PROD_TAILREC]  Theorem

      |- ∀b.
           FINITE_BAG b ⇒
           ∀x a. BAG_GEN_PROD (BAG_INSERT x b) a = BAG_GEN_PROD b (x * a)

   [BAG_GEN_PROD_UNION]  Theorem

      |- ∀b1 b2.
           FINITE_BAG b1 ∧ FINITE_BAG b2 ⇒
           (BAG_GEN_PROD (b1 ⊎ b2) 1 =
            BAG_GEN_PROD b1 1 * BAG_GEN_PROD b2 1)

   [BAG_GEN_PROD_UNION_LEM]  Theorem

      |- ∀b1.
           FINITE_BAG b1 ⇒
           ∀b2 a b.
             FINITE_BAG b2 ⇒
             (BAG_GEN_PROD (b1 ⊎ b2) (a * b) =
              BAG_GEN_PROD b1 a * BAG_GEN_PROD b2 b)

   [BAG_GEN_SUM_EMPTY]  Theorem

      |- ∀n. BAG_GEN_SUM {||} n = n

   [BAG_GEN_SUM_REC]  Theorem

      |- ∀b.
           FINITE_BAG b ⇒
           ∀x a. BAG_GEN_SUM (BAG_INSERT x b) a = x + BAG_GEN_SUM b a

   [BAG_GEN_SUM_TAILREC]  Theorem

      |- ∀b.
           FINITE_BAG b ⇒
           ∀x a. BAG_GEN_SUM (BAG_INSERT x b) a = BAG_GEN_SUM b (x + a)

   [BAG_IMAGE_COMPOSE]  Theorem

      |- ∀f g b.
           FINITE_BAG b ⇒
           (BAG_IMAGE (f o g) b = BAG_IMAGE f (BAG_IMAGE g b))

   [BAG_IMAGE_EMPTY]  Theorem

      |- ∀f. BAG_IMAGE f {||} = {||}

   [BAG_IMAGE_FINITE]  Theorem

      |- ∀b. FINITE_BAG b ⇒ FINITE_BAG (BAG_IMAGE f b)

   [BAG_IMAGE_FINITE_I]  Theorem

      |- ∀b. FINITE_BAG b ⇒ (BAG_IMAGE I b = b)

   [BAG_IMAGE_FINITE_INSERT]  Theorem

      |- ∀b f e.
           FINITE_BAG b ⇒
           (BAG_IMAGE f (BAG_INSERT e b) =
            BAG_INSERT (f e) (BAG_IMAGE f b))

   [BAG_IMAGE_FINITE_RESTRICTED_I]  Theorem

      |- ∀b. FINITE_BAG b ∧ BAG_EVERY (λe. f e = e) b ⇒ (BAG_IMAGE f b = b)

   [BAG_IMAGE_FINITE_UNION]  Theorem

      |- ∀b1 b2 f.
           FINITE_BAG b1 ∧ FINITE_BAG b2 ⇒
           (BAG_IMAGE f (b1 ⊎ b2) = BAG_IMAGE f b1 ⊎ BAG_IMAGE f b2)

   [BAG_INN_0]  Theorem

      |- ∀b e. BAG_INN e 0 b

   [BAG_INN_BAG_DELETE]  Theorem

      |- ∀b n e. BAG_INN e n b ∧ n > 0 ⇒ ∃b'. BAG_DELETE b e b'

   [BAG_INN_BAG_FILTER]  Theorem

      |- BAG_INN e n (BAG_FILTER P b) ⇔ (n = 0) ∨ P e ∧ BAG_INN e n b

   [BAG_INN_BAG_INSERT]  Theorem

      |- ∀b e1 e2.
           BAG_INN e1 n (BAG_INSERT e2 b) ⇔
           BAG_INN e1 (n − 1) b ∧ (e1 = e2) ∨ BAG_INN e1 n b

   [BAG_INN_BAG_INSERT_STRONG]  Theorem

      |- ∀b n e1 e2.
           BAG_INN e1 n (BAG_INSERT e2 b) ⇔
           BAG_INN e1 (n − 1) b ∧ (e1 = e2) ∨ BAG_INN e1 n b ∧ e1 ≠ e2

   [BAG_INN_BAG_MERGE]  Theorem

      |- ∀n e b1 b2.
           BAG_INN e n (BAG_MERGE b1 b2) ⇔ BAG_INN e n b1 ∨ BAG_INN e n b2

   [BAG_INN_BAG_UNION]  Theorem

      |- ∀n e b1 b2.
           BAG_INN e n (b1 ⊎ b2) ⇔
           ∃m1 m2. (n = m1 + m2) ∧ BAG_INN e m1 b1 ∧ BAG_INN e m2 b2

   [BAG_INN_EMPTY_BAG]  Theorem

      |- ∀e n. BAG_INN e n {||} ⇔ (n = 0)

   [BAG_INN_LESS]  Theorem

      |- ∀b e n m. BAG_INN e n b ∧ m < n ⇒ BAG_INN e m b

   [BAG_INSERT_CHOICE_REST]  Theorem

      |- ∀b. b ≠ {||} ⇒ (b = BAG_INSERT (BAG_CHOICE b) (BAG_REST b))

   [BAG_INSERT_DIFF]  Theorem

      |- ∀x b. BAG_INSERT x b ≠ b

   [BAG_INSERT_EQUAL]  Theorem

      |- (BAG_INSERT a M = BAG_INSERT b N) ⇔
         (M = N) ∧ (a = b) ∨
         ∃k. (M = BAG_INSERT b k) ∧ (N = BAG_INSERT a k)

   [BAG_INSERT_EQ_UNION]  Theorem

      |- ∀e b1 b2 b. (BAG_INSERT e b = b1 ⊎ b2) ⇒ e ⋲ b1 ∨ e ⋲ b2

   [BAG_INSERT_NOT_EMPTY]  Theorem

      |- ∀x b. BAG_INSERT x b ≠ {||}

   [BAG_INSERT_ONE_ONE]  Theorem

      |- ∀b1 b2 x. (BAG_INSERT x b1 = BAG_INSERT x b2) ⇔ (b1 = b2)

   [BAG_INSERT_UNION]  Theorem

      |- ∀b e. BAG_INSERT e b = EL_BAG e ⊎ b

   [BAG_INSERT_commutes]  Theorem

      |- ∀b e1 e2.
           BAG_INSERT e1 (BAG_INSERT e2 b) =
           BAG_INSERT e2 (BAG_INSERT e1 b)

   [BAG_IN_BAG_DELETE]  Theorem

      |- ∀b e. e ⋲ b ⇒ ∃b'. BAG_DELETE b e b'

   [BAG_IN_BAG_DIFF_ALL_DISTINCT]  Theorem

      |- ∀b1 b2 e. BAG_ALL_DISTINCT b1 ⇒ (e ⋲ b1 − b2 ⇔ e ⋲ b1 ∧ ¬(e ⋲ b2))

   [BAG_IN_BAG_FILTER]  Theorem

      |- e ⋲ BAG_FILTER P b ⇔ P e ∧ e ⋲ b

   [BAG_IN_BAG_INSERT]  Theorem

      |- ∀b e1 e2. e1 ⋲ BAG_INSERT e2 b ⇔ (e1 = e2) ∨ e1 ⋲ b

   [BAG_IN_BAG_MERGE]  Theorem

      |- ∀e b1 b2. e ⋲ BAG_MERGE b1 b2 ⇔ e ⋲ b1 ∨ e ⋲ b2

   [BAG_IN_BAG_OF_SET]  Theorem

      |- ∀P p. p ⋲ BAG_OF_SET P ⇔ p ∈ P

   [BAG_IN_BAG_UNION]  Theorem

      |- ∀b1 b2 e. e ⋲ b1 ⊎ b2 ⇔ e ⋲ b1 ∨ e ⋲ b2

   [BAG_IN_BIG_BAG_UNION]  Theorem

      |- FINITE P ⇒ (e ⋲ BIG_BAG_UNION P ⇔ ∃b. e ⋲ b ∧ b ∈ P)

   [BAG_IN_DIFF_E]  Theorem

      |- e ⋲ b1 − b2 ⇒ e ⋲ b1

   [BAG_IN_DIFF_I]  Theorem

      |- e ⋲ b1 ∧ ¬(e ⋲ b2) ⇒ e ⋲ b1 − b2

   [BAG_IN_DIVIDES]  Theorem

      |- ∀b x a. FINITE_BAG b ∧ x ⋲ b ⇒ divides x (BAG_GEN_PROD b a)

   [BAG_IN_FINITE_BAG_IMAGE]  Theorem

      |- FINITE_BAG b ⇒ (x ⋲ BAG_IMAGE f b ⇔ ∃y. (f y = x) ∧ y ⋲ b)

   [BAG_LESS_ADD]  Theorem

      |- mlt1 r N (M0 ⊎ {|a|}) ⇒
         (∃M. mlt1 r M M0 ∧ (N = M ⊎ {|a|})) ∨
         ∃KK. (∀b. b ⋲ KK ⇒ r b a) ∧ (N = M0 ⊎ KK)

   [BAG_MERGE_IDEM]  Theorem

      |- ∀b. BAG_MERGE b b = b

   [BAG_NOT_LESS_EMPTY]  Theorem

      |- ¬mlt1 r b {||}

   [BAG_OF_EMPTY]  Theorem

      |- SET_OF_BAG {||} = ∅

   [BAG_REST_SING]  Theorem

      |- BAG_REST {|x|} = {||}

   [BAG_SIZE_EMPTY]  Theorem

      |- bag_size eltsize {||} = 0

   [BAG_SIZE_INSERT]  Theorem

      |- FINITE_BAG b ⇒
         (bag_size eltsize (BAG_INSERT e b) =
          1 + eltsize e + bag_size eltsize b)

   [BAG_UNION_DIFF]  Theorem

      |- ∀X Y Z.
           Z ≤ Y ⇒ (X ⊎ (Y − Z) = X ⊎ Y − Z) ∧ (Y − Z ⊎ X = X ⊎ Y − Z)

   [BAG_UNION_DIFF_eliminate]  Theorem

      |- (b ⊎ c − c = b) ∧ (c ⊎ b − c = b)

   [BAG_UNION_EMPTY]  Theorem

      |- (∀b. b ⊎ {||} = b) ∧ (∀b. {||} ⊎ b = b) ∧
         ∀b1 b2. (b1 ⊎ b2 = {||}) ⇔ (b1 = {||}) ∧ (b2 = {||})

   [BAG_UNION_EQ_LEFT]  Theorem

      |- ∀b c d. (b ⊎ c = b ⊎ d) ⇒ (c = d)

   [BAG_UNION_INSERT]  Theorem

      |- ∀e b1 b2.
           (BAG_INSERT e b1 ⊎ b2 = BAG_INSERT e (b1 ⊎ b2)) ∧
           (b1 ⊎ BAG_INSERT e b2 = BAG_INSERT e (b1 ⊎ b2))

   [BAG_UNION_LEFT_CANCEL]  Theorem

      |- ∀b b1 b2. (b ⊎ b1 = b ⊎ b2) ⇔ (b1 = b2)

   [BAG_UNION_RIGHT_CANCEL]  Theorem

      |- ∀b b1 b2. (b1 ⊎ b = b2 ⊎ b) ⇔ (b1 = b2)

   [BAG_cases]  Theorem

      |- ∀b. (b = {||}) ∨ ∃b0 e. b = BAG_INSERT e b0

   [BCARD_0]  Theorem

      |- ∀b. FINITE_BAG b ⇒ ((BAG_CARD b = 0) ⇔ (b = {||}))

   [BCARD_SUC]  Theorem

      |- ∀b.
           FINITE_BAG b ⇒
           ∀n.
             (BAG_CARD b = SUC n) ⇔
             ∃b0 e. (b = BAG_INSERT e b0) ∧ (BAG_CARD b0 = n)

   [BIG_BAG_UNION_DELETE]  Theorem

      |- FINITE sob ⇒
         (BIG_BAG_UNION (sob DELETE b) =
          if b ∈ sob then BIG_BAG_UNION sob − b else BIG_BAG_UNION sob)

   [BIG_BAG_UNION_EMPTY]  Theorem

      |- BIG_BAG_UNION ∅ = {||}

   [BIG_BAG_UNION_EQ_ELEMENT]  Theorem

      |- FINITE sob ∧ b ∈ sob ⇒
         ((BIG_BAG_UNION sob = b) ⇔ ∀b'. b' ∈ sob ⇒ (b' = b) ∨ (b' = {||}))

   [BIG_BAG_UNION_EQ_EMPTY_BAG]  Theorem

      |- ∀sob.
           FINITE sob ⇒
           ((BIG_BAG_UNION sob = {||}) ⇔ ∀b. b ∈ sob ⇒ (b = {||}))

   [BIG_BAG_UNION_INSERT]  Theorem

      |- FINITE sob ⇒
         (BIG_BAG_UNION (b INSERT sob) = b ⊎ BIG_BAG_UNION (sob DELETE b))

   [BIG_BAG_UNION_ITSET_BAG_UNION]  Theorem

      |- ∀sob. FINITE sob ⇒ (BIG_BAG_UNION sob = ITSET $⊎ sob {||})

   [BIG_BAG_UNION_UNION]  Theorem

      |- FINITE s1 ∧ FINITE s2 ⇒
         (BIG_BAG_UNION (s1 ∪ s2) =
          BIG_BAG_UNION s1 ⊎ BIG_BAG_UNION s2 − BIG_BAG_UNION (s1 ∩ s2))

   [COMMUTING_ITBAG_INSERT]  Theorem

      |- ∀f b.
           (∀x y z. f x (f y z) = f y (f x z)) ∧ FINITE_BAG b ⇒
           ∀x a. ITBAG f (BAG_INSERT x b) a = ITBAG f b (f x a)

   [COMMUTING_ITBAG_RECURSES]  Theorem

      |- ∀f e b a.
           (∀x y z. f x (f y z) = f y (f x z)) ∧ FINITE_BAG b ⇒
           (ITBAG f (BAG_INSERT e b) a = f e (ITBAG f b a))

   [COMM_BAG_UNION]  Theorem

      |- ∀b1 b2. b1 ⊎ b2 = b2 ⊎ b1

   [C_BAG_INSERT_ONE_ONE]  Theorem

      |- ∀x y b. (BAG_INSERT x b = BAG_INSERT y b) ⇔ (x = y)

   [EL_BAG_11]  Theorem

      |- ∀x y. (EL_BAG x = EL_BAG y) ⇒ (x = y)

   [EL_BAG_INSERT_squeeze]  Theorem

      |- ∀x b y. (EL_BAG x = BAG_INSERT y b) ⇒ (x = y) ∧ (b = {||})

   [EMPTY_BAG_alt]  Theorem

      |- {||} = (λx. 0)

   [FINITE_BAG_DIFF]  Theorem

      |- ∀b1. FINITE_BAG b1 ⇒ ∀b2. FINITE_BAG (b1 − b2)

   [FINITE_BAG_DIFF_dual]  Theorem

      |- ∀b1. FINITE_BAG b1 ⇒ ∀b2. FINITE_BAG (b2 − b1) ⇒ FINITE_BAG b2

   [FINITE_BAG_FILTER]  Theorem

      |- ∀b. FINITE_BAG b ⇒ FINITE_BAG (BAG_FILTER P b)

   [FINITE_BAG_INDUCT]  Theorem

      |- ∀P.
           P {||} ∧ (∀b. P b ⇒ ∀e. P (BAG_INSERT e b)) ⇒
           ∀b. FINITE_BAG b ⇒ P b

   [FINITE_BAG_INSERT]  Theorem

      |- ∀b. FINITE_BAG b ⇒ ∀e. FINITE_BAG (BAG_INSERT e b)

   [FINITE_BAG_THM]  Theorem

      |- FINITE_BAG {||} ∧ ∀e b. FINITE_BAG (BAG_INSERT e b) ⇔ FINITE_BAG b

   [FINITE_BAG_UNION]  Theorem

      |- ∀b1 b2. FINITE_BAG (b1 ⊎ b2) ⇔ FINITE_BAG b1 ∧ FINITE_BAG b2

   [FINITE_BIG_BAG_UNION]  Theorem

      |- ∀sob.
           FINITE sob ∧ (∀b. b ∈ sob ⇒ FINITE_BAG b) ⇒
           FINITE_BAG (BIG_BAG_UNION sob)

   [FINITE_EMPTY_BAG]  Theorem

      |- FINITE_BAG {||}

   [FINITE_SET_OF_BAG]  Theorem

      |- ∀b. FINITE (SET_OF_BAG b) ⇔ FINITE_BAG b

   [FINITE_SUB_BAG]  Theorem

      |- ∀b1. FINITE_BAG b1 ⇒ ∀b2. b2 ≤ b1 ⇒ FINITE_BAG b2

   [IN_SET_OF_BAG]  Theorem

      |- ∀x b. x ∈ SET_OF_BAG b ⇔ x ⋲ b

   [ITBAG_EMPTY]  Theorem

      |- ∀f acc. ITBAG f {||} acc = acc

   [ITBAG_IND]  Theorem

      |- ∀P.
           (∀b acc.
              (FINITE_BAG b ∧ b ≠ {||} ⇒
               P (BAG_REST b) (f (BAG_CHOICE b) acc)) ⇒
              P b acc) ⇒
           ∀v v1. P v v1

   [ITBAG_INSERT]  Theorem

      |- ∀f acc.
           FINITE_BAG b ⇒
           (ITBAG f (BAG_INSERT x b) acc =
            ITBAG f (BAG_REST (BAG_INSERT x b))
              (f (BAG_CHOICE (BAG_INSERT x b)) acc))

   [ITBAG_THM]  Theorem

      |- ∀b f acc.
           FINITE_BAG b ⇒
           (ITBAG f b acc =
            if b = {||} then
              acc
            else
              ITBAG f (BAG_REST b) (f (BAG_CHOICE b) acc))

   [MEMBER_NOT_EMPTY]  Theorem

      |- ∀b. (∃x. x ⋲ b) ⇔ b ≠ {||}

   [NOT_BAG_IN]  Theorem

      |- ∀b x. (b x = 0) ⇔ ¬(x ⋲ b)

   [NOT_IN_BAG_DIFF]  Theorem

      |- ∀x b1 b2. ¬(x ⋲ b1) ⇒ (b1 − BAG_INSERT x b2 = b1 − b2)

   [NOT_IN_EMPTY_BAG]  Theorem

      |- ∀x. ¬(x ⋲ {||})

   [NOT_IN_SUB_BAG_INSERT]  Theorem

      |- ∀b1 b2 e. ¬(e ⋲ b1) ⇒ (b1 ≤ BAG_INSERT e b2 ⇔ b1 ≤ b2)

   [PSUB_BAG_ANTISYM]  Theorem

      |- ∀b1 b2. ¬(b1 < b2 ∧ b2 < b1)

   [PSUB_BAG_CARD]  Theorem

      |- ∀b1 b2. FINITE_BAG b2 ∧ b1 < b2 ⇒ BAG_CARD b1 < BAG_CARD b2

   [PSUB_BAG_IRREFL]  Theorem

      |- ∀b. ¬(b < b)

   [PSUB_BAG_NOT_EQ]  Theorem

      |- ∀b1 b2. b1 < b2 ⇒ b1 ≠ b2

   [PSUB_BAG_REST]  Theorem

      |- ∀b. b ≠ {||} ⇒ BAG_REST b < b

   [PSUB_BAG_SUB_BAG]  Theorem

      |- ∀b1 b2. b1 < b2 ⇒ b1 ≤ b2

   [PSUB_BAG_TRANS]  Theorem

      |- ∀b1 b2 b3. b1 < b2 ∧ b2 < b3 ⇒ b1 < b3

   [SET_BAG_I]  Theorem

      |- ∀s. SET_OF_BAG (BAG_OF_SET s) = s

   [SET_OF_BAG_DIFF_SUBSET_down]  Theorem

      |- ∀b1 b2. SET_OF_BAG b1 DIFF SET_OF_BAG b2 ⊆ SET_OF_BAG (b1 − b2)

   [SET_OF_BAG_DIFF_SUBSET_up]  Theorem

      |- ∀b1 b2. SET_OF_BAG (b1 − b2) ⊆ SET_OF_BAG b1

   [SET_OF_BAG_EQ_EMPTY]  Theorem

      |- ∀b.
           ((∅ = SET_OF_BAG b) ⇔ (b = {||})) ∧
           ((SET_OF_BAG b = ∅) ⇔ (b = {||}))

   [SET_OF_BAG_EQ_INSERT]  Theorem

      |- ∀b e s.
           (e INSERT s = SET_OF_BAG b) ⇔
           ∃b0 eb.
             (b = eb ⊎ b0) ∧ (s = SET_OF_BAG b0) ∧
             (∀e'. e' ⋲ eb ⇒ (e' = e)) ∧ (e ∉ s ⇒ e ⋲ eb)

   [SET_OF_BAG_IMAGE]  Theorem

      |- SET_OF_BAG (BAG_IMAGE f b) = IMAGE f (SET_OF_BAG b)

   [SET_OF_BAG_INSERT]  Theorem

      |- ∀e b. SET_OF_BAG (BAG_INSERT e b) = e INSERT SET_OF_BAG b

   [SET_OF_BAG_MERGE]  Theorem

      |- ∀b1 b2.
           SET_OF_BAG (BAG_MERGE b1 b2) = SET_OF_BAG b1 ∪ SET_OF_BAG b2

   [SET_OF_BAG_UNION]  Theorem

      |- ∀b1 b2. SET_OF_BAG (b1 ⊎ b2) = SET_OF_BAG b1 ∪ SET_OF_BAG b2

   [SET_OF_EL_BAG]  Theorem

      |- ∀e. SET_OF_BAG (EL_BAG e) = {e}

   [SET_OF_EMPTY]  Theorem

      |- BAG_OF_SET ∅ = {||}

   [SING_BAG_THM]  Theorem

      |- ∀e. SING_BAG {|e|}

   [SING_EL_BAG]  Theorem

      |- ∀e. SING_BAG (EL_BAG e)

   [STRONG_FINITE_BAG_INDUCT]  Theorem

      |- ∀P.
           P {||} ∧ (∀b. FINITE_BAG b ∧ P b ⇒ ∀e. P (BAG_INSERT e b)) ⇒
           ∀b. FINITE_BAG b ⇒ P b

   [SUB_BAG_ALL_DISTINCT]  Theorem

      |- ∀b1 b2. BAG_ALL_DISTINCT b1 ⇒ (b1 ≤ b2 ⇔ ∀x. x ⋲ b1 ⇒ x ⋲ b2)

   [SUB_BAG_ANTISYM]  Theorem

      |- ∀b1 b2. b1 ≤ b2 ∧ b2 ≤ b1 ⇒ (b1 = b2)

   [SUB_BAG_BAG_DIFF]  Theorem

      |- ∀X Y Y' Z W. X − Y ≤ Z − W ⇒ X − (Y ⊎ Y') ≤ Z − (W ⊎ Y')

   [SUB_BAG_BAG_IN]  Theorem

      |- ∀x b1 b2. BAG_INSERT x b1 ≤ b2 ⇒ x ⋲ b2

   [SUB_BAG_CARD]  Theorem

      |- ∀b1 b2. FINITE_BAG b2 ∧ b1 ≤ b2 ⇒ BAG_CARD b1 ≤ BAG_CARD b2

   [SUB_BAG_DIFF]  Theorem

      |- (∀b1 b2. b1 ≤ b2 ⇒ ∀b3. b1 − b3 ≤ b2) ∧
         ∀b1 b2 b3 b4.
           b2 ≤ b1 ⇒ b4 ≤ b3 ⇒ (b1 − b2 ≤ b3 − b4 ⇔ b1 ⊎ b4 ≤ b2 ⊎ b3)

   [SUB_BAG_DIFF_EQ]  Theorem

      |- ∀b1 b2. b1 ≤ b2 ⇒ (b2 = b1 ⊎ (b2 − b1))

   [SUB_BAG_EL_BAG]  Theorem

      |- ∀e b. EL_BAG e ≤ b ⇔ e ⋲ b

   [SUB_BAG_EMPTY]  Theorem

      |- (∀b. {||} ≤ b) ∧ ∀b. b ≤ {||} ⇔ (b = {||})

   [SUB_BAG_EXISTS]  Theorem

      |- ∀b1 b2. b1 ≤ b2 ⇔ ∃b. b2 = b1 ⊎ b

   [SUB_BAG_INSERT]  Theorem

      |- ∀e b1 b2. BAG_INSERT e b1 ≤ BAG_INSERT e b2 ⇔ b1 ≤ b2

   [SUB_BAG_LEQ]  Theorem

      |- b1 ≤ b2 ⇔ ∀x. b1 x ≤ b2 x

   [SUB_BAG_PSUB_BAG]  Theorem

      |- ∀b1 b2. b1 ≤ b2 ⇔ b1 < b2 ∨ (b1 = b2)

   [SUB_BAG_REFL]  Theorem

      |- ∀b. b ≤ b

   [SUB_BAG_REST]  Theorem

      |- ∀b. BAG_REST b ≤ b

   [SUB_BAG_SET]  Theorem

      |- ∀b1 b2. b1 ≤ b2 ⇒ SET_OF_BAG b1 ⊆ SET_OF_BAG b2

   [SUB_BAG_TRANS]  Theorem

      |- ∀b1 b2 b3. b1 ≤ b2 ∧ b2 ≤ b3 ⇒ b1 ≤ b3

   [SUB_BAG_UNION]  Theorem

      |- (∀b1 b2. b1 ≤ b2 ⇒ ∀b. b1 ≤ b2 ⊎ b) ∧
         (∀b1 b2. b1 ≤ b2 ⇒ ∀b. b1 ≤ b ⊎ b2) ∧
         (∀b1 b2 b3. b1 ≤ b2 ⊎ b3 ⇒ ∀b. b1 ≤ b2 ⊎ b ⊎ b3) ∧
         (∀b1 b2 b3. b1 ≤ b2 ⊎ b3 ⇒ ∀b. b1 ≤ b ⊎ b2 ⊎ b3) ∧
         (∀b1 b2 b3. b1 ≤ b3 ⊎ b2 ⇒ ∀b. b1 ≤ b3 ⊎ (b2 ⊎ b)) ∧
         (∀b1 b2 b3. b1 ≤ b3 ⊎ b2 ⇒ ∀b. b1 ≤ b3 ⊎ (b ⊎ b2)) ∧
         (∀b1 b2 b3 b4. b1 ≤ b3 ⇒ b2 ≤ b4 ⇒ b1 ⊎ b2 ≤ b3 ⊎ b4) ∧
         (∀b1 b2 b3 b4. b1 ≤ b4 ⇒ b2 ≤ b3 ⇒ b1 ⊎ b2 ≤ b3 ⊎ b4) ∧
         (∀b1 b2 b3 b4 b5.
            b1 ≤ b3 ⊎ b5 ⇒ b2 ≤ b4 ⇒ b1 ⊎ b2 ≤ b3 ⊎ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b1 ≤ b4 ⊎ b5 ⇒ b2 ≤ b3 ⇒ b1 ⊎ b2 ≤ b3 ⊎ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b2 ≤ b3 ⊎ b5 ⇒ b1 ≤ b4 ⇒ b1 ⊎ b2 ≤ b3 ⊎ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b2 ≤ b4 ⊎ b5 ⇒ b1 ≤ b3 ⇒ b1 ⊎ b2 ≤ b3 ⊎ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b1 ≤ b5 ⊎ b3 ⇒ b2 ≤ b4 ⇒ b2 ⊎ b1 ≤ b5 ⊎ (b3 ⊎ b4)) ∧
         (∀b1 b2 b3 b4 b5.
            b1 ≤ b5 ⊎ b4 ⇒ b2 ≤ b3 ⇒ b2 ⊎ b1 ≤ b5 ⊎ (b3 ⊎ b4)) ∧
         (∀b1 b2 b3 b4 b5.
            b2 ≤ b5 ⊎ b3 ⇒ b1 ≤ b4 ⇒ b2 ⊎ b1 ≤ b5 ⊎ (b3 ⊎ b4)) ∧
         (∀b1 b2 b3 b4 b5.
            b2 ≤ b5 ⊎ b4 ⇒ b1 ≤ b3 ⇒ b2 ⊎ b1 ≤ b5 ⊎ (b3 ⊎ b4)) ∧
         (∀b1 b2 b3 b4 b5.
            b1 ⊎ b2 ≤ b4 ⇒ b3 ≤ b5 ⇒ b1 ⊎ b3 ⊎ b2 ≤ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b1 ⊎ b2 ≤ b5 ⇒ b3 ≤ b4 ⇒ b1 ⊎ b3 ⊎ b2 ≤ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b3 ⊎ b2 ≤ b4 ⇒ b1 ≤ b5 ⇒ b1 ⊎ b3 ⊎ b2 ≤ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b3 ⊎ b2 ≤ b5 ⇒ b1 ≤ b4 ⇒ b1 ⊎ b3 ⊎ b2 ≤ b4 ⊎ b5) ∧
         (∀b1 b2 b3 b4 b5.
            b2 ⊎ b1 ≤ b4 ⇒ b3 ≤ b5 ⇒ b2 ⊎ (b1 ⊎ b3) ≤ b5 ⊎ b4) ∧
         (∀b1 b2 b3 b4 b5.
            b2 ⊎ b1 ≤ b5 ⇒ b3 ≤ b4 ⇒ b2 ⊎ (b1 ⊎ b3) ≤ b5 ⊎ b4) ∧
         (∀b1 b2 b3 b4 b5.
            b2 ⊎ b3 ≤ b4 ⇒ b1 ≤ b5 ⇒ b2 ⊎ (b1 ⊎ b3) ≤ b5 ⊎ b4) ∧
         ∀b1 b2 b3 b4 b5. b2 ⊎ b3 ≤ b5 ⇒ b1 ≤ b4 ⇒ b2 ⊎ (b1 ⊎ b3) ≤ b5 ⊎ b4

   [SUB_BAG_UNION_DIFF]  Theorem

      |- ∀b1 b2 b3. b1 ≤ b3 ⇒ (b2 ≤ b3 − b1 ⇔ b1 ⊎ b2 ≤ b3)

   [SUB_BAG_UNION_MONO]  Theorem

      |- ∀x y. x ≤ x ⊎ y

   [SUB_BAG_UNION_down]  Theorem

      |- ∀b1 b2 b3. b1 ⊎ b2 ≤ b3 ⇒ b1 ≤ b3 ∧ b2 ≤ b3

   [SUB_BAG_UNION_eliminate]  Theorem

      |- ∀b1 b2 b3.
           (b1 ⊎ b2 ≤ b1 ⊎ b3 ⇔ b2 ≤ b3) ∧ (b1 ⊎ b2 ≤ b3 ⊎ b1 ⇔ b2 ≤ b3) ∧
           (b2 ⊎ b1 ≤ b1 ⊎ b3 ⇔ b2 ≤ b3) ∧ (b2 ⊎ b1 ≤ b3 ⊎ b1 ⇔ b2 ≤ b3)

   [TC_mlt1_FINITE_BAG]  Theorem

      |- ∀b1 b2. mlt R b1 b2 ⇒ FINITE_BAG b1 ∧ FINITE_BAG b2

   [TC_mlt1_UNION1_I]  Theorem

      |- ∀b2 b1.
           FINITE_BAG b2 ∧ FINITE_BAG b1 ∧ b1 ≠ {||} ⇒ mlt R b2 (b1 ⊎ b2)

   [TC_mlt1_UNION2_I]  Theorem

      |- ∀b2 b1.
           FINITE_BAG b2 ∧ FINITE_BAG b1 ∧ b2 ≠ {||} ⇒ mlt R b1 (b1 ⊎ b2)

   [WF_mlt1]  Theorem

      |- WF R ⇒ WF (mlt1 R)

   [mlt1_all_accessible]  Theorem

      |- WF R ⇒ ∀M. WFP (mlt1 R) M

   [mlt_TO_EMPTY_BAG]  Theorem

      |- FINITE_BAG b2 ∧ b2 ≠ {||} ⇒ mlt r {||} b2

   [move_BAG_UNION_over_eq]  Theorem

      |- ∀X Y Z. (X ⊎ Y = Z) ⇒ (X = Z − Y)


*)
end
