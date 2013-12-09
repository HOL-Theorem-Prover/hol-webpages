signature util_probTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val DFUNSET_def : thm
    val FUNSET_def : thm
    val PREIMAGE_def : thm
    val countable_def : thm
    val enumerate_def : thm
    val lg_def : thm
    val logr_def : thm
    val minimal_def : thm
    val pair_def : thm
    val powr_def : thm
    val prod_sets_def : thm
    val schroeder_close_def : thm

  (*  Theorems  *)
    val BIGINTER_SUBSET : thm
    val BIGUNION_IMAGE_UNIV : thm
    val BIGUNION_PAIR : thm
    val BIJ_ALT : thm
    val BIJ_FINITE_SUBSET : thm
    val BIJ_INJ_SURJ : thm
    val BIJ_INSERT : thm
    val BIJ_INV : thm
    val BIJ_NUM_COUNTABLE : thm
    val BIJ_SYM : thm
    val BIJ_SYM_IMP : thm
    val BIJ_TRANS : thm
    val COUNTABLE_ALT : thm
    val COUNTABLE_BIGUNION : thm
    val COUNTABLE_COUNT : thm
    val COUNTABLE_EMPTY : thm
    val COUNTABLE_ENUM : thm
    val COUNTABLE_IMAGE : thm
    val COUNTABLE_IMAGE_NUM : thm
    val COUNTABLE_NUM : thm
    val COUNTABLE_SUBSET : thm
    val COUNTABLE_UNION : thm
    val DELETE_THEN_INSERT : thm
    val DIFF_BIGINTER : thm
    val DIFF_BIGINTER1 : thm
    val DIFF_DIFF_SUBSET : thm
    val DIFF_INTER : thm
    val DIFF_INTER2 : thm
    val DISJOINT_ALT : thm
    val DISJOINT_COUNT : thm
    val DISJOINT_DIFF : thm
    val DISJOINT_DIFFS : thm
    val ELT_IN_DELETE : thm
    val EMPTY_FUNSET : thm
    val ENUMERATE : thm
    val EQ_SUBSET_SUBSET : thm
    val EQ_T_IMP : thm
    val EXPLICIT_ENUMERATE_MONO : thm
    val EXPLICIT_ENUMERATE_NOT_EMPTY : thm
    val FINITE_BIJ : thm
    val FINITE_BIJ_COUNT : thm
    val FINITE_COUNTABLE : thm
    val FINITE_INJ : thm
    val FINITE_REST : thm
    val FUNSET_DFUNSET : thm
    val FUNSET_EMPTY : thm
    val FUNSET_INTER : thm
    val FUNSET_THM : thm
    val GBIGUNION_IMAGE : thm
    val HALF_CANCEL : thm
    val HALF_LT_1 : thm
    val HALF_POS : thm
    val IMAGE_I : thm
    val IMAGE_IMAGE : thm
    val INCREASING_SEQ : thm
    val INFINITE_EXPLICIT_ENUMERATE : thm
    val INFINITE_INJ : thm
    val INF_CLOSE : thm
    val INF_DEF_ALT : thm
    val INF_GREATER : thm
    val INF_LE : thm
    val INJ_IMAGE_BIJ : thm
    val IN_BIGINTER_IMAGE : thm
    val IN_BIGUNION_IMAGE : thm
    val IN_DFUNSET : thm
    val IN_EQ_UNIV_IMP : thm
    val IN_FUNSET : thm
    val IN_PAIR : thm
    val IN_PREIMAGE : thm
    val IN_PROD_SETS : thm
    val IN_o : thm
    val K_PARTIAL : thm
    val K_SUBSET : thm
    val LE_INF : thm
    val LE_SUC : thm
    val LT_SUC : thm
    val MAX_LE_X : thm
    val MINIMAL_EXISTS : thm
    val MINIMAL_EXISTS0 : thm
    val NUM_2D_BIJ : thm
    val NUM_2D_BIJ_BIG_SQUARE : thm
    val NUM_2D_BIJ_INV : thm
    val NUM_2D_BIJ_NZ : thm
    val NUM_2D_BIJ_NZ_ALT : thm
    val NUM_2D_BIJ_NZ_ALT2 : thm
    val NUM_2D_BIJ_NZ_ALT2_INV : thm
    val NUM_2D_BIJ_NZ_ALT_INV : thm
    val NUM_2D_BIJ_NZ_INV : thm
    val NUM_2D_BIJ_SMALL_SQUARE : thm
    val ONE_MINUS_HALF : thm
    val PAIRED_BETA_THM : thm
    val PAIR_UNIV : thm
    val POS_SUMMABLE : thm
    val POW_HALF_MONO : thm
    val POW_HALF_POS : thm
    val POW_HALF_SER : thm
    val POW_HALF_SMALL : thm
    val PREIMAGE_ALT : thm
    val PREIMAGE_BIGUNION : thm
    val PREIMAGE_COMP : thm
    val PREIMAGE_COMPL : thm
    val PREIMAGE_COMPL_INTER : thm
    val PREIMAGE_CROSS : thm
    val PREIMAGE_DIFF : thm
    val PREIMAGE_DISJOINT : thm
    val PREIMAGE_EMPTY : thm
    val PREIMAGE_I : thm
    val PREIMAGE_INTER : thm
    val PREIMAGE_K : thm
    val PREIMAGE_REAL_COMPL1 : thm
    val PREIMAGE_REAL_COMPL2 : thm
    val PREIMAGE_REAL_COMPL3 : thm
    val PREIMAGE_REAL_COMPL4 : thm
    val PREIMAGE_SUBSET : thm
    val PREIMAGE_UNION : thm
    val PREIMAGE_UNIV : thm
    val REAL_LE_LT_MUL : thm
    val REAL_LT_LE_MUL : thm
    val REAL_MUL_IDEMPOT : thm
    val REAL_SUP_LE_X : thm
    val REAL_X_LE_SUP : thm
    val SCHROEDER_BERNSTEIN : thm
    val SCHROEDER_BERNSTEIN_AUTO : thm
    val SCHROEDER_CLOSE : thm
    val SCHROEDER_CLOSED : thm
    val SCHROEDER_CLOSE_SET : thm
    val SCHROEDER_CLOSE_SUBSET : thm
    val SEQ_SANDWICH : thm
    val SER_POS : thm
    val SER_POS_COMPARE : thm
    val SER_POS_MONO : thm
    val SUBSET_ADD : thm
    val SUBSET_INTER : thm
    val SUBSET_INTER1 : thm
    val SUBSET_INTER2 : thm
    val SUBSET_K : thm
    val SUBSET_THM : thm
    val SUMINF_2D : thm
    val SUMINF_ADD : thm
    val SUMINF_POS : thm
    val SUMMABLE_LE : thm
    val SUMS_EQ : thm
    val SUM_CONST : thm
    val SUM_LT : thm
    val SUM_PICK : thm
    val SURJ_IMP_INJ : thm
    val TRANSFORM_2D_NUM : thm
    val TRIANGLE_2D_NUM : thm
    val UNIV_FUNSET_UNIV : thm
    val UNIV_NEQ_EMPTY : thm
    val X_HALF_HALF : thm
    val X_LE_MAX : thm
    val finite_enumeration_of_sets_has_max_non_empty : thm
    val lg_1 : thm
    val lg_2 : thm
    val lg_inv : thm
    val lg_mul : thm
    val lg_nonzero : thm
    val lg_pow : thm
    val logr_1 : thm
    val logr_div : thm
    val logr_inv : thm
    val logr_mul : thm
    val neg_lg : thm
    val neg_logr : thm

  val util_prob_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [real_sigma] Parent theory of "util_prob"

   [DFUNSET_def]  Definition

      |- ∀P Q. P --> Q = (λf. ∀x. x ∈ P ⇒ f x ∈ Q x)

   [FUNSET_def]  Definition

      |- ∀P Q. P -> Q = (λf. ∀x. x ∈ P ⇒ f x ∈ Q)

   [PREIMAGE_def]  Definition

      |- ∀f s. PREIMAGE f s = {x | f x ∈ s}

   [countable_def]  Definition

      |- ∀s. countable s ⇔ ∃f. ∀x. x ∈ s ⇒ ∃n. f n = x

   [enumerate_def]  Definition

      |- ∀s. enumerate s = @f. BIJ f 𝕌(:num) s

   [lg_def]  Definition

      |- ∀x. lg x = logr 2 x

   [logr_def]  Definition

      |- ∀a x. logr a x = ln x / ln a

   [minimal_def]  Definition

      |- ∀p. minimal p = @n. p n ∧ ∀m. m < n ⇒ ¬p m

   [pair_def]  Definition

      |- ∀X Y. pair X Y = (λ(x,y). x ∈ X ∧ y ∈ Y)

   [powr_def]  Definition

      |- ∀x a. x powr a = exp (a * ln x)

   [prod_sets_def]  Definition

      |- ∀a b. prod_sets a b = {s × t | s ∈ a ∧ t ∈ b}

   [schroeder_close_def]  Definition

      |- ∀f s x. schroeder_close f s x ⇔ ∃n. x ∈ FUNPOW (IMAGE f) n s

   [BIGINTER_SUBSET]  Theorem

      |- ∀sp s. (∀t. t ∈ s ⇒ t ⊆ sp) ∧ s ≠ ∅ ⇒ BIGINTER s ⊆ sp

   [BIGUNION_IMAGE_UNIV]  Theorem

      |- ∀f N.
           (∀n. N ≤ n ⇒ (f n = ∅)) ⇒
           (BIGUNION (IMAGE f 𝕌(:num)) = BIGUNION (IMAGE f (count N)))

   [BIGUNION_PAIR]  Theorem

      |- ∀s t. BIGUNION {s; t} = s ∪ t

   [BIJ_ALT]  Theorem

      |- ∀f s t. BIJ f s t ⇔ f ∈ (s -> t) ∧ ∀y::t. ∃!x::s. y = f x

   [BIJ_FINITE_SUBSET]  Theorem

      |- ∀f s t.
           BIJ f 𝕌(:num) s ∧ FINITE t ∧ t ⊆ s ⇒ ∃N. ∀n. N ≤ n ⇒ f n ∉ t

   [BIJ_INJ_SURJ]  Theorem

      |- ∀s t. (∃f. INJ f s t) ∧ (∃g. SURJ g s t) ⇒ ∃h. BIJ h s t

   [BIJ_INSERT]  Theorem

      |- ∀f e s t.
           e ∉ s ∧ BIJ f (e INSERT s) t ⇒
           ∃u. (f e INSERT u = t) ∧ f e ∉ u ∧ BIJ f s u

   [BIJ_INV]  Theorem

      |- ∀f s t.
           BIJ f s t ⇒
           ∃g.
             BIJ g t s ∧ (∀x. x ∈ s ⇒ ((g o f) x = x)) ∧
             ∀x. x ∈ t ⇒ ((f o g) x = x)

   [BIJ_NUM_COUNTABLE]  Theorem

      |- ∀s. (∃f. BIJ f 𝕌(:num) s) ⇒ countable s

   [BIJ_SYM]  Theorem

      |- ∀s t. (∃f. BIJ f s t) ⇔ ∃g. BIJ g t s

   [BIJ_SYM_IMP]  Theorem

      |- ∀s t. (∃f. BIJ f s t) ⇒ ∃g. BIJ g t s

   [BIJ_TRANS]  Theorem

      |- ∀s t u. (∃f. BIJ f s t) ∧ (∃g. BIJ g t u) ⇒ ∃h. BIJ h s u

   [COUNTABLE_ALT]  Theorem

      |- ∀s. countable s ⇔ FINITE s ∨ BIJ (enumerate s) 𝕌(:num) s

   [COUNTABLE_BIGUNION]  Theorem

      |- ∀c.
           countable c ∧ (∀s. s ∈ c ⇒ countable s) ⇒ countable (BIGUNION c)

   [COUNTABLE_COUNT]  Theorem

      |- ∀n. countable (count n)

   [COUNTABLE_EMPTY]  Theorem

      |- countable ∅

   [COUNTABLE_ENUM]  Theorem

      |- ∀c. countable c ⇔ (c = ∅) ∨ ∃f. c = IMAGE f 𝕌(:num)

   [COUNTABLE_IMAGE]  Theorem

      |- ∀s f. countable s ⇒ countable (IMAGE f s)

   [COUNTABLE_IMAGE_NUM]  Theorem

      |- ∀f s. countable (IMAGE f s)

   [COUNTABLE_NUM]  Theorem

      |- ∀s. countable s

   [COUNTABLE_SUBSET]  Theorem

      |- ∀s t. s ⊆ t ∧ countable t ⇒ countable s

   [COUNTABLE_UNION]  Theorem

      |- ∀s t. countable s ∧ countable t ⇒ countable (s ∪ t)

   [DELETE_THEN_INSERT]  Theorem

      |- ∀s (x::s). x INSERT s DELETE x = s

   [DIFF_BIGINTER]  Theorem

      |- ∀sp s.
           (∀t. t ∈ s ⇒ t ⊆ sp) ∧ s ≠ ∅ ⇒
           (BIGINTER s = sp DIFF BIGUNION (IMAGE (λu. sp DIFF u) s))

   [DIFF_BIGINTER1]  Theorem

      |- ∀sp s. sp DIFF BIGINTER s = BIGUNION (IMAGE (λu. sp DIFF u) s)

   [DIFF_DIFF_SUBSET]  Theorem

      |- ∀s t. t ⊆ s ⇒ (s DIFF (s DIFF t) = t)

   [DIFF_INTER]  Theorem

      |- ∀s t g. (s DIFF t) ∩ g = s ∩ g DIFF t

   [DIFF_INTER2]  Theorem

      |- ∀s t. s DIFF t ∩ s = s DIFF t

   [DISJOINT_ALT]  Theorem

      |- ∀s t. DISJOINT s t ⇔ ∀x. x ∈ s ⇒ x ∉ t

   [DISJOINT_COUNT]  Theorem

      |- ∀f.
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
           ∀n. DISJOINT (f n) (BIGUNION (IMAGE f (count n)))

   [DISJOINT_DIFF]  Theorem

      |- ∀s t. DISJOINT t (s DIFF t) ∧ DISJOINT (s DIFF t) t

   [DISJOINT_DIFFS]  Theorem

      |- ∀f m n.
           (∀n. f n ⊆ f (SUC n)) ∧ (∀n. g n = f (SUC n) DIFF f n) ∧ m ≠ n ⇒
           DISJOINT (g m) (g n)

   [ELT_IN_DELETE]  Theorem

      |- ∀x s. x ∉ s DELETE x

   [EMPTY_FUNSET]  Theorem

      |- ∀s. ∅ -> s = 𝕌(:α -> β)

   [ENUMERATE]  Theorem

      |- ∀s. (∃f. BIJ f 𝕌(:num) s) ⇔ BIJ (enumerate s) 𝕌(:num) s

   [EQ_SUBSET_SUBSET]  Theorem

      |- ∀s t. (s = t) ⇒ s ⊆ t ∧ t ⊆ s

   [EQ_T_IMP]  Theorem

      |- ∀x. x ⇔ T ⇒ x

   [EXPLICIT_ENUMERATE_MONO]  Theorem

      |- ∀n s. FUNPOW REST n s ⊆ s

   [EXPLICIT_ENUMERATE_NOT_EMPTY]  Theorem

      |- ∀n s. INFINITE s ⇒ FUNPOW REST n s ≠ ∅

   [FINITE_BIJ]  Theorem

      |- ∀f s t. FINITE s ∧ BIJ f s t ⇒ FINITE t ∧ (CARD s = CARD t)

   [FINITE_BIJ_COUNT]  Theorem

      |- ∀s. FINITE s ⇔ ∃c n. BIJ c (count n) s

   [FINITE_COUNTABLE]  Theorem

      |- ∀s. FINITE s ⇒ countable s

   [FINITE_INJ]  Theorem

      |- ∀f s t. INJ f s t ∧ FINITE t ⇒ FINITE s

   [FINITE_REST]  Theorem

      |- ∀s. FINITE (REST s) ⇔ FINITE s

   [FUNSET_DFUNSET]  Theorem

      |- ∀x y. x -> y = x --> K y

   [FUNSET_EMPTY]  Theorem

      |- ∀s f. f ∈ (s -> ∅) ⇔ (s = ∅)

   [FUNSET_INTER]  Theorem

      |- ∀a b c. a -> b ∩ c = (a -> b) ∩ (a -> c)

   [FUNSET_THM]  Theorem

      |- ∀s t f x. f ∈ (s -> t) ∧ x ∈ s ⇒ f x ∈ t

   [GBIGUNION_IMAGE]  Theorem

      |- ∀s p n. {s | ∃n. p s n} = BIGUNION (IMAGE (λn. {s | p s n}) 𝕌(:γ))

   [HALF_CANCEL]  Theorem

      |- 2 * (1 / 2) = 1

   [HALF_LT_1]  Theorem

      |- 1 / 2 < 1

   [HALF_POS]  Theorem

      |- 0 < 1 / 2

   [IMAGE_I]  Theorem

      |- IMAGE I = I

   [IMAGE_IMAGE]  Theorem

      |- ∀f g s. IMAGE f (IMAGE g s) = IMAGE (f o g) s

   [INCREASING_SEQ]  Theorem

      |- ∀f l.
           (∀n. f n ≤ f (SUC n)) ∧ (∀n. f n ≤ l) ∧
           (∀e. 0 < e ⇒ ∃n. l < f n + e) ⇒
           f --> l

   [INFINITE_EXPLICIT_ENUMERATE]  Theorem

      |- ∀s. INFINITE s ⇒ INJ (λn. CHOICE (FUNPOW REST n s)) 𝕌(:num) s

   [INFINITE_INJ]  Theorem

      |- ∀f s t. INJ f s t ∧ INFINITE s ⇒ INFINITE t

   [INF_CLOSE]  Theorem

      |- ∀p e. (∃x. x ∈ p) ∧ 0 < e ⇒ ∃x. x ∈ p ∧ x < inf p + e

   [INF_DEF_ALT]  Theorem

      |- ∀p. inf p = -sup (λr. -r ∈ p)

   [INF_GREATER]  Theorem

      |- ∀p z. (∃x. x ∈ p) ∧ inf p < z ⇒ ∃x. x ∈ p ∧ x < z

   [INF_LE]  Theorem

      |- ∀p r. (∃z. ∀x. x ∈ p ⇒ z ≤ x) ∧ (∃x. x ∈ p ∧ x ≤ r) ⇒ inf p ≤ r

   [INJ_IMAGE_BIJ]  Theorem

      |- ∀s f. (∃t. INJ f s t) ⇒ BIJ f s (IMAGE f s)

   [IN_BIGINTER_IMAGE]  Theorem

      |- ∀x f s. x ∈ BIGINTER (IMAGE f s) ⇔ ∀y. y ∈ s ⇒ x ∈ f y

   [IN_BIGUNION_IMAGE]  Theorem

      |- ∀f s y. y ∈ BIGUNION (IMAGE f s) ⇔ ∃x. x ∈ s ∧ y ∈ f x

   [IN_DFUNSET]  Theorem

      |- ∀f P Q. f ∈ P --> Q ⇔ ∀x. x ∈ P ⇒ f x ∈ Q x

   [IN_EQ_UNIV_IMP]  Theorem

      |- ∀s. (s = 𝕌(:α)) ⇒ ∀v. v ∈ s

   [IN_FUNSET]  Theorem

      |- ∀f P Q. f ∈ (P -> Q) ⇔ ∀x. x ∈ P ⇒ f x ∈ Q

   [IN_PAIR]  Theorem

      |- ∀x X Y. x ∈ pair X Y ⇔ FST x ∈ X ∧ SND x ∈ Y

   [IN_PREIMAGE]  Theorem

      |- ∀f s x. x ∈ PREIMAGE f s ⇔ f x ∈ s

   [IN_PROD_SETS]  Theorem

      |- ∀s a b. s ∈ prod_sets a b ⇔ ∃t u. (s = t × u) ∧ t ∈ a ∧ u ∈ b

   [IN_o]  Theorem

      |- ∀x f s. x ∈ s o f ⇔ f x ∈ s

   [K_PARTIAL]  Theorem

      |- ∀x. K x = (λz. x)

   [K_SUBSET]  Theorem

      |- ∀x y. K x ⊆ y ⇔ ¬x ∨ 𝕌(:α) ⊆ y

   [LE_INF]  Theorem

      |- ∀p r. (∃x. x ∈ p) ∧ (∀x. x ∈ p ⇒ r ≤ x) ⇒ r ≤ inf p

   [LE_SUC]  Theorem

      |- ∀a b. a ≤ SUC b ⇔ a ≤ b ∨ (a = SUC b)

   [LT_SUC]  Theorem

      |- ∀a b. a < SUC b ⇔ a < b ∨ (a = b)

   [MAX_LE_X]  Theorem

      |- ∀m n k. MAX m n ≤ k ⇔ m ≤ k ∧ n ≤ k

   [MINIMAL_EXISTS]  Theorem

      |- ∀P. (∃n. P n) ⇔ P (minimal P) ∧ ∀n. n < minimal P ⇒ ¬P n

   [MINIMAL_EXISTS0]  Theorem

      |- (∃n. P n) ⇔ ∃n. P n ∧ ∀m. m < n ⇒ ¬P m

   [NUM_2D_BIJ]  Theorem

      |- ∃f. BIJ f (𝕌(:num) × 𝕌(:num)) 𝕌(:num)

   [NUM_2D_BIJ_BIG_SQUARE]  Theorem

      |- ∀f N.
           BIJ f 𝕌(:num) (𝕌(:num) × 𝕌(:num)) ⇒
           ∃k. IMAGE f (count N) ⊆ count k × count k

   [NUM_2D_BIJ_INV]  Theorem

      |- ∃f. BIJ f 𝕌(:num) (𝕌(:num) × 𝕌(:num))

   [NUM_2D_BIJ_NZ]  Theorem

      |- ∃f. BIJ f (𝕌(:num) × (𝕌(:num) DIFF {0})) 𝕌(:num)

   [NUM_2D_BIJ_NZ_ALT]  Theorem

      |- ∃f. BIJ f (𝕌(:num) × 𝕌(:num)) (𝕌(:num) DIFF {0})

   [NUM_2D_BIJ_NZ_ALT2]  Theorem

      |- ∃f. BIJ f ((𝕌(:num) DIFF {0}) × (𝕌(:num) DIFF {0})) 𝕌(:num)

   [NUM_2D_BIJ_NZ_ALT2_INV]  Theorem

      |- ∃f. BIJ f 𝕌(:num) ((𝕌(:num) DIFF {0}) × (𝕌(:num) DIFF {0}))

   [NUM_2D_BIJ_NZ_ALT_INV]  Theorem

      |- ∃f. BIJ f (𝕌(:num) DIFF {0}) (𝕌(:num) × 𝕌(:num))

   [NUM_2D_BIJ_NZ_INV]  Theorem

      |- ∃f. BIJ f 𝕌(:num) (𝕌(:num) × (𝕌(:num) DIFF {0}))

   [NUM_2D_BIJ_SMALL_SQUARE]  Theorem

      |- ∀f k.
           BIJ f 𝕌(:num) (𝕌(:num) × 𝕌(:num)) ⇒
           ∃N. count k × count k ⊆ IMAGE f (count N)

   [ONE_MINUS_HALF]  Theorem

      |- 1 − 1 / 2 = 1 / 2

   [PAIRED_BETA_THM]  Theorem

      |- ∀f z. UNCURRY f z = f (FST z) (SND z)

   [PAIR_UNIV]  Theorem

      |- pair 𝕌(:α) 𝕌(:β) = 𝕌(:α # β)

   [POS_SUMMABLE]  Theorem

      |- ∀f. (∀n. 0 ≤ f n) ∧ (∃x. ∀n. sum (0,n) f ≤ x) ⇒ summable f

   [POW_HALF_MONO]  Theorem

      |- ∀m n. m ≤ n ⇒ (1 / 2) pow n ≤ (1 / 2) pow m

   [POW_HALF_POS]  Theorem

      |- ∀n. 0 < (1 / 2) pow n

   [POW_HALF_SER]  Theorem

      |- (λn. (1 / 2) pow (n + 1)) sums 1

   [POW_HALF_SMALL]  Theorem

      |- ∀e. 0 < e ⇒ ∃n. (1 / 2) pow n < e

   [PREIMAGE_ALT]  Theorem

      |- ∀f s. PREIMAGE f s = s o f

   [PREIMAGE_BIGUNION]  Theorem

      |- ∀f s. PREIMAGE f (BIGUNION s) = BIGUNION (IMAGE (PREIMAGE f) s)

   [PREIMAGE_COMP]  Theorem

      |- ∀f g s. PREIMAGE f (PREIMAGE g s) = PREIMAGE (g o f) s

   [PREIMAGE_COMPL]  Theorem

      |- ∀f s. PREIMAGE f (COMPL s) = COMPL (PREIMAGE f s)

   [PREIMAGE_COMPL_INTER]  Theorem

      |- ∀f t sp. PREIMAGE f (COMPL t) ∩ sp = sp DIFF PREIMAGE f t

   [PREIMAGE_CROSS]  Theorem

      |- ∀f a b.
           PREIMAGE f (a × b) = PREIMAGE (FST o f) a ∩ PREIMAGE (SND o f) b

   [PREIMAGE_DIFF]  Theorem

      |- ∀f s t. PREIMAGE f (s DIFF t) = PREIMAGE f s DIFF PREIMAGE f t

   [PREIMAGE_DISJOINT]  Theorem

      |- ∀f s t. DISJOINT s t ⇒ DISJOINT (PREIMAGE f s) (PREIMAGE f t)

   [PREIMAGE_EMPTY]  Theorem

      |- ∀f. PREIMAGE f ∅ = ∅

   [PREIMAGE_I]  Theorem

      |- PREIMAGE I = I

   [PREIMAGE_INTER]  Theorem

      |- ∀f s t. PREIMAGE f (s ∩ t) = PREIMAGE f s ∩ PREIMAGE f t

   [PREIMAGE_K]  Theorem

      |- ∀x s. PREIMAGE (K x) s = if x ∈ s then 𝕌(:β) else ∅

   [PREIMAGE_REAL_COMPL1]  Theorem

      |- ∀c. COMPL {x | c < x} = {x | x ≤ c}

   [PREIMAGE_REAL_COMPL2]  Theorem

      |- ∀c. COMPL {x | c ≤ x} = {x | x < c}

   [PREIMAGE_REAL_COMPL3]  Theorem

      |- ∀c. COMPL {x | x ≤ c} = {x | c < x}

   [PREIMAGE_REAL_COMPL4]  Theorem

      |- ∀c. COMPL {x | x < c} = {x | c ≤ x}

   [PREIMAGE_SUBSET]  Theorem

      |- ∀f s t. s ⊆ t ⇒ PREIMAGE f s ⊆ PREIMAGE f t

   [PREIMAGE_UNION]  Theorem

      |- ∀f s t. PREIMAGE f (s ∪ t) = PREIMAGE f s ∪ PREIMAGE f t

   [PREIMAGE_UNIV]  Theorem

      |- ∀f. PREIMAGE f 𝕌(:β) = 𝕌(:α)

   [REAL_LE_LT_MUL]  Theorem

      |- ∀x y. 0 ≤ x ∧ 0 < y ⇒ 0 ≤ x * y

   [REAL_LT_LE_MUL]  Theorem

      |- ∀x y. 0 < x ∧ 0 ≤ y ⇒ 0 ≤ x * y

   [REAL_MUL_IDEMPOT]  Theorem

      |- ∀r. (r * r = r) ⇔ (r = 0) ∨ (r = 1)

   [REAL_SUP_LE_X]  Theorem

      |- ∀P x. (∃r. P r) ∧ (∀r. P r ⇒ r ≤ x) ⇒ sup P ≤ x

   [REAL_X_LE_SUP]  Theorem

      |- ∀P x.
           (∃r. P r) ∧ (∃z. ∀r. P r ⇒ r ≤ z) ∧ (∃r. P r ∧ x ≤ r) ⇒
           x ≤ sup P

   [SCHROEDER_BERNSTEIN]  Theorem

      |- ∀s t. (∃f. INJ f s t) ∧ (∃g. INJ g t s) ⇒ ∃h. BIJ h s t

   [SCHROEDER_BERNSTEIN_AUTO]  Theorem

      |- ∀s t. t ⊆ s ∧ (∃f. INJ f s t) ⇒ ∃g. BIJ g s t

   [SCHROEDER_CLOSE]  Theorem

      |- ∀f s. x ∈ schroeder_close f s ⇔ ∃n. x ∈ FUNPOW (IMAGE f) n s

   [SCHROEDER_CLOSED]  Theorem

      |- ∀f s. IMAGE f (schroeder_close f s) ⊆ schroeder_close f s

   [SCHROEDER_CLOSE_SET]  Theorem

      |- ∀f s t. f ∈ (s -> s) ∧ t ⊆ s ⇒ schroeder_close f t ⊆ s

   [SCHROEDER_CLOSE_SUBSET]  Theorem

      |- ∀f s. s ⊆ schroeder_close f s

   [SEQ_SANDWICH]  Theorem

      |- ∀f g h l.
           f --> l ∧ h --> l ∧ (∀n. f n ≤ g n ∧ g n ≤ h n) ⇒ g --> l

   [SER_POS]  Theorem

      |- ∀f. summable f ∧ (∀n. 0 ≤ f n) ⇒ 0 ≤ suminf f

   [SER_POS_COMPARE]  Theorem

      |- ∀f g.
           (∀n. 0 ≤ f n) ∧ summable g ∧ (∀n. f n ≤ g n) ⇒
           summable f ∧ suminf f ≤ suminf g

   [SER_POS_MONO]  Theorem

      |- ∀f. (∀n. 0 ≤ f n) ⇒ mono (λn. sum (0,n) f)

   [SUBSET_ADD]  Theorem

      |- ∀f n d. (∀n. f n ⊆ f (SUC n)) ⇒ f n ⊆ f (n + d)

   [SUBSET_INTER]  Theorem

      |- ∀s t u. s ⊆ t ∩ u ⇔ s ⊆ t ∧ s ⊆ u

   [SUBSET_INTER1]  Theorem

      |- ∀s t. s ⊆ t ⇒ (s ∩ t = s)

   [SUBSET_INTER2]  Theorem

      |- ∀s t. s ⊆ t ⇒ (t ∩ s = s)

   [SUBSET_K]  Theorem

      |- ∀x y. x ⊆ K y ⇔ x ⊆ ∅ ∨ y

   [SUBSET_THM]  Theorem

      |- ∀P Q. P ⊆ Q ⇒ ∀x. x ∈ P ⇒ x ∈ Q

   [SUMINF_2D]  Theorem

      |- ∀f g h.
           (∀m n. 0 ≤ f m n) ∧ (∀n. f n sums g n) ∧ summable g ∧
           BIJ h 𝕌(:num) (𝕌(:num) × 𝕌(:num)) ⇒
           UNCURRY f o h sums suminf g

   [SUMINF_ADD]  Theorem

      |- ∀f g.
           summable f ∧ summable g ⇒
           summable (λn. f n + g n) ∧
           (suminf f + suminf g = suminf (λn. f n + g n))

   [SUMINF_POS]  Theorem

      |- ∀f. (∀n. 0 ≤ f n) ∧ summable f ⇒ 0 ≤ suminf f

   [SUMMABLE_LE]  Theorem

      |- ∀f x. summable f ∧ (∀n. sum (0,n) f ≤ x) ⇒ suminf f ≤ x

   [SUMS_EQ]  Theorem

      |- ∀f x. f sums x ⇔ summable f ∧ (suminf f = x)

   [SUM_CONST]  Theorem

      |- ∀n r. sum (0,n) (K r) = &n * r

   [SUM_LT]  Theorem

      |- ∀f g m n.
           (∀r. m ≤ r ∧ r < n + m ⇒ f r < g r) ∧ 0 < n ⇒
           sum (m,n) f < sum (m,n) g

   [SUM_PICK]  Theorem

      |- ∀n k x.
           sum (0,n) (λm. if m = k then x else 0) = if k < n then x else 0

   [SURJ_IMP_INJ]  Theorem

      |- ∀s t. (∃f. SURJ f s t) ⇒ ∃g. INJ g t s

   [TRANSFORM_2D_NUM]  Theorem

      |- ∀P. (∀m n. P m n ⇒ P n m) ∧ (∀m n. P m (m + n)) ⇒ ∀m n. P m n

   [TRIANGLE_2D_NUM]  Theorem

      |- ∀P. (∀d n. P n (d + n)) ⇒ ∀m n. m ≤ n ⇒ P m n

   [UNIV_FUNSET_UNIV]  Theorem

      |- 𝕌(:α) -> 𝕌(:β) = 𝕌(:α -> β)

   [UNIV_NEQ_EMPTY]  Theorem

      |- 𝕌(:α) ≠ ∅

   [X_HALF_HALF]  Theorem

      |- ∀x. 1 / 2 * x + 1 / 2 * x = x

   [X_LE_MAX]  Theorem

      |- ∀m n k. k ≤ MAX m n ⇔ k ≤ m ∨ k ≤ n

   [finite_enumeration_of_sets_has_max_non_empty]  Theorem

      |- ∀f s.
           FINITE s ∧ (∀x. f x ∈ s) ∧
           (∀m n. m ≠ n ⇒ DISJOINT (f m) (f n)) ⇒
           ∃N. ∀n. n ≥ N ⇒ (f n = ∅)

   [lg_1]  Theorem

      |- lg 1 = 0

   [lg_2]  Theorem

      |- lg 2 = 1

   [lg_inv]  Theorem

      |- ∀x. 0 < x ⇒ (lg (inv x) = -lg x)

   [lg_mul]  Theorem

      |- ∀x y. 0 < x ∧ 0 < y ⇒ (lg (x * y) = lg x + lg y)

   [lg_nonzero]  Theorem

      |- ∀x. x ≠ 0 ∧ 0 ≤ x ⇒ (lg x ≠ 0 ⇔ x ≠ 1)

   [lg_pow]  Theorem

      |- ∀n. lg (2 pow n) = &n

   [logr_1]  Theorem

      |- ∀b. logr b 1 = 0

   [logr_div]  Theorem

      |- ∀b x y. 0 < x ∧ 0 < y ⇒ (logr b (x / y) = logr b x − logr b y)

   [logr_inv]  Theorem

      |- ∀b x. 0 < x ⇒ (logr b (inv x) = -logr b x)

   [logr_mul]  Theorem

      |- ∀b x y. 0 < x ∧ 0 < y ⇒ (logr b (x * y) = logr b x + logr b y)

   [neg_lg]  Theorem

      |- ∀x. 0 < x ⇒ (-lg x = lg (inv x))

   [neg_logr]  Theorem

      |- ∀b x. 0 < x ⇒ (-logr b x = logr b (inv x))


*)
end
