signature pred_setTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BIGINTER : thm
    val BIGUNION : thm
    val BIJ_DEF : thm
    val CARD_DEF : thm
    val CHOICE_DEF : thm
    val COMPL_DEF : thm
    val CROSS_DEF : thm
    val DELETE_DEF : thm
    val DIFF_DEF : thm
    val DISJOINT_DEF : thm
    val EMPTY_DEF : thm
    val FINITE_DEF : thm
    val GSPECIFICATION : thm
    val IMAGE_DEF : thm
    val INJ_DEF : thm
    val INSERT_DEF : thm
    val INTER_DEF : thm
    val ITSET_curried_def : thm
    val ITSET_tupled_primitive_def : thm
    val LINV_DEF : thm
    val MAX_SET_DEF : thm
    val MIN_SET_DEF : thm
    val POW_DEF : thm
    val PROD_IMAGE_DEF : thm
    val PROD_SET_DEF : thm
    val PSUBSET_DEF : thm
    val REL_RESTRICT_DEF : thm
    val REST_DEF : thm
    val RINV_DEF : thm
    val SING_DEF : thm
    val SUBSET_DEF : thm
    val SUM_IMAGE_DEF : thm
    val SUM_SET_DEF : thm
    val SURJ_DEF : thm
    val UNION_DEF : thm
    val UNIV_DEF : thm
    val chooser_def : thm
    val count_def : thm
    val countable_def : thm
    val equiv_on_def : thm
    val num_to_pair_def : thm
    val pair_to_num_def : thm
    val pairwise_def : thm
    val partition_def : thm

  (*  Theorems  *)
    val ABSORPTION : thm
    val ABSORPTION_RWT : thm
    val ABS_DIFF_SUM_IMAGE : thm
    val ABS_applied : thm
    val BIGINTER_EMPTY : thm
    val BIGINTER_INSERT : thm
    val BIGINTER_INTER : thm
    val BIGINTER_SING : thm
    val BIGINTER_UNION : thm
    val BIGINTER_applied : thm
    val BIGUNION_EMPTY : thm
    val BIGUNION_EQ_EMPTY : thm
    val BIGUNION_INSERT : thm
    val BIGUNION_SING : thm
    val BIGUNION_SUBSET : thm
    val BIGUNION_UNION : thm
    val BIGUNION_applied : thm
    val BIGUNION_partition : thm
    val BIJ_COMPOSE : thm
    val BIJ_DELETE : thm
    val BIJ_EMPTY : thm
    val BIJ_FINITE : thm
    val BIJ_ID : thm
    val BIJ_IFF_INV : thm
    val BIJ_INSERT : thm
    val BIJ_LINV_BIJ : thm
    val BIJ_LINV_INV : thm
    val CARD_BIGUNION_SAME_SIZED_SETS : thm
    val CARD_COUNT : thm
    val CARD_CROSS : thm
    val CARD_DELETE : thm
    val CARD_DIFF : thm
    val CARD_DIFF_EQN : thm
    val CARD_EMPTY : thm
    val CARD_EQ_0 : thm
    val CARD_INJ_IMAGE : thm
    val CARD_INSERT : thm
    val CARD_INTER_LESS_EQ : thm
    val CARD_POW : thm
    val CARD_PSUBSET : thm
    val CARD_SING : thm
    val CARD_SING_CROSS : thm
    val CARD_SUBSET : thm
    val CARD_UNION : thm
    val CARD_UNION_EQN : thm
    val CHOICE_INSERT_REST : thm
    val CHOICE_NOT_IN_REST : thm
    val CHOICE_SING : thm
    val COMMUTING_ITSET_INSERT : thm
    val COMMUTING_ITSET_RECURSES : thm
    val COMPL_CLAUSES : thm
    val COMPL_COMPL : thm
    val COMPL_EMPTY : thm
    val COMPL_INTER : thm
    val COMPL_SPLITS : thm
    val COMPL_UNION : thm
    val COMPL_applied : thm
    val COMPONENT : thm
    val COUNT_11 : thm
    val COUNT_SUC : thm
    val COUNT_ZERO : thm
    val COUNT_applied : thm
    val CROSS_EMPTY : thm
    val CROSS_EQNS : thm
    val CROSS_INSERT_LEFT : thm
    val CROSS_INSERT_RIGHT : thm
    val CROSS_SINGS : thm
    val CROSS_SUBSET : thm
    val CROSS_UNIV : thm
    val CROSS_applied : thm
    val DECOMPOSITION : thm
    val DELETE_COMM : thm
    val DELETE_DELETE : thm
    val DELETE_EQ_SING : thm
    val DELETE_INSERT : thm
    val DELETE_INTER : thm
    val DELETE_NON_ELEMENT : thm
    val DELETE_SUBSET : thm
    val DELETE_SUBSET_INSERT : thm
    val DELETE_applied : thm
    val DIFF_COMM : thm
    val DIFF_DIFF : thm
    val DIFF_EMPTY : thm
    val DIFF_EQ_EMPTY : thm
    val DIFF_INSERT : thm
    val DIFF_SAME_UNION : thm
    val DIFF_SUBSET : thm
    val DIFF_UNION : thm
    val DIFF_UNIV : thm
    val DIFF_applied : thm
    val DISJOINT_BIGINTER : thm
    val DISJOINT_BIGUNION : thm
    val DISJOINT_DELETE_SYM : thm
    val DISJOINT_EMPTY : thm
    val DISJOINT_EMPTY_REFL : thm
    val DISJOINT_EMPTY_REFL_RWT : thm
    val DISJOINT_INSERT : thm
    val DISJOINT_SING_EMPTY : thm
    val DISJOINT_SUBSET : thm
    val DISJOINT_SYM : thm
    val DISJOINT_UNION : thm
    val DISJOINT_UNION_BOTH : thm
    val EMPTY_DELETE : thm
    val EMPTY_DIFF : thm
    val EMPTY_NOT_IN_partition : thm
    val EMPTY_NOT_UNIV : thm
    val EMPTY_SUBSET : thm
    val EMPTY_UNION : thm
    val EMPTY_applied : thm
    val EQUAL_SING : thm
    val EQ_UNIV : thm
    val EXTENSION : thm
    val FINITELY_INJECTIVE_IMAGE_FINITE : thm
    val FINITE_BIGUNION : thm
    val FINITE_BIGUNION_EQ : thm
    val FINITE_BIJ_CARD_EQ : thm
    val FINITE_COMPLETE_INDUCTION : thm
    val FINITE_COUNT : thm
    val FINITE_CROSS : thm
    val FINITE_CROSS_EQ : thm
    val FINITE_DELETE : thm
    val FINITE_DIFF : thm
    val FINITE_DIFF_down : thm
    val FINITE_EMPTY : thm
    val FINITE_INDUCT : thm
    val FINITE_INJ : thm
    val FINITE_INSERT : thm
    val FINITE_INTER : thm
    val FINITE_ISO_NUM : thm
    val FINITE_POW : thm
    val FINITE_PSUBSET_INFINITE : thm
    val FINITE_PSUBSET_UNIV : thm
    val FINITE_REST : thm
    val FINITE_SING : thm
    val FINITE_StrongOrder_WF : thm
    val FINITE_UNION : thm
    val FINITE_WEAK_ENUMERATE : thm
    val FINITE_WF_noloops : thm
    val FINITE_partition : thm
    val GSPEC_AND : thm
    val GSPEC_EQ : thm
    val GSPEC_EQ2 : thm
    val GSPEC_ETA : thm
    val GSPEC_F : thm
    val GSPEC_F_COND : thm
    val GSPEC_ID : thm
    val GSPEC_OR : thm
    val GSPEC_T : thm
    val IMAGE_11 : thm
    val IMAGE_11_INFINITE : thm
    val IMAGE_BIGUNION : thm
    val IMAGE_COMPOSE : thm
    val IMAGE_CONG : thm
    val IMAGE_DELETE : thm
    val IMAGE_EMPTY : thm
    val IMAGE_EQ_EMPTY : thm
    val IMAGE_FINITE : thm
    val IMAGE_ID : thm
    val IMAGE_IN : thm
    val IMAGE_INSERT : thm
    val IMAGE_INTER : thm
    val IMAGE_SUBSET : thm
    val IMAGE_SURJ : thm
    val IMAGE_UNION : thm
    val IMAGE_applied : thm
    val INFINITE_DEF : thm
    val INFINITE_DIFF_FINITE : thm
    val INFINITE_INHAB : thm
    val INFINITE_NUM_UNIV : thm
    val INFINITE_PAIR_UNIV : thm
    val INFINITE_SUBSET : thm
    val INFINITE_UNIV : thm
    val INJECTIVE_IMAGE_FINITE : thm
    val INJ_CARD : thm
    val INJ_COMPOSE : thm
    val INJ_DELETE : thm
    val INJ_EMPTY : thm
    val INJ_ID : thm
    val INJ_IFF : thm
    val INJ_INL : thm
    val INJ_INR : thm
    val INJ_INSERT : thm
    val INJ_SUBSET : thm
    val INSERT_COMM : thm
    val INSERT_DELETE : thm
    val INSERT_DIFF : thm
    val INSERT_INSERT : thm
    val INSERT_INTER : thm
    val INSERT_SING_UNION : thm
    val INSERT_SUBSET : thm
    val INSERT_UNION : thm
    val INSERT_UNION_EQ : thm
    val INSERT_UNIV : thm
    val INSERT_applied : thm
    val INTER_ASSOC : thm
    val INTER_COMM : thm
    val INTER_EMPTY : thm
    val INTER_FINITE : thm
    val INTER_IDEMPOT : thm
    val INTER_OVER_UNION : thm
    val INTER_SUBSET : thm
    val INTER_SUBSET_EQN : thm
    val INTER_UNION : thm
    val INTER_UNION_COMPL : thm
    val INTER_UNIV : thm
    val INTER_applied : thm
    val IN_ABS : thm
    val IN_BIGINTER : thm
    val IN_BIGUNION : thm
    val IN_COMPL : thm
    val IN_COUNT : thm
    val IN_CROSS : thm
    val IN_DELETE : thm
    val IN_DELETE_EQ : thm
    val IN_DIFF : thm
    val IN_DISJOINT : thm
    val IN_IMAGE : thm
    val IN_INFINITE_NOT_FINITE : thm
    val IN_INSERT : thm
    val IN_INSERT_EXPAND : thm
    val IN_INTER : thm
    val IN_POW : thm
    val IN_SING : thm
    val IN_UNION : thm
    val IN_UNIV : thm
    val ITSET_EMPTY : thm
    val ITSET_IND : thm
    val ITSET_INSERT : thm
    val ITSET_THM : thm
    val ITSET_def : thm
    val ITSET_ind : thm
    val KoenigsLemma : thm
    val KoenigsLemma_WF : thm
    val LESS_CARD_DIFF : thm
    val MAX_SET_ELIM : thm
    val MAX_SET_THM : thm
    val MAX_SET_UNION : thm
    val MEMBER_NOT_EMPTY : thm
    val MIN_SET_ELIM : thm
    val MIN_SET_LEM : thm
    val MIN_SET_LEQ_MAX_SET : thm
    val MIN_SET_THM : thm
    val MIN_SET_UNION : thm
    val NOT_EMPTY_INSERT : thm
    val NOT_EMPTY_SING : thm
    val NOT_EQUAL_SETS : thm
    val NOT_INSERT_EMPTY : thm
    val NOT_IN_EMPTY : thm
    val NOT_IN_FINITE : thm
    val NOT_PSUBSET_EMPTY : thm
    val NOT_SING_EMPTY : thm
    val NOT_UNIV_PSUBSET : thm
    val NUM_SET_WOP : thm
    val PHP : thm
    val POW_EQNS : thm
    val POW_INSERT : thm
    val PROD_IMAGE_THM : thm
    val PROD_SET_EMPTY : thm
    val PROD_SET_IMAGE_REDUCTION : thm
    val PROD_SET_THM : thm
    val PSUBSET_EQN : thm
    val PSUBSET_FINITE : thm
    val PSUBSET_INSERT_SUBSET : thm
    val PSUBSET_IRREFL : thm
    val PSUBSET_MEMBER : thm
    val PSUBSET_SING : thm
    val PSUBSET_SUBSET_TRANS : thm
    val PSUBSET_TRANS : thm
    val PSUBSET_UNIV : thm
    val REL_RESTRICT_EMPTY : thm
    val REL_RESTRICT_SUBSET : thm
    val REST_PSUBSET : thm
    val REST_SING : thm
    val REST_SUBSET : thm
    val SET_CASES : thm
    val SET_EQ_SUBSET : thm
    val SET_MINIMUM : thm
    val SING : thm
    val SING_DELETE : thm
    val SING_EMPTY : thm
    val SING_FINITE : thm
    val SING_IFF_CARD1 : thm
    val SING_IFF_EMPTY_REST : thm
    val SING_INSERT : thm
    val SING_UNION : thm
    val SING_applied : thm
    val SPECIFICATION : thm
    val SUBSET_ANTISYM : thm
    val SUBSET_BIGINTER : thm
    val SUBSET_BIGUNION_I : thm
    val SUBSET_DELETE : thm
    val SUBSET_DELETE_BOTH : thm
    val SUBSET_DIFF : thm
    val SUBSET_EMPTY : thm
    val SUBSET_EQ_CARD : thm
    val SUBSET_FINITE : thm
    val SUBSET_FINITE_I : thm
    val SUBSET_INSERT : thm
    val SUBSET_INSERT_DELETE : thm
    val SUBSET_INSERT_RIGHT : thm
    val SUBSET_INTER : thm
    val SUBSET_INTER_ABSORPTION : thm
    val SUBSET_MAX_SET : thm
    val SUBSET_MIN_SET : thm
    val SUBSET_POW : thm
    val SUBSET_PSUBSET_TRANS : thm
    val SUBSET_REFL : thm
    val SUBSET_TRANS : thm
    val SUBSET_UNION : thm
    val SUBSET_UNION_ABSORPTION : thm
    val SUBSET_UNIV : thm
    val SUM_IMAGE_CONG : thm
    val SUM_IMAGE_DELETE : thm
    val SUM_IMAGE_IN_LE : thm
    val SUM_IMAGE_MONO_LESS : thm
    val SUM_IMAGE_MONO_LESS_EQ : thm
    val SUM_IMAGE_SING : thm
    val SUM_IMAGE_SUBSET_LE : thm
    val SUM_IMAGE_THM : thm
    val SUM_IMAGE_UNION : thm
    val SUM_IMAGE_ZERO : thm
    val SUM_IMAGE_lower_bound : thm
    val SUM_IMAGE_upper_bound : thm
    val SUM_SAME_IMAGE : thm
    val SUM_SET_DELETE : thm
    val SUM_SET_EMPTY : thm
    val SUM_SET_IN_LE : thm
    val SUM_SET_SING : thm
    val SUM_SET_SUBSET_LE : thm
    val SUM_SET_THM : thm
    val SUM_SET_UNION : thm
    val SUM_UNIV : thm
    val SURJ_COMPOSE : thm
    val SURJ_EMPTY : thm
    val SURJ_ID : thm
    val SURJ_IMAGE : thm
    val SURJ_INJ_INV : thm
    val UNION_ASSOC : thm
    val UNION_COMM : thm
    val UNION_DELETE : thm
    val UNION_DIFF : thm
    val UNION_EMPTY : thm
    val UNION_IDEMPOT : thm
    val UNION_OVER_INTER : thm
    val UNION_SUBSET : thm
    val UNION_UNIV : thm
    val UNION_applied : thm
    val UNIQUE_MEMBER_SING : thm
    val UNIV_BOOL : thm
    val UNIV_FUN_TO_BOOL : thm
    val UNIV_NOT_EMPTY : thm
    val UNIV_SUBSET : thm
    val bigunion_countable : thm
    val chooser_def_compute : thm
    val count_EQN : thm
    val countable_EMPTY : thm
    val countable_INSERT : thm
    val countable_Uprod : thm
    val countable_Usum : thm
    val countable_image_nats : thm
    val countable_surj : thm
    val cross_countable : thm
    val cross_countable_IFF : thm
    val finite_countable : thm
    val image_countable : thm
    val infinite_num_inj : thm
    val infinite_pow_uncountable : thm
    val infinite_rest : thm
    val inj_countable : thm
    val inj_image_countable_IFF : thm
    val inj_surj : thm
    val inter_countable : thm
    val num_countable : thm
    val pair_to_num_formula : thm
    val pair_to_num_inv : thm
    val pairwise_SUBSET : thm
    val pairwise_UNION : thm
    val partition_CARD : thm
    val partition_SUBSET : thm
    val partition_elements_disjoint : thm
    val partition_elements_interrelate : thm
    val pow_no_surj : thm
    val subset_countable : thm
    val union_countable : thm
    val union_countable_IFF : thm

  val pred_set_grammars : type_grammar.grammar * term_grammar.grammar

  val SET_SPEC_ss : simpLib.ssfrag

(*
   [numpair] Parent theory of "pred_set"

   [BIGINTER]  Definition

      |- ∀P. BIGINTER P = {x | ∀s. s ∈ P ⇒ x ∈ s}

   [BIGUNION]  Definition

      |- ∀P. BIGUNION P = {x | ∃s. s ∈ P ∧ x ∈ s}

   [BIJ_DEF]  Definition

      |- ∀f s t. BIJ f s t ⇔ INJ f s t ∧ SURJ f s t

   [CARD_DEF]  Definition

      |- (CARD ∅ = 0) ∧
         ∀s.
           FINITE s ⇒
           ∀x. CARD (x INSERT s) = if x ∈ s then CARD s else SUC (CARD s)

   [CHOICE_DEF]  Definition

      |- ∀s. s ≠ ∅ ⇒ CHOICE s ∈ s

   [COMPL_DEF]  Definition

      |- ∀P. COMPL P = 𝕌(:α) DIFF P

   [CROSS_DEF]  Definition

      |- ∀P Q. P × Q = {p | FST p ∈ P ∧ SND p ∈ Q}

   [DELETE_DEF]  Definition

      |- ∀s x. s DELETE x = s DIFF {x}

   [DIFF_DEF]  Definition

      |- ∀s t. s DIFF t = {x | x ∈ s ∧ x ∉ t}

   [DISJOINT_DEF]  Definition

      |- ∀s t. DISJOINT s t ⇔ (s ∩ t = ∅)

   [EMPTY_DEF]  Definition

      |- ∅ = (λx. F)

   [FINITE_DEF]  Definition

      |- ∀s. FINITE s ⇔ ∀P. P ∅ ∧ (∀s. P s ⇒ ∀e. P (e INSERT s)) ⇒ P s

   [GSPECIFICATION]  Definition

      |- ∀f v. v ∈ GSPEC f ⇔ ∃x. (v,T) = f x

   [IMAGE_DEF]  Definition

      |- ∀f s. IMAGE f s = {f x | x ∈ s}

   [INJ_DEF]  Definition

      |- ∀f s t.
           INJ f s t ⇔
           (∀x. x ∈ s ⇒ f x ∈ t) ∧
           ∀x y. x ∈ s ∧ y ∈ s ⇒ (f x = f y) ⇒ (x = y)

   [INSERT_DEF]  Definition

      |- ∀x s. x INSERT s = {y | (y = x) ∨ y ∈ s}

   [INTER_DEF]  Definition

      |- ∀s t. s ∩ t = {x | x ∈ s ∧ x ∈ t}

   [ITSET_curried_def]  Definition

      |- ∀f x x1. ITSET f x x1 = ITSET_tupled f (x,x1)

   [ITSET_tupled_primitive_def]  Definition

      |- ∀f.
           ITSET_tupled f =
           WFREC
             (@R.
                WF R ∧
                ∀b s. FINITE s ∧ s ≠ ∅ ⇒ R (REST s,f (CHOICE s) b) (s,b))
             (λITSET_tupled a.
                case a of
                  (s,b) =>
                    I
                      (if FINITE s then
                         if s = ∅ then b
                         else ITSET_tupled (REST s,f (CHOICE s) b)
                       else ARB))

   [LINV_DEF]  Definition

      |- ∀f s t. INJ f s t ⇒ ∀x. x ∈ s ⇒ (LINV f s (f x) = x)

   [MAX_SET_DEF]  Definition

      |- ∀s. FINITE s ∧ s ≠ ∅ ⇒ MAX_SET s ∈ s ∧ ∀y. y ∈ s ⇒ y ≤ MAX_SET s

   [MIN_SET_DEF]  Definition

      |- MIN_SET = $LEAST

   [POW_DEF]  Definition

      |- ∀set. POW set = {s | s ⊆ set}

   [PROD_IMAGE_DEF]  Definition

      |- ∀f s. Π f s = ITSET (λe acc. f e * acc) s 1

   [PROD_SET_DEF]  Definition

      |- PROD_SET = Π I

   [PSUBSET_DEF]  Definition

      |- ∀s t. s ⊂ t ⇔ s ⊆ t ∧ s ≠ t

   [REL_RESTRICT_DEF]  Definition

      |- ∀R s x y. REL_RESTRICT R s x y ⇔ x ∈ s ∧ y ∈ s ∧ R x y

   [REST_DEF]  Definition

      |- ∀s. REST s = s DELETE CHOICE s

   [RINV_DEF]  Definition

      |- ∀f s t. SURJ f s t ⇒ ∀x. x ∈ t ⇒ (f (RINV f s x) = x)

   [SING_DEF]  Definition

      |- ∀s. SING s ⇔ ∃x. s = {x}

   [SUBSET_DEF]  Definition

      |- ∀s t. s ⊆ t ⇔ ∀x. x ∈ s ⇒ x ∈ t

   [SUM_IMAGE_DEF]  Definition

      |- ∀f s. ∑ f s = ITSET (λe acc. f e + acc) s 0

   [SUM_SET_DEF]  Definition

      |- SUM_SET = ∑ I

   [SURJ_DEF]  Definition

      |- ∀f s t.
           SURJ f s t ⇔
           (∀x. x ∈ s ⇒ f x ∈ t) ∧ ∀x. x ∈ t ⇒ ∃y. y ∈ s ∧ (f y = x)

   [UNION_DEF]  Definition

      |- ∀s t. s ∪ t = {x | x ∈ s ∨ x ∈ t}

   [UNIV_DEF]  Definition

      |- 𝕌(:α) = (λx. T)

   [chooser_def]  Definition

      |- (∀s. chooser s 0 = CHOICE s) ∧
         ∀s n. chooser s (SUC n) = chooser (REST s) n

   [count_def]  Definition

      |- ∀n. count n = {m | m < n}

   [countable_def]  Definition

      |- ∀s. countable s ⇔ ∃f. INJ f s 𝕌(:num)

   [equiv_on_def]  Definition

      |- ∀R s.
           R equiv_on s ⇔
           (∀x. x ∈ s ⇒ R x x) ∧ (∀x y. x ∈ s ∧ y ∈ s ⇒ (R x y ⇔ R y x)) ∧
           ∀x y z. x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ R x y ∧ R y z ⇒ R x z

   [num_to_pair_def]  Definition

      |- ∀n. num_to_pair n = (nfst n,nsnd n)

   [pair_to_num_def]  Definition

      |- ∀m n. pair_to_num (m,n) = m ⊗ n

   [pairwise_def]  Definition

      |- ∀P s. pairwise P s ⇔ ∀e1 e2. e1 ∈ s ∧ e2 ∈ s ⇒ P e1 e2

   [partition_def]  Definition

      |- ∀R s. partition R s = {t | ∃x. x ∈ s ∧ (t = {y | y ∈ s ∧ R x y})}

   [ABSORPTION]  Theorem

      |- ∀x s. x ∈ s ⇔ (x INSERT s = s)

   [ABSORPTION_RWT]  Theorem

      |- ∀x s. x ∈ s ⇒ (x INSERT s = s)

   [ABS_DIFF_SUM_IMAGE]  Theorem

      |- ∀s.
           FINITE s ⇒
           ABS_DIFF (∑ f s) (∑ g s) ≤ ∑ (λx. ABS_DIFF (f x) (g x)) s

   [ABS_applied]  Theorem

      |- T

   [BIGINTER_EMPTY]  Theorem

      |- BIGINTER ∅ = 𝕌(:α)

   [BIGINTER_INSERT]  Theorem

      |- ∀P B. BIGINTER (P INSERT B) = P ∩ BIGINTER B

   [BIGINTER_INTER]  Theorem

      |- ∀P Q. BIGINTER {P; Q} = P ∩ Q

   [BIGINTER_SING]  Theorem

      |- ∀P. BIGINTER {P} = P

   [BIGINTER_UNION]  Theorem

      |- ∀s1 s2. BIGINTER (s1 ∪ s2) = BIGINTER s1 ∩ BIGINTER s2

   [BIGINTER_applied]  Theorem

      |- BIGINTER B x ⇔ ∀P. P ∈ B ⇒ x ∈ P

   [BIGUNION_EMPTY]  Theorem

      |- BIGUNION ∅ = ∅

   [BIGUNION_EQ_EMPTY]  Theorem

      |- ∀P.
           ((BIGUNION P = ∅) ⇔ (P = ∅) ∨ (P = {∅})) ∧
           ((∅ = BIGUNION P) ⇔ (P = ∅) ∨ (P = {∅}))

   [BIGUNION_INSERT]  Theorem

      |- ∀s P. BIGUNION (s INSERT P) = s ∪ BIGUNION P

   [BIGUNION_SING]  Theorem

      |- ∀x. BIGUNION {x} = x

   [BIGUNION_SUBSET]  Theorem

      |- ∀X P. BIGUNION P ⊆ X ⇔ ∀Y. Y ∈ P ⇒ Y ⊆ X

   [BIGUNION_UNION]  Theorem

      |- ∀s1 s2. BIGUNION (s1 ∪ s2) = BIGUNION s1 ∪ BIGUNION s2

   [BIGUNION_applied]  Theorem

      |- ∀x sos. BIGUNION sos x ⇔ ∃s. x ∈ s ∧ s ∈ sos

   [BIGUNION_partition]  Theorem

      |- R equiv_on s ⇒ (BIGUNION (partition R s) = s)

   [BIJ_COMPOSE]  Theorem

      |- ∀f g s t u. BIJ f s t ∧ BIJ g t u ⇒ BIJ (g o f) s u

   [BIJ_DELETE]  Theorem

      |- ∀s t f. BIJ f s t ⇒ ∀e. e ∈ s ⇒ BIJ f (s DELETE e) (t DELETE f e)

   [BIJ_EMPTY]  Theorem

      |- ∀f. (∀s. BIJ f ∅ s ⇔ (s = ∅)) ∧ ∀s. BIJ f s ∅ ⇔ (s = ∅)

   [BIJ_FINITE]  Theorem

      |- ∀f s t. BIJ f s t ∧ FINITE s ⇒ FINITE t

   [BIJ_ID]  Theorem

      |- ∀s. BIJ (λx. x) s s

   [BIJ_IFF_INV]  Theorem

      |- ∀f s t.
           BIJ f s t ⇔
           (∀x. x ∈ s ⇒ f x ∈ t) ∧
           ∃g.
             (∀x. x ∈ t ⇒ g x ∈ s) ∧ (∀x. x ∈ s ⇒ (g (f x) = x)) ∧
             ∀x. x ∈ t ⇒ (f (g x) = x)

   [BIJ_INSERT]  Theorem

      |- BIJ f (e INSERT s) t ⇔
         e ∉ s ∧ f e ∈ t ∧ BIJ f s (t DELETE f e) ∨ e ∈ s ∧ BIJ f s t

   [BIJ_LINV_BIJ]  Theorem

      |- ∀f s t. BIJ f s t ⇒ BIJ (LINV f s) t s

   [BIJ_LINV_INV]  Theorem

      |- ∀f s t. BIJ f s t ⇒ ∀x. x ∈ t ⇒ (f (LINV f s x) = x)

   [CARD_BIGUNION_SAME_SIZED_SETS]  Theorem

      |- ∀n s.
           FINITE s ∧ (∀e. e ∈ s ⇒ FINITE e ∧ (CARD e = n)) ∧
           (∀e1 e2. e1 ∈ s ∧ e2 ∈ s ∧ e1 ≠ e2 ⇒ DISJOINT e1 e2) ⇒
           (CARD (BIGUNION s) = CARD s * n)

   [CARD_COUNT]  Theorem

      |- ∀n. CARD (count n) = n

   [CARD_CROSS]  Theorem

      |- ∀P Q. FINITE P ∧ FINITE Q ⇒ (CARD (P × Q) = CARD P * CARD Q)

   [CARD_DELETE]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀x. CARD (s DELETE x) = if x ∈ s then CARD s − 1 else CARD s

   [CARD_DIFF]  Theorem

      |- ∀t.
           FINITE t ⇒
           ∀s. FINITE s ⇒ (CARD (s DIFF t) = CARD s − CARD (s ∩ t))

   [CARD_DIFF_EQN]  Theorem

      |- ∀s. FINITE s ⇒ (CARD (s DIFF t) = CARD s − CARD (s ∩ t))

   [CARD_EMPTY]  Theorem

      |- CARD ∅ = 0

   [CARD_EQ_0]  Theorem

      |- ∀s. FINITE s ⇒ ((CARD s = 0) ⇔ (s = ∅))

   [CARD_INJ_IMAGE]  Theorem

      |- ∀f s.
           (∀x y. (f x = f y) ⇔ (x = y)) ∧ FINITE s ⇒
           (CARD (IMAGE f s) = CARD s)

   [CARD_INSERT]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀x. CARD (x INSERT s) = if x ∈ s then CARD s else SUC (CARD s)

   [CARD_INTER_LESS_EQ]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. CARD (s ∩ t) ≤ CARD s

   [CARD_POW]  Theorem

      |- ∀s. FINITE s ⇒ (CARD (POW s) = 2 ** CARD s)

   [CARD_PSUBSET]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. t ⊂ s ⇒ CARD t < CARD s

   [CARD_SING]  Theorem

      |- ∀x. CARD {x} = 1

   [CARD_SING_CROSS]  Theorem

      |- ∀x P. FINITE P ⇒ (CARD ({x} × P) = CARD P)

   [CARD_SUBSET]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. t ⊆ s ⇒ CARD t ≤ CARD s

   [CARD_UNION]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀t. FINITE t ⇒ (CARD (s ∪ t) + CARD (s ∩ t) = CARD s + CARD t)

   [CARD_UNION_EQN]  Theorem

      |- ∀s t.
           FINITE s ∧ FINITE t ⇒
           (CARD (s ∪ t) = CARD s + CARD t − CARD (s ∩ t))

   [CHOICE_INSERT_REST]  Theorem

      |- ∀s. s ≠ ∅ ⇒ (CHOICE s INSERT REST s = s)

   [CHOICE_NOT_IN_REST]  Theorem

      |- ∀s. CHOICE s ∉ REST s

   [CHOICE_SING]  Theorem

      |- ∀x. CHOICE {x} = x

   [COMMUTING_ITSET_INSERT]  Theorem

      |- ∀f s.
           (∀x y z. f x (f y z) = f y (f x z)) ∧ FINITE s ⇒
           ∀x b. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)

   [COMMUTING_ITSET_RECURSES]  Theorem

      |- ∀f e s b.
           (∀x y z. f x (f y z) = f y (f x z)) ∧ FINITE s ⇒
           (ITSET f (e INSERT s) b = f e (ITSET f (s DELETE e) b))

   [COMPL_CLAUSES]  Theorem

      |- ∀s. (COMPL s ∩ s = ∅) ∧ (COMPL s ∪ s = 𝕌(:α))

   [COMPL_COMPL]  Theorem

      |- ∀s. COMPL (COMPL s) = s

   [COMPL_EMPTY]  Theorem

      |- COMPL ∅ = 𝕌(:α)

   [COMPL_INTER]  Theorem

      |- (x ∩ COMPL x = ∅) ∧ (COMPL x ∩ x = ∅)

   [COMPL_SPLITS]  Theorem

      |- ∀p q. p ∩ q ∪ COMPL p ∩ q = q

   [COMPL_UNION]  Theorem

      |- COMPL (s ∪ t) = COMPL s ∩ COMPL t

   [COMPL_applied]  Theorem

      |- ∀x s. COMPL s x ⇔ x ∉ s

   [COMPONENT]  Theorem

      |- ∀x s. x ∈ x INSERT s

   [COUNT_11]  Theorem

      |- (count n1 = count n2) ⇔ (n1 = n2)

   [COUNT_SUC]  Theorem

      |- ∀n. count (SUC n) = n INSERT count n

   [COUNT_ZERO]  Theorem

      |- count 0 = ∅

   [COUNT_applied]  Theorem

      |- ∀m n. count n m ⇔ m < n

   [CROSS_EMPTY]  Theorem

      |- ∀P. (P × ∅ = ∅) ∧ (∅ × P = ∅)

   [CROSS_EQNS]  Theorem

      |- ∀s1 s2.
           (∅ × s2 = ∅) ∧
           ((a INSERT s1) × s2 = IMAGE (λy. (a,y)) s2 ∪ s1 × s2)

   [CROSS_INSERT_LEFT]  Theorem

      |- ∀P Q x. (x INSERT P) × Q = {x} × Q ∪ P × Q

   [CROSS_INSERT_RIGHT]  Theorem

      |- ∀P Q x. P × (x INSERT Q) = P × {x} ∪ P × Q

   [CROSS_SINGS]  Theorem

      |- ∀x y. {x} × {y} = {(x,y)}

   [CROSS_SUBSET]  Theorem

      |- ∀P Q P0 Q0.
           P0 × Q0 ⊆ P × Q ⇔ (P0 = ∅) ∨ (Q0 = ∅) ∨ P0 ⊆ P ∧ Q0 ⊆ Q

   [CROSS_UNIV]  Theorem

      |- 𝕌(:α # β) = 𝕌(:α) × 𝕌(:β)

   [CROSS_applied]  Theorem

      |- ∀P Q x. (P × Q) x ⇔ FST x ∈ P ∧ SND x ∈ Q

   [DECOMPOSITION]  Theorem

      |- ∀s x. x ∈ s ⇔ ∃t. (s = x INSERT t) ∧ x ∉ t

   [DELETE_COMM]  Theorem

      |- ∀x y s. s DELETE x DELETE y = s DELETE y DELETE x

   [DELETE_DELETE]  Theorem

      |- ∀x s. s DELETE x DELETE x = s DELETE x

   [DELETE_EQ_SING]  Theorem

      |- ∀s x. x ∈ s ⇒ ((s DELETE x = ∅) ⇔ (s = {x}))

   [DELETE_INSERT]  Theorem

      |- ∀x y s.
           (x INSERT s) DELETE y =
           if x = y then s DELETE y else x INSERT s DELETE y

   [DELETE_INTER]  Theorem

      |- ∀s t x. (s DELETE x) ∩ t = s ∩ t DELETE x

   [DELETE_NON_ELEMENT]  Theorem

      |- ∀x s. x ∉ s ⇔ (s DELETE x = s)

   [DELETE_SUBSET]  Theorem

      |- ∀x s. s DELETE x ⊆ s

   [DELETE_SUBSET_INSERT]  Theorem

      |- ∀s e s2. s DELETE e ⊆ s2 ⇔ s ⊆ e INSERT s2

   [DELETE_applied]  Theorem

      |- ∀s x y. (s DELETE y) x ⇔ x ∈ s ∧ x ≠ y

   [DIFF_COMM]  Theorem

      |- ∀x y z. x DIFF y DIFF z = x DIFF z DIFF y

   [DIFF_DIFF]  Theorem

      |- ∀s t. s DIFF t DIFF t = s DIFF t

   [DIFF_EMPTY]  Theorem

      |- ∀s. s DIFF ∅ = s

   [DIFF_EQ_EMPTY]  Theorem

      |- ∀s. s DIFF s = ∅

   [DIFF_INSERT]  Theorem

      |- ∀s t x. s DIFF (x INSERT t) = s DELETE x DIFF t

   [DIFF_SAME_UNION]  Theorem

      |- ∀x y. (x ∪ y DIFF x = y DIFF x) ∧ (x ∪ y DIFF y = x DIFF y)

   [DIFF_SUBSET]  Theorem

      |- ∀s t. s DIFF t ⊆ s

   [DIFF_UNION]  Theorem

      |- ∀x y z. x DIFF (y ∪ z) = x DIFF y DIFF z

   [DIFF_UNIV]  Theorem

      |- ∀s. s DIFF 𝕌(:α) = ∅

   [DIFF_applied]  Theorem

      |- ∀s t x. (s DIFF t) x ⇔ x ∈ s ∧ x ∉ t

   [DISJOINT_BIGINTER]  Theorem

      |- ∀X Y P.
           Y ∈ P ∧ DISJOINT Y X ⇒
           DISJOINT X (BIGINTER P) ∧ DISJOINT (BIGINTER P) X

   [DISJOINT_BIGUNION]  Theorem

      |- (∀s t. DISJOINT (BIGUNION s) t ⇔ ∀s'. s' ∈ s ⇒ DISJOINT s' t) ∧
         ∀s t. DISJOINT t (BIGUNION s) ⇔ ∀s'. s' ∈ s ⇒ DISJOINT t s'

   [DISJOINT_DELETE_SYM]  Theorem

      |- ∀s t x. DISJOINT (s DELETE x) t ⇔ DISJOINT (t DELETE x) s

   [DISJOINT_EMPTY]  Theorem

      |- ∀s. DISJOINT ∅ s ∧ DISJOINT s ∅

   [DISJOINT_EMPTY_REFL]  Theorem

      |- ∀s. (s = ∅) ⇔ DISJOINT s s

   [DISJOINT_EMPTY_REFL_RWT]  Theorem

      |- ∀s. DISJOINT s s ⇔ (s = ∅)

   [DISJOINT_INSERT]  Theorem

      |- ∀x s t. DISJOINT (x INSERT s) t ⇔ DISJOINT s t ∧ x ∉ t

   [DISJOINT_SING_EMPTY]  Theorem

      |- ∀x. DISJOINT {x} ∅

   [DISJOINT_SUBSET]  Theorem

      |- ∀s t u. DISJOINT s t ∧ u ⊆ t ⇒ DISJOINT s u

   [DISJOINT_SYM]  Theorem

      |- ∀s t. DISJOINT s t ⇔ DISJOINT t s

   [DISJOINT_UNION]  Theorem

      |- ∀s t u. DISJOINT (s ∪ t) u ⇔ DISJOINT s u ∧ DISJOINT t u

   [DISJOINT_UNION_BOTH]  Theorem

      |- ∀s t u.
           (DISJOINT (s ∪ t) u ⇔ DISJOINT s u ∧ DISJOINT t u) ∧
           (DISJOINT u (s ∪ t) ⇔ DISJOINT s u ∧ DISJOINT t u)

   [EMPTY_DELETE]  Theorem

      |- ∀x. ∅ DELETE x = ∅

   [EMPTY_DIFF]  Theorem

      |- ∀s. ∅ DIFF s = ∅

   [EMPTY_NOT_IN_partition]  Theorem

      |- R equiv_on s ⇒ ∅ ∉ partition R s

   [EMPTY_NOT_UNIV]  Theorem

      |- ∅ ≠ 𝕌(:α)

   [EMPTY_SUBSET]  Theorem

      |- ∀s. ∅ ⊆ s

   [EMPTY_UNION]  Theorem

      |- ∀s t. (s ∪ t = ∅) ⇔ (s = ∅) ∧ (t = ∅)

   [EMPTY_applied]  Theorem

      |- ∅ x ⇔ F

   [EQUAL_SING]  Theorem

      |- ∀x y. ({x} = {y}) ⇔ (x = y)

   [EQ_UNIV]  Theorem

      |- (∀x. x ∈ s) ⇔ (s = 𝕌(:α))

   [EXTENSION]  Theorem

      |- ∀s t. (s = t) ⇔ ∀x. x ∈ s ⇔ x ∈ t

   [FINITELY_INJECTIVE_IMAGE_FINITE]  Theorem

      |- ∀f. (∀x. FINITE {y | x = f y}) ⇒ ∀s. FINITE (IMAGE f s) ⇔ FINITE s

   [FINITE_BIGUNION]  Theorem

      |- ∀P. FINITE P ∧ (∀s. s ∈ P ⇒ FINITE s) ⇒ FINITE (BIGUNION P)

   [FINITE_BIGUNION_EQ]  Theorem

      |- ∀P. FINITE (BIGUNION P) ⇔ FINITE P ∧ ∀s. s ∈ P ⇒ FINITE s

   [FINITE_BIJ_CARD_EQ]  Theorem

      |- ∀S. FINITE S ⇒ ∀t f. BIJ f S t ∧ FINITE t ⇒ (CARD S = CARD t)

   [FINITE_COMPLETE_INDUCTION]  Theorem

      |- ∀P. (∀x. (∀y. y ⊂ x ⇒ P y) ⇒ FINITE x ⇒ P x) ⇒ ∀x. FINITE x ⇒ P x

   [FINITE_COUNT]  Theorem

      |- ∀n. FINITE (count n)

   [FINITE_CROSS]  Theorem

      |- ∀P Q. FINITE P ∧ FINITE Q ⇒ FINITE (P × Q)

   [FINITE_CROSS_EQ]  Theorem

      |- ∀P Q. FINITE (P × Q) ⇔ (P = ∅) ∨ (Q = ∅) ∨ FINITE P ∧ FINITE Q

   [FINITE_DELETE]  Theorem

      |- ∀x s. FINITE (s DELETE x) ⇔ FINITE s

   [FINITE_DIFF]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. FINITE (s DIFF t)

   [FINITE_DIFF_down]  Theorem

      |- ∀P Q. FINITE (P DIFF Q) ∧ FINITE Q ⇒ FINITE P

   [FINITE_EMPTY]  Theorem

      |- FINITE ∅

   [FINITE_INDUCT]  Theorem

      |- ∀P.
           P ∅ ∧ (∀s. FINITE s ∧ P s ⇒ ∀e. e ∉ s ⇒ P (e INSERT s)) ⇒
           ∀s. FINITE s ⇒ P s

   [FINITE_INJ]  Theorem

      |- ∀f s t. INJ f s t ∧ FINITE t ⇒ FINITE s

   [FINITE_INSERT]  Theorem

      |- ∀x s. FINITE (x INSERT s) ⇔ FINITE s

   [FINITE_INTER]  Theorem

      |- ∀s1 s2. FINITE s1 ∨ FINITE s2 ⇒ FINITE (s1 ∩ s2)

   [FINITE_ISO_NUM]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∃f.
             (∀n m. n < CARD s ∧ m < CARD s ⇒ (f n = f m) ⇒ (n = m)) ∧
             (s = {f n | n < CARD s})

   [FINITE_POW]  Theorem

      |- ∀s. FINITE s ⇒ FINITE (POW s)

   [FINITE_PSUBSET_INFINITE]  Theorem

      |- ∀s. INFINITE s ⇔ ∀t. FINITE t ⇒ t ⊆ s ⇒ t ⊂ s

   [FINITE_PSUBSET_UNIV]  Theorem

      |- INFINITE 𝕌(:α) ⇔ ∀s. FINITE s ⇒ s ⊂ 𝕌(:α)

   [FINITE_REST]  Theorem

      |- ∀s. FINITE s ⇒ FINITE (REST s)

   [FINITE_SING]  Theorem

      |- ∀x. FINITE {x}

   [FINITE_StrongOrder_WF]  Theorem

      |- ∀R s.
           FINITE s ∧ StrongOrder (REL_RESTRICT R s) ⇒
           WF (REL_RESTRICT R s)

   [FINITE_UNION]  Theorem

      |- ∀s t. FINITE (s ∪ t) ⇔ FINITE s ∧ FINITE t

   [FINITE_WEAK_ENUMERATE]  Theorem

      |- ∀s. FINITE s ⇔ ∃f b. ∀e. e ∈ s ⇔ ∃n. n < b ∧ (e = f n)

   [FINITE_WF_noloops]  Theorem

      |- ∀s.
           FINITE s ⇒
           (WF (REL_RESTRICT R s) ⇔ irreflexive (REL_RESTRICT R s)⁺)

   [FINITE_partition]  Theorem

      |- ∀R s.
           FINITE s ⇒
           FINITE (partition R s) ∧ ∀t. t ∈ partition R s ⇒ FINITE t

   [GSPEC_AND]  Theorem

      |- ∀P Q. {x | P x ∧ Q x} = {x | P x} ∩ {x | Q x}

   [GSPEC_EQ]  Theorem

      |- {x | x = y} = {y}

   [GSPEC_EQ2]  Theorem

      |- {x | y = x} = {y}

   [GSPEC_ETA]  Theorem

      |- {x | P x} = P

   [GSPEC_F]  Theorem

      |- {x | F} = ∅

   [GSPEC_F_COND]  Theorem

      |- ∀f. (∀x. ¬SND (f x)) ⇒ (GSPEC f = ∅)

   [GSPEC_ID]  Theorem

      |- {x | x ∈ y} = y

   [GSPEC_OR]  Theorem

      |- ∀P Q. {x | P x ∨ Q x} = {x | P x} ∪ {x | Q x}

   [GSPEC_T]  Theorem

      |- {x | T} = 𝕌(:α)

   [IMAGE_11]  Theorem

      |- (∀x y. (f x = f y) ⇔ (x = y)) ⇒
         ((IMAGE f s1 = IMAGE f s2) ⇔ (s1 = s2))

   [IMAGE_11_INFINITE]  Theorem

      |- ∀f.
           (∀x y. (f x = f y) ⇒ (x = y)) ⇒
           ∀s. INFINITE s ⇒ INFINITE (IMAGE f s)

   [IMAGE_BIGUNION]  Theorem

      |- ∀f M. IMAGE f (BIGUNION M) = BIGUNION (IMAGE (IMAGE f) M)

   [IMAGE_COMPOSE]  Theorem

      |- ∀f g s. IMAGE (f o g) s = IMAGE f (IMAGE g s)

   [IMAGE_CONG]  Theorem

      |- ∀f s f' s'.
           (s = s') ∧ (∀x. x ∈ s' ⇒ (f x = f' x)) ⇒
           (IMAGE f s = IMAGE f' s')

   [IMAGE_DELETE]  Theorem

      |- ∀f x s. x ∉ s ⇒ (IMAGE f (s DELETE x) = IMAGE f s)

   [IMAGE_EMPTY]  Theorem

      |- ∀f. IMAGE f ∅ = ∅

   [IMAGE_EQ_EMPTY]  Theorem

      |- ∀s f. (IMAGE f s = ∅) ⇔ (s = ∅)

   [IMAGE_FINITE]  Theorem

      |- ∀s. FINITE s ⇒ ∀f. FINITE (IMAGE f s)

   [IMAGE_ID]  Theorem

      |- ∀s. IMAGE (λx. x) s = s

   [IMAGE_IN]  Theorem

      |- ∀x s. x ∈ s ⇒ ∀f. f x ∈ IMAGE f s

   [IMAGE_INSERT]  Theorem

      |- ∀f x s. IMAGE f (x INSERT s) = f x INSERT IMAGE f s

   [IMAGE_INTER]  Theorem

      |- ∀f s t. IMAGE f (s ∩ t) ⊆ IMAGE f s ∩ IMAGE f t

   [IMAGE_SUBSET]  Theorem

      |- ∀s t. s ⊆ t ⇒ ∀f. IMAGE f s ⊆ IMAGE f t

   [IMAGE_SURJ]  Theorem

      |- ∀f s t. SURJ f s t ⇔ (IMAGE f s = t)

   [IMAGE_UNION]  Theorem

      |- ∀f s t. IMAGE f (s ∪ t) = IMAGE f s ∪ IMAGE f t

   [IMAGE_applied]  Theorem

      |- ∀y s f. IMAGE f s y ⇔ ∃x. (y = f x) ∧ x ∈ s

   [INFINITE_DEF]  Theorem

      |- T

   [INFINITE_DIFF_FINITE]  Theorem

      |- ∀s t. INFINITE s ∧ FINITE t ⇒ s DIFF t ≠ ∅

   [INFINITE_INHAB]  Theorem

      |- ∀P. INFINITE P ⇒ ∃x. x ∈ P

   [INFINITE_NUM_UNIV]  Theorem

      |- INFINITE 𝕌(:num)

   [INFINITE_PAIR_UNIV]  Theorem

      |- FINITE 𝕌(:α # β) ⇔ FINITE 𝕌(:α) ∧ FINITE 𝕌(:β)

   [INFINITE_SUBSET]  Theorem

      |- ∀s. INFINITE s ⇒ ∀t. s ⊆ t ⇒ INFINITE t

   [INFINITE_UNIV]  Theorem

      |- INFINITE 𝕌(:α) ⇔
         ∃f. (∀x y. (f x = f y) ⇒ (x = y)) ∧ ∃y. ∀x. f x ≠ y

   [INJECTIVE_IMAGE_FINITE]  Theorem

      |- ∀f.
           (∀x y. (f x = f y) ⇔ (x = y)) ⇒
           ∀s. FINITE (IMAGE f s) ⇔ FINITE s

   [INJ_CARD]  Theorem

      |- ∀f s t. INJ f s t ∧ FINITE t ⇒ CARD s ≤ CARD t

   [INJ_COMPOSE]  Theorem

      |- ∀f g s t u. INJ f s t ∧ INJ g t u ⇒ INJ (g o f) s u

   [INJ_DELETE]  Theorem

      |- ∀s t f. INJ f s t ⇒ ∀e. e ∈ s ⇒ INJ f (s DELETE e) (t DELETE f e)

   [INJ_EMPTY]  Theorem

      |- ∀f. (∀s. INJ f ∅ s) ∧ ∀s. INJ f s ∅ ⇔ (s = ∅)

   [INJ_ID]  Theorem

      |- ∀s. INJ (λx. x) s s

   [INJ_IFF]  Theorem

      |- INJ f s t ⇔
         (∀x. x ∈ s ⇒ f x ∈ t) ∧
         ∀x y. x ∈ s ∧ y ∈ s ⇒ ((f x = f y) ⇔ (x = y))

   [INJ_INL]  Theorem

      |- (∀x. x ∈ s ⇒ INL x ∈ t) ⇒ INJ INL s t

   [INJ_INR]  Theorem

      |- (∀x. x ∈ s ⇒ INR x ∈ t) ⇒ INJ INR s t

   [INJ_INSERT]  Theorem

      |- ∀f x s t.
           INJ f (x INSERT s) t ⇔
           INJ f s t ∧ f x ∈ t ∧ ∀y. y ∈ s ∧ (f x = f y) ⇒ (x = y)

   [INJ_SUBSET]  Theorem

      |- ∀f s t s0 t0. INJ f s t ∧ s0 ⊆ s ∧ t ⊆ t0 ⇒ INJ f s0 t0

   [INSERT_COMM]  Theorem

      |- ∀x y s. x INSERT y INSERT s = y INSERT x INSERT s

   [INSERT_DELETE]  Theorem

      |- ∀x s. x ∈ s ⇒ (x INSERT s DELETE x = s)

   [INSERT_DIFF]  Theorem

      |- ∀s t x.
           (x INSERT s) DIFF t =
           if x ∈ t then s DIFF t else x INSERT s DIFF t

   [INSERT_INSERT]  Theorem

      |- ∀x s. x INSERT x INSERT s = x INSERT s

   [INSERT_INTER]  Theorem

      |- ∀x s t. (x INSERT s) ∩ t = if x ∈ t then x INSERT s ∩ t else s ∩ t

   [INSERT_SING_UNION]  Theorem

      |- ∀s x. x INSERT s = {x} ∪ s

   [INSERT_SUBSET]  Theorem

      |- ∀x s t. x INSERT s ⊆ t ⇔ x ∈ t ∧ s ⊆ t

   [INSERT_UNION]  Theorem

      |- ∀x s t. (x INSERT s) ∪ t = if x ∈ t then s ∪ t else x INSERT s ∪ t

   [INSERT_UNION_EQ]  Theorem

      |- ∀x s t. (x INSERT s) ∪ t = x INSERT s ∪ t

   [INSERT_UNIV]  Theorem

      |- ∀x. x INSERT 𝕌(:α) = 𝕌(:α)

   [INSERT_applied]  Theorem

      |- ∀x y s. (y INSERT s) x ⇔ (x = y) ∨ x ∈ s

   [INTER_ASSOC]  Theorem

      |- ∀s t u. s ∩ (t ∩ u) = s ∩ t ∩ u

   [INTER_COMM]  Theorem

      |- ∀s t. s ∩ t = t ∩ s

   [INTER_EMPTY]  Theorem

      |- (∀s. ∅ ∩ s = ∅) ∧ ∀s. s ∩ ∅ = ∅

   [INTER_FINITE]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. FINITE (s ∩ t)

   [INTER_IDEMPOT]  Theorem

      |- ∀s. s ∩ s = s

   [INTER_OVER_UNION]  Theorem

      |- ∀s t u. s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u)

   [INTER_SUBSET]  Theorem

      |- (∀s t. s ∩ t ⊆ s) ∧ ∀s t. t ∩ s ⊆ s

   [INTER_SUBSET_EQN]  Theorem

      |- ((A ∩ B = A) ⇔ A ⊆ B) ∧ ((A ∩ B = B) ⇔ B ⊆ A)

   [INTER_UNION]  Theorem

      |- ((A ∪ B) ∩ A = A) ∧ ((B ∪ A) ∩ A = A) ∧ (A ∩ (A ∪ B) = A) ∧
         (A ∩ (B ∪ A) = A)

   [INTER_UNION_COMPL]  Theorem

      |- ∀s t. s ∩ t = COMPL (COMPL s ∪ COMPL t)

   [INTER_UNIV]  Theorem

      |- (∀s. 𝕌(:α) ∩ s = s) ∧ ∀s. s ∩ 𝕌(:α) = s

   [INTER_applied]  Theorem

      |- ∀s t x. (s ∩ t) x ⇔ x ∈ s ∧ x ∈ t

   [IN_ABS]  Theorem

      |- ∀x P. x ∈ (λx. P x) ⇔ P x

   [IN_BIGINTER]  Theorem

      |- x ∈ BIGINTER B ⇔ ∀P. P ∈ B ⇒ x ∈ P

   [IN_BIGUNION]  Theorem

      |- ∀x sos. x ∈ BIGUNION sos ⇔ ∃s. x ∈ s ∧ s ∈ sos

   [IN_COMPL]  Theorem

      |- ∀x s. x ∈ COMPL s ⇔ x ∉ s

   [IN_COUNT]  Theorem

      |- ∀m n. m ∈ count n ⇔ m < n

   [IN_CROSS]  Theorem

      |- ∀P Q x. x ∈ P × Q ⇔ FST x ∈ P ∧ SND x ∈ Q

   [IN_DELETE]  Theorem

      |- ∀s x y. x ∈ s DELETE y ⇔ x ∈ s ∧ x ≠ y

   [IN_DELETE_EQ]  Theorem

      |- ∀s x x'. (x ∈ s ⇔ x' ∈ s) ⇔ (x ∈ s DELETE x' ⇔ x' ∈ s DELETE x)

   [IN_DIFF]  Theorem

      |- ∀s t x. x ∈ s DIFF t ⇔ x ∈ s ∧ x ∉ t

   [IN_DISJOINT]  Theorem

      |- ∀s t. DISJOINT s t ⇔ ¬∃x. x ∈ s ∧ x ∈ t

   [IN_IMAGE]  Theorem

      |- ∀y s f. y ∈ IMAGE f s ⇔ ∃x. (y = f x) ∧ x ∈ s

   [IN_INFINITE_NOT_FINITE]  Theorem

      |- ∀s t. INFINITE s ∧ FINITE t ⇒ ∃x. x ∈ s ∧ x ∉ t

   [IN_INSERT]  Theorem

      |- ∀x y s. x ∈ y INSERT s ⇔ (x = y) ∨ x ∈ s

   [IN_INSERT_EXPAND]  Theorem

      |- ∀x y P. x ∈ y INSERT P ⇔ (x = y) ∨ x ≠ y ∧ x ∈ P

   [IN_INTER]  Theorem

      |- ∀s t x. x ∈ s ∩ t ⇔ x ∈ s ∧ x ∈ t

   [IN_POW]  Theorem

      |- ∀set e. e ∈ POW set ⇔ e ⊆ set

   [IN_SING]  Theorem

      |- ∀x y. x ∈ {y} ⇔ (x = y)

   [IN_UNION]  Theorem

      |- ∀s t x. x ∈ s ∪ t ⇔ x ∈ s ∨ x ∈ t

   [IN_UNIV]  Theorem

      |- ∀x. x ∈ 𝕌(:α)

   [ITSET_EMPTY]  Theorem

      |- ∀f b. ITSET f ∅ b = b

   [ITSET_IND]  Theorem

      |- ∀P.
           (∀s b.
              (FINITE s ∧ s ≠ ∅ ⇒ P (REST s) (f (CHOICE s) b)) ⇒ P s b) ⇒
           ∀v v1. P v v1

   [ITSET_INSERT]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀f x b.
             ITSET f (x INSERT s) b =
             ITSET f (REST (x INSERT s)) (f (CHOICE (x INSERT s)) b)

   [ITSET_THM]  Theorem

      |- ∀s f b.
           FINITE s ⇒
           (ITSET f s b =
            if s = ∅ then b else ITSET f (REST s) (f (CHOICE s) b))

   [ITSET_def]  Theorem

      |- ∀s f b.
           ITSET f s b =
           if FINITE s then
             if s = ∅ then b else ITSET f (REST s) (f (CHOICE s) b)
           else ARB

   [ITSET_ind]  Theorem

      |- ∀P.
           (∀s b.
              (FINITE s ∧ s ≠ ∅ ⇒ P (REST s) (f (CHOICE s) b)) ⇒ P s b) ⇒
           ∀v v1. P v v1

   [KoenigsLemma]  Theorem

      |- ∀R.
           (∀x. FINITE {y | R x y}) ⇒
           ∀x.
             INFINITE {y | R^* x y} ⇒
             ∃f. (f 0 = x) ∧ ∀n. R (f n) (f (SUC n))

   [KoenigsLemma_WF]  Theorem

      |- ∀R.
           (∀x. FINITE {y | R x y}) ∧ WF (inv R) ⇒ ∀x. FINITE {y | R^* x y}

   [LESS_CARD_DIFF]  Theorem

      |- ∀t.
           FINITE t ⇒ ∀s. FINITE s ⇒ CARD t < CARD s ⇒ 0 < CARD (s DIFF t)

   [MAX_SET_ELIM]  Theorem

      |- ∀P Q.
           FINITE P ∧ P ≠ ∅ ∧ (∀x. (∀y. y ∈ P ⇒ y ≤ x) ∧ x ∈ P ⇒ Q x) ⇒
           Q (MAX_SET P)

   [MAX_SET_THM]  Theorem

      |- (∀e. MAX_SET {e} = e) ∧
         ∀s.
           FINITE s ⇒
           ∀e1 e2.
             MAX_SET (e1 INSERT e2 INSERT s) =
             MAX e1 (MAX_SET (e2 INSERT s))

   [MAX_SET_UNION]  Theorem

      |- ∀A B.
           FINITE A ∧ FINITE B ∧ A ≠ ∅ ∧ B ≠ ∅ ⇒
           (MAX_SET (A ∪ B) = MAX (MAX_SET A) (MAX_SET B))

   [MEMBER_NOT_EMPTY]  Theorem

      |- ∀s. (∃x. x ∈ s) ⇔ s ≠ ∅

   [MIN_SET_ELIM]  Theorem

      |- ∀P Q.
           P ≠ ∅ ∧ (∀x. (∀y. y ∈ P ⇒ x ≤ y) ∧ x ∈ P ⇒ Q x) ⇒ Q (MIN_SET P)

   [MIN_SET_LEM]  Theorem

      |- ∀s. s ≠ ∅ ⇒ MIN_SET s ∈ s ∧ ∀x. x ∈ s ⇒ MIN_SET s ≤ x

   [MIN_SET_LEQ_MAX_SET]  Theorem

      |- ∀s. s ≠ ∅ ∧ FINITE s ⇒ MIN_SET s ≤ MAX_SET s

   [MIN_SET_THM]  Theorem

      |- (∀e. MIN_SET {e} = e) ∧
         ∀s e1 e2.
           MIN_SET (e1 INSERT e2 INSERT s) = MIN e1 (MIN_SET (e2 INSERT s))

   [MIN_SET_UNION]  Theorem

      |- ∀A B.
           FINITE A ∧ FINITE B ∧ A ≠ ∅ ∧ B ≠ ∅ ⇒
           (MIN_SET (A ∪ B) = MIN (MIN_SET A) (MIN_SET B))

   [NOT_EMPTY_INSERT]  Theorem

      |- ∀x s. ∅ ≠ x INSERT s

   [NOT_EMPTY_SING]  Theorem

      |- ∀x. ∅ ≠ {x}

   [NOT_EQUAL_SETS]  Theorem

      |- ∀s t. s ≠ t ⇔ ∃x. x ∈ t ⇔ x ∉ s

   [NOT_INSERT_EMPTY]  Theorem

      |- ∀x s. x INSERT s ≠ ∅

   [NOT_IN_EMPTY]  Theorem

      |- ∀x. x ∉ ∅

   [NOT_IN_FINITE]  Theorem

      |- INFINITE 𝕌(:α) ⇔ ∀s. FINITE s ⇒ ∃x. x ∉ s

   [NOT_PSUBSET_EMPTY]  Theorem

      |- ∀s. ¬(s ⊂ ∅)

   [NOT_SING_EMPTY]  Theorem

      |- ∀x. {x} ≠ ∅

   [NOT_UNIV_PSUBSET]  Theorem

      |- ∀s. ¬(𝕌(:α) ⊂ s)

   [NUM_SET_WOP]  Theorem

      |- ∀s. (∃n. n ∈ s) ⇔ ∃n. n ∈ s ∧ ∀m. m ∈ s ⇒ n ≤ m

   [PHP]  Theorem

      |- ∀f s t. FINITE t ∧ CARD t < CARD s ⇒ ¬INJ f s t

   [POW_EQNS]  Theorem

      |- (POW ∅ = {∅}) ∧
         ∀e s.
           POW (e INSERT s) = (let ps = POW s in IMAGE ($INSERT e) ps ∪ ps)

   [POW_INSERT]  Theorem

      |- ∀e s. POW (e INSERT s) = IMAGE ($INSERT e) (POW s) ∪ POW s

   [PROD_IMAGE_THM]  Theorem

      |- ∀f.
           (Π f ∅ = 1) ∧
           ∀e s. FINITE s ⇒ (Π f (e INSERT s) = f e * Π f (s DELETE e))

   [PROD_SET_EMPTY]  Theorem

      |- PROD_SET ∅ = 1

   [PROD_SET_IMAGE_REDUCTION]  Theorem

      |- ∀f s x.
           FINITE (IMAGE f s) ∧ f x ∉ IMAGE f s ⇒
           (PROD_SET (IMAGE f (x INSERT s)) = f x * PROD_SET (IMAGE f s))

   [PROD_SET_THM]  Theorem

      |- (PROD_SET ∅ = 1) ∧
         ∀x s.
           FINITE s ⇒ (PROD_SET (x INSERT s) = x * PROD_SET (s DELETE x))

   [PSUBSET_EQN]  Theorem

      |- ∀s1 s2. s1 ⊂ s2 ⇔ s1 ⊆ s2 ∧ ¬(s2 ⊆ s1)

   [PSUBSET_FINITE]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. t ⊂ s ⇒ FINITE t

   [PSUBSET_INSERT_SUBSET]  Theorem

      |- ∀s t. s ⊂ t ⇔ ∃x. x ∉ s ∧ x INSERT s ⊆ t

   [PSUBSET_IRREFL]  Theorem

      |- ∀s. ¬(s ⊂ s)

   [PSUBSET_MEMBER]  Theorem

      |- ∀s t. s ⊂ t ⇔ s ⊆ t ∧ ∃y. y ∈ t ∧ y ∉ s

   [PSUBSET_SING]  Theorem

      |- ∀s x. x ⊂ {s} ⇔ (x = ∅)

   [PSUBSET_SUBSET_TRANS]  Theorem

      |- ∀s t u. s ⊂ t ∧ t ⊆ u ⇒ s ⊂ u

   [PSUBSET_TRANS]  Theorem

      |- ∀s t u. s ⊂ t ∧ t ⊂ u ⇒ s ⊂ u

   [PSUBSET_UNIV]  Theorem

      |- ∀s. s ⊂ 𝕌(:α) ⇔ ∃x. x ∉ s

   [REL_RESTRICT_EMPTY]  Theorem

      |- REL_RESTRICT R ∅ = REMPTY

   [REL_RESTRICT_SUBSET]  Theorem

      |- s1 ⊆ s2 ⇒ REL_RESTRICT R s1 RSUBSET REL_RESTRICT R s2

   [REST_PSUBSET]  Theorem

      |- ∀s. s ≠ ∅ ⇒ REST s ⊂ s

   [REST_SING]  Theorem

      |- ∀x. REST {x} = ∅

   [REST_SUBSET]  Theorem

      |- ∀s. REST s ⊆ s

   [SET_CASES]  Theorem

      |- ∀s. (s = ∅) ∨ ∃x t. (s = x INSERT t) ∧ x ∉ t

   [SET_EQ_SUBSET]  Theorem

      |- ∀s1 s2. (s1 = s2) ⇔ s1 ⊆ s2 ∧ s2 ⊆ s1

   [SET_MINIMUM]  Theorem

      |- ∀s M. (∃x. x ∈ s) ⇔ ∃x. x ∈ s ∧ ∀y. y ∈ s ⇒ M x ≤ M y

   [SING]  Theorem

      |- ∀x. SING {x}

   [SING_DELETE]  Theorem

      |- ∀x. {x} DELETE x = ∅

   [SING_EMPTY]  Theorem

      |- SING ∅ ⇔ F

   [SING_FINITE]  Theorem

      |- ∀s. SING s ⇒ FINITE s

   [SING_IFF_CARD1]  Theorem

      |- ∀s. SING s ⇔ (CARD s = 1) ∧ FINITE s

   [SING_IFF_EMPTY_REST]  Theorem

      |- ∀s. SING s ⇔ s ≠ ∅ ∧ (REST s = ∅)

   [SING_INSERT]  Theorem

      |- SING (x INSERT s) ⇔ (s = ∅) ∨ (s = {x})

   [SING_UNION]  Theorem

      |- SING (s ∪ t) ⇔
         SING s ∧ (t = ∅) ∨ SING t ∧ (s = ∅) ∨ SING s ∧ SING t ∧ (s = t)

   [SING_applied]  Theorem

      |- ∀x y. {y} x ⇔ (x = y)

   [SPECIFICATION]  Theorem

      |- ∀P x. x ∈ P ⇔ P x

   [SUBSET_ANTISYM]  Theorem

      |- ∀s t. s ⊆ t ∧ t ⊆ s ⇒ (s = t)

   [SUBSET_BIGINTER]  Theorem

      |- ∀X P. X ⊆ BIGINTER P ⇔ ∀Y. Y ∈ P ⇒ X ⊆ Y

   [SUBSET_BIGUNION_I]  Theorem

      |- x ∈ P ⇒ x ⊆ BIGUNION P

   [SUBSET_DELETE]  Theorem

      |- ∀x s t. s ⊆ t DELETE x ⇔ x ∉ s ∧ s ⊆ t

   [SUBSET_DELETE_BOTH]  Theorem

      |- ∀s1 s2 x. s1 ⊆ s2 ⇒ s1 DELETE x ⊆ s2 DELETE x

   [SUBSET_DIFF]  Theorem

      |- ∀s1 s2 s3. s1 ⊆ s2 DIFF s3 ⇔ s1 ⊆ s2 ∧ DISJOINT s1 s3

   [SUBSET_EMPTY]  Theorem

      |- ∀s. s ⊆ ∅ ⇔ (s = ∅)

   [SUBSET_EQ_CARD]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. FINITE t ∧ (CARD s = CARD t) ∧ s ⊆ t ⇒ (s = t)

   [SUBSET_FINITE]  Theorem

      |- ∀s. FINITE s ⇒ ∀t. t ⊆ s ⇒ FINITE t

   [SUBSET_FINITE_I]  Theorem

      |- ∀s t. FINITE s ∧ t ⊆ s ⇒ FINITE t

   [SUBSET_INSERT]  Theorem

      |- ∀x s. x ∉ s ⇒ ∀t. s ⊆ x INSERT t ⇔ s ⊆ t

   [SUBSET_INSERT_DELETE]  Theorem

      |- ∀x s t. s ⊆ x INSERT t ⇔ s DELETE x ⊆ t

   [SUBSET_INSERT_RIGHT]  Theorem

      |- ∀e s1 s2. s1 ⊆ s2 ⇒ s1 ⊆ e INSERT s2

   [SUBSET_INTER]  Theorem

      |- ∀s t u. s ⊆ t ∩ u ⇔ s ⊆ t ∧ s ⊆ u

   [SUBSET_INTER_ABSORPTION]  Theorem

      |- ∀s t. s ⊆ t ⇔ (s ∩ t = s)

   [SUBSET_MAX_SET]  Theorem

      |- ∀I J n.
           FINITE I ∧ FINITE J ∧ I ≠ ∅ ∧ J ≠ ∅ ∧ I ⊆ J ⇒
           MAX_SET I ≤ MAX_SET J

   [SUBSET_MIN_SET]  Theorem

      |- ∀I J n. I ≠ ∅ ∧ J ≠ ∅ ∧ I ⊆ J ⇒ MIN_SET J ≤ MIN_SET I

   [SUBSET_POW]  Theorem

      |- ∀s1 s2. s1 ⊆ s2 ⇒ POW s1 ⊆ POW s2

   [SUBSET_PSUBSET_TRANS]  Theorem

      |- ∀s t u. s ⊆ t ∧ t ⊂ u ⇒ s ⊂ u

   [SUBSET_REFL]  Theorem

      |- ∀s. s ⊆ s

   [SUBSET_TRANS]  Theorem

      |- ∀s t u. s ⊆ t ∧ t ⊆ u ⇒ s ⊆ u

   [SUBSET_UNION]  Theorem

      |- (∀s t. s ⊆ s ∪ t) ∧ ∀s t. s ⊆ t ∪ s

   [SUBSET_UNION_ABSORPTION]  Theorem

      |- ∀s t. s ⊆ t ⇔ (s ∪ t = t)

   [SUBSET_UNIV]  Theorem

      |- ∀s. s ⊆ 𝕌(:α)

   [SUM_IMAGE_CONG]  Theorem

      |- (s1 = s2) ∧ (∀x. x ∈ s2 ⇒ (f1 x = f2 x)) ⇒ (∑ f1 s1 = ∑ f2 s2)

   [SUM_IMAGE_DELETE]  Theorem

      |- ∀f s.
           FINITE s ⇒
           ∀e. ∑ f (s DELETE e) = if e ∈ s then ∑ f s − f e else ∑ f s

   [SUM_IMAGE_IN_LE]  Theorem

      |- ∀f s e. FINITE s ∧ e ∈ s ⇒ f e ≤ ∑ f s

   [SUM_IMAGE_MONO_LESS]  Theorem

      |- ∀s.
           FINITE s ⇒
           (∃x. x ∈ s ∧ f x < g x) ∧ (∀x. x ∈ s ⇒ f x ≤ g x) ⇒
           ∑ f s < ∑ g s

   [SUM_IMAGE_MONO_LESS_EQ]  Theorem

      |- ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ≤ g x) ⇒ ∑ f s ≤ ∑ g s

   [SUM_IMAGE_SING]  Theorem

      |- ∀f e. ∑ f {e} = f e

   [SUM_IMAGE_SUBSET_LE]  Theorem

      |- ∀f s t. FINITE s ∧ t ⊆ s ⇒ ∑ f t ≤ ∑ f s

   [SUM_IMAGE_THM]  Theorem

      |- ∀f.
           (∑ f ∅ = 0) ∧
           ∀e s. FINITE s ⇒ (∑ f (e INSERT s) = f e + ∑ f (s DELETE e))

   [SUM_IMAGE_UNION]  Theorem

      |- ∀f s t.
           FINITE s ∧ FINITE t ⇒
           (∑ f (s ∪ t) = ∑ f s + ∑ f t − ∑ f (s ∩ t))

   [SUM_IMAGE_ZERO]  Theorem

      |- ∀s. FINITE s ⇒ ((∑ f s = 0) ⇔ ∀x. x ∈ s ⇒ (f x = 0))

   [SUM_IMAGE_lower_bound]  Theorem

      |- ∀s. FINITE s ⇒ ∀n. (∀x. x ∈ s ⇒ n ≤ f x) ⇒ CARD s * n ≤ ∑ f s

   [SUM_IMAGE_upper_bound]  Theorem

      |- ∀s. FINITE s ⇒ ∀n. (∀x. x ∈ s ⇒ f x ≤ n) ⇒ ∑ f s ≤ CARD s * n

   [SUM_SAME_IMAGE]  Theorem

      |- ∀P.
           FINITE P ⇒
           ∀f p. p ∈ P ∧ (∀q. q ∈ P ⇒ (f p = f q)) ⇒ (∑ f P = CARD P * f p)

   [SUM_SET_DELETE]  Theorem

      |- ∀s.
           FINITE s ⇒
           ∀e.
             SUM_SET (s DELETE e) =
             if e ∈ s then SUM_SET s − e else SUM_SET s

   [SUM_SET_EMPTY]  Theorem

      |- SUM_SET ∅ = 0

   [SUM_SET_IN_LE]  Theorem

      |- ∀x s. FINITE s ∧ x ∈ s ⇒ x ≤ SUM_SET s

   [SUM_SET_SING]  Theorem

      |- ∀n. SUM_SET {n} = n

   [SUM_SET_SUBSET_LE]  Theorem

      |- ∀s t. FINITE t ∧ s ⊆ t ⇒ SUM_SET s ≤ SUM_SET t

   [SUM_SET_THM]  Theorem

      |- (SUM_SET ∅ = 0) ∧
         ∀x s. FINITE s ⇒ (SUM_SET (x INSERT s) = x + SUM_SET (s DELETE x))

   [SUM_SET_UNION]  Theorem

      |- ∀s t.
           FINITE s ∧ FINITE t ⇒
           (SUM_SET (s ∪ t) = SUM_SET s + SUM_SET t − SUM_SET (s ∩ t))

   [SUM_UNIV]  Theorem

      |- 𝕌(:α + β) = IMAGE INL 𝕌(:α) ∪ IMAGE INR 𝕌(:β)

   [SURJ_COMPOSE]  Theorem

      |- ∀f g s t u. SURJ f s t ∧ SURJ g t u ⇒ SURJ (g o f) s u

   [SURJ_EMPTY]  Theorem

      |- ∀f. (∀s. SURJ f ∅ s ⇔ (s = ∅)) ∧ ∀s. SURJ f s ∅ ⇔ (s = ∅)

   [SURJ_ID]  Theorem

      |- ∀s. SURJ (λx. x) s s

   [SURJ_IMAGE]  Theorem

      |- SURJ f s (IMAGE f s)

   [SURJ_INJ_INV]  Theorem

      |- SURJ f s t ⇒ ∃g. INJ g t s ∧ ∀y. y ∈ t ⇒ (f (g y) = y)

   [UNION_ASSOC]  Theorem

      |- ∀s t u. s ∪ (t ∪ u) = s ∪ t ∪ u

   [UNION_COMM]  Theorem

      |- ∀s t. s ∪ t = t ∪ s

   [UNION_DELETE]  Theorem

      |- ∀A B x. A ∪ B DELETE x = A DELETE x ∪ (B DELETE x)

   [UNION_DIFF]  Theorem

      |- s ⊆ t ⇒ (s ∪ (t DIFF s) = t) ∧ (t DIFF s ∪ s = t)

   [UNION_EMPTY]  Theorem

      |- (∀s. ∅ ∪ s = s) ∧ ∀s. s ∪ ∅ = s

   [UNION_IDEMPOT]  Theorem

      |- ∀s. s ∪ s = s

   [UNION_OVER_INTER]  Theorem

      |- ∀s t u. s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u

   [UNION_SUBSET]  Theorem

      |- ∀s t u. s ∪ t ⊆ u ⇔ s ⊆ u ∧ t ⊆ u

   [UNION_UNIV]  Theorem

      |- (∀s. 𝕌(:α) ∪ s = 𝕌(:α)) ∧ ∀s. s ∪ 𝕌(:α) = 𝕌(:α)

   [UNION_applied]  Theorem

      |- ∀s t x. (s ∪ t) x ⇔ x ∈ s ∨ x ∈ t

   [UNIQUE_MEMBER_SING]  Theorem

      |- ∀x s. x ∈ s ∧ (∀y. y ∈ s ⇒ (x = y)) ⇔ (s = {x})

   [UNIV_BOOL]  Theorem

      |- 𝕌(:bool) = {T; F}

   [UNIV_FUN_TO_BOOL]  Theorem

      |- 𝕌(:α -> bool) = POW 𝕌(:α)

   [UNIV_NOT_EMPTY]  Theorem

      |- 𝕌(:α) ≠ ∅

   [UNIV_SUBSET]  Theorem

      |- ∀s. 𝕌(:α) ⊆ s ⇔ (s = 𝕌(:α))

   [bigunion_countable]  Theorem

      |- ∀s.
           countable s ∧ (∀x. x ∈ s ⇒ countable x) ⇒ countable (BIGUNION s)

   [chooser_def_compute]  Theorem

      |- (∀s. chooser s 0 = CHOICE s) ∧
         (∀s n.
            chooser s (NUMERAL (BIT1 n)) =
            chooser (REST s) (NUMERAL (BIT1 n) − 1)) ∧
         ∀s n.
           chooser s (NUMERAL (BIT2 n)) =
           chooser (REST s) (NUMERAL (BIT1 n))

   [count_EQN]  Theorem

      |- ∀n.
           count n =
           if n = 0 then ∅ else (let p = PRE n in p INSERT count p)

   [countable_EMPTY]  Theorem

      |- countable ∅

   [countable_INSERT]  Theorem

      |- countable (x INSERT s) ⇔ countable s

   [countable_Uprod]  Theorem

      |- countable 𝕌(:α # β) ⇔ countable 𝕌(:α) ∧ countable 𝕌(:β)

   [countable_Usum]  Theorem

      |- countable 𝕌(:α + β) ⇔ countable 𝕌(:α) ∧ countable 𝕌(:β)

   [countable_image_nats]  Theorem

      |- countable (IMAGE f 𝕌(:num))

   [countable_surj]  Theorem

      |- ∀s. countable s ⇔ (s = ∅) ∨ ∃f. SURJ f 𝕌(:num) s

   [cross_countable]  Theorem

      |- ∀s t. countable s ∧ countable t ⇒ countable (s × t)

   [cross_countable_IFF]  Theorem

      |- countable (s × t) ⇔ (s = ∅) ∨ (t = ∅) ∨ countable s ∧ countable t

   [finite_countable]  Theorem

      |- ∀s. FINITE s ⇒ countable s

   [image_countable]  Theorem

      |- ∀f s. countable s ⇒ countable (IMAGE f s)

   [infinite_num_inj]  Theorem

      |- ∀s. INFINITE s ⇔ ∃f. INJ f 𝕌(:num) s

   [infinite_pow_uncountable]  Theorem

      |- ∀s. INFINITE s ⇒ ¬countable (POW s)

   [infinite_rest]  Theorem

      |- ∀s. INFINITE s ⇒ INFINITE (REST s)

   [inj_countable]  Theorem

      |- ∀f s t. countable t ∧ INJ f s t ⇒ countable s

   [inj_image_countable_IFF]  Theorem

      |- INJ f s (IMAGE f s) ⇒ (countable (IMAGE f s) ⇔ countable s)

   [inj_surj]  Theorem

      |- ∀f s t. INJ f s t ⇒ (s = ∅) ∨ ∃f'. SURJ f' t s

   [inter_countable]  Theorem

      |- ∀s t. countable s ∨ countable t ⇒ countable (s ∩ t)

   [num_countable]  Theorem

      |- countable 𝕌(:num)

   [pair_to_num_formula]  Theorem

      |- ∀x y. pair_to_num (x,y) = (x + y + 1) * (x + y) DIV 2 + y

   [pair_to_num_inv]  Theorem

      |- (∀x. pair_to_num (num_to_pair x) = x) ∧
         ∀x y. num_to_pair (pair_to_num (x,y)) = (x,y)

   [pairwise_SUBSET]  Theorem

      |- ∀R s t. pairwise R t ∧ s ⊆ t ⇒ pairwise R s

   [pairwise_UNION]  Theorem

      |- pairwise R (s1 ∪ s2) ⇔
         pairwise R s1 ∧ pairwise R s2 ∧
         ∀x y. x ∈ s1 ∧ y ∈ s2 ⇒ R x y ∧ R y x

   [partition_CARD]  Theorem

      |- ∀R s. R equiv_on s ∧ FINITE s ⇒ (CARD s = ∑ CARD (partition R s))

   [partition_SUBSET]  Theorem

      |- ∀R s t. t ∈ partition R s ⇒ t ⊆ s

   [partition_elements_disjoint]  Theorem

      |- R equiv_on s ⇒
         ∀t1 t2.
           t1 ∈ partition R s ∧ t2 ∈ partition R s ∧ t1 ≠ t2 ⇒
           DISJOINT t1 t2

   [partition_elements_interrelate]  Theorem

      |- R equiv_on s ⇒ ∀t. t ∈ partition R s ⇒ ∀x y. x ∈ t ∧ y ∈ t ⇒ R x y

   [pow_no_surj]  Theorem

      |- ∀s. ¬∃f. SURJ f s (POW s)

   [subset_countable]  Theorem

      |- ∀s t. countable s ∧ t ⊆ s ⇒ countable t

   [union_countable]  Theorem

      |- ∀s t. countable s ∧ countable t ⇒ countable (s ∪ t)

   [union_countable_IFF]  Theorem

      |- countable (s ∪ t) ⇔ countable s ∧ countable t


*)
end
