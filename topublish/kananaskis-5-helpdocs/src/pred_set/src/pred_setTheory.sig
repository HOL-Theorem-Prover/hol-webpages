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
    val INFINITE_DEF : thm
    val INJ_DEF : thm
    val INSERT_DEF : thm
    val INTER_DEF : thm
    val ITSET_curried_def : thm
    val ITSET_tupled_primitive_def : thm
    val LINV_DEF : thm
    val MAX_SET_DEF : thm
    val MIN_SET_DEF : thm
    val POW_DEF : thm
    val PSUBSET_DEF : thm
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
    val pair_to_num_primitive_def : thm
    val partition_def : thm
  
  (*  Theorems  *)
    val ABSORPTION : thm
    val BIGINTER_EMPTY : thm
    val BIGINTER_INSERT : thm
    val BIGINTER_INTER : thm
    val BIGINTER_SING : thm
    val BIGUNION_EMPTY : thm
    val BIGUNION_EQ_EMPTY : thm
    val BIGUNION_INSERT : thm
    val BIGUNION_SING : thm
    val BIGUNION_SUBSET : thm
    val BIGUNION_UNION : thm
    val BIGUNION_partition : thm
    val BIJ_COMPOSE : thm
    val BIJ_DELETE : thm
    val BIJ_EMPTY : thm
    val BIJ_ID : thm
    val BIJ_LINV_BIJ : thm
    val BIJ_LINV_INV : thm
    val CARD_COUNT : thm
    val CARD_CROSS : thm
    val CARD_DELETE : thm
    val CARD_DIFF : thm
    val CARD_EMPTY : thm
    val CARD_EQ_0 : thm
    val CARD_INSERT : thm
    val CARD_INTER_LESS_EQ : thm
    val CARD_POW : thm
    val CARD_PSUBSET : thm
    val CARD_SING : thm
    val CARD_SING_CROSS : thm
    val CARD_SUBSET : thm
    val CARD_UNION : thm
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
    val COMPONENT : thm
    val COUNT_SUC : thm
    val COUNT_ZERO : thm
    val CROSS_EMPTY : thm
    val CROSS_EQNS : thm
    val CROSS_INSERT_LEFT : thm
    val CROSS_INSERT_RIGHT : thm
    val CROSS_SINGS : thm
    val CROSS_SUBSET : thm
    val DECOMPOSITION : thm
    val DELETE_COMM : thm
    val DELETE_DELETE : thm
    val DELETE_EQ_SING : thm
    val DELETE_INSERT : thm
    val DELETE_INTER : thm
    val DELETE_NON_ELEMENT : thm
    val DELETE_SUBSET : thm
    val DELETE_SUBSET_INSERT : thm
    val DIFF_DIFF : thm
    val DIFF_EMPTY : thm
    val DIFF_EQ_EMPTY : thm
    val DIFF_INSERT : thm
    val DIFF_SUBSET : thm
    val DIFF_UNIV : thm
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
    val FINITE_SING : thm
    val FINITE_UNION : thm
    val FINITE_WEAK_ENUMERATE : thm
    val FINITE_partition : thm
    val GSPEC_AND : thm
    val GSPEC_EQ : thm
    val GSPEC_EQ2 : thm
    val GSPEC_F : thm
    val GSPEC_F_COND : thm
    val GSPEC_ID : thm
    val GSPEC_OR : thm
    val GSPEC_T : thm
    val IMAGE_11_INFINITE : thm
    val IMAGE_BIGUNION : thm
    val IMAGE_COMPOSE : thm
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
    val INFINITE_DIFF_FINITE : thm
    val INFINITE_INHAB : thm
    val INFINITE_SUBSET : thm
    val INFINITE_UNIV : thm
    val INJECTIVE_IMAGE_FINITE : thm
    val INJ_CARD : thm
    val INJ_COMPOSE : thm
    val INJ_DELETE : thm
    val INJ_EMPTY : thm
    val INJ_ID : thm
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
    val PSUBSET_EQN : thm
    val PSUBSET_FINITE : thm
    val PSUBSET_INSERT_SUBSET : thm
    val PSUBSET_IRREFL : thm
    val PSUBSET_MEMBER : thm
    val PSUBSET_SING : thm
    val PSUBSET_TRANS : thm
    val PSUBSET_UNIV : thm
    val REST_PSUBSET : thm
    val REST_SING : thm
    val REST_SUBSET : thm
    val SET_CASES : thm
    val SET_EQ_SUBSET : thm
    val SET_MINIMUM : thm
    val SING : thm
    val SING_DELETE : thm
    val SING_FINITE : thm
    val SING_IFF_CARD1 : thm
    val SING_IFF_EMPTY_REST : thm
    val SPECIFICATION : thm
    val SUBSET_ANTISYM : thm
    val SUBSET_BIGINTER : thm
    val SUBSET_DELETE : thm
    val SUBSET_DELETE_BOTH : thm
    val SUBSET_DIFF : thm
    val SUBSET_EMPTY : thm
    val SUBSET_EQ_CARD : thm
    val SUBSET_FINITE : thm
    val SUBSET_INSERT : thm
    val SUBSET_INSERT_DELETE : thm
    val SUBSET_INSERT_RIGHT : thm
    val SUBSET_INTER : thm
    val SUBSET_INTER_ABSORPTION : thm
    val SUBSET_MAX_SET : thm
    val SUBSET_MIN_SET : thm
    val SUBSET_POW : thm
    val SUBSET_REFL : thm
    val SUBSET_TRANS : thm
    val SUBSET_UNION : thm
    val SUBSET_UNION_ABSORPTION : thm
    val SUBSET_UNIV : thm
    val SUM_IMAGE_DELETE : thm
    val SUM_IMAGE_IN_LE : thm
    val SUM_IMAGE_SING : thm
    val SUM_IMAGE_SUBSET_LE : thm
    val SUM_IMAGE_THM : thm
    val SUM_IMAGE_UNION : thm
    val SUM_IMAGE_lower_bound : thm
    val SUM_IMAGE_upper_bound : thm
    val SUM_SAME_IMAGE : thm
    val SUM_SET_DELETE : thm
    val SUM_SET_IN_LE : thm
    val SUM_SET_SING : thm
    val SUM_SET_SUBSET_LE : thm
    val SUM_SET_THM : thm
    val SUM_SET_UNION : thm
    val SURJ_COMPOSE : thm
    val SURJ_EMPTY : thm
    val SURJ_ID : thm
    val UNION_ASSOC : thm
    val UNION_COMM : thm
    val UNION_DELETE : thm
    val UNION_EMPTY : thm
    val UNION_IDEMPOT : thm
    val UNION_OVER_INTER : thm
    val UNION_SUBSET : thm
    val UNION_UNIV : thm
    val UNIQUE_MEMBER_SING : thm
    val UNIV_NOT_EMPTY : thm
    val UNIV_SUBSET : thm
    val bigunion_countable : thm
    val count_EQN : thm
    val countable_surj : thm
    val cross_countable : thm
    val finite_countable : thm
    val image_countable : thm
    val infinite_num_inj : thm
    val infinite_pow_uncountable : thm
    val infinite_rest : thm
    val inj_countable : thm
    val inj_surj : thm
    val inter_countable : thm
    val num_countable : thm
    val pair_to_num_def : thm
    val pair_to_num_formula : thm
    val pair_to_num_ind : thm
    val pair_to_num_inv : thm
    val partition_CARD : thm
    val partition_SUBSET : thm
    val partition_elements_disjoint : thm
    val partition_elements_interrelate : thm
    val pow_no_surj : thm
    val subset_countable : thm
    val union_countable : thm
  
  val pred_set_grammars : type_grammar.grammar * term_grammar.grammar
  
  val pred_set_rwts : simpLib.ssfrag
  
  val SET_SPEC_ss : simpLib.ssfrag
  
(*
   [basicSize] Parent theory of "pred_set"
   
   [while] Parent theory of "pred_set"
   
   [BIGINTER]  Definition
      
      |- !P. BIGINTER P = {x | !s. s IN P ==> x IN s}
   
   [BIGUNION]  Definition
      
      |- !P. BIGUNION P = {x | ?s. s IN P /\ x IN s}
   
   [BIJ_DEF]  Definition
      
      |- !f s t. BIJ f s t <=> INJ f s t /\ SURJ f s t
   
   [CARD_DEF]  Definition
      
      |- (CARD {} = 0) /\
         !s.
           FINITE s ==>
           !x. CARD (x INSERT s) = if x IN s then CARD s else SUC (CARD s)
   
   [CHOICE_DEF]  Definition
      
      |- !s. s <> {} ==> CHOICE s IN s
   
   [COMPL_DEF]  Definition
      
      |- !P. COMPL P = UNIV DIFF P
   
   [CROSS_DEF]  Definition
      
      |- !P Q. P CROSS Q = {p | FST p IN P /\ SND p IN Q}
   
   [DELETE_DEF]  Definition
      
      |- !s x. s DELETE x = s DIFF {x}
   
   [DIFF_DEF]  Definition
      
      |- !s t. s DIFF t = {x | x IN s /\ x NOTIN t}
   
   [DISJOINT_DEF]  Definition
      
      |- !s t. DISJOINT s t <=> (s INTER t = {})
   
   [EMPTY_DEF]  Definition
      
      |- {} = (\x. F)
   
   [FINITE_DEF]  Definition
      
      |- !s.
           FINITE s <=>
           !P. P {} /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s
   
   [GSPECIFICATION]  Definition
      
      |- !f v. v IN GSPEC f <=> ?x. (v,T) = f x
   
   [IMAGE_DEF]  Definition
      
      |- !f s. IMAGE f s = {f x | x IN s}
   
   [INFINITE_DEF]  Definition
      
      |- !s. INFINITE s <=> ~FINITE s
   
   [INJ_DEF]  Definition
      
      |- !f s t.
           INJ f s t <=>
           (!x. x IN s ==> f x IN t) /\
           !x y. x IN s /\ y IN s ==> (f x = f y) ==> (x = y)
   
   [INSERT_DEF]  Definition
      
      |- !x s. x INSERT s = {y | (y = x) \/ y IN s}
   
   [INTER_DEF]  Definition
      
      |- !s t. s INTER t = {x | x IN s /\ x IN t}
   
   [ITSET_curried_def]  Definition
      
      |- !f x x1. ITSET f x x1 = ITSET_tupled f (x,x1)
   
   [ITSET_tupled_primitive_def]  Definition
      
      |- !f.
           ITSET_tupled f =
           WFREC
             (@R.
                WF R /\
                !b s.
                  FINITE s /\ s <> {} ==> R (REST s,f (CHOICE s) b) (s,b))
             (\ITSET_tupled a.
                case a of
                   (s,b) ->
                     I
                       (if FINITE s then
                          if s = {} then
                            b
                          else
                            ITSET_tupled (REST s,f (CHOICE s) b)
                        else
                          ARB))
   
   [LINV_DEF]  Definition
      
      |- !f s t. INJ f s t ==> !x. x IN s ==> (LINV f s (f x) = x)
   
   [MAX_SET_DEF]  Definition
      
      |- !s.
           FINITE s /\ s <> {} ==>
           MAX_SET s IN s /\ !y. y IN s ==> y <= MAX_SET s
   
   [MIN_SET_DEF]  Definition
      
      |- MIN_SET = $LEAST
   
   [POW_DEF]  Definition
      
      |- !set. POW set = {s | s SUBSET set}
   
   [PSUBSET_DEF]  Definition
      
      |- !s t. s PSUBSET t <=> s SUBSET t /\ s <> t
   
   [REST_DEF]  Definition
      
      |- !s. REST s = s DELETE CHOICE s
   
   [RINV_DEF]  Definition
      
      |- !f s t. SURJ f s t ==> !x. x IN t ==> (f (RINV f s x) = x)
   
   [SING_DEF]  Definition
      
      |- !s. SING s <=> ?x. s = {x}
   
   [SUBSET_DEF]  Definition
      
      |- !s t. s SUBSET t <=> !x. x IN s ==> x IN t
   
   [SUM_IMAGE_DEF]  Definition
      
      |- !f s. SIGMA f s = ITSET (\e acc. f e + acc) s 0
   
   [SUM_SET_DEF]  Definition
      
      |- SUM_SET = SIGMA I
   
   [SURJ_DEF]  Definition
      
      |- !f s t.
           SURJ f s t <=>
           (!x. x IN s ==> f x IN t) /\
           !x. x IN t ==> ?y. y IN s /\ (f y = x)
   
   [UNION_DEF]  Definition
      
      |- !s t. s UNION t = {x | x IN s \/ x IN t}
   
   [UNIV_DEF]  Definition
      
      |- UNIV = (\x. T)
   
   [chooser_def]  Definition
      
      |- (!s. chooser s 0 = CHOICE s) /\
         !s n. chooser s (SUC n) = chooser (REST s) n
   
   [count_def]  Definition
      
      |- !n. count n = {m | m < n}
   
   [countable_def]  Definition
      
      |- !s. countable s <=> ?f. INJ f s UNIV
   
   [equiv_on_def]  Definition
      
      |- !R s.
           R equiv_on s <=>
           (!x. x IN s ==> R x x) /\
           (!x y. x IN s /\ y IN s ==> (R x y <=> R y x)) /\
           !x y z. x IN s /\ y IN s /\ z IN s /\ R x y /\ R y z ==> R x z
   
   [num_to_pair_def]  Definition
      
      |- (num_to_pair 0 = (0,0)) /\
         !n.
           num_to_pair (SUC n) =
           case num_to_pair n of
              (0,y) -> (SUC y,0)
           || (SUC x,y) -> (x,SUC y)
   
   [pair_to_num_primitive_def]  Definition
      
      |- pair_to_num =
         WFREC
           (@R.
              WF R /\ (!x. R (0,x) (SUC x,0)) /\
              (!y. R (SUC 0,y) (0,SUC y)) /\
              !y v2. R (SUC (SUC v2),y) (SUC v2,SUC y))
           (\pair_to_num a.
              case a of
                 (0,0) -> I 0
              || (0,SUC v4) -> I (SUC (pair_to_num (SUC 0,v4)))
              || (SUC x,0) -> I (SUC (pair_to_num (0,x)))
              || (SUC x,SUC v5) -> I (SUC (pair_to_num (SUC (SUC x),v5))))
   
   [partition_def]  Definition
      
      |- !R s.
           partition R s = {t | ?x. x IN s /\ (t = {y | y IN s /\ R x y})}
   
   [ABSORPTION]  Theorem
      
      |- !x s. x IN s <=> (x INSERT s = s)
   
   [BIGINTER_EMPTY]  Theorem
      
      |- BIGINTER {} = UNIV
   
   [BIGINTER_INSERT]  Theorem
      
      |- !P B. BIGINTER (P INSERT B) = P INTER BIGINTER B
   
   [BIGINTER_INTER]  Theorem
      
      |- !P Q. BIGINTER {P; Q} = P INTER Q
   
   [BIGINTER_SING]  Theorem
      
      |- !P. BIGINTER {P} = P
   
   [BIGUNION_EMPTY]  Theorem
      
      |- BIGUNION {} = {}
   
   [BIGUNION_EQ_EMPTY]  Theorem
      
      |- !P.
           ((BIGUNION P = {}) <=> (P = {}) \/ (P = {{}})) /\
           (({} = BIGUNION P) <=> (P = {}) \/ (P = {{}}))
   
   [BIGUNION_INSERT]  Theorem
      
      |- !s P. BIGUNION (s INSERT P) = s UNION BIGUNION P
   
   [BIGUNION_SING]  Theorem
      
      |- !x. BIGUNION {x} = x
   
   [BIGUNION_SUBSET]  Theorem
      
      |- !X P. BIGUNION P SUBSET X <=> !Y. Y IN P ==> Y SUBSET X
   
   [BIGUNION_UNION]  Theorem
      
      |- !s1 s2. BIGUNION (s1 UNION s2) = BIGUNION s1 UNION BIGUNION s2
   
   [BIGUNION_partition]  Theorem
      
      |- R equiv_on s ==> (BIGUNION (partition R s) = s)
   
   [BIJ_COMPOSE]  Theorem
      
      |- !f g s t u. BIJ f s t /\ BIJ g t u ==> BIJ (g o f) s u
   
   [BIJ_DELETE]  Theorem
      
      |- !s t f.
           BIJ f s t ==> !e. e IN s ==> BIJ f (s DELETE e) (t DELETE f e)
   
   [BIJ_EMPTY]  Theorem
      
      |- !f. (!s. BIJ f {} s <=> (s = {})) /\ !s. BIJ f s {} <=> (s = {})
   
   [BIJ_ID]  Theorem
      
      |- !s. BIJ (\x. x) s s
   
   [BIJ_LINV_BIJ]  Theorem
      
      |- !f s t. BIJ f s t ==> BIJ (LINV f s) t s
   
   [BIJ_LINV_INV]  Theorem
      
      |- !f s t. BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)
   
   [CARD_COUNT]  Theorem
      
      |- !n. CARD (count n) = n
   
   [CARD_CROSS]  Theorem
      
      |- !P Q.
           FINITE P /\ FINITE Q ==> (CARD (P CROSS Q) = CARD P * CARD Q)
   
   [CARD_DELETE]  Theorem
      
      |- !s.
           FINITE s ==>
           !x. CARD (s DELETE x) = if x IN s then CARD s - 1 else CARD s
   
   [CARD_DIFF]  Theorem
      
      |- !t.
           FINITE t ==>
           !s. FINITE s ==> (CARD (s DIFF t) = CARD s - CARD (s INTER t))
   
   [CARD_EMPTY]  Theorem
      
      |- CARD {} = 0
   
   [CARD_EQ_0]  Theorem
      
      |- !s. FINITE s ==> ((CARD s = 0) <=> (s = {}))
   
   [CARD_INSERT]  Theorem
      
      |- !s.
           FINITE s ==>
           !x. CARD (x INSERT s) = if x IN s then CARD s else SUC (CARD s)
   
   [CARD_INTER_LESS_EQ]  Theorem
      
      |- !s. FINITE s ==> !t. CARD (s INTER t) <= CARD s
   
   [CARD_POW]  Theorem
      
      |- !s. FINITE s ==> (CARD (POW s) = 2 ** CARD s)
   
   [CARD_PSUBSET]  Theorem
      
      |- !s. FINITE s ==> !t. t PSUBSET s ==> CARD t < CARD s
   
   [CARD_SING]  Theorem
      
      |- !x. CARD {x} = 1
   
   [CARD_SING_CROSS]  Theorem
      
      |- !x P. FINITE P ==> (CARD ({x} CROSS P) = CARD P)
   
   [CARD_SUBSET]  Theorem
      
      |- !s. FINITE s ==> !t. t SUBSET s ==> CARD t <= CARD s
   
   [CARD_UNION]  Theorem
      
      |- !s.
           FINITE s ==>
           !t.
             FINITE t ==>
             (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)
   
   [CHOICE_INSERT_REST]  Theorem
      
      |- !s. s <> {} ==> (CHOICE s INSERT REST s = s)
   
   [CHOICE_NOT_IN_REST]  Theorem
      
      |- !s. CHOICE s NOTIN REST s
   
   [CHOICE_SING]  Theorem
      
      |- !x. CHOICE {x} = x
   
   [COMMUTING_ITSET_INSERT]  Theorem
      
      |- !f s.
           (!x y z. f x (f y z) = f y (f x z)) /\ FINITE s ==>
           !x b. ITSET f (x INSERT s) b = ITSET f (s DELETE x) (f x b)
   
   [COMMUTING_ITSET_RECURSES]  Theorem
      
      |- !f e s b.
           (!x y z. f x (f y z) = f y (f x z)) /\ FINITE s ==>
           (ITSET f (e INSERT s) b = f e (ITSET f (s DELETE e) b))
   
   [COMPL_CLAUSES]  Theorem
      
      |- !s. (COMPL s INTER s = {}) /\ (COMPL s UNION s = UNIV)
   
   [COMPL_COMPL]  Theorem
      
      |- !s. COMPL (COMPL s) = s
   
   [COMPL_EMPTY]  Theorem
      
      |- COMPL {} = UNIV
   
   [COMPL_INTER]  Theorem
      
      |- (x INTER COMPL x = {}) /\ (COMPL x INTER x = {})
   
   [COMPL_SPLITS]  Theorem
      
      |- !p q. p INTER q UNION COMPL p INTER q = q
   
   [COMPONENT]  Theorem
      
      |- !x s. x IN x INSERT s
   
   [COUNT_SUC]  Theorem
      
      |- !n. count (SUC n) = n INSERT count n
   
   [COUNT_ZERO]  Theorem
      
      |- count 0 = {}
   
   [CROSS_EMPTY]  Theorem
      
      |- !P. (P CROSS {} = {}) /\ ({} CROSS P = {})
   
   [CROSS_EQNS]  Theorem
      
      |- !s1 s2.
           ({} CROSS s2 = {}) /\
           ((a INSERT s1) CROSS s2 =
            IMAGE (\y. (a,y)) s2 UNION s1 CROSS s2)
   
   [CROSS_INSERT_LEFT]  Theorem
      
      |- !P Q x. (x INSERT P) CROSS Q = {x} CROSS Q UNION P CROSS Q
   
   [CROSS_INSERT_RIGHT]  Theorem
      
      |- !P Q x. P CROSS (x INSERT Q) = P CROSS {x} UNION P CROSS Q
   
   [CROSS_SINGS]  Theorem
      
      |- !x y. {x} CROSS {y} = {(x,y)}
   
   [CROSS_SUBSET]  Theorem
      
      |- !P Q P0 Q0.
           P0 CROSS Q0 SUBSET P CROSS Q <=>
           (P0 = {}) \/ (Q0 = {}) \/ P0 SUBSET P /\ Q0 SUBSET Q
   
   [DECOMPOSITION]  Theorem
      
      |- !s x. x IN s <=> ?t. (s = x INSERT t) /\ x NOTIN t
   
   [DELETE_COMM]  Theorem
      
      |- !x y s. s DELETE x DELETE y = s DELETE y DELETE x
   
   [DELETE_DELETE]  Theorem
      
      |- !x s. s DELETE x DELETE x = s DELETE x
   
   [DELETE_EQ_SING]  Theorem
      
      |- !s x. x IN s ==> ((s DELETE x = {}) <=> (s = {x}))
   
   [DELETE_INSERT]  Theorem
      
      |- !x y s.
           (x INSERT s) DELETE y =
           if x = y then s DELETE y else x INSERT s DELETE y
   
   [DELETE_INTER]  Theorem
      
      |- !s t x. (s DELETE x) INTER t = s INTER t DELETE x
   
   [DELETE_NON_ELEMENT]  Theorem
      
      |- !x s. x NOTIN s <=> (s DELETE x = s)
   
   [DELETE_SUBSET]  Theorem
      
      |- !x s. s DELETE x SUBSET s
   
   [DELETE_SUBSET_INSERT]  Theorem
      
      |- !s e s2. s DELETE e SUBSET s2 <=> s SUBSET e INSERT s2
   
   [DIFF_DIFF]  Theorem
      
      |- !s t. s DIFF t DIFF t = s DIFF t
   
   [DIFF_EMPTY]  Theorem
      
      |- !s. s DIFF {} = s
   
   [DIFF_EQ_EMPTY]  Theorem
      
      |- !s. s DIFF s = {}
   
   [DIFF_INSERT]  Theorem
      
      |- !s t x. s DIFF (x INSERT t) = s DELETE x DIFF t
   
   [DIFF_SUBSET]  Theorem
      
      |- !s t. s DIFF t SUBSET s
   
   [DIFF_UNIV]  Theorem
      
      |- !s. s DIFF UNIV = {}
   
   [DISJOINT_BIGINTER]  Theorem
      
      |- !X Y P.
           Y IN P /\ DISJOINT Y X ==>
           DISJOINT X (BIGINTER P) /\ DISJOINT (BIGINTER P) X
   
   [DISJOINT_BIGUNION]  Theorem
      
      |- (!s t.
            DISJOINT (BIGUNION s) t <=> !s'. s' IN s ==> DISJOINT s' t) /\
         !s t. DISJOINT t (BIGUNION s) <=> !s'. s' IN s ==> DISJOINT t s'
   
   [DISJOINT_DELETE_SYM]  Theorem
      
      |- !s t x. DISJOINT (s DELETE x) t <=> DISJOINT (t DELETE x) s
   
   [DISJOINT_EMPTY]  Theorem
      
      |- !s. DISJOINT {} s /\ DISJOINT s {}
   
   [DISJOINT_EMPTY_REFL]  Theorem
      
      |- !s. (s = {}) <=> DISJOINT s s
   
   [DISJOINT_EMPTY_REFL_RWT]  Theorem
      
      |- !s. DISJOINT s s <=> (s = {})
   
   [DISJOINT_INSERT]  Theorem
      
      |- !x s t. DISJOINT (x INSERT s) t <=> DISJOINT s t /\ x NOTIN t
   
   [DISJOINT_SING_EMPTY]  Theorem
      
      |- !x. DISJOINT {x} {}
   
   [DISJOINT_SUBSET]  Theorem
      
      |- !s t u. DISJOINT s t /\ u SUBSET t ==> DISJOINT s u
   
   [DISJOINT_SYM]  Theorem
      
      |- !s t. DISJOINT s t <=> DISJOINT t s
   
   [DISJOINT_UNION]  Theorem
      
      |- !s t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u
   
   [DISJOINT_UNION_BOTH]  Theorem
      
      |- !s t u.
           (DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u) /\
           (DISJOINT u (s UNION t) <=> DISJOINT s u /\ DISJOINT t u)
   
   [EMPTY_DELETE]  Theorem
      
      |- !x. {} DELETE x = {}
   
   [EMPTY_DIFF]  Theorem
      
      |- !s. {} DIFF s = {}
   
   [EMPTY_NOT_IN_partition]  Theorem
      
      |- R equiv_on s ==> {} NOTIN partition R s
   
   [EMPTY_NOT_UNIV]  Theorem
      
      |- {} <> UNIV
   
   [EMPTY_SUBSET]  Theorem
      
      |- !s. {} SUBSET s
   
   [EMPTY_UNION]  Theorem
      
      |- !s t. (s UNION t = {}) <=> (s = {}) /\ (t = {})
   
   [EQUAL_SING]  Theorem
      
      |- !x y. ({x} = {y}) <=> (x = y)
   
   [EQ_UNIV]  Theorem
      
      |- (!x. x IN s) <=> (s = UNIV)
   
   [EXTENSION]  Theorem
      
      |- !s t. (s = t) <=> !x. x IN s <=> x IN t
   
   [FINITELY_INJECTIVE_IMAGE_FINITE]  Theorem
      
      |- !f.
           (!x. FINITE {y | x = f y}) ==>
           !s. FINITE (IMAGE f s) <=> FINITE s
   
   [FINITE_BIGUNION]  Theorem
      
      |- !P. FINITE P /\ (!s. s IN P ==> FINITE s) ==> FINITE (BIGUNION P)
   
   [FINITE_BIGUNION_EQ]  Theorem
      
      |- !P. FINITE (BIGUNION P) <=> FINITE P /\ !s. s IN P ==> FINITE s
   
   [FINITE_BIJ_CARD_EQ]  Theorem
      
      |- !S. FINITE S ==> !t f. BIJ f S t /\ FINITE t ==> (CARD S = CARD t)
   
   [FINITE_COMPLETE_INDUCTION]  Theorem
      
      |- !P.
           (!x. (!y. y PSUBSET x ==> P y) ==> FINITE x ==> P x) ==>
           !x. FINITE x ==> P x
   
   [FINITE_COUNT]  Theorem
      
      |- !n. FINITE (count n)
   
   [FINITE_CROSS]  Theorem
      
      |- !P Q. FINITE P /\ FINITE Q ==> FINITE (P CROSS Q)
   
   [FINITE_CROSS_EQ]  Theorem
      
      |- !P Q.
           FINITE (P CROSS Q) <=>
           (P = {}) \/ (Q = {}) \/ FINITE P /\ FINITE Q
   
   [FINITE_DELETE]  Theorem
      
      |- !x s. FINITE (s DELETE x) <=> FINITE s
   
   [FINITE_DIFF]  Theorem
      
      |- !s. FINITE s ==> !t. FINITE (s DIFF t)
   
   [FINITE_DIFF_down]  Theorem
      
      |- !P Q. FINITE (P DIFF Q) /\ FINITE Q ==> FINITE P
   
   [FINITE_EMPTY]  Theorem
      
      |- FINITE {}
   
   [FINITE_INDUCT]  Theorem
      
      |- !P.
           P {} /\
           (!s. FINITE s /\ P s ==> !e. e NOTIN s ==> P (e INSERT s)) ==>
           !s. FINITE s ==> P s
   
   [FINITE_INJ]  Theorem
      
      |- !f s t. INJ f s t /\ FINITE t ==> FINITE s
   
   [FINITE_INSERT]  Theorem
      
      |- !x s. FINITE (x INSERT s) <=> FINITE s
   
   [FINITE_INTER]  Theorem
      
      |- !s1 s2. FINITE s1 \/ FINITE s2 ==> FINITE (s1 INTER s2)
   
   [FINITE_ISO_NUM]  Theorem
      
      |- !s.
           FINITE s ==>
           ?f.
             (!n m.
                n < CARD s /\ m < CARD s ==> (f n = f m) ==> (n = m)) /\
             (s = {f n | n < CARD s})
   
   [FINITE_POW]  Theorem
      
      |- !s. FINITE s ==> FINITE (POW s)
   
   [FINITE_PSUBSET_INFINITE]  Theorem
      
      |- !s. INFINITE s <=> !t. FINITE t ==> t SUBSET s ==> t PSUBSET s
   
   [FINITE_PSUBSET_UNIV]  Theorem
      
      |- INFINITE UNIV <=> !s. FINITE s ==> s PSUBSET UNIV
   
   [FINITE_SING]  Theorem
      
      |- !x. FINITE {x}
   
   [FINITE_UNION]  Theorem
      
      |- !s t. FINITE (s UNION t) <=> FINITE s /\ FINITE t
   
   [FINITE_WEAK_ENUMERATE]  Theorem
      
      |- !s. FINITE s <=> ?f b. !e. e IN s <=> ?n. n < b /\ (e = f n)
   
   [FINITE_partition]  Theorem
      
      |- !R s.
           R equiv_on s /\ FINITE s ==>
           FINITE (partition R s) /\ !t. t IN partition R s ==> FINITE t
   
   [GSPEC_AND]  Theorem
      
      |- !P Q. {x | P x /\ Q x} = {x | P x} INTER {x | Q x}
   
   [GSPEC_EQ]  Theorem
      
      |- {x | x = y} = {y}
   
   [GSPEC_EQ2]  Theorem
      
      |- {x | y = x} = {y}
   
   [GSPEC_F]  Theorem
      
      |- {x | F} = {}
   
   [GSPEC_F_COND]  Theorem
      
      |- !f. (!x. ~SND (f x)) ==> (GSPEC f = {})
   
   [GSPEC_ID]  Theorem
      
      |- {x | x IN y} = y
   
   [GSPEC_OR]  Theorem
      
      |- !P Q. {x | P x \/ Q x} = {x | P x} UNION {x | Q x}
   
   [GSPEC_T]  Theorem
      
      |- {x | T} = UNIV
   
   [IMAGE_11_INFINITE]  Theorem
      
      |- !f.
           (!x y. (f x = f y) ==> (x = y)) ==>
           !s. INFINITE s ==> INFINITE (IMAGE f s)
   
   [IMAGE_BIGUNION]  Theorem
      
      |- !f M. IMAGE f (BIGUNION M) = BIGUNION (IMAGE (IMAGE f) M)
   
   [IMAGE_COMPOSE]  Theorem
      
      |- !f g s. IMAGE (f o g) s = IMAGE f (IMAGE g s)
   
   [IMAGE_DELETE]  Theorem
      
      |- !f x s. x NOTIN s ==> (IMAGE f (s DELETE x) = IMAGE f s)
   
   [IMAGE_EMPTY]  Theorem
      
      |- !f. IMAGE f {} = {}
   
   [IMAGE_EQ_EMPTY]  Theorem
      
      |- !s f. (IMAGE f s = {}) <=> (s = {})
   
   [IMAGE_FINITE]  Theorem
      
      |- !s. FINITE s ==> !f. FINITE (IMAGE f s)
   
   [IMAGE_ID]  Theorem
      
      |- !s. IMAGE (\x. x) s = s
   
   [IMAGE_IN]  Theorem
      
      |- !x s. x IN s ==> !f. f x IN IMAGE f s
   
   [IMAGE_INSERT]  Theorem
      
      |- !f x s. IMAGE f (x INSERT s) = f x INSERT IMAGE f s
   
   [IMAGE_INTER]  Theorem
      
      |- !f s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t
   
   [IMAGE_SUBSET]  Theorem
      
      |- !s t. s SUBSET t ==> !f. IMAGE f s SUBSET IMAGE f t
   
   [IMAGE_SURJ]  Theorem
      
      |- !f s t. SURJ f s t <=> (IMAGE f s = t)
   
   [IMAGE_UNION]  Theorem
      
      |- !f s t. IMAGE f (s UNION t) = IMAGE f s UNION IMAGE f t
   
   [INFINITE_DIFF_FINITE]  Theorem
      
      |- !s t. INFINITE s /\ FINITE t ==> s DIFF t <> {}
   
   [INFINITE_INHAB]  Theorem
      
      |- !P. INFINITE P ==> ?x. x IN P
   
   [INFINITE_SUBSET]  Theorem
      
      |- !s. INFINITE s ==> !t. s SUBSET t ==> INFINITE t
   
   [INFINITE_UNIV]  Theorem
      
      |- INFINITE UNIV <=>
         ?f. (!x y. (f x = f y) ==> (x = y)) /\ ?y. !x. f x <> y
   
   [INJECTIVE_IMAGE_FINITE]  Theorem
      
      |- !f.
           (!x y. (f x = f y) <=> (x = y)) ==>
           !s. FINITE (IMAGE f s) <=> FINITE s
   
   [INJ_CARD]  Theorem
      
      |- !f s t. INJ f s t /\ FINITE t ==> CARD s <= CARD t
   
   [INJ_COMPOSE]  Theorem
      
      |- !f g s t u. INJ f s t /\ INJ g t u ==> INJ (g o f) s u
   
   [INJ_DELETE]  Theorem
      
      |- !s t f.
           INJ f s t ==> !e. e IN s ==> INJ f (s DELETE e) (t DELETE f e)
   
   [INJ_EMPTY]  Theorem
      
      |- !f. (!s. INJ f {} s) /\ !s. INJ f s {} <=> (s = {})
   
   [INJ_ID]  Theorem
      
      |- !s. INJ (\x. x) s s
   
   [INSERT_COMM]  Theorem
      
      |- !x y s. x INSERT y INSERT s = y INSERT x INSERT s
   
   [INSERT_DELETE]  Theorem
      
      |- !x s. x IN s ==> (x INSERT s DELETE x = s)
   
   [INSERT_DIFF]  Theorem
      
      |- !s t x.
           (x INSERT s) DIFF t =
           if x IN t then s DIFF t else x INSERT s DIFF t
   
   [INSERT_INSERT]  Theorem
      
      |- !x s. x INSERT x INSERT s = x INSERT s
   
   [INSERT_INTER]  Theorem
      
      |- !x s t.
           (x INSERT s) INTER t =
           if x IN t then x INSERT s INTER t else s INTER t
   
   [INSERT_SING_UNION]  Theorem
      
      |- !s x. x INSERT s = {x} UNION s
   
   [INSERT_SUBSET]  Theorem
      
      |- !x s t. x INSERT s SUBSET t <=> x IN t /\ s SUBSET t
   
   [INSERT_UNION]  Theorem
      
      |- !x s t.
           (x INSERT s) UNION t =
           if x IN t then s UNION t else x INSERT s UNION t
   
   [INSERT_UNION_EQ]  Theorem
      
      |- !x s t. (x INSERT s) UNION t = x INSERT s UNION t
   
   [INSERT_UNIV]  Theorem
      
      |- !x. x INSERT UNIV = UNIV
   
   [INTER_ASSOC]  Theorem
      
      |- !s t u. s INTER (t INTER u) = s INTER t INTER u
   
   [INTER_COMM]  Theorem
      
      |- !s t. s INTER t = t INTER s
   
   [INTER_EMPTY]  Theorem
      
      |- (!s. {} INTER s = {}) /\ !s. s INTER {} = {}
   
   [INTER_FINITE]  Theorem
      
      |- !s. FINITE s ==> !t. FINITE (s INTER t)
   
   [INTER_IDEMPOT]  Theorem
      
      |- !s. s INTER s = s
   
   [INTER_OVER_UNION]  Theorem
      
      |- !s t u. s UNION t INTER u = (s UNION t) INTER (s UNION u)
   
   [INTER_SUBSET]  Theorem
      
      |- (!s t. s INTER t SUBSET s) /\ !s t. t INTER s SUBSET s
   
   [INTER_SUBSET_EQN]  Theorem
      
      |- ((A INTER B = A) <=> A SUBSET B) /\
         ((A INTER B = B) <=> B SUBSET A)
   
   [INTER_UNION]  Theorem
      
      |- ((A UNION B) INTER A = A) /\ ((B UNION A) INTER A = A) /\
         (A INTER (A UNION B) = A) /\ (A INTER (B UNION A) = A)
   
   [INTER_UNION_COMPL]  Theorem
      
      |- !s t. s INTER t = COMPL (COMPL s UNION COMPL t)
   
   [INTER_UNIV]  Theorem
      
      |- (!s. UNIV INTER s = s) /\ !s. s INTER UNIV = s
   
   [IN_ABS]  Theorem
      
      |- !x P. x IN (\x. P x) <=> P x
   
   [IN_BIGINTER]  Theorem
      
      |- x IN BIGINTER B <=> !P. P IN B ==> x IN P
   
   [IN_BIGUNION]  Theorem
      
      |- !x sos. x IN BIGUNION sos <=> ?s. x IN s /\ s IN sos
   
   [IN_COMPL]  Theorem
      
      |- !x s. x IN COMPL s <=> x NOTIN s
   
   [IN_COUNT]  Theorem
      
      |- !m n. m IN count n <=> m < n
   
   [IN_CROSS]  Theorem
      
      |- !P Q x. x IN P CROSS Q <=> FST x IN P /\ SND x IN Q
   
   [IN_DELETE]  Theorem
      
      |- !s x y. x IN s DELETE y <=> x IN s /\ x <> y
   
   [IN_DELETE_EQ]  Theorem
      
      |- !s x x'.
           (x IN s <=> x' IN s) <=> (x IN s DELETE x' <=> x' IN s DELETE x)
   
   [IN_DIFF]  Theorem
      
      |- !s t x. x IN s DIFF t <=> x IN s /\ x NOTIN t
   
   [IN_DISJOINT]  Theorem
      
      |- !s t. DISJOINT s t <=> ~?x. x IN s /\ x IN t
   
   [IN_IMAGE]  Theorem
      
      |- !y s f. y IN IMAGE f s <=> ?x. (y = f x) /\ x IN s
   
   [IN_INFINITE_NOT_FINITE]  Theorem
      
      |- !s t. INFINITE s /\ FINITE t ==> ?x. x IN s /\ x NOTIN t
   
   [IN_INSERT]  Theorem
      
      |- !x y s. x IN y INSERT s <=> (x = y) \/ x IN s
   
   [IN_INSERT_EXPAND]  Theorem
      
      |- !x y P. x IN y INSERT P <=> (x = y) \/ x <> y /\ x IN P
   
   [IN_INTER]  Theorem
      
      |- !s t x. x IN s INTER t <=> x IN s /\ x IN t
   
   [IN_POW]  Theorem
      
      |- !set e. e IN POW set <=> e SUBSET set
   
   [IN_SING]  Theorem
      
      |- !x y. x IN {y} <=> (x = y)
   
   [IN_UNION]  Theorem
      
      |- !s t x. x IN s UNION t <=> x IN s \/ x IN t
   
   [IN_UNIV]  Theorem
      
      |- !x. x IN UNIV
   
   [ITSET_EMPTY]  Theorem
      
      |- !f b. ITSET f {} b = b
   
   [ITSET_IND]  Theorem
      
      |- !P.
           (!s b.
              (FINITE s /\ s <> {} ==> P (REST s) (f (CHOICE s) b)) ==>
              P s b) ==>
           !v v1. P v v1
   
   [ITSET_INSERT]  Theorem
      
      |- !s.
           FINITE s ==>
           !f x b.
             ITSET f (x INSERT s) b =
             ITSET f (REST (x INSERT s)) (f (CHOICE (x INSERT s)) b)
   
   [ITSET_THM]  Theorem
      
      |- !s f b.
           FINITE s ==>
           (ITSET f s b =
            if s = {} then b else ITSET f (REST s) (f (CHOICE s) b))
   
   [ITSET_def]  Theorem
      
      |- ITSET f s b =
         if FINITE s then
           if s = {} then b else ITSET f (REST s) (f (CHOICE s) b)
         else
           ARB
   
   [ITSET_ind]  Theorem
      
      |- !P.
           (!s b.
              (FINITE s /\ s <> {} ==> P (REST s) (f (CHOICE s) b)) ==>
              P s b) ==>
           !v v1. P v v1
   
   [KoenigsLemma]  Theorem
      
      |- !R.
           (!x. FINITE {y | R x y}) ==>
           !x.
             ~FINITE {y | R^* x y} ==>
             ?f. (f 0 = x) /\ !n. R (f n) (f (SUC n))
   
   [KoenigsLemma_WF]  Theorem
      
      |- !R.
           (!x. FINITE {y | R x y}) /\ WF (inv R) ==>
           !x. FINITE {y | R^* x y}
   
   [LESS_CARD_DIFF]  Theorem
      
      |- !t.
           FINITE t ==>
           !s. FINITE s ==> CARD t < CARD s ==> 0 < CARD (s DIFF t)
   
   [MAX_SET_THM]  Theorem
      
      |- (!e. MAX_SET {e} = e) /\
         !s.
           FINITE s ==>
           !e1 e2.
             MAX_SET (e1 INSERT e2 INSERT s) =
             MAX e1 (MAX_SET (e2 INSERT s))
   
   [MAX_SET_UNION]  Theorem
      
      |- !A B.
           FINITE A /\ FINITE B /\ A <> {} /\ B <> {} ==>
           (MAX_SET (A UNION B) = MAX (MAX_SET A) (MAX_SET B))
   
   [MEMBER_NOT_EMPTY]  Theorem
      
      |- !s. (?x. x IN s) <=> s <> {}
   
   [MIN_SET_ELIM]  Theorem
      
      |- !P Q.
           P <> {} /\ (!x. (!y. y IN P ==> x <= y) /\ x IN P ==> Q x) ==>
           Q (MIN_SET P)
   
   [MIN_SET_LEM]  Theorem
      
      |- !s. s <> {} ==> MIN_SET s IN s /\ !x. x IN s ==> MIN_SET s <= x
   
   [MIN_SET_LEQ_MAX_SET]  Theorem
      
      |- !s. s <> {} /\ FINITE s ==> MIN_SET s <= MAX_SET s
   
   [MIN_SET_THM]  Theorem
      
      |- (!e. MIN_SET {e} = e) /\
         !s e1 e2.
           MIN_SET (e1 INSERT e2 INSERT s) = MIN e1 (MIN_SET (e2 INSERT s))
   
   [MIN_SET_UNION]  Theorem
      
      |- !A B.
           FINITE A /\ FINITE B /\ A <> {} /\ B <> {} ==>
           (MIN_SET (A UNION B) = MIN (MIN_SET A) (MIN_SET B))
   
   [NOT_EMPTY_INSERT]  Theorem
      
      |- !x s. {} <> x INSERT s
   
   [NOT_EMPTY_SING]  Theorem
      
      |- !x. {} <> {x}
   
   [NOT_EQUAL_SETS]  Theorem
      
      |- !s t. s <> t <=> ?x. x IN t <=> x NOTIN s
   
   [NOT_INSERT_EMPTY]  Theorem
      
      |- !x s. x INSERT s <> {}
   
   [NOT_IN_EMPTY]  Theorem
      
      |- !x. x NOTIN {}
   
   [NOT_IN_FINITE]  Theorem
      
      |- INFINITE UNIV <=> !s. FINITE s ==> ?x. x NOTIN s
   
   [NOT_PSUBSET_EMPTY]  Theorem
      
      |- !s. ~(s PSUBSET {})
   
   [NOT_SING_EMPTY]  Theorem
      
      |- !x. {x} <> {}
   
   [NOT_UNIV_PSUBSET]  Theorem
      
      |- !s. ~(UNIV PSUBSET s)
   
   [NUM_SET_WOP]  Theorem
      
      |- !s. (?n. n IN s) <=> ?n. n IN s /\ !m. m IN s ==> n <= m
   
   [PHP]  Theorem
      
      |- !f s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t
   
   [POW_EQNS]  Theorem
      
      |- (POW {} = {{}}) /\
         !e s.
           POW (e INSERT s) =
           (let ps = POW s in IMAGE ($INSERT e) ps UNION ps)
   
   [POW_INSERT]  Theorem
      
      |- !e s. POW (e INSERT s) = IMAGE ($INSERT e) (POW s) UNION POW s
   
   [PSUBSET_EQN]  Theorem
      
      |- !s1 s2. s1 PSUBSET s2 <=> s1 SUBSET s2 /\ ~(s2 SUBSET s1)
   
   [PSUBSET_FINITE]  Theorem
      
      |- !s. FINITE s ==> !t. t PSUBSET s ==> FINITE t
   
   [PSUBSET_INSERT_SUBSET]  Theorem
      
      |- !s t. s PSUBSET t <=> ?x. x NOTIN s /\ x INSERT s SUBSET t
   
   [PSUBSET_IRREFL]  Theorem
      
      |- !s. ~(s PSUBSET s)
   
   [PSUBSET_MEMBER]  Theorem
      
      |- !s t. s PSUBSET t <=> s SUBSET t /\ ?y. y IN t /\ y NOTIN s
   
   [PSUBSET_SING]  Theorem
      
      |- !s x. x PSUBSET {s} <=> (x = {})
   
   [PSUBSET_TRANS]  Theorem
      
      |- !s t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u
   
   [PSUBSET_UNIV]  Theorem
      
      |- !s. s PSUBSET UNIV <=> ?x. x NOTIN s
   
   [REST_PSUBSET]  Theorem
      
      |- !s. s <> {} ==> REST s PSUBSET s
   
   [REST_SING]  Theorem
      
      |- !x. REST {x} = {}
   
   [REST_SUBSET]  Theorem
      
      |- !s. REST s SUBSET s
   
   [SET_CASES]  Theorem
      
      |- !s. (s = {}) \/ ?x t. (s = x INSERT t) /\ x NOTIN t
   
   [SET_EQ_SUBSET]  Theorem
      
      |- !s1 s2. (s1 = s2) <=> s1 SUBSET s2 /\ s2 SUBSET s1
   
   [SET_MINIMUM]  Theorem
      
      |- !s M. (?x. x IN s) <=> ?x. x IN s /\ !y. y IN s ==> M x <= M y
   
   [SING]  Theorem
      
      |- !x. SING {x}
   
   [SING_DELETE]  Theorem
      
      |- !x. {x} DELETE x = {}
   
   [SING_FINITE]  Theorem
      
      |- !s. SING s ==> FINITE s
   
   [SING_IFF_CARD1]  Theorem
      
      |- !s. SING s <=> (CARD s = 1) /\ FINITE s
   
   [SING_IFF_EMPTY_REST]  Theorem
      
      |- !s. SING s <=> s <> {} /\ (REST s = {})
   
   [SPECIFICATION]  Theorem
      
      |- !P x. x IN P <=> P x
   
   [SUBSET_ANTISYM]  Theorem
      
      |- !s t. s SUBSET t /\ t SUBSET s ==> (s = t)
   
   [SUBSET_BIGINTER]  Theorem
      
      |- !X P. X SUBSET BIGINTER P <=> !Y. Y IN P ==> X SUBSET Y
   
   [SUBSET_DELETE]  Theorem
      
      |- !x s t. s SUBSET t DELETE x <=> x NOTIN s /\ s SUBSET t
   
   [SUBSET_DELETE_BOTH]  Theorem
      
      |- !s1 s2 x. s1 SUBSET s2 ==> s1 DELETE x SUBSET s2 DELETE x
   
   [SUBSET_DIFF]  Theorem
      
      |- !s1 s2 s3. s1 SUBSET s2 DIFF s3 <=> s1 SUBSET s2 /\ DISJOINT s1 s3
   
   [SUBSET_EMPTY]  Theorem
      
      |- !s. s SUBSET {} <=> (s = {})
   
   [SUBSET_EQ_CARD]  Theorem
      
      |- !s.
           FINITE s ==>
           !t. FINITE t /\ (CARD s = CARD t) /\ s SUBSET t ==> (s = t)
   
   [SUBSET_FINITE]  Theorem
      
      |- !s. FINITE s ==> !t. t SUBSET s ==> FINITE t
   
   [SUBSET_INSERT]  Theorem
      
      |- !x s. x NOTIN s ==> !t. s SUBSET x INSERT t <=> s SUBSET t
   
   [SUBSET_INSERT_DELETE]  Theorem
      
      |- !x s t. s SUBSET x INSERT t <=> s DELETE x SUBSET t
   
   [SUBSET_INSERT_RIGHT]  Theorem
      
      |- !e s1 s2. s1 SUBSET s2 ==> s1 SUBSET e INSERT s2
   
   [SUBSET_INTER]  Theorem
      
      |- !s t u. s SUBSET t INTER u <=> s SUBSET t /\ s SUBSET u
   
   [SUBSET_INTER_ABSORPTION]  Theorem
      
      |- !s t. s SUBSET t <=> (s INTER t = s)
   
   [SUBSET_MAX_SET]  Theorem
      
      |- !I J n.
           FINITE I /\ FINITE J /\ I <> {} /\ J <> {} /\ I SUBSET J ==>
           MAX_SET I <= MAX_SET J
   
   [SUBSET_MIN_SET]  Theorem
      
      |- !I J n.
           I <> {} /\ J <> {} /\ I SUBSET J ==> MIN_SET J <= MIN_SET I
   
   [SUBSET_POW]  Theorem
      
      |- !s1 s2. s1 SUBSET s2 ==> POW s1 SUBSET POW s2
   
   [SUBSET_REFL]  Theorem
      
      |- !s. s SUBSET s
   
   [SUBSET_TRANS]  Theorem
      
      |- !s t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u
   
   [SUBSET_UNION]  Theorem
      
      |- (!s t. s SUBSET s UNION t) /\ !s t. s SUBSET t UNION s
   
   [SUBSET_UNION_ABSORPTION]  Theorem
      
      |- !s t. s SUBSET t <=> (s UNION t = t)
   
   [SUBSET_UNIV]  Theorem
      
      |- !s. s SUBSET UNIV
   
   [SUM_IMAGE_DELETE]  Theorem
      
      |- !f s.
           FINITE s ==>
           !e.
             SIGMA f (s DELETE e) =
             if e IN s then SIGMA f s - f e else SIGMA f s
   
   [SUM_IMAGE_IN_LE]  Theorem
      
      |- !f s e. FINITE s /\ e IN s ==> f e <= SIGMA f s
   
   [SUM_IMAGE_SING]  Theorem
      
      |- !f e. SIGMA f {e} = f e
   
   [SUM_IMAGE_SUBSET_LE]  Theorem
      
      |- !f s t. FINITE s /\ t SUBSET s ==> SIGMA f t <= SIGMA f s
   
   [SUM_IMAGE_THM]  Theorem
      
      |- !f.
           (SIGMA f {} = 0) /\
           !e s.
             FINITE s ==>
             (SIGMA f (e INSERT s) = f e + SIGMA f (s DELETE e))
   
   [SUM_IMAGE_UNION]  Theorem
      
      |- !f s t.
           FINITE s /\ FINITE t ==>
           (SIGMA f (s UNION t) =
            SIGMA f s + SIGMA f t - SIGMA f (s INTER t))
   
   [SUM_IMAGE_lower_bound]  Theorem
      
      |- !s.
           FINITE s ==>
           !n. (!x. x IN s ==> n <= f x) ==> CARD s * n <= SIGMA f s
   
   [SUM_IMAGE_upper_bound]  Theorem
      
      |- !s.
           FINITE s ==>
           !n. (!x. x IN s ==> f x <= n) ==> SIGMA f s <= CARD s * n
   
   [SUM_SAME_IMAGE]  Theorem
      
      |- !P.
           FINITE P ==>
           !f p.
             p IN P /\ (!q. q IN P ==> (f p = f q)) ==>
             (SIGMA f P = CARD P * f p)
   
   [SUM_SET_DELETE]  Theorem
      
      |- !s.
           FINITE s ==>
           !e.
             SUM_SET (s DELETE e) =
             if e IN s then SUM_SET s - e else SUM_SET s
   
   [SUM_SET_IN_LE]  Theorem
      
      |- !x s. FINITE s /\ x IN s ==> x <= SUM_SET s
   
   [SUM_SET_SING]  Theorem
      
      |- !n. SUM_SET {n} = n
   
   [SUM_SET_SUBSET_LE]  Theorem
      
      |- !s t. FINITE t /\ s SUBSET t ==> SUM_SET s <= SUM_SET t
   
   [SUM_SET_THM]  Theorem
      
      |- (SUM_SET {} = 0) /\
         !x s.
           FINITE s ==> (SUM_SET (x INSERT s) = x + SUM_SET (s DELETE x))
   
   [SUM_SET_UNION]  Theorem
      
      |- !s t.
           FINITE s /\ FINITE t ==>
           (SUM_SET (s UNION t) =
            SUM_SET s + SUM_SET t - SUM_SET (s INTER t))
   
   [SURJ_COMPOSE]  Theorem
      
      |- !f g s t u. SURJ f s t /\ SURJ g t u ==> SURJ (g o f) s u
   
   [SURJ_EMPTY]  Theorem
      
      |- !f. (!s. SURJ f {} s <=> (s = {})) /\ !s. SURJ f s {} <=> (s = {})
   
   [SURJ_ID]  Theorem
      
      |- !s. SURJ (\x. x) s s
   
   [UNION_ASSOC]  Theorem
      
      |- !s t u. s UNION (t UNION u) = s UNION t UNION u
   
   [UNION_COMM]  Theorem
      
      |- !s t. s UNION t = t UNION s
   
   [UNION_DELETE]  Theorem
      
      |- !A B x. A UNION B DELETE x = A DELETE x UNION (B DELETE x)
   
   [UNION_EMPTY]  Theorem
      
      |- (!s. {} UNION s = s) /\ !s. s UNION {} = s
   
   [UNION_IDEMPOT]  Theorem
      
      |- !s. s UNION s = s
   
   [UNION_OVER_INTER]  Theorem
      
      |- !s t u. s INTER (t UNION u) = s INTER t UNION s INTER u
   
   [UNION_SUBSET]  Theorem
      
      |- !s t u. s UNION t SUBSET u <=> s SUBSET u /\ t SUBSET u
   
   [UNION_UNIV]  Theorem
      
      |- (!s. UNIV UNION s = UNIV) /\ !s. s UNION UNIV = UNIV
   
   [UNIQUE_MEMBER_SING]  Theorem
      
      |- !x s. x IN s /\ (!y. y IN s ==> (x = y)) <=> (s = {x})
   
   [UNIV_NOT_EMPTY]  Theorem
      
      |- UNIV <> {}
   
   [UNIV_SUBSET]  Theorem
      
      |- !s. UNIV SUBSET s <=> (s = UNIV)
   
   [bigunion_countable]  Theorem
      
      |- !s.
           countable s /\ (!x. x IN s ==> countable x) ==>
           countable (BIGUNION s)
   
   [count_EQN]  Theorem
      
      |- !n.
           count n =
           if n = 0 then {} else (let p = PRE n in p INSERT count p)
   
   [countable_surj]  Theorem
      
      |- !s. countable s <=> (s = {}) \/ ?f. SURJ f UNIV s
   
   [cross_countable]  Theorem
      
      |- !s t. countable s /\ countable t ==> countable (s CROSS t)
   
   [finite_countable]  Theorem
      
      |- !s. FINITE s ==> countable s
   
   [image_countable]  Theorem
      
      |- !f s. countable s ==> countable (IMAGE f s)
   
   [infinite_num_inj]  Theorem
      
      |- !s. INFINITE s <=> ?f. INJ f UNIV s
   
   [infinite_pow_uncountable]  Theorem
      
      |- !s. INFINITE s ==> ~countable (POW s)
   
   [infinite_rest]  Theorem
      
      |- !s. INFINITE s ==> INFINITE (REST s)
   
   [inj_countable]  Theorem
      
      |- !f s t. countable t /\ INJ f s t ==> countable s
   
   [inj_surj]  Theorem
      
      |- !f s t. INJ f s t ==> (s = {}) \/ ?f'. SURJ f' t s
   
   [inter_countable]  Theorem
      
      |- !s t. countable s \/ countable t ==> countable (s INTER t)
   
   [num_countable]  Theorem
      
      |- countable UNIV
   
   [pair_to_num_def]  Theorem
      
      |- (pair_to_num (0,0) = 0) /\
         (pair_to_num (SUC x,0) = SUC (pair_to_num (0,x))) /\
         (pair_to_num (0,SUC y) = SUC (pair_to_num (SUC 0,y))) /\
         (pair_to_num (SUC v2,SUC y) = SUC (pair_to_num (SUC (SUC v2),y)))
   
   [pair_to_num_formula]  Theorem
      
      |- !x y. pair_to_num (x,y) = (x + y + 1) * (x + y) DIV 2 + y
   
   [pair_to_num_ind]  Theorem
      
      |- !P.
           P (0,0) /\ (!x. P (0,x) ==> P (SUC x,0)) /\
           (!y. P (SUC 0,y) ==> P (0,SUC y)) /\
           (!v2 y. P (SUC (SUC v2),y) ==> P (SUC v2,SUC y)) ==>
           !v v1. P (v,v1)
   
   [pair_to_num_inv]  Theorem
      
      |- (!x. pair_to_num (num_to_pair x) = x) /\
         !x y. num_to_pair (pair_to_num (x,y)) = (x,y)
   
   [partition_CARD]  Theorem
      
      |- !R s.
           R equiv_on s /\ FINITE s ==>
           (CARD s = SIGMA CARD (partition R s))
   
   [partition_SUBSET]  Theorem
      
      |- !R s t. R equiv_on s /\ t IN partition R s ==> t SUBSET s
   
   [partition_elements_disjoint]  Theorem
      
      |- R equiv_on s ==>
         !t1 t2.
           t1 IN partition R s /\ t2 IN partition R s /\ t1 <> t2 ==>
           DISJOINT t1 t2
   
   [partition_elements_interrelate]  Theorem
      
      |- R equiv_on s ==>
         !t. t IN partition R s ==> !x y. x IN t /\ y IN t ==> R x y
   
   [pow_no_surj]  Theorem
      
      |- !s. ~?f. SURJ f s (POW s)
   
   [subset_countable]  Theorem
      
      |- !s t. countable s /\ t SUBSET s ==> countable t
   
   [union_countable]  Theorem
      
      |- !s t. countable s /\ countable t ==> countable (s UNION t)
   
   
*)
end
