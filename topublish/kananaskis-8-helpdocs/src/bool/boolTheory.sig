signature boolTheory =
sig
  type thm = Thm.thm

  (*  Axioms  *)
    val BOOL_CASES_AX : thm
    val ETA_AX : thm
    val INFINITY_AX : thm
    val SELECT_AX : thm

  (*  Definitions  *)
    val AND_DEF : thm
    val BOUNDED_DEF : thm
    val COND_DEF : thm
    val DATATYPE_TAG_DEF : thm
    val EXISTS_DEF : thm
    val EXISTS_UNIQUE_DEF : thm
    val FORALL_DEF : thm
    val F_DEF : thm
    val IN_DEF : thm
    val LET_DEF : thm
    val NOT_DEF : thm
    val ONE_ONE_DEF : thm
    val ONTO_DEF : thm
    val OR_DEF : thm
    val RES_ABSTRACT_DEF : thm
    val RES_EXISTS_DEF : thm
    val RES_EXISTS_UNIQUE_DEF : thm
    val RES_FORALL_DEF : thm
    val RES_SELECT_DEF : thm
    val TYPE_DEFINITION : thm
    val T_DEF : thm
    val bool_case_DEF : thm
    val itself_TY_DEF : thm
    val itself_case_thm : thm
    val literal_case_DEF : thm

  (*  Theorems  *)
    val ABS_REP_THM : thm
    val ABS_SIMP : thm
    val AND1_THM : thm
    val AND2_THM : thm
    val AND_CLAUSES : thm
    val AND_CONG : thm
    val AND_IMP_INTRO : thm
    val AND_INTRO_THM : thm
    val BETA_THM : thm
    val BOOL_EQ_DISTINCT : thm
    val BOOL_FUN_CASES_THM : thm
    val BOOL_FUN_INDUCT : thm
    val BOTH_EXISTS_AND_THM : thm
    val BOTH_EXISTS_IMP_THM : thm
    val BOTH_FORALL_IMP_THM : thm
    val BOTH_FORALL_OR_THM : thm
    val BOUNDED_THM : thm
    val COND_ABS : thm
    val COND_CLAUSES : thm
    val COND_CONG : thm
    val COND_EXPAND : thm
    val COND_EXPAND_IMP : thm
    val COND_EXPAND_OR : thm
    val COND_ID : thm
    val COND_RAND : thm
    val COND_RATOR : thm
    val CONJ_ASSOC : thm
    val CONJ_COMM : thm
    val CONJ_SYM : thm
    val DATATYPE_BOOL : thm
    val DATATYPE_TAG_THM : thm
    val DE_MORGAN_THM : thm
    val DISJ_ASSOC : thm
    val DISJ_COMM : thm
    val DISJ_IMP_THM : thm
    val DISJ_SYM : thm
    val EQ_CLAUSES : thm
    val EQ_EXPAND : thm
    val EQ_EXT : thm
    val EQ_IMP_THM : thm
    val EQ_REFL : thm
    val EQ_SYM : thm
    val EQ_SYM_EQ : thm
    val EQ_TRANS : thm
    val ETA_THM : thm
    val EXCLUDED_MIDDLE : thm
    val EXISTS_OR_THM : thm
    val EXISTS_REFL : thm
    val EXISTS_SIMP : thm
    val EXISTS_THM : thm
    val EXISTS_UNIQUE_REFL : thm
    val EXISTS_UNIQUE_THM : thm
    val FALSITY : thm
    val FORALL_AND_THM : thm
    val FORALL_BOOL : thm
    val FORALL_SIMP : thm
    val FORALL_THM : thm
    val FUN_EQ_THM : thm
    val F_IMP : thm
    val IMP_ANTISYM_AX : thm
    val IMP_CLAUSES : thm
    val IMP_CONG : thm
    val IMP_CONJ_THM : thm
    val IMP_DISJ_THM : thm
    val IMP_F : thm
    val IMP_F_EQ_F : thm
    val ITSELF_UNIQUE : thm
    val JRH_INDUCT_UTIL : thm
    val LCOMM_THM : thm
    val LEFT_AND_CONG : thm
    val LEFT_AND_FORALL_THM : thm
    val LEFT_AND_OVER_OR : thm
    val LEFT_EXISTS_AND_THM : thm
    val LEFT_EXISTS_IMP_THM : thm
    val LEFT_FORALL_IMP_THM : thm
    val LEFT_FORALL_OR_THM : thm
    val LEFT_OR_CONG : thm
    val LEFT_OR_EXISTS_THM : thm
    val LEFT_OR_OVER_AND : thm
    val LET_CONG : thm
    val LET_RAND : thm
    val LET_RATOR : thm
    val LET_THM : thm
    val MONO_ALL : thm
    val MONO_AND : thm
    val MONO_COND : thm
    val MONO_EXISTS : thm
    val MONO_IMP : thm
    val MONO_NOT : thm
    val MONO_NOT_EQ : thm
    val MONO_OR : thm
    val NOT_AND : thm
    val NOT_CLAUSES : thm
    val NOT_EXISTS_THM : thm
    val NOT_F : thm
    val NOT_FORALL_THM : thm
    val NOT_IMP : thm
    val ONE_ONE_THM : thm
    val ONTO_THM : thm
    val OR_CLAUSES : thm
    val OR_CONG : thm
    val OR_ELIM_THM : thm
    val OR_IMP_THM : thm
    val OR_INTRO_THM1 : thm
    val OR_INTRO_THM2 : thm
    val PEIRCE : thm
    val PULL_EXISTS : thm
    val PULL_FORALL : thm
    val REFL_CLAUSE : thm
    val RES_EXISTS_CONG : thm
    val RES_EXISTS_FALSE : thm
    val RES_EXISTS_THM : thm
    val RES_EXISTS_UNIQUE_THM : thm
    val RES_FORALL_CONG : thm
    val RES_FORALL_THM : thm
    val RES_FORALL_TRUE : thm
    val RES_SELECT_THM : thm
    val RIGHT_AND_FORALL_THM : thm
    val RIGHT_AND_OVER_OR : thm
    val RIGHT_EXISTS_AND_THM : thm
    val RIGHT_EXISTS_IMP_THM : thm
    val RIGHT_FORALL_IMP_THM : thm
    val RIGHT_FORALL_OR_THM : thm
    val RIGHT_OR_EXISTS_THM : thm
    val RIGHT_OR_OVER_AND : thm
    val SELECT_ELIM_THM : thm
    val SELECT_REFL : thm
    val SELECT_REFL_2 : thm
    val SELECT_THM : thm
    val SELECT_UNIQUE : thm
    val SKOLEM_THM : thm
    val SWAP_EXISTS_THM : thm
    val SWAP_FORALL_THM : thm
    val TRUTH : thm
    val TYPE_DEFINITION_THM : thm
    val UEXISTS_OR_THM : thm
    val UEXISTS_SIMP : thm
    val UNWIND_FORALL_THM1 : thm
    val UNWIND_FORALL_THM2 : thm
    val UNWIND_THM1 : thm
    val UNWIND_THM2 : thm
    val boolAxiom : thm
    val bool_INDUCT : thm
    val bool_case_CONG : thm
    val bool_case_EQ_COND : thm
    val bool_case_ID : thm
    val bool_case_thm : thm
    val itself_Axiom : thm
    val itself_induction : thm
    val literal_case_CONG : thm
    val literal_case_RAND : thm
    val literal_case_RATOR : thm
    val literal_case_THM : thm
    val literal_case_id : thm

  val bool_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [min] Parent theory of "bool"

   [BOOL_CASES_AX]  Axiom

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t. (t ⇔ T) ∨ (t ⇔ F)

   [ETA_AX]  Axiom

      [oracles: ] [axioms: ETA_AX] [] |- ∀t. (λx. t x) = t

   [INFINITY_AX]  Axiom

      [oracles: ] [axioms: INFINITY_AX] [] |- ∃f. ONE_ONE f ∧ ¬ONTO f

   [SELECT_AX]  Axiom

      [oracles: ] [axioms: SELECT_AX] [] |- ∀P x. P x ⇒ P ($@ P)

   [AND_DEF]  Definition

      |- $/\ = (λt1 t2. ∀t. (t1 ⇒ t2 ⇒ t) ⇒ t)

   [BOUNDED_DEF]  Definition

      |- BOUNDED = (λv. T)

   [COND_DEF]  Definition

      |- COND = (λt t1 t2. @x. ((t ⇔ T) ⇒ (x = t1)) ∧ ((t ⇔ F) ⇒ (x = t2)))

   [DATATYPE_TAG_DEF]  Definition

      |- DATATYPE = (λx. T)

   [EXISTS_DEF]  Definition

      |- $? = (λP. P ($@ P))

   [EXISTS_UNIQUE_DEF]  Definition

      |- $?! = (λP. $? P ∧ ∀x y. P x ∧ P y ⇒ (x = y))

   [FORALL_DEF]  Definition

      |- $! = (λP. P = (λx. T))

   [F_DEF]  Definition

      |- F ⇔ ∀t. t

   [IN_DEF]  Definition

      |- $IN = (λx f. f x)

   [LET_DEF]  Definition

      |- LET = (λf x. f x)

   [NOT_DEF]  Definition

      |- $~ = (λt. t ⇒ F)

   [ONE_ONE_DEF]  Definition

      |- ONE_ONE = (λf. ∀x1 x2. (f x1 = f x2) ⇒ (x1 = x2))

   [ONTO_DEF]  Definition

      |- ONTO = (λf. ∀y. ∃x. y = f x)

   [OR_DEF]  Definition

      |- $\/ = (λt1 t2. ∀t. (t1 ⇒ t) ⇒ (t2 ⇒ t) ⇒ t)

   [RES_ABSTRACT_DEF]  Definition

      [oracles: ] [axioms: ETA_AX, BOOL_CASES_AX, SELECT_AX] []
      |- (∀p m x. x ∈ p ⇒ (RES_ABSTRACT p m x = m x)) ∧
         ∀p m1 m2.
           (∀x. x ∈ p ⇒ (m1 x = m2 x)) ⇒
           (RES_ABSTRACT p m1 = RES_ABSTRACT p m2)

   [RES_EXISTS_DEF]  Definition

      |- RES_EXISTS = (λp m. ∃x. x ∈ p ∧ m x)

   [RES_EXISTS_UNIQUE_DEF]  Definition

      |- RES_EXISTS_UNIQUE =
         (λp m. (∃x::p. m x) ∧ ∀x y::p. m x ∧ m y ⇒ (x = y))

   [RES_FORALL_DEF]  Definition

      |- RES_FORALL = (λp m. ∀x. x ∈ p ⇒ m x)

   [RES_SELECT_DEF]  Definition

      |- RES_SELECT = (λp m. @x. x ∈ p ∧ m x)

   [TYPE_DEFINITION]  Definition

      |- TYPE_DEFINITION =
         (λP rep.
            (∀x' x''. (rep x' = rep x'') ⇒ (x' = x'')) ∧
            ∀x. P x ⇔ ∃x'. x = rep x')

   [T_DEF]  Definition

      |- T ⇔ ((λx. x) = (λx. x))

   [bool_case_DEF]  Definition

      |- bool_case = (λx y b. if b then x else y)

   [itself_TY_DEF]  Definition

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∃rep. TYPE_DEFINITION ($= ARB) rep

   [itself_case_thm]  Definition

      |- ∀b. itself_case b (:α) = b

   [literal_case_DEF]  Definition

      |- literal_case = (λf x. f x)

   [ABS_REP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀P.
           (∃rep. TYPE_DEFINITION P rep) ⇒
           ∃rep abs. (∀a. abs (rep a) = a) ∧ ∀r. P r ⇔ (rep (abs r) = r)

   [ABS_SIMP]  Theorem

      |- ∀t1 t2. (λx. t1) t2 = t1

   [AND1_THM]  Theorem

      |- ∀t1 t2. t1 ∧ t2 ⇒ t1

   [AND2_THM]  Theorem

      |- ∀t1 t2. t1 ∧ t2 ⇒ t2

   [AND_CLAUSES]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t.
           (T ∧ t ⇔ t) ∧ (t ∧ T ⇔ t) ∧ (F ∧ t ⇔ F) ∧ (t ∧ F ⇔ F) ∧
           (t ∧ t ⇔ t)

   [AND_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P P' Q Q'. (Q ⇒ (P ⇔ P')) ∧ (P' ⇒ (Q ⇔ Q')) ⇒ (P ∧ Q ⇔ P' ∧ Q')

   [AND_IMP_INTRO]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t1 t2 t3. t1 ⇒ t2 ⇒ t3 ⇔ t1 ∧ t2 ⇒ t3

   [AND_INTRO_THM]  Theorem

      |- ∀t1 t2. t1 ⇒ t2 ⇒ t1 ∧ t2

   [BETA_THM]  Theorem

      |- ∀f y. (λx. f x) y = f y

   [BOOL_EQ_DISTINCT]  Theorem

      |- (T ⇎ F) ∧ (F ⇎ T)

   [BOOL_FUN_CASES_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, ETA_AX] []
      |- ∀f. (f = (λb. T)) ∨ (f = (λb. F)) ∨ (f = (λb. b)) ∨ (f = (λb. ¬b))

   [BOOL_FUN_INDUCT]  Theorem

      [oracles: ] [axioms: ETA_AX, BOOL_CASES_AX] []
      |- ∀P. P (λb. T) ∧ P (λb. F) ∧ P (λb. b) ∧ P (λb. ¬b) ⇒ ∀f. P f

   [BOTH_EXISTS_AND_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P ∧ Q) ⇔ (∃x. P) ∧ ∃x. Q

   [BOTH_EXISTS_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P ⇒ Q) ⇔ (∀x. P) ⇒ ∃x. Q

   [BOTH_FORALL_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∀x. P ⇒ Q) ⇔ (∃x. P) ⇒ ∀x. Q

   [BOTH_FORALL_OR_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∀x. P ∨ Q) ⇔ (∀x. P) ∨ ∀x. Q

   [BOUNDED_THM]  Theorem

      |- ∀v. BOUNDED v ⇔ T

   [COND_ABS]  Theorem

      [oracles: ] [axioms: SELECT_AX, BOOL_CASES_AX, ETA_AX] []
      |- ∀b f g. (λx. if b then f x else g x) = if b then f else g

   [COND_CLAUSES]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀t1 t2.
           ((if T then t1 else t2) = t1) ∧ ((if F then t1 else t2) = t2)

   [COND_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀P Q x x' y y'.
           (P ⇔ Q) ∧ (Q ⇒ (x = x')) ∧ (¬Q ⇒ (y = y')) ⇒
           ((if P then x else y) = if Q then x' else y')

   [COND_EXPAND]  Theorem

      [oracles: ] [axioms: SELECT_AX, BOOL_CASES_AX] []
      |- ∀b t1 t2. (if b then t1 else t2) ⇔ (¬b ∨ t1) ∧ (b ∨ t2)

   [COND_EXPAND_IMP]  Theorem

      [oracles: ] [axioms: SELECT_AX, BOOL_CASES_AX] []
      |- ∀b t1 t2. (if b then t1 else t2) ⇔ (b ⇒ t1) ∧ (¬b ⇒ t2)

   [COND_EXPAND_OR]  Theorem

      [oracles: ] [axioms: SELECT_AX, BOOL_CASES_AX] []
      |- ∀b t1 t2. (if b then t1 else t2) ⇔ b ∧ t1 ∨ ¬b ∧ t2

   [COND_ID]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀b t. (if b then t else t) = t

   [COND_RAND]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀f b x y. f (if b then x else y) = if b then f x else f y

   [COND_RATOR]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀b f g x. (if b then f else g) x = if b then f x else g x

   [CONJ_ASSOC]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t1 t2 t3. t1 ∧ t2 ∧ t3 ⇔ (t1 ∧ t2) ∧ t3

   [CONJ_COMM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t1 t2. t1 ∧ t2 ⇔ t2 ∧ t1

   [CONJ_SYM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t1 t2. t1 ∧ t2 ⇔ t2 ∧ t1

   [DATATYPE_BOOL]  Theorem

      |- DATATYPE (bool T F) ⇔ T

   [DATATYPE_TAG_THM]  Theorem

      |- ∀x. DATATYPE x ⇔ T

   [DE_MORGAN_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀A B. (¬(A ∧ B) ⇔ ¬A ∨ ¬B) ∧ (¬(A ∨ B) ⇔ ¬A ∧ ¬B)

   [DISJ_ASSOC]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀A B C. A ∨ B ∨ C ⇔ (A ∨ B) ∨ C

   [DISJ_COMM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀A B. A ∨ B ⇔ B ∨ A

   [DISJ_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q R. P ∨ Q ⇒ R ⇔ (P ⇒ R) ∧ (Q ⇒ R)

   [DISJ_SYM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀A B. A ∨ B ⇔ B ∨ A

   [EQ_CLAUSES]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t.
           ((T ⇔ t) ⇔ t) ∧ ((t ⇔ T) ⇔ t) ∧ ((F ⇔ t) ⇔ ¬t) ∧ ((t ⇔ F) ⇔ ¬t)

   [EQ_EXPAND]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t1 t2. (t1 ⇔ t2) ⇔ t1 ∧ t2 ∨ ¬t1 ∧ ¬t2

   [EQ_EXT]  Theorem

      [oracles: ] [axioms: ETA_AX] [] |- ∀f g. (∀x. f x = g x) ⇒ (f = g)

   [EQ_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t1 t2. (t1 ⇔ t2) ⇔ (t1 ⇒ t2) ∧ (t2 ⇒ t1)

   [EQ_REFL]  Theorem

      |- ∀x. x = x

   [EQ_SYM]  Theorem

      |- ∀x y. (x = y) ⇒ (y = x)

   [EQ_SYM_EQ]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀x y. (x = y) ⇔ (y = x)

   [EQ_TRANS]  Theorem

      |- ∀x y z. (x = y) ∧ (y = z) ⇒ (x = z)

   [ETA_THM]  Theorem

      [oracles: ] [axioms: ETA_AX] [] |- ∀M. (λx. M x) = M

   [EXCLUDED_MIDDLE]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t. t ∨ ¬t

   [EXISTS_OR_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P x ∨ Q x) ⇔ (∃x. P x) ∨ ∃x. Q x

   [EXISTS_REFL]  Theorem

      |- ∀a. ∃x. x = a

   [EXISTS_SIMP]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t. (∃x. t) ⇔ t

   [EXISTS_THM]  Theorem

      [oracles: ] [axioms: ETA_AX] [] |- $? f ⇔ ∃x. f x

   [EXISTS_UNIQUE_REFL]  Theorem

      |- ∀a. ∃!x. x = a

   [EXISTS_UNIQUE_THM]  Theorem

      |- (∃!x. P x) ⇔ (∃x. P x) ∧ ∀x y. P x ∧ P y ⇒ (x = y)

   [FALSITY]  Theorem

      |- ∀t. F ⇒ t

   [FORALL_AND_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∀x. P x ∧ Q x) ⇔ (∀x. P x) ∧ ∀x. Q x

   [FORALL_BOOL]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- (∀b. P b) ⇔ P T ∧ P F

   [FORALL_SIMP]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t. (∀x. t) ⇔ t

   [FORALL_THM]  Theorem

      [oracles: ] [axioms: ETA_AX] [] |- $! f ⇔ ∀x. f x

   [FUN_EQ_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, ETA_AX] []
      |- ∀f g. (f = g) ⇔ ∀x. f x = g x

   [F_IMP]  Theorem

      |- ∀t. ¬t ⇒ t ⇒ F

   [IMP_ANTISYM_AX]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t1 t2. (t1 ⇒ t2) ⇒ (t2 ⇒ t1) ⇒ (t1 ⇔ t2)

   [IMP_CLAUSES]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t.
           (T ⇒ t ⇔ t) ∧ (t ⇒ T ⇔ T) ∧ (F ⇒ t ⇔ T) ∧ (t ⇒ t ⇔ T) ∧
           (t ⇒ F ⇔ ¬t)

   [IMP_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀x x' y y'. (x ⇔ x') ∧ (x' ⇒ (y ⇔ y')) ⇒ (x ⇒ y ⇔ x' ⇒ y')

   [IMP_CONJ_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q R. P ⇒ Q ∧ R ⇔ (P ⇒ Q) ∧ (P ⇒ R)

   [IMP_DISJ_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀A B. A ⇒ B ⇔ ¬A ∨ B

   [IMP_F]  Theorem

      |- ∀t. (t ⇒ F) ⇒ ¬t

   [IMP_F_EQ_F]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t. t ⇒ F ⇔ (t ⇔ F)

   [ITSELF_UNIQUE]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀i. i = (:α)

   [JRH_INDUCT_UTIL]  Theorem

      [oracles: ] [axioms: ETA_AX] [] |- ∀P t. (∀x. (x = t) ⇒ P x) ⇒ $? P

   [LCOMM_THM]  Theorem

      |- ∀f.
           (∀x y z. f x (f y z) = f (f x y) z) ⇒
           (∀x y. f x y = f y x) ⇒
           ∀x y z. f x (f y z) = f y (f x z)

   [LEFT_AND_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P P' Q Q'. (P ⇔ P') ∧ (P' ⇒ (Q ⇔ Q')) ⇒ (P ∧ Q ⇔ P' ∧ Q')

   [LEFT_AND_FORALL_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∀x. P x) ∧ Q ⇔ ∀x. P x ∧ Q

   [LEFT_AND_OVER_OR]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀A B C. A ∧ (B ∨ C) ⇔ A ∧ B ∨ A ∧ C

   [LEFT_EXISTS_AND_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P x ∧ Q) ⇔ (∃x. P x) ∧ Q

   [LEFT_EXISTS_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P x ⇒ Q) ⇔ (∀x. P x) ⇒ Q

   [LEFT_FORALL_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∀x. P x ⇒ Q) ⇔ (∃x. P x) ⇒ Q

   [LEFT_FORALL_OR_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀Q P. (∀x. P x ∨ Q) ⇔ (∀x. P x) ∨ Q

   [LEFT_OR_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P P' Q Q'. (P ⇔ P') ∧ (¬P' ⇒ (Q ⇔ Q')) ⇒ (P ∨ Q ⇔ P' ∨ Q')

   [LEFT_OR_EXISTS_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P x) ∨ Q ⇔ ∃x. P x ∨ Q

   [LEFT_OR_OVER_AND]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀A B C. A ∨ B ∧ C ⇔ (A ∨ B) ∧ (A ∨ C)

   [LET_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀f g M N.
           (M = N) ∧ (∀x. (x = N) ⇒ (f x = g x)) ⇒ (LET f M = LET g N)

   [LET_RAND]  Theorem

      |- P (let x = M in N x) ⇔ (let x = M in P (N x))

   [LET_RATOR]  Theorem

      |- (let x = M in N x) b = (let x = M in N x b)

   [LET_THM]  Theorem

      |- ∀f x. LET f x = f x

   [MONO_ALL]  Theorem

      |- (∀x. P x ⇒ Q x) ⇒ (∀x. P x) ⇒ ∀x. Q x

   [MONO_AND]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- (x ⇒ y) ∧ (z ⇒ w) ⇒ x ∧ z ⇒ y ∧ w

   [MONO_COND]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- (x ⇒ y) ⇒ (z ⇒ w) ⇒ (if b then x else z) ⇒ if b then y else w

   [MONO_EXISTS]  Theorem

      |- (∀x. P x ⇒ Q x) ⇒ (∃x. P x) ⇒ ∃x. Q x

   [MONO_IMP]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- (y ⇒ x) ∧ (z ⇒ w) ⇒ (x ⇒ z) ⇒ y ⇒ w

   [MONO_NOT]  Theorem

      |- (y ⇒ x) ⇒ ¬x ⇒ ¬y

   [MONO_NOT_EQ]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- y ⇒ x ⇔ ¬x ⇒ ¬y

   [MONO_OR]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- (x ⇒ y) ∧ (z ⇒ w) ⇒ x ∨ z ⇒ y ∨ w

   [NOT_AND]  Theorem

      |- ¬(t ∧ ¬t)

   [NOT_CLAUSES]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- (∀t. ¬ ¬t ⇔ t) ∧ (¬T ⇔ F) ∧ (¬F ⇔ T)

   [NOT_EXISTS_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀P. ¬(∃x. P x) ⇔ ∀x. ¬P x

   [NOT_F]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀t. ¬t ⇒ (t ⇔ F)

   [NOT_FORALL_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀P. ¬(∀x. P x) ⇔ ∃x. ¬P x

   [NOT_IMP]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀A B. ¬(A ⇒ B) ⇔ A ∧ ¬B

   [ONE_ONE_THM]  Theorem

      |- ∀f. ONE_ONE f ⇔ ∀x1 x2. (f x1 = f x2) ⇒ (x1 = x2)

   [ONTO_THM]  Theorem

      |- ∀f. ONTO f ⇔ ∀y. ∃x. y = f x

   [OR_CLAUSES]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀t.
           (T ∨ t ⇔ T) ∧ (t ∨ T ⇔ T) ∧ (F ∨ t ⇔ t) ∧ (t ∨ F ⇔ t) ∧
           (t ∨ t ⇔ t)

   [OR_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P P' Q Q'. (¬Q ⇒ (P ⇔ P')) ∧ (¬P' ⇒ (Q ⇔ Q')) ⇒ (P ∨ Q ⇔ P' ∨ Q')

   [OR_ELIM_THM]  Theorem

      |- ∀t t1 t2. t1 ∨ t2 ⇒ (t1 ⇒ t) ⇒ (t2 ⇒ t) ⇒ t

   [OR_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀A B. (A ⇔ B ∨ A) ⇔ B ⇒ A

   [OR_INTRO_THM1]  Theorem

      |- ∀t1 t2. t1 ⇒ t1 ∨ t2

   [OR_INTRO_THM2]  Theorem

      |- ∀t1 t2. t2 ⇒ t1 ∨ t2

   [PEIRCE]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ((P ⇒ Q) ⇒ P) ⇒ P

   [PULL_EXISTS]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q.
           ((∃x. P x) ⇒ Q ⇔ ∀x. P x ⇒ Q) ∧ ((∃x. P x) ∧ Q ⇔ ∃x. P x ∧ Q) ∧
           (Q ∧ (∃x. P x) ⇔ ∃x. Q ∧ P x)

   [PULL_FORALL]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q.
           (Q ⇒ (∀x. P x) ⇔ ∀x. Q ⇒ P x) ∧ ((∀x. P x) ∧ Q ⇔ ∀x. P x ∧ Q) ∧
           (Q ∧ (∀x. P x) ⇔ ∀x. Q ∧ P x)

   [REFL_CLAUSE]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀x. (x = x) ⇔ T

   [RES_EXISTS_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- (P = Q) ⇒
         (∀x. x ∈ Q ⇒ (f x ⇔ g x)) ⇒
         (RES_EXISTS P f ⇔ RES_EXISTS Q g)

   [RES_EXISTS_FALSE]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- (∃x::P. F) ⇔ F

   [RES_EXISTS_THM]  Theorem

      |- ∀P f. RES_EXISTS P f ⇔ ∃x. x ∈ P ∧ f x

   [RES_EXISTS_UNIQUE_THM]  Theorem

      |- ∀P f.
           RES_EXISTS_UNIQUE P f ⇔
           (∃x::P. f x) ∧ ∀x y::P. f x ∧ f y ⇒ (x = y)

   [RES_FORALL_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- (P = Q) ⇒
         (∀x. x ∈ Q ⇒ (f x ⇔ g x)) ⇒
         (RES_FORALL P f ⇔ RES_FORALL Q g)

   [RES_FORALL_THM]  Theorem

      |- ∀P f. RES_FORALL P f ⇔ ∀x. x ∈ P ⇒ f x

   [RES_FORALL_TRUE]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- (∀x::P. T) ⇔ T

   [RES_SELECT_THM]  Theorem

      |- ∀P f. RES_SELECT P f = @x. x ∈ P ∧ f x

   [RIGHT_AND_FORALL_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. P ∧ (∀x. Q x) ⇔ ∀x. P ∧ Q x

   [RIGHT_AND_OVER_OR]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀A B C. (B ∨ C) ∧ A ⇔ B ∧ A ∨ C ∧ A

   [RIGHT_EXISTS_AND_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P ∧ Q x) ⇔ P ∧ ∃x. Q x

   [RIGHT_EXISTS_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃x. P ⇒ Q x) ⇔ P ⇒ ∃x. Q x

   [RIGHT_FORALL_IMP_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∀x. P ⇒ Q x) ⇔ P ⇒ ∀x. Q x

   [RIGHT_FORALL_OR_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∀x. P ∨ Q x) ⇔ P ∨ ∀x. Q x

   [RIGHT_OR_EXISTS_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. P ∨ (∃x. Q x) ⇔ ∃x. P ∨ Q x

   [RIGHT_OR_OVER_AND]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀A B C. B ∧ C ∨ A ⇔ (B ∨ A) ∧ (C ∨ A)

   [SELECT_ELIM_THM]  Theorem

      [oracles: ] [axioms: SELECT_AX] []
      |- ∀P Q. (∃x. P x) ∧ (∀x. P x ⇒ Q x) ⇒ Q ($@ P)

   [SELECT_REFL]  Theorem

      [oracles: ] [axioms: SELECT_AX] [] |- ∀x. (@y. y = x) = x

   [SELECT_REFL_2]  Theorem

      [oracles: ] [axioms: SELECT_AX] [] |- ∀x. (@y. x = y) = x

   [SELECT_THM]  Theorem

      |- ∀P. P (@x. P x) ⇔ ∃x. P x

   [SELECT_UNIQUE]  Theorem

      [oracles: ] [axioms: ETA_AX, BOOL_CASES_AX, SELECT_AX] []
      |- ∀P x. (∀y. P y ⇔ (y = x)) ⇒ ($@ P = x)

   [SKOLEM_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀P. (∀x. ∃y. P x y) ⇔ ∃f. ∀x. P x (f x)

   [SWAP_EXISTS_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P. (∃x y. P x y) ⇔ ∃y x. P x y

   [SWAP_FORALL_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P. (∀x y. P x y) ⇔ ∀y x. P x y

   [TRUTH]  Theorem

      |- T

   [TYPE_DEFINITION_THM]  Theorem

      |- ∀P rep.
           TYPE_DEFINITION P rep ⇔
           (∀x' x''. (rep x' = rep x'') ⇒ (x' = x'')) ∧
           ∀x. P x ⇔ ∃x'. x = rep x'

   [UEXISTS_OR_THM]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P Q. (∃!x. P x ∨ Q x) ⇒ (∃!x. P x) ∨ ∃!x. Q x

   [UEXISTS_SIMP]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- (∃!x. t) ⇔ t ∧ ∀x y. x = y

   [UNWIND_FORALL_THM1]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀f v. (∀x. (v = x) ⇒ f x) ⇔ f v

   [UNWIND_FORALL_THM2]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀f v. (∀x. (x = v) ⇒ f x) ⇔ f v

   [UNWIND_THM1]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P a. (∃x. (a = x) ∧ P x) ⇔ P a

   [UNWIND_THM2]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀P a. (∃x. (x = a) ∧ P x) ⇔ P a

   [boolAxiom]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀e0 e1. ∃fn. (fn T = e0) ∧ (fn F = e1)

   [bool_INDUCT]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀P. P T ∧ P F ⇒ ∀b. P b

   [bool_case_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀P Q x x' y y'.
           (P ⇔ Q) ∧ (Q ⇒ (x = x')) ∧ (¬Q ⇒ (y = y')) ⇒
           (bool_case x y P = if Q then x' else y')

   [bool_case_EQ_COND]  Theorem

      |- ∀b x y. bool_case x y b = if b then x else y

   [bool_case_ID]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- ∀x b. bool_case x x b = x

   [bool_case_thm]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- (∀e0 e1. bool_case e0 e1 T = e0) ∧ ∀e0 e1. bool_case e0 e1 F = e1

   [itself_Axiom]  Theorem

      |- ∀e. ∃f. f (:β) = e

   [itself_induction]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] [] |- ∀P. P (:α) ⇒ ∀i. P i

   [literal_case_CONG]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX] []
      |- ∀f g M N.
           (M = N) ∧ (∀x. (x = N) ⇒ (f x = g x)) ⇒
           (literal_case f M = literal_case g N)

   [literal_case_RAND]  Theorem

      |- P (literal_case (λx. N x) M) ⇔ literal_case (λx. P (N x)) M

   [literal_case_RATOR]  Theorem

      |- literal_case (λx. N x) M b = literal_case (λx. N x b) M

   [literal_case_THM]  Theorem

      |- ∀f x. literal_case f x = f x

   [literal_case_id]  Theorem

      [oracles: ] [axioms: BOOL_CASES_AX, SELECT_AX] []
      |- literal_case (λx. bool_case t u (x = a)) a = t


*)
end
