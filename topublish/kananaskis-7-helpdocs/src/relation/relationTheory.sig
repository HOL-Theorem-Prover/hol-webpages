signature relationTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val CR_def : thm
    val EMPTY_REL_DEF : thm
    val EQC_DEF : thm
    val IDEM_DEF : thm
    val INDUCTIVE_INVARIANT_DEF : thm
    val INDUCTIVE_INVARIANT_ON_DEF : thm
    val INVOL_DEF : thm
    val LinearOrder : thm
    val O_DEF : thm
    val Order : thm
    val PreOrder : thm
    val RCOMPL : thm
    val RC_DEF : thm
    val RDOM_DEF : thm
    val RESTRICT_DEF : thm
    val RINTER : thm
    val RRANGE : thm
    val RSUBSET : thm
    val RTC_DEF : thm
    val RUNION : thm
    val RUNIV : thm
    val SC_DEF : thm
    val SN_def : thm
    val STRORD : thm
    val StrongLinearOrder : thm
    val StrongOrder : thm
    val TC_DEF : thm
    val WCR_def : thm
    val WFP_DEF : thm
    val WFREC_DEF : thm
    val WF_DEF : thm
    val WeakLinearOrder : thm
    val WeakOrder : thm
    val antisymmetric_def : thm
    val approx_def : thm
    val diag_def : thm
    val diamond_def : thm
    val equivalence_def : thm
    val inv_DEF : thm
    val inv_image_def : thm
    val irreflexive_def : thm
    val nf_def : thm
    val rcdiamond_def : thm
    val reflexive_def : thm
    val symmetric_def : thm
    val the_fun_def : thm
    val total_def : thm
    val transitive_def : thm
    val trichotomous : thm
  
  (*  Theorems  *)
    val ALT_equivalence : thm
    val EQC_EQUIVALENCE : thm
    val EQC_IDEM : thm
    val EQC_INDUCTION : thm
    val EQC_MONOTONE : thm
    val EQC_MOVES_IN : thm
    val EQC_R : thm
    val EQC_REFL : thm
    val EQC_SYM : thm
    val EQC_TRANS : thm
    val EXTEND_RTC_TC : thm
    val EXTEND_RTC_TC_EQN : thm
    val EqIsBothRSUBSET : thm
    val IDEM : thm
    val IDEM_RC : thm
    val IDEM_RTC : thm
    val IDEM_SC : thm
    val IDEM_STRORD : thm
    val IDEM_TC : thm
    val INDUCTION_WF_THM : thm
    val INDUCTIVE_INVARIANT_ON_WFREC : thm
    val INDUCTIVE_INVARIANT_WFREC : thm
    val INVOL : thm
    val INVOL_ONE_ENO : thm
    val INVOL_ONE_ONE : thm
    val IN_RDOM : thm
    val IN_RRANGE : thm
    val Id_O : thm
    val NOT_INVOL : thm
    val Newmans_lemma : thm
    val O_ASSOC : thm
    val O_Id : thm
    val O_MONO : thm
    val RC_IDEM : thm
    val RC_MONOTONE : thm
    val RC_MOVES_OUT : thm
    val RC_OR_Id : thm
    val RC_REFLEXIVE : thm
    val RC_RTC : thm
    val RC_STRORD : thm
    val RC_SUBSET : thm
    val RC_Weak : thm
    val RC_lifts_equalities : thm
    val RC_lifts_invariants : thm
    val RC_lifts_monotonicities : thm
    val REMPTY_SUBSET : thm
    val RESTRICT_LEMMA : thm
    val RINTER_ASSOC : thm
    val RINTER_COMM : thm
    val RSUBSET_ANTISYM : thm
    val RSUBSET_WeakOrder : thm
    val RSUBSET_antisymmetric : thm
    val RTC_CASES1 : thm
    val RTC_CASES2 : thm
    val RTC_CASES_RTC_TWICE : thm
    val RTC_CASES_TC : thm
    val RTC_EQC : thm
    val RTC_IDEM : thm
    val RTC_INDUCT : thm
    val RTC_INDUCT_RIGHT1 : thm
    val RTC_MONOTONE : thm
    val RTC_REFL : thm
    val RTC_REFLEXIVE : thm
    val RTC_RTC : thm
    val RTC_RULES : thm
    val RTC_RULES_RIGHT1 : thm
    val RTC_SINGLE : thm
    val RTC_STRONG_INDUCT : thm
    val RTC_STRONG_INDUCT_RIGHT1 : thm
    val RTC_SUBSET : thm
    val RTC_TC_RC : thm
    val RTC_TRANSITIVE : thm
    val RTC_lifts_equalities : thm
    val RTC_lifts_invariants : thm
    val RTC_lifts_monotonicities : thm
    val RTC_lifts_reflexive_transitive_relations : thm
    val RUNION_ASSOC : thm
    val RUNION_COMM : thm
    val RUNIV_SUBSET : thm
    val SC_IDEM : thm
    val SC_MONOTONE : thm
    val SC_SYMMETRIC : thm
    val SC_lifts_equalities : thm
    val SC_lifts_monotonicities : thm
    val STRONG_EQC_INDUCTION : thm
    val STRORD_AND_NOT_Id : thm
    val STRORD_RC : thm
    val STRORD_Strong : thm
    val StrongOrd_Ord : thm
    val TC_CASES1 : thm
    val TC_CASES2 : thm
    val TC_IDEM : thm
    val TC_INDUCT : thm
    val TC_INDUCT_LEFT1 : thm
    val TC_INDUCT_RIGHT1 : thm
    val TC_MONOTONE : thm
    val TC_RC_EQNS : thm
    val TC_RTC : thm
    val TC_RULES : thm
    val TC_STRONG_INDUCT : thm
    val TC_STRONG_INDUCT_LEFT1 : thm
    val TC_STRONG_INDUCT_RIGHT1 : thm
    val TC_SUBSET : thm
    val TC_TRANSITIVE : thm
    val TC_implies_one_step : thm
    val TC_lifts_equalities : thm
    val TC_lifts_invariants : thm
    val TC_lifts_monotonicities : thm
    val TC_lifts_transitive_relations : thm
    val TFL_INDUCTIVE_INVARIANT_ON_WFREC : thm
    val TFL_INDUCTIVE_INVARIANT_WFREC : thm
    val WFP_CASES : thm
    val WFP_INDUCT : thm
    val WFP_RULES : thm
    val WFP_STRONG_INDUCT : thm
    val WFREC_COROLLARY : thm
    val WFREC_THM : thm
    val WF_EMPTY_REL : thm
    val WF_EQ_INDUCTION_THM : thm
    val WF_EQ_WFP : thm
    val WF_INDUCTION_THM : thm
    val WF_NOT_REFL : thm
    val WF_RECURSION_THM : thm
    val WF_SUBSET : thm
    val WF_TC : thm
    val WF_TC_EQN : thm
    val WF_antisymmetric : thm
    val WF_inv_image : thm
    val WF_irreflexive : thm
    val WF_noloops : thm
    val WeakLinearOrder_dichotomy : thm
    val WeakOrd_Ord : thm
    val WeakOrder_EQ : thm
    val antisymmetric_RC : thm
    val antisymmetric_RINTER : thm
    val antisymmetric_inv : thm
    val diamond_RC_diamond : thm
    val diamond_TC_diamond : thm
    val equivalence_inv_identity : thm
    val establish_CR : thm
    val inv_EQC : thm
    val inv_INVOL : thm
    val inv_Id : thm
    val inv_MOVES_OUT : thm
    val inv_O : thm
    val inv_RC : thm
    val inv_SC : thm
    val inv_TC : thm
    val inv_diag : thm
    val inv_inv : thm
    val irreflexive_RSUBSET : thm
    val irreflexive_inv : thm
    val rcdiamond_diamond : thm
    val reflexive_EQC : thm
    val reflexive_Id_RSUBSET : thm
    val reflexive_RC : thm
    val reflexive_RC_identity : thm
    val reflexive_RTC : thm
    val reflexive_TC : thm
    val reflexive_inv : thm
    val symmetric_EQC : thm
    val symmetric_RC : thm
    val symmetric_SC_identity : thm
    val symmetric_TC : thm
    val symmetric_inv : thm
    val symmetric_inv_RSUBSET : thm
    val symmetric_inv_identity : thm
    val transitive_EQC : thm
    val transitive_O_RSUBSET : thm
    val transitive_RC : thm
    val transitive_RINTER : thm
    val transitive_RTC : thm
    val transitive_TC_identity : thm
    val transitive_inv : thm
  
  val relation_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [combin] Parent theory of "relation"
   
   [normalForms] Parent theory of "relation"
   
   [sat] Parent theory of "relation"
   
   [CR_def]  Definition
      
      |- ∀R. CR R ⇔ diamond R^*
   
   [EMPTY_REL_DEF]  Definition
      
      |- ∀x y. REMPTY x y ⇔ F
   
   [EQC_DEF]  Definition
      
      |- ∀R. R^= = RC (SC R)⁺
   
   [IDEM_DEF]  Definition
      
      |- ∀f. IDEM f ⇔ (f o f = f)
   
   [INDUCTIVE_INVARIANT_DEF]  Definition
      
      |- ∀R P M.
           INDUCTIVE_INVARIANT R P M ⇔
           ∀f x. (∀y. R y x ⇒ P y (f y)) ⇒ P x (M f x)
   
   [INDUCTIVE_INVARIANT_ON_DEF]  Definition
      
      |- ∀R D P M.
           INDUCTIVE_INVARIANT_ON R D P M ⇔
           ∀f x. D x ∧ (∀y. D y ⇒ R y x ⇒ P y (f y)) ⇒ P x (M f x)
   
   [INVOL_DEF]  Definition
      
      |- ∀f. INVOL f ⇔ (f o f = I)
   
   [LinearOrder]  Definition
      
      |- ∀R. LinearOrder R ⇔ Order R ∧ trichotomous R
   
   [O_DEF]  Definition
      
      |- ∀R1 R2 x z. (R1 O R2) x z ⇔ ∃y. R2 x y ∧ R1 y z
   
   [Order]  Definition
      
      |- ∀Z. Order Z ⇔ antisymmetric Z ∧ transitive Z
   
   [PreOrder]  Definition
      
      |- ∀R. PreOrder R ⇔ reflexive R ∧ transitive R
   
   [RCOMPL]  Definition
      
      |- ∀R x y. RCOMPL R x y ⇔ ¬R x y
   
   [RC_DEF]  Definition
      
      |- ∀R x y. RC R x y ⇔ (x = y) ∨ R x y
   
   [RDOM_DEF]  Definition
      
      |- ∀R x. RDOM R x ⇔ ∃y. R x y
   
   [RESTRICT_DEF]  Definition
      
      |- ∀f R x. RESTRICT f R x = (λy. if R y x then f y else ARB)
   
   [RINTER]  Definition
      
      |- ∀R1 R2 x y. (R1 RINTER R2) x y ⇔ R1 x y ∧ R2 x y
   
   [RRANGE]  Definition
      
      |- ∀R y. RRANGE R y ⇔ ∃x. R x y
   
   [RSUBSET]  Definition
      
      |- ∀R1 R2. R1 RSUBSET R2 ⇔ ∀x y. R1 x y ⇒ R2 x y
   
   [RTC_DEF]  Definition
      
      |- ∀R a b.
           R^* a b ⇔
           ∀P. (∀x. P x x) ∧ (∀x y z. R x y ∧ P y z ⇒ P x z) ⇒ P a b
   
   [RUNION]  Definition
      
      |- ∀R1 R2 x y. (R1 RUNION R2) x y ⇔ R1 x y ∨ R2 x y
   
   [RUNIV]  Definition
      
      |- ∀x y. RUNIV x y ⇔ T
   
   [SC_DEF]  Definition
      
      |- ∀R x y. SC R x y ⇔ R x y ∨ R y x
   
   [SN_def]  Definition
      
      |- ∀R. SN R ⇔ WF (inv R)
   
   [STRORD]  Definition
      
      |- ∀R a b. STRORD R a b ⇔ R a b ∧ a ≠ b
   
   [StrongLinearOrder]  Definition
      
      |- ∀R. StrongLinearOrder R ⇔ StrongOrder R ∧ trichotomous R
   
   [StrongOrder]  Definition
      
      |- ∀Z. StrongOrder Z ⇔ irreflexive Z ∧ antisymmetric Z ∧ transitive Z
   
   [TC_DEF]  Definition
      
      |- ∀R a b.
           R⁺ a b ⇔
           ∀P.
             (∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
             P a b
   
   [WCR_def]  Definition
      
      |- ∀R. WCR R ⇔ ∀x y z. R x y ∧ R x z ⇒ ∃u. R^* y u ∧ R^* z u
   
   [WFP_DEF]  Definition
      
      |- ∀R a. WFP R a ⇔ ∀P. (∀x. (∀y. R y x ⇒ P y) ⇒ P x) ⇒ P a
   
   [WFREC_DEF]  Definition
      
      |- ∀R M.
           WFREC R M =
           (λx.
              M (RESTRICT (the_fun R⁺ (λf v. M (RESTRICT f R v) v) x) R x)
                x)
   
   [WF_DEF]  Definition
      
      |- ∀R. WF R ⇔ ∀B. (∃w. B w) ⇒ ∃min. B min ∧ ∀b. R b min ⇒ ¬B b
   
   [WeakLinearOrder]  Definition
      
      |- ∀R. WeakLinearOrder R ⇔ WeakOrder R ∧ trichotomous R
   
   [WeakOrder]  Definition
      
      |- ∀Z. WeakOrder Z ⇔ reflexive Z ∧ antisymmetric Z ∧ transitive Z
   
   [antisymmetric_def]  Definition
      
      |- ∀R. antisymmetric R ⇔ ∀x y. R x y ∧ R y x ⇒ (x = y)
   
   [approx_def]  Definition
      
      |- ∀R M x f.
           approx R M x f ⇔ (f = RESTRICT (λy. M (RESTRICT f R y) y) R x)
   
   [diag_def]  Definition
      
      |- ∀A x y. diag A x y ⇔ (x = y) ∧ x ∈ A
   
   [diamond_def]  Definition
      
      |- ∀R. diamond R ⇔ ∀x y z. R x y ∧ R x z ⇒ ∃u. R y u ∧ R z u
   
   [equivalence_def]  Definition
      
      |- ∀R. equivalence R ⇔ reflexive R ∧ symmetric R ∧ transitive R
   
   [inv_DEF]  Definition
      
      |- ∀R x y. inv R x y ⇔ R y x
   
   [inv_image_def]  Definition
      
      |- ∀R f. inv_image R f = (λx y. R (f x) (f y))
   
   [irreflexive_def]  Definition
      
      |- ∀R. irreflexive R ⇔ ∀x. ¬R x x
   
   [nf_def]  Definition
      
      |- ∀R x. nf R x ⇔ ∀y. ¬R x y
   
   [rcdiamond_def]  Definition
      
      |- ∀R. rcdiamond R ⇔ ∀x y z. R x y ∧ R x z ⇒ ∃u. RC R y u ∧ RC R z u
   
   [reflexive_def]  Definition
      
      |- ∀R. reflexive R ⇔ ∀x. R x x
   
   [symmetric_def]  Definition
      
      |- ∀R. symmetric R ⇔ ∀x y. R x y ⇔ R y x
   
   [the_fun_def]  Definition
      
      |- ∀R M x. the_fun R M x = @f. approx R M x f
   
   [total_def]  Definition
      
      |- ∀R. total R ⇔ ∀x y. R x y ∨ R y x
   
   [transitive_def]  Definition
      
      |- ∀R. transitive R ⇔ ∀x y z. R x y ∧ R y z ⇒ R x z
   
   [trichotomous]  Definition
      
      |- ∀R. trichotomous R ⇔ ∀a b. R a b ∨ R b a ∨ (a = b)
   
   [ALT_equivalence]  Theorem
      
      |- ∀R. equivalence R ⇔ ∀x y. R x y ⇔ (R x = R y)
   
   [EQC_EQUIVALENCE]  Theorem
      
      |- ∀R. equivalence R^=
   
   [EQC_IDEM]  Theorem
      
      |- ∀R. R^= ^= = R^=
   
   [EQC_INDUCTION]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧ (∀x. P x x) ∧ (∀x y. P x y ⇒ P y x) ∧
           (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
           ∀x y. R^= x y ⇒ P x y
   
   [EQC_MONOTONE]  Theorem
      
      |- (∀x y. R x y ⇒ R' x y) ⇒ R^= x y ⇒ R'^= x y
   
   [EQC_MOVES_IN]  Theorem
      
      |- ∀R. ((RC R)^= = R^=) ∧ ((SC R)^= = R^=) ∧ (R⁺ ^= = R^=)
   
   [EQC_R]  Theorem
      
      |- ∀R x y. R x y ⇒ R^= x y
   
   [EQC_REFL]  Theorem
      
      |- ∀R x. R^= x x
   
   [EQC_SYM]  Theorem
      
      |- ∀R x y. R^= x y ⇒ R^= y x
   
   [EQC_TRANS]  Theorem
      
      |- ∀R x y z. R^= x y ∧ R^= y z ⇒ R^= x z
   
   [EXTEND_RTC_TC]  Theorem
      
      |- ∀R x y z. R x y ∧ R^* y z ⇒ R⁺ x z
   
   [EXTEND_RTC_TC_EQN]  Theorem
      
      |- ∀R x z. R⁺ x z ⇔ ∃y. R x y ∧ R^* y z
   
   [EqIsBothRSUBSET]  Theorem
      
      |- ∀y z. (y = z) ⇔ y RSUBSET z ∧ z RSUBSET y
   
   [IDEM]  Theorem
      
      |- ∀f. IDEM f ⇔ ∀x. f (f x) = f x
   
   [IDEM_RC]  Theorem
      
      |- IDEM RC
   
   [IDEM_RTC]  Theorem
      
      |- IDEM RTC
   
   [IDEM_SC]  Theorem
      
      |- IDEM SC
   
   [IDEM_STRORD]  Theorem
      
      |- IDEM STRORD
   
   [IDEM_TC]  Theorem
      
      |- IDEM TC
   
   [INDUCTION_WF_THM]  Theorem
      
      |- ∀R. (∀P. (∀x. (∀y. R y x ⇒ P y) ⇒ P x) ⇒ ∀x. P x) ⇒ WF R
   
   [INDUCTIVE_INVARIANT_ON_WFREC]  Theorem
      
      |- ∀R P M D x.
           WF R ∧ INDUCTIVE_INVARIANT_ON R D P M ∧ D x ⇒ P x (WFREC R M x)
   
   [INDUCTIVE_INVARIANT_WFREC]  Theorem
      
      |- ∀R P M. WF R ∧ INDUCTIVE_INVARIANT R P M ⇒ ∀x. P x (WFREC R M x)
   
   [INVOL]  Theorem
      
      |- ∀f. INVOL f ⇔ ∀x. f (f x) = x
   
   [INVOL_ONE_ENO]  Theorem
      
      |- ∀f. INVOL f ⇒ ∀a b. (f a = b) ⇔ (a = f b)
   
   [INVOL_ONE_ONE]  Theorem
      
      |- ∀f. INVOL f ⇒ ∀a b. (f a = f b) ⇔ (a = b)
   
   [IN_RDOM]  Theorem
      
      |- x ∈ RDOM R ⇔ ∃y. R x y
   
   [IN_RRANGE]  Theorem
      
      |- y ∈ RRANGE R ⇔ ∃x. R x y
   
   [Id_O]  Theorem
      
      |- $= O R = R
   
   [NOT_INVOL]  Theorem
      
      |- INVOL $~
   
   [Newmans_lemma]  Theorem
      
      |- ∀R. WCR R ∧ SN R ⇒ CR R
   
   [O_ASSOC]  Theorem
      
      |- R1 O R2 O R3 = (R1 O R2) O R3
   
   [O_Id]  Theorem
      
      |- R O $= = R
   
   [O_MONO]  Theorem
      
      |- R1 RSUBSET R2 ∧ S1 RSUBSET S2 ⇒ R1 O S1 RSUBSET R2 O S2
   
   [RC_IDEM]  Theorem
      
      |- ∀R. RC (RC R) = RC R
   
   [RC_MONOTONE]  Theorem
      
      |- (∀x y. R x y ⇒ Q x y) ⇒ RC R x y ⇒ RC Q x y
   
   [RC_MOVES_OUT]  Theorem
      
      |- ∀R.
           (SC (RC R) = RC (SC R)) ∧ (RC (RC R) = RC R) ∧ ((RC R)⁺ = RC R⁺)
   
   [RC_OR_Id]  Theorem
      
      |- RC R = R RUNION $=
   
   [RC_REFLEXIVE]  Theorem
      
      |- ∀R. reflexive (RC R)
   
   [RC_RTC]  Theorem
      
      |- ∀R x y. RC R x y ⇒ R^* x y
   
   [RC_STRORD]  Theorem
      
      |- ∀R. WeakOrder R ⇒ (RC (STRORD R) = R)
   
   [RC_SUBSET]  Theorem
      
      |- ∀R x y. R x y ⇒ RC R x y
   
   [RC_Weak]  Theorem
      
      |- Order R ⇔ WeakOrder (RC R)
   
   [RC_lifts_equalities]  Theorem
      
      |- (∀x y. R x y ⇒ (f x = f y)) ⇒ ∀x y. RC R x y ⇒ (f x = f y)
   
   [RC_lifts_invariants]  Theorem
      
      |- (∀x y. P x ∧ R x y ⇒ P y) ⇒ ∀x y. P x ∧ RC R x y ⇒ P y
   
   [RC_lifts_monotonicities]  Theorem
      
      |- (∀x y. R x y ⇒ R (f x) (f y)) ⇒ ∀x y. RC R x y ⇒ RC R (f x) (f y)
   
   [REMPTY_SUBSET]  Theorem
      
      |- REMPTY RSUBSET R ∧ (R RSUBSET REMPTY ⇔ (R = REMPTY))
   
   [RESTRICT_LEMMA]  Theorem
      
      |- ∀f R y z. R y z ⇒ (RESTRICT f R z y = f y)
   
   [RINTER_ASSOC]  Theorem
      
      |- R1 RINTER (R2 RINTER R3) = R1 RINTER R2 RINTER R3
   
   [RINTER_COMM]  Theorem
      
      |- R1 RINTER R2 = R2 RINTER R1
   
   [RSUBSET_ANTISYM]  Theorem
      
      |- ∀R1 R2. R1 RSUBSET R2 ∧ R2 RSUBSET R1 ⇒ (R1 = R2)
   
   [RSUBSET_WeakOrder]  Theorem
      
      |- WeakOrder $RSUBSET
   
   [RSUBSET_antisymmetric]  Theorem
      
      |- antisymmetric $RSUBSET
   
   [RTC_CASES1]  Theorem
      
      |- ∀R x y. R^* x y ⇔ (x = y) ∨ ∃u. R x u ∧ R^* u y
   
   [RTC_CASES2]  Theorem
      
      |- ∀R x y. R^* x y ⇔ (x = y) ∨ ∃u. R^* x u ∧ R u y
   
   [RTC_CASES_RTC_TWICE]  Theorem
      
      |- ∀R x y. R^* x y ⇔ ∃u. R^* x u ∧ R^* u y
   
   [RTC_CASES_TC]  Theorem
      
      |- ∀R x y. R^* x y ⇔ (x = y) ∨ R⁺ x y
   
   [RTC_EQC]  Theorem
      
      |- ∀x y. R^* x y ⇒ R^= x y
   
   [RTC_IDEM]  Theorem
      
      |- ∀R. R^* ^* = R^*
   
   [RTC_INDUCT]  Theorem
      
      |- ∀R P.
           (∀x. P x x) ∧ (∀x y z. R x y ∧ P y z ⇒ P x z) ⇒
           ∀x y. R^* x y ⇒ P x y
   
   [RTC_INDUCT_RIGHT1]  Theorem
      
      |- ∀R P.
           (∀x. P x x) ∧ (∀x y z. P x y ∧ R y z ⇒ P x z) ⇒
           ∀x y. R^* x y ⇒ P x y
   
   [RTC_MONOTONE]  Theorem
      
      |- (∀x y. R x y ⇒ Q x y) ⇒ R^* x y ⇒ Q^* x y
   
   [RTC_REFL]  Theorem
      
      |- R^* x x
   
   [RTC_REFLEXIVE]  Theorem
      
      |- ∀R. reflexive R^*
   
   [RTC_RTC]  Theorem
      
      |- ∀R x y. R^* x y ⇒ ∀z. R^* y z ⇒ R^* x z
   
   [RTC_RULES]  Theorem
      
      |- ∀R. (∀x. R^* x x) ∧ ∀x y z. R x y ∧ R^* y z ⇒ R^* x z
   
   [RTC_RULES_RIGHT1]  Theorem
      
      |- ∀R. (∀x. R^* x x) ∧ ∀x y z. R^* x y ∧ R y z ⇒ R^* x z
   
   [RTC_SINGLE]  Theorem
      
      |- ∀R x y. R x y ⇒ R^* x y
   
   [RTC_STRONG_INDUCT]  Theorem
      
      |- ∀R P.
           (∀x. P x x) ∧ (∀x y z. R x y ∧ R^* y z ∧ P y z ⇒ P x z) ⇒
           ∀x y. R^* x y ⇒ P x y
   
   [RTC_STRONG_INDUCT_RIGHT1]  Theorem
      
      |- ∀R P.
           (∀x. P x x) ∧ (∀x y z. P x y ∧ R^* x y ∧ R y z ⇒ P x z) ⇒
           ∀x y. R^* x y ⇒ P x y
   
   [RTC_SUBSET]  Theorem
      
      |- ∀R x y. R x y ⇒ R^* x y
   
   [RTC_TC_RC]  Theorem
      
      |- ∀R x y. R^* x y ⇒ RC R x y ∨ R⁺ x y
   
   [RTC_TRANSITIVE]  Theorem
      
      |- ∀R. transitive R^*
   
   [RTC_lifts_equalities]  Theorem
      
      |- (∀x y. R x y ⇒ (f x = f y)) ⇒ ∀x y. R^* x y ⇒ (f x = f y)
   
   [RTC_lifts_invariants]  Theorem
      
      |- (∀x y. P x ∧ R x y ⇒ P y) ⇒ ∀x y. P x ∧ R^* x y ⇒ P y
   
   [RTC_lifts_monotonicities]  Theorem
      
      |- (∀x y. R x y ⇒ R (f x) (f y)) ⇒ ∀x y. R^* x y ⇒ R^* (f x) (f y)
   
   [RTC_lifts_reflexive_transitive_relations]  Theorem
      
      |- (∀x y. R x y ⇒ Q (f x) (f y)) ∧ reflexive Q ∧ transitive Q ⇒
         ∀x y. R^* x y ⇒ Q (f x) (f y)
   
   [RUNION_ASSOC]  Theorem
      
      |- R1 RUNION (R2 RUNION R3) = R1 RUNION R2 RUNION R3
   
   [RUNION_COMM]  Theorem
      
      |- R1 RUNION R2 = R2 RUNION R1
   
   [RUNIV_SUBSET]  Theorem
      
      |- (RUNIV RSUBSET R ⇔ (R = RUNIV)) ∧ R RSUBSET RUNIV
   
   [SC_IDEM]  Theorem
      
      |- ∀R. SC (SC R) = SC R
   
   [SC_MONOTONE]  Theorem
      
      |- (∀x y. R x y ⇒ Q x y) ⇒ SC R x y ⇒ SC Q x y
   
   [SC_SYMMETRIC]  Theorem
      
      |- ∀R. symmetric (SC R)
   
   [SC_lifts_equalities]  Theorem
      
      |- (∀x y. R x y ⇒ (f x = f y)) ⇒ ∀x y. SC R x y ⇒ (f x = f y)
   
   [SC_lifts_monotonicities]  Theorem
      
      |- (∀x y. R x y ⇒ R (f x) (f y)) ⇒ ∀x y. SC R x y ⇒ SC R (f x) (f y)
   
   [STRONG_EQC_INDUCTION]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧ (∀x. P x x) ∧
           (∀x y. R^= x y ∧ P x y ⇒ P y x) ∧
           (∀x y z. P x y ∧ P y z ∧ R^= x y ∧ R^= y z ⇒ P x z) ⇒
           ∀x y. R^= x y ⇒ P x y
   
   [STRORD_AND_NOT_Id]  Theorem
      
      |- STRORD R = R RINTER RCOMPL $=
   
   [STRORD_RC]  Theorem
      
      |- ∀R. StrongOrder R ⇒ (STRORD (RC R) = R)
   
   [STRORD_Strong]  Theorem
      
      |- ∀R. Order R ⇔ StrongOrder (STRORD R)
   
   [StrongOrd_Ord]  Theorem
      
      |- ∀R. StrongOrder R ⇒ Order R
   
   [TC_CASES1]  Theorem
      
      |- ∀R x z. R⁺ x z ⇒ R x z ∨ ∃y. R x y ∧ R⁺ y z
   
   [TC_CASES2]  Theorem
      
      |- ∀R x z. R⁺ x z ⇒ R x z ∨ ∃y. R⁺ x y ∧ R y z
   
   [TC_IDEM]  Theorem
      
      |- ∀R. R⁺ ⁺ = R⁺
   
   [TC_INDUCT]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ P y z ⇒ P x z) ⇒
           ∀u v. R⁺ u v ⇒ P u v
   
   [TC_INDUCT_LEFT1]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧ (∀x y z. R x y ∧ P y z ⇒ P x z) ⇒
           ∀x y. R⁺ x y ⇒ P x y
   
   [TC_INDUCT_RIGHT1]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧ (∀x y z. P x y ∧ R y z ⇒ P x z) ⇒
           ∀x y. R⁺ x y ⇒ P x y
   
   [TC_MONOTONE]  Theorem
      
      |- (∀x y. R x y ⇒ Q x y) ⇒ R⁺ x y ⇒ Q⁺ x y
   
   [TC_RC_EQNS]  Theorem
      
      |- ∀R. (RC R⁺ = R^* ) ∧ ((RC R)⁺ = R^* )
   
   [TC_RTC]  Theorem
      
      |- ∀R x y. R⁺ x y ⇒ R^* x y
   
   [TC_RULES]  Theorem
      
      |- ∀R. (∀x y. R x y ⇒ R⁺ x y) ∧ ∀x y z. R⁺ x y ∧ R⁺ y z ⇒ R⁺ x z
   
   [TC_STRONG_INDUCT]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧
           (∀x y z. P x y ∧ P y z ∧ R⁺ x y ∧ R⁺ y z ⇒ P x z) ⇒
           ∀u v. R⁺ u v ⇒ P u v
   
   [TC_STRONG_INDUCT_LEFT1]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧
           (∀x y z. R x y ∧ P y z ∧ R⁺ y z ⇒ P x z) ⇒
           ∀u v. R⁺ u v ⇒ P u v
   
   [TC_STRONG_INDUCT_RIGHT1]  Theorem
      
      |- ∀R P.
           (∀x y. R x y ⇒ P x y) ∧
           (∀x y z. P x y ∧ R⁺ x y ∧ R y z ⇒ P x z) ⇒
           ∀u v. R⁺ u v ⇒ P u v
   
   [TC_SUBSET]  Theorem
      
      |- ∀R x y. R x y ⇒ R⁺ x y
   
   [TC_TRANSITIVE]  Theorem
      
      |- ∀R. transitive R⁺
   
   [TC_implies_one_step]  Theorem
      
      |- ∀x y. R⁺ x y ∧ x ≠ y ⇒ ∃z. R x z ∧ x ≠ z
   
   [TC_lifts_equalities]  Theorem
      
      |- (∀x y. R x y ⇒ (f x = f y)) ⇒ ∀x y. R⁺ x y ⇒ (f x = f y)
   
   [TC_lifts_invariants]  Theorem
      
      |- (∀x y. P x ∧ R x y ⇒ P y) ⇒ ∀x y. P x ∧ R⁺ x y ⇒ P y
   
   [TC_lifts_monotonicities]  Theorem
      
      |- (∀x y. R x y ⇒ R (f x) (f y)) ⇒ ∀x y. R⁺ x y ⇒ R⁺ (f x) (f y)
   
   [TC_lifts_transitive_relations]  Theorem
      
      |- (∀x y. R x y ⇒ Q (f x) (f y)) ∧ transitive Q ⇒
         ∀x y. R⁺ x y ⇒ Q (f x) (f y)
   
   [TFL_INDUCTIVE_INVARIANT_ON_WFREC]  Theorem
      
      |- ∀f R D P M x.
           (f = WFREC R M) ∧ WF R ∧ INDUCTIVE_INVARIANT_ON R D P M ∧ D x ⇒
           P x (f x)
   
   [TFL_INDUCTIVE_INVARIANT_WFREC]  Theorem
      
      |- ∀f R P M x.
           (f = WFREC R M) ∧ WF R ∧ INDUCTIVE_INVARIANT R P M ⇒ P x (f x)
   
   [WFP_CASES]  Theorem
      
      |- ∀R x. WFP R x ⇔ ∀y. R y x ⇒ WFP R y
   
   [WFP_INDUCT]  Theorem
      
      |- ∀R P. (∀x. (∀y. R y x ⇒ P y) ⇒ P x) ⇒ ∀x. WFP R x ⇒ P x
   
   [WFP_RULES]  Theorem
      
      |- ∀R x. (∀y. R y x ⇒ WFP R y) ⇒ WFP R x
   
   [WFP_STRONG_INDUCT]  Theorem
      
      |- ∀R. (∀x. WFP R x ∧ (∀y. R y x ⇒ P y) ⇒ P x) ⇒ ∀x. WFP R x ⇒ P x
   
   [WFREC_COROLLARY]  Theorem
      
      |- ∀M R f. (f = WFREC R M) ⇒ WF R ⇒ ∀x. f x = M (RESTRICT f R x) x
   
   [WFREC_THM]  Theorem
      
      |- ∀R M. WF R ⇒ ∀x. WFREC R M x = M (RESTRICT (WFREC R M) R x) x
   
   [WF_EMPTY_REL]  Theorem
      
      |- WF REMPTY
   
   [WF_EQ_INDUCTION_THM]  Theorem
      
      |- ∀R. WF R ⇔ ∀P. (∀x. (∀y. R y x ⇒ P y) ⇒ P x) ⇒ ∀x. P x
   
   [WF_EQ_WFP]  Theorem
      
      |- ∀R. WF R ⇔ ∀x. WFP R x
   
   [WF_INDUCTION_THM]  Theorem
      
      |- ∀R. WF R ⇒ ∀P. (∀x. (∀y. R y x ⇒ P y) ⇒ P x) ⇒ ∀x. P x
   
   [WF_NOT_REFL]  Theorem
      
      |- ∀R x y. WF R ⇒ R x y ⇒ x ≠ y
   
   [WF_RECURSION_THM]  Theorem
      
      |- ∀R. WF R ⇒ ∀M. ∃!f. ∀x. f x = M (RESTRICT f R x) x
   
   [WF_SUBSET]  Theorem
      
      |- ∀R P. WF R ∧ (∀x y. P x y ⇒ R x y) ⇒ WF P
   
   [WF_TC]  Theorem
      
      |- ∀R. WF R ⇒ WF R⁺
   
   [WF_TC_EQN]  Theorem
      
      |- WF R⁺ ⇔ WF R
   
   [WF_antisymmetric]  Theorem
      
      |- WF R ⇒ antisymmetric R
   
   [WF_inv_image]  Theorem
      
      |- ∀R f. WF R ⇒ WF (inv_image R f)
   
   [WF_irreflexive]  Theorem
      
      |- WF R ⇒ irreflexive R
   
   [WF_noloops]  Theorem
      
      |- WF R ⇒ R⁺ x y ⇒ x ≠ y
   
   [WeakLinearOrder_dichotomy]  Theorem
      
      |- ∀R. WeakLinearOrder R ⇔ WeakOrder R ∧ ∀a b. R a b ∨ R b a
   
   [WeakOrd_Ord]  Theorem
      
      |- ∀R. WeakOrder R ⇒ Order R
   
   [WeakOrder_EQ]  Theorem
      
      |- ∀R. WeakOrder R ⇒ ∀y z. (y = z) ⇔ R y z ∧ R z y
   
   [antisymmetric_RC]  Theorem
      
      |- ∀R. antisymmetric (RC R) ⇔ antisymmetric R
   
   [antisymmetric_RINTER]  Theorem
      
      |- (antisymmetric R1 ⇒ antisymmetric (R1 RINTER R2)) ∧
         (antisymmetric R2 ⇒ antisymmetric (R1 RINTER R2))
   
   [antisymmetric_inv]  Theorem
      
      |- ∀R. antisymmetric (inv R) ⇔ antisymmetric R
   
   [diamond_RC_diamond]  Theorem
      
      |- ∀R. diamond R ⇒ diamond (RC R)
   
   [diamond_TC_diamond]  Theorem
      
      |- ∀R. diamond R ⇒ diamond R⁺
   
   [equivalence_inv_identity]  Theorem
      
      |- ∀R. equivalence R ⇒ (inv R = R)
   
   [establish_CR]  Theorem
      
      |- ∀R. (rcdiamond R ⇒ CR R) ∧ (diamond R ⇒ CR R)
   
   [inv_EQC]  Theorem
      
      |- ∀R. (inv R^= = R^=) ∧ ((inv R)^= = R^=)
   
   [inv_INVOL]  Theorem
      
      |- INVOL inv
   
   [inv_Id]  Theorem
      
      |- inv $= = $=
   
   [inv_MOVES_OUT]  Theorem
      
      |- ∀R.
           (inv (inv R) = R) ∧ (SC (inv R) = SC R) ∧
           (RC (inv R) = inv (RC R)) ∧ ((inv R)⁺ = inv R⁺) ∧
           ((inv R)^* = inv R^* ) ∧ ((inv R)^= = R^=)
   
   [inv_O]  Theorem
      
      |- ∀R R'. inv (R O R') = inv R' O inv R
   
   [inv_RC]  Theorem
      
      |- ∀R. inv (RC R) = RC (inv R)
   
   [inv_SC]  Theorem
      
      |- ∀R. (inv (SC R) = SC R) ∧ (SC (inv R) = SC R)
   
   [inv_TC]  Theorem
      
      |- ∀R. inv R⁺ = (inv R)⁺
   
   [inv_diag]  Theorem
      
      |- inv (diag A) = diag A
   
   [inv_inv]  Theorem
      
      |- ∀R. inv (inv R) = R
   
   [irreflexive_RSUBSET]  Theorem
      
      |- ∀R1 R2. irreflexive R2 ∧ R1 RSUBSET R2 ⇒ irreflexive R1
   
   [irreflexive_inv]  Theorem
      
      |- ∀R. irreflexive (inv R) ⇔ irreflexive R
   
   [rcdiamond_diamond]  Theorem
      
      |- ∀R. rcdiamond R ⇔ diamond (RC R)
   
   [reflexive_EQC]  Theorem
      
      |- reflexive R^=
   
   [reflexive_Id_RSUBSET]  Theorem
      
      |- ∀R. reflexive R ⇔ $= RSUBSET R
   
   [reflexive_RC]  Theorem
      
      |- ∀R. reflexive (RC R)
   
   [reflexive_RC_identity]  Theorem
      
      |- ∀R. reflexive R ⇒ (RC R = R)
   
   [reflexive_RTC]  Theorem
      
      |- ∀R. reflexive R^*
   
   [reflexive_TC]  Theorem
      
      |- ∀R. reflexive R ⇒ reflexive R⁺
   
   [reflexive_inv]  Theorem
      
      |- ∀R. reflexive (inv R) ⇔ reflexive R
   
   [symmetric_EQC]  Theorem
      
      |- symmetric R^=
   
   [symmetric_RC]  Theorem
      
      |- ∀R. symmetric (RC R) ⇔ symmetric R
   
   [symmetric_SC_identity]  Theorem
      
      |- ∀R. symmetric R ⇒ (SC R = R)
   
   [symmetric_TC]  Theorem
      
      |- ∀R. symmetric R ⇒ symmetric R⁺
   
   [symmetric_inv]  Theorem
      
      |- ∀R. symmetric (inv R) ⇔ symmetric R
   
   [symmetric_inv_RSUBSET]  Theorem
      
      |- symmetric R ⇔ inv R RSUBSET R
   
   [symmetric_inv_identity]  Theorem
      
      |- ∀R. symmetric R ⇒ (inv R = R)
   
   [transitive_EQC]  Theorem
      
      |- transitive R^=
   
   [transitive_O_RSUBSET]  Theorem
      
      |- transitive R ⇔ R O R RSUBSET R
   
   [transitive_RC]  Theorem
      
      |- ∀R. transitive R ⇒ transitive (RC R)
   
   [transitive_RINTER]  Theorem
      
      |- transitive R1 ∧ transitive R2 ⇒ transitive (R1 RINTER R2)
   
   [transitive_RTC]  Theorem
      
      |- ∀R. transitive R^*
   
   [transitive_TC_identity]  Theorem
      
      |- ∀R. transitive R ⇒ (R⁺ = R)
   
   [transitive_inv]  Theorem
      
      |- ∀R. transitive (inv R) ⇔ transitive R
   
   
*)
end
