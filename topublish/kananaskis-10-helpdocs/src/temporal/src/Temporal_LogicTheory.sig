signature Temporal_LogicTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ALWAYS : thm
    val BEFORE : thm
    val EVENTUAL : thm
    val NEXT : thm
    val SBEFORE : thm
    val SUNTIL : thm
    val SWHEN : thm
    val UNTIL : thm
    val UPTO : thm
    val WATCH : thm
    val WHEN : thm

  (*  Theorems  *)
    val ALWAYS_AS_BEFORE : thm
    val ALWAYS_AS_SBEFORE : thm
    val ALWAYS_AS_SUNTIL : thm
    val ALWAYS_AS_SWHEN : thm
    val ALWAYS_AS_UNTIL : thm
    val ALWAYS_AS_WHEN : thm
    val ALWAYS_FIX : thm
    val ALWAYS_IDEM : thm
    val ALWAYS_INVARIANT : thm
    val ALWAYS_LINORD : thm
    val ALWAYS_NEXT : thm
    val ALWAYS_REC : thm
    val ALWAYS_SIGNAL : thm
    val AND_NEXT : thm
    val BEFORE_AS_NOT_SWHEN : thm
    val BEFORE_AS_SBEFORE : thm
    val BEFORE_AS_SUNTIL : thm
    val BEFORE_AS_SWHEN : thm
    val BEFORE_AS_UNTIL : thm
    val BEFORE_AS_WHEN : thm
    val BEFORE_AS_WHEN_UNTIL : thm
    val BEFORE_EVENT : thm
    val BEFORE_FIX : thm
    val BEFORE_HW : thm
    val BEFORE_IDEM : thm
    val BEFORE_IMP : thm
    val BEFORE_INVARIANT : thm
    val BEFORE_LINORD : thm
    val BEFORE_NEXT : thm
    val BEFORE_REC : thm
    val BEFORE_SIGNAL : thm
    val BEFORE_SIMP : thm
    val DELTA_CASES : thm
    val EQUIV_NEXT : thm
    val EVENTUAL_AS_BEFORE : thm
    val EVENTUAL_AS_SBEFORE : thm
    val EVENTUAL_AS_SUNTIL : thm
    val EVENTUAL_AS_SWHEN : thm
    val EVENTUAL_AS_UNTIL : thm
    val EVENTUAL_AS_WHEN : thm
    val EVENTUAL_FIX : thm
    val EVENTUAL_IDEM : thm
    val EVENTUAL_INVARIANT : thm
    val EVENTUAL_LINORD : thm
    val EVENTUAL_NEXT : thm
    val EVENTUAL_REC : thm
    val EVENTUAL_SIGNAL : thm
    val IMMEDIATE_EVENT : thm
    val IMP_NEXT : thm
    val MORE_EVENT : thm
    val NEXT_LINORD : thm
    val NOT_ALWAYS : thm
    val NOT_BEFORE : thm
    val NOT_EVENTUAL : thm
    val NOT_NEXT : thm
    val NOT_SBEFORE : thm
    val NOT_SUNTIL : thm
    val NOT_SWHEN : thm
    val NOT_UNTIL : thm
    val NOT_WHEN : thm
    val NO_EVENT : thm
    val OR_NEXT : thm
    val SBEFORE_AS_BEFORE : thm
    val SBEFORE_AS_SUNTIL : thm
    val SBEFORE_AS_SWHEN : thm
    val SBEFORE_AS_UNTIL : thm
    val SBEFORE_AS_WHEN : thm
    val SBEFORE_EVENT : thm
    val SBEFORE_IDEM : thm
    val SBEFORE_IMP : thm
    val SBEFORE_INVARIANT : thm
    val SBEFORE_LINORD : thm
    val SBEFORE_NEXT : thm
    val SBEFORE_REC : thm
    val SBEFORE_SIGNAL : thm
    val SBEFORE_SIMP : thm
    val SOME_EVENT : thm
    val SUNTIL_AS_BEFORE : thm
    val SUNTIL_AS_SBEFORE : thm
    val SUNTIL_AS_SWHEN : thm
    val SUNTIL_AS_UNTIL : thm
    val SUNTIL_AS_WHEN : thm
    val SUNTIL_EVENT : thm
    val SUNTIL_IDEM : thm
    val SUNTIL_IMP : thm
    val SUNTIL_INVARIANT : thm
    val SUNTIL_LINORD : thm
    val SUNTIL_NEXT : thm
    val SUNTIL_REC : thm
    val SUNTIL_SIGNAL : thm
    val SUNTIL_SIMP : thm
    val SWHEN_AS_BEFORE : thm
    val SWHEN_AS_NOT_WHEN : thm
    val SWHEN_AS_SBEFORE : thm
    val SWHEN_AS_SUNTIL : thm
    val SWHEN_AS_UNTIL : thm
    val SWHEN_AS_WHEN : thm
    val SWHEN_EVENT : thm
    val SWHEN_IDEM : thm
    val SWHEN_IMP : thm
    val SWHEN_INVARIANT : thm
    val SWHEN_LINORD : thm
    val SWHEN_NEXT : thm
    val SWHEN_REC : thm
    val SWHEN_SIGNAL : thm
    val SWHEN_SIMP : thm
    val UNTIL_AS_BEFORE : thm
    val UNTIL_AS_SBEFORE : thm
    val UNTIL_AS_SUNTIL : thm
    val UNTIL_AS_SWHEN : thm
    val UNTIL_AS_WHEN : thm
    val UNTIL_EVENT : thm
    val UNTIL_FIX : thm
    val UNTIL_IDEM : thm
    val UNTIL_IMP : thm
    val UNTIL_INVARIANT : thm
    val UNTIL_LINORD : thm
    val UNTIL_NEXT : thm
    val UNTIL_REC : thm
    val UNTIL_SIGNAL : thm
    val UNTIL_SIMP : thm
    val WATCH_EXISTS : thm
    val WATCH_REC : thm
    val WATCH_SIGNAL : thm
    val WELL_ORDER : thm
    val WELL_ORDER_UNIQUE : thm
    val WHEN_AS_BEFORE : thm
    val WHEN_AS_NOT_SWHEN : thm
    val WHEN_AS_SBEFORE : thm
    val WHEN_AS_SUNTIL : thm
    val WHEN_AS_SWHEN : thm
    val WHEN_AS_UNTIL : thm
    val WHEN_EVENT : thm
    val WHEN_FIX : thm
    val WHEN_IDEM : thm
    val WHEN_IMP : thm
    val WHEN_INVARIANT : thm
    val WHEN_LINORD : thm
    val WHEN_NEXT : thm
    val WHEN_REC : thm
    val WHEN_SIGNAL : thm
    val WHEN_SIMP : thm
    val WHEN_SWHEN_LEMMA : thm

  val Temporal_Logic_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "Temporal_Logic"

   [ALWAYS]  Definition

      |- ∀P t0. ALWAYS P t0 ⇔ ∀t. P (t + t0)

   [BEFORE]  Definition

      |- ∀a b t0.
           (a BEFORE b) t0 ⇔
           ∃q.
             (q WATCH b) t0 ∧
             ((∃t. ¬q (t + t0) ∧ ¬b (t + t0) ∧ a (t + t0)) ∨
              ∀t. ¬b (t + t0))

   [EVENTUAL]  Definition

      |- ∀P t0. EVENTUAL P t0 ⇔ ∃t. P (t + t0)

   [NEXT]  Definition

      |- ∀P. NEXT P = (λt. P (SUC t))

   [SBEFORE]  Definition

      |- ∀a b t0.
           (a SBEFORE b) t0 ⇔
           ∃q. (q WATCH b) t0 ∧ ∃t. ¬q (t + t0) ∧ ¬b (t + t0) ∧ a (t + t0)

   [SUNTIL]  Definition

      |- ∀a b t0.
           (a SUNTIL b) t0 ⇔
           ∃q.
             (q WATCH b) t0 ∧ (∀t. q (t + t0) ∨ b (t + t0) ∨ a (t + t0)) ∧
             ∃t. b (t + t0)

   [SWHEN]  Definition

      |- ∀a b t0.
           (a SWHEN b) t0 ⇔
           ∃q. (q WATCH b) t0 ∧ ∃t. ¬q (t + t0) ∧ b (t + t0) ∧ a (t + t0)

   [UNTIL]  Definition

      |- ∀a b t0.
           (a UNTIL b) t0 ⇔
           ∃q. (q WATCH b) t0 ∧ ∀t. q (t + t0) ∨ b (t + t0) ∨ a (t + t0)

   [UPTO]  Definition

      |- ∀t0 t1 a. UPTO (t0,t1,a) ⇔ ∀t2. t0 ≤ t2 ∧ t2 < t1 ⇒ a t2

   [WATCH]  Definition

      |- ∀q b t0.
           (q WATCH b) t0 ⇔
           ∀t. (q t0 ⇔ F) ∧ (q (SUC (t + t0)) ⇔ q (t + t0) ∨ b (t + t0))

   [WHEN]  Definition

      |- ∀a b t0.
           (a WHEN b) t0 ⇔
           ∃q. (q WATCH b) t0 ∧ ∀t. q (t + t0) ∨ (b (t + t0) ⇒ a (t + t0))

   [ALWAYS_AS_BEFORE]  Theorem

      |- ALWAYS b = (λt. F) BEFORE (λt. ¬b t)

   [ALWAYS_AS_SBEFORE]  Theorem

      |- ALWAYS b = (λt0. ¬((λt. ¬b t) SBEFORE (λt. F)) t0)

   [ALWAYS_AS_SUNTIL]  Theorem

      |- ALWAYS a = (λt. ¬((λt. T) SUNTIL (λt. ¬a t)) t)

   [ALWAYS_AS_SWHEN]  Theorem

      |- ALWAYS a = (λt. ¬((λt. T) SWHEN (λt. ¬a t)) t)

   [ALWAYS_AS_UNTIL]  Theorem

      |- ALWAYS a = a UNTIL (λt. F)

   [ALWAYS_AS_WHEN]  Theorem

      |- ALWAYS a = (λt. F) WHEN (λt. ¬a t)

   [ALWAYS_FIX]  Theorem

      |- (y = (λt. a t ∧ y (t + 1))) ⇔ (y = ALWAYS a) ∨ (y = (λt. F))

   [ALWAYS_IDEM]  Theorem

      |- ALWAYS a = ALWAYS (ALWAYS a)

   [ALWAYS_INVARIANT]  Theorem

      |- ALWAYS a t0 ⇔
         ∃J. J t0 ∧ ∀t. J (t + t0) ⇒ a (t + t0) ∧ J (t + (t0 + 1))

   [ALWAYS_LINORD]  Theorem

      |- ALWAYS a t0 ⇔ ∀t1. t0 ≤ t1 ⇒ a t1

   [ALWAYS_NEXT]  Theorem

      |- ∀a. NEXT (ALWAYS a) = ALWAYS (NEXT a)

   [ALWAYS_REC]  Theorem

      |- ALWAYS P t0 ⇔ P t0 ∧ NEXT (ALWAYS P) t0

   [ALWAYS_SIGNAL]  Theorem

      |- ALWAYS a t0 ⇔ ∀t. a (t + t0)

   [AND_NEXT]  Theorem

      |- ∀Q P. NEXT (λt. P t ∧ Q t) = (λt. NEXT P t ∧ NEXT Q t)

   [BEFORE_AS_NOT_SWHEN]  Theorem

      |- a BEFORE b = (λt0. ¬(b SWHEN (λt. a t ∨ b t)) t0)

   [BEFORE_AS_SBEFORE]  Theorem

      |- a BEFORE b = (λt0. (a SBEFORE b) t0 ∨ ALWAYS (λt. ¬b t) t0)

   [BEFORE_AS_SUNTIL]  Theorem

      |- a BEFORE b = (λt. ¬((λt. ¬a t) SUNTIL b) t)

   [BEFORE_AS_SWHEN]  Theorem

      |- a BEFORE b =
         (λt0.
            ((λt. ¬b t) SWHEN (λt. a t ∨ b t)) t0 ∨
            ALWAYS (λt. ¬a t ∧ ¬b t) t0)

   [BEFORE_AS_UNTIL]  Theorem

      |- a BEFORE b =
         (λt0. ¬((λt. ¬a t) UNTIL b) t0 ∨ ALWAYS (λt. ¬b t) t0)

   [BEFORE_AS_WHEN]  Theorem

      |- a BEFORE b = (λt. ¬b t) WHEN (λt. a t ∨ b t)

   [BEFORE_AS_WHEN_UNTIL]  Theorem

      |- a BEFORE b = (λt. ((λt. ¬b t) UNTIL a) t ∧ ((λt. ¬b t) WHEN a) t)

   [BEFORE_EVENT]  Theorem

      |- a BEFORE b = (λt. a t ∧ ¬b t) BEFORE b

   [BEFORE_FIX]  Theorem

      |- ∀y.
           (y = (λt. ¬b t ∧ (a t ∨ y (t + 1)))) ⇔
           (y = a BEFORE b) ∨ (y = a SBEFORE b)

   [BEFORE_HW]  Theorem

      |- (a BEFORE b) t0 ⇔
         ∃q. (q WATCH a) t0 ∧ ∀t. q (t + t0) ∨ ¬b (t + t0)

   [BEFORE_IDEM]  Theorem

      |- a BEFORE b = (a BEFORE b) BEFORE b

   [BEFORE_IMP]  Theorem

      |- (a BEFORE b) t0 ⇔
         ∀q.
           (q WATCH b) t0 ⇒
           (∃t. ¬q (t + t0) ∧ ¬b (t + t0) ∧ a (t + t0)) ∨ ∀t. ¬b (t + t0)

   [BEFORE_INVARIANT]  Theorem

      |- (a BEFORE b) t0 ⇔
         ∃J.
           J t0 ∧ (∀t. J (t + t0) ∧ ¬a (t + t0) ⇒ J (SUC (t + t0))) ∧
           ∀d. J (d + t0) ⇒ ¬b (d + t0)

   [BEFORE_LINORD]  Theorem

      |- (a BEFORE b) t0 ⇔ ∀t1. t0 ≤ t1 ∧ UPTO (t0,t1,(λt. ¬a t)) ⇒ ¬b t1

   [BEFORE_NEXT]  Theorem

      |- ∀a b. NEXT (a BEFORE b) = NEXT a BEFORE NEXT b

   [BEFORE_REC]  Theorem

      |- (a BEFORE b) t0 ⇔ ¬b t0 ∧ (a t0 ∨ NEXT (a BEFORE b) t0)

   [BEFORE_SIGNAL]  Theorem

      |- (a BEFORE b) t0 ⇔
         ∀delta.
           (∀t. t < delta ⇒ ¬b (t + t0)) ∧ b (delta + t0) ⇒
           ∃t. t < delta ∧ a (t + t0)

   [BEFORE_SIMP]  Theorem

      |- ((λt. F) BEFORE b = ALWAYS (λt. ¬b t)) ∧
         ((λt. T) BEFORE b = (λt. ¬b t)) ∧ (a BEFORE (λt. F) = (λt. T)) ∧
         (a BEFORE (λt. T) = (λt. F)) ∧ (a BEFORE a = ALWAYS (λt. ¬a t))

   [DELTA_CASES]  Theorem

      |- (∃d. (∀t. t < d ⇒ ¬b (t + t0)) ∧ b (d + t0)) ∨ ∀d. ¬b (d + t0)

   [EQUIV_NEXT]  Theorem

      |- ∀Q P. NEXT (λt. P t ⇔ Q t) = (λt. NEXT P t ⇔ NEXT Q t)

   [EVENTUAL_AS_BEFORE]  Theorem

      |- EVENTUAL b = (λt0. ¬((λt. F) BEFORE b) t0)

   [EVENTUAL_AS_SBEFORE]  Theorem

      |- EVENTUAL b = b SBEFORE (λt. F)

   [EVENTUAL_AS_SUNTIL]  Theorem

      |- EVENTUAL a = (λt. T) SUNTIL a

   [EVENTUAL_AS_SWHEN]  Theorem

      |- EVENTUAL a = (λt. T) SWHEN a

   [EVENTUAL_AS_UNTIL]  Theorem

      |- EVENTUAL a = (λt. ¬((λt. ¬a t) UNTIL (λt. F)) t)

   [EVENTUAL_AS_WHEN]  Theorem

      |- EVENTUAL a = (λt. ¬((λt. F) WHEN a) t)

   [EVENTUAL_FIX]  Theorem

      |- (y = (λt. a t ∨ y (t + 1))) ⇔ (y = EVENTUAL a) ∨ (y = (λt. T))

   [EVENTUAL_IDEM]  Theorem

      |- EVENTUAL a = EVENTUAL (EVENTUAL a)

   [EVENTUAL_INVARIANT]  Theorem

      |- EVENTUAL b t0 ⇔
         ∃J.
           0 < J t0 ∧
           (∀t. J (SUC (t + t0)) < J (t + t0) ∨ (J (SUC (t + t0)) = 0)) ∧
           ∀t. 0 < J (t + t0) ∧ (J (SUC (t + t0)) = 0) ⇒ b (t + t0)

   [EVENTUAL_LINORD]  Theorem

      |- EVENTUAL a t0 ⇔ ∃t1. t0 ≤ t1 ∧ a t1

   [EVENTUAL_NEXT]  Theorem

      |- ∀a. NEXT (EVENTUAL a) = EVENTUAL (NEXT a)

   [EVENTUAL_REC]  Theorem

      |- EVENTUAL P t0 ⇔ P t0 ∨ NEXT (EVENTUAL P) t0

   [EVENTUAL_SIGNAL]  Theorem

      |- EVENTUAL a t0 ⇔ ∃t. a (t + t0)

   [IMMEDIATE_EVENT]  Theorem

      |- b t0 ⇒
         (∀a. (a WHEN b) t0 ⇔ a t0) ∧ (∀a. (a UNTIL b) t0 ⇔ T) ∧
         (∀a. (a BEFORE b) t0 ⇔ F) ∧ (∀a. (a SWHEN b) t0 ⇔ a t0) ∧
         (∀a. (a SUNTIL b) t0 ⇔ T) ∧ ∀a. (a SBEFORE b) t0 ⇔ F

   [IMP_NEXT]  Theorem

      |- ∀Q P. NEXT (λt. P t ⇒ Q t) = (λt. NEXT P t ⇒ NEXT Q t)

   [MORE_EVENT]  Theorem

      |- (a WHEN b = (λt. a t ∧ b t) WHEN b) ∧
         (a UNTIL b = (λt. a t ∧ ¬b t) UNTIL b) ∧
         (a BEFORE b = (λt. a t ∧ ¬b t) BEFORE b) ∧
         (a SWHEN b = (λt. a t ∧ b t) SWHEN b) ∧
         (a SUNTIL b = (λt. a t ∧ ¬b t) SUNTIL b) ∧
         (a SBEFORE b = (λt. a t ∧ ¬b t) SBEFORE b)

   [NEXT_LINORD]  Theorem

      |- NEXT a t0 ⇔ ∃t1. t0 < t1 ∧ (∀t3. t0 < t3 ⇒ t1 ≤ t3) ∧ a t1

   [NOT_ALWAYS]  Theorem

      |- ¬ALWAYS a t0 ⇔ EVENTUAL (λt. ¬a t) t0

   [NOT_BEFORE]  Theorem

      |- ¬(a BEFORE b) t0 ⇔ ((λt. ¬a t) SUNTIL b) t0

   [NOT_EVENTUAL]  Theorem

      |- ¬EVENTUAL a t0 ⇔ ALWAYS (λt. ¬a t) t0

   [NOT_NEXT]  Theorem

      |- ∀P. NEXT (λt. ¬P t) = (λt. ¬NEXT P t)

   [NOT_SBEFORE]  Theorem

      |- ¬(a SBEFORE b) t0 ⇔ ((λt. ¬a t) UNTIL b) t0

   [NOT_SUNTIL]  Theorem

      |- ¬(a SUNTIL b) t0 ⇔ ((λt. ¬a t) BEFORE b) t0

   [NOT_SWHEN]  Theorem

      |- ¬(a SWHEN b) t0 ⇔ ((λt. ¬a t) WHEN b) t0

   [NOT_UNTIL]  Theorem

      |- ¬(a UNTIL b) t0 ⇔ ((λt. ¬a t) SBEFORE b) t0

   [NOT_WHEN]  Theorem

      |- ¬(a WHEN b) t0 ⇔ ((λt. ¬a t) SWHEN b) t0

   [NO_EVENT]  Theorem

      |- ALWAYS (λt. ¬b t) t0 ⇒
         (∀a. (a WHEN b) t0 ⇔ T) ∧ (∀a. (a UNTIL b) t0 ⇔ ALWAYS a t0) ∧
         (∀a. (a BEFORE b) t0 ⇔ T) ∧ (∀a. (a SWHEN b) t0 ⇔ F) ∧
         (∀a. (a SUNTIL b) t0 ⇔ F) ∧ ∀a. (a SBEFORE b) t0 ⇔ EVENTUAL a t0

   [OR_NEXT]  Theorem

      |- ∀Q P. NEXT (λt. P t ∨ Q t) = (λt. NEXT P t ∨ NEXT Q t)

   [SBEFORE_AS_BEFORE]  Theorem

      |- a SBEFORE b = (λt0. (a BEFORE b) t0 ∧ EVENTUAL a t0)

   [SBEFORE_AS_SUNTIL]  Theorem

      |- a SBEFORE b = (λt0. ¬((λt. ¬a t) SUNTIL b) t0 ∧ EVENTUAL a t0)

   [SBEFORE_AS_SWHEN]  Theorem

      |- a SBEFORE b = (λt. ¬b t) SWHEN (λt. a t ∨ b t)

   [SBEFORE_AS_UNTIL]  Theorem

      |- a SBEFORE b = (λt0. ¬((λt. ¬a t) UNTIL b) t0)

   [SBEFORE_AS_WHEN]  Theorem

      |- a SBEFORE b =
         (λt0. ((λt. ¬b t) WHEN (λt. a t ∨ b t)) t0 ∧ EVENTUAL a t0)

   [SBEFORE_EVENT]  Theorem

      |- a SBEFORE b = (λt. a t ∧ ¬b t) SBEFORE b

   [SBEFORE_IDEM]  Theorem

      |- a SBEFORE b = (a SBEFORE b) SBEFORE b

   [SBEFORE_IMP]  Theorem

      |- (a SBEFORE b) t0 ⇔
         ∀q. (q WATCH b) t0 ⇒ ∃t. ¬q (t + t0) ∧ ¬b (t + t0) ∧ a (t + t0)

   [SBEFORE_INVARIANT]  Theorem

      |- (a SBEFORE b) t0 ⇔
         (∃J1.
            J1 t0 ∧ (∀t. J1 (t + t0) ∧ ¬a (t + t0) ⇒ J1 (SUC (t + t0))) ∧
            ∀d. J1 (d + t0) ⇒ ¬b (d + t0)) ∧
         ∃J2.
           0 < J2 t0 ∧
           (∀t.
              J2 (SUC (t + t0)) < J2 (t + t0) ∨ (J2 (SUC (t + t0)) = 0)) ∧
           ∀t. 0 < J2 (t + t0) ∧ (J2 (SUC (t + t0)) = 0) ⇒ a (t + t0)

   [SBEFORE_LINORD]  Theorem

      |- (a SBEFORE b) t0 ⇔
         ∃t1. t0 ≤ t1 ∧ a t1 ∧ ¬b t1 ∧ UPTO (t0,t1,(λt. ¬b t))

   [SBEFORE_NEXT]  Theorem

      |- ∀a b. NEXT (a SBEFORE b) = NEXT a SBEFORE NEXT b

   [SBEFORE_REC]  Theorem

      |- (a SBEFORE b) t0 ⇔ ¬b t0 ∧ (a t0 ∨ NEXT (a SBEFORE b) t0)

   [SBEFORE_SIGNAL]  Theorem

      |- (a SBEFORE b) t0 ⇔
         ∃delta. a (delta + t0) ∧ ∀t. t ≤ delta ⇒ ¬b (t + t0)

   [SBEFORE_SIMP]  Theorem

      |- ((λt. F) SBEFORE b = (λt. F)) ∧ ((λt. T) SBEFORE b = (λt. ¬b t)) ∧
         (a SBEFORE (λt. F) = EVENTUAL a) ∧ (a SBEFORE (λt. T) = (λt. F)) ∧
         (a SBEFORE a = (λt. F))

   [SOME_EVENT]  Theorem

      |- (EVENTUAL b t0 ⇔ ∀a. (a WHEN b) t0 ⇔ (a SWHEN b) t0) ∧
         (EVENTUAL b t0 ⇔ ∀a. (a UNTIL b) t0 ⇔ (a SUNTIL b) t0) ∧
         (EVENTUAL b t0 ⇔ ∀a. (a BEFORE b) t0 ⇔ (a SBEFORE b) t0)

   [SUNTIL_AS_BEFORE]  Theorem

      |- a SUNTIL b = (λt0. ¬((λt. ¬a t) BEFORE b) t0)

   [SUNTIL_AS_SBEFORE]  Theorem

      |- a SUNTIL b = (λt0. ¬((λt. ¬a t) SBEFORE b) t0 ∧ EVENTUAL b t0)

   [SUNTIL_AS_SWHEN]  Theorem

      |- a SUNTIL b = b SWHEN (λt. a t ⇒ b t)

   [SUNTIL_AS_UNTIL]  Theorem

      |- a SUNTIL b = (λt0. (a UNTIL b) t0 ∧ EVENTUAL b t0)

   [SUNTIL_AS_WHEN]  Theorem

      |- a SUNTIL b = (λt. (b WHEN (λt. a t ⇒ b t)) t ∧ EVENTUAL b t)

   [SUNTIL_EVENT]  Theorem

      |- a SUNTIL b = (λt. a t ∧ ¬b t) SUNTIL b

   [SUNTIL_IDEM]  Theorem

      |- a SUNTIL b = (a SUNTIL b) SUNTIL b

   [SUNTIL_IMP]  Theorem

      |- (a SUNTIL b) t0 ⇔
         ∀q.
           (q WATCH b) t0 ⇒
           (∀t. q (t + t0) ∨ b (t + t0) ∨ a (t + t0)) ∧ ∃t. b (t + t0)

   [SUNTIL_INVARIANT]  Theorem

      |- (a SUNTIL b) t0 ⇔
         (∃J1.
            J1 t0 ∧
            ∀t.
              J1 (t + t0) ∧ ¬b (t + t0) ⇒ a (t + t0) ∧ J1 (SUC (t + t0))) ∧
         ∃J2.
           0 < J2 t0 ∧
           (∀t.
              J2 (SUC (t + t0)) < J2 (t + t0) ∨ (J2 (SUC (t + t0)) = 0)) ∧
           ∀t. 0 < J2 (t + t0) ∧ (J2 (SUC (t + t0)) = 0) ⇒ b (t + t0)

   [SUNTIL_LINORD]  Theorem

      |- (a SUNTIL b) t0 ⇔ ∃t1. t0 ≤ t1 ∧ b t1 ∧ UPTO (t0,t1,a)

   [SUNTIL_NEXT]  Theorem

      |- ∀a b. NEXT (a SUNTIL b) = NEXT a SUNTIL NEXT b

   [SUNTIL_REC]  Theorem

      |- (a SUNTIL b) t0 ⇔ ¬b t0 ⇒ a t0 ∧ NEXT (a SUNTIL b) t0

   [SUNTIL_SIGNAL]  Theorem

      |- (a SUNTIL b) t0 ⇔
         ∃delta.
           (∀t. t < delta ⇒ a (t + t0) ∧ ¬b (t + t0)) ∧ b (delta + t0)

   [SUNTIL_SIMP]  Theorem

      |- ((λt. F) SUNTIL b = (λt. b t)) ∧ ((λt. T) SUNTIL b = EVENTUAL b) ∧
         (a SUNTIL (λt. F) = (λt. F)) ∧ (a SUNTIL (λt. T) = (λt. T)) ∧
         (a SUNTIL a = (λt. a t))

   [SWHEN_AS_BEFORE]  Theorem

      |- a SWHEN b = (λt0. ¬(b BEFORE (λt. a t ∧ b t)) t0)

   [SWHEN_AS_NOT_WHEN]  Theorem

      |- (a SWHEN b) t0 ⇔ ¬((λt. ¬a t) WHEN b) t0

   [SWHEN_AS_SBEFORE]  Theorem

      |- a SWHEN b = b SBEFORE (λt. ¬a t ∧ b t)

   [SWHEN_AS_SUNTIL]  Theorem

      |- a SWHEN b = (λt. ¬b t) SUNTIL (λt. a t ∧ b t)

   [SWHEN_AS_UNTIL]  Theorem

      |- a SWHEN b =
         (λt. ((λt. ¬b t) UNTIL (λt. a t ∧ b t)) t ∧ EVENTUAL b t)

   [SWHEN_AS_WHEN]  Theorem

      |- a SWHEN b = (λt0. (a WHEN b) t0 ∧ EVENTUAL b t0)

   [SWHEN_EVENT]  Theorem

      |- a SWHEN b = (λt. a t ∧ b t) SWHEN b

   [SWHEN_IDEM]  Theorem

      |- a SWHEN b = (a SWHEN b) SWHEN b

   [SWHEN_IMP]  Theorem

      |- (a SWHEN b) t0 ⇔
         ∀q. (q WATCH b) t0 ⇒ ∃t. ¬q (t + t0) ∧ b (t + t0) ∧ a (t + t0)

   [SWHEN_INVARIANT]  Theorem

      |- (a SWHEN b) t0 ⇔
         (∃J1.
            J1 t0 ∧ (∀t. ¬b (t + t0) ∧ J1 (t + t0) ⇒ J1 (SUC (t + t0))) ∧
            ∀d. b (d + t0) ∧ J1 (d + t0) ⇒ a (d + t0)) ∧
         ∃J2.
           0 < J2 t0 ∧
           (∀t.
              J2 (SUC (t + t0)) < J2 (t + t0) ∨ (J2 (SUC (t + t0)) = 0)) ∧
           ∀t. 0 < J2 (t + t0) ∧ (J2 (SUC (t + t0)) = 0) ⇒ b (t + t0)

   [SWHEN_LINORD]  Theorem

      |- (a SWHEN b) t0 ⇔
         ∃t1. t0 ≤ t1 ∧ a t1 ∧ b t1 ∧ UPTO (t0,t1,(λt. ¬b t))

   [SWHEN_NEXT]  Theorem

      |- ∀a b. NEXT (a SWHEN b) = NEXT a SWHEN NEXT b

   [SWHEN_REC]  Theorem

      |- (a SWHEN b) t0 ⇔ if b t0 then a t0 else NEXT (a SWHEN b) t0

   [SWHEN_SIGNAL]  Theorem

      |- (a SWHEN b) t0 ⇔
         ∃delta.
           (∀t. t < delta ⇒ ¬b (t + t0)) ∧ b (delta + t0) ∧ a (delta + t0)

   [SWHEN_SIMP]  Theorem

      |- ((λt. F) SWHEN b = (λt. F)) ∧ ((λt. T) SWHEN b = EVENTUAL b) ∧
         (a SWHEN (λt. F) = (λt. F)) ∧ (a SWHEN (λt. T) = (λt. a t)) ∧
         (a SWHEN a = EVENTUAL a)

   [UNTIL_AS_BEFORE]  Theorem

      |- a UNTIL b = (λt0. ¬((λt. ¬a t) BEFORE b) t0 ∨ ALWAYS a t0)

   [UNTIL_AS_SBEFORE]  Theorem

      |- a UNTIL b = (λt0. ¬((λt. ¬a t) SBEFORE b) t0)

   [UNTIL_AS_SUNTIL]  Theorem

      |- a UNTIL b = (λt. (a SUNTIL b) t ∨ ALWAYS a t)

   [UNTIL_AS_SWHEN]  Theorem

      |- a UNTIL b = (λt. (b SWHEN (λt. a t ⇒ b t)) t ∨ ALWAYS a t)

   [UNTIL_AS_WHEN]  Theorem

      |- a UNTIL b = b WHEN (λt. a t ⇒ b t)

   [UNTIL_EVENT]  Theorem

      |- a UNTIL b = (λt. a t ∧ ¬b t) UNTIL b

   [UNTIL_FIX]  Theorem

      |- (y = (λt. ¬b t ⇒ a t ∧ y (t + 1))) ⇔
         (y = a UNTIL b) ∨ (y = a SUNTIL b)

   [UNTIL_IDEM]  Theorem

      |- a UNTIL b = (a UNTIL b) UNTIL b

   [UNTIL_IMP]  Theorem

      |- (a UNTIL b) t0 ⇔
         ∀q. (q WATCH b) t0 ⇒ ∀t. q (t + t0) ∨ b (t + t0) ∨ a (t + t0)

   [UNTIL_INVARIANT]  Theorem

      |- ∀t0.
           (a UNTIL b) t0 ⇔
           ∃J.
             J t0 ∧
             ∀t. J (t + t0) ∧ ¬b (t + t0) ⇒ a (t + t0) ∧ J (SUC (t + t0))

   [UNTIL_LINORD]  Theorem

      |- (a UNTIL b) t0 ⇔
         ∀t1. t0 ≤ t1 ∧ ¬b t1 ∧ UPTO (t0,t1,(λt. ¬b t)) ⇒ a t1

   [UNTIL_NEXT]  Theorem

      |- ∀a b. NEXT (a UNTIL b) = NEXT a UNTIL NEXT b

   [UNTIL_REC]  Theorem

      |- (a UNTIL b) t0 ⇔ ¬b t0 ⇒ a t0 ∧ NEXT (a UNTIL b) t0

   [UNTIL_SIGNAL]  Theorem

      |- (a UNTIL b) t0 ⇔
         ((∀t. ¬b (t + t0)) ⇒ ∀t. a (t + t0)) ∧
         ∀d.
           (∀t. t < d ⇒ ¬b (t + t0)) ∧ b (d + t0) ⇒ ∀t. t < d ⇒ a (t + t0)

   [UNTIL_SIMP]  Theorem

      |- ((λt. F) UNTIL b = (λt. b t)) ∧ ((λt. T) UNTIL b = (λt. T)) ∧
         (a UNTIL (λt. F) = ALWAYS a) ∧ (a UNTIL (λt. T) = (λt. T)) ∧
         (a UNTIL a = (λt. a t))

   [WATCH_EXISTS]  Theorem

      |- ∀b t0. ∃q. (q WATCH b) t0

   [WATCH_REC]  Theorem

      |- (q WATCH b) t0 ⇔
         ¬q t0 ∧ if b t0 then NEXT (ALWAYS q) t0 else NEXT (q WATCH b) t0

   [WATCH_SIGNAL]  Theorem

      |- (q WATCH b) t0 ⇔
         ((∀t. ¬b (t + t0)) ⇒ ∀t. ¬q (t + t0)) ∧
         ∀d.
           b (d + t0) ∧ (∀t. t < d ⇒ ¬b (t + t0)) ⇒
           (∀t. t ≤ d ⇒ ¬q (t + t0)) ∧ ∀t. q (SUC (t + (d + t0)))

   [WELL_ORDER]  Theorem

      |- (∃n. P n) ⇔ ∃m. P m ∧ ∀n. n < m ⇒ ¬P n

   [WELL_ORDER_UNIQUE]  Theorem

      |- ∀m2 m1 P.
           (P m1 ∧ ∀n. n < m1 ⇒ ¬P n) ∧ P m2 ∧ (∀n. n < m2 ⇒ ¬P n) ⇒
           (m1 = m2)

   [WHEN_AS_BEFORE]  Theorem

      |- a WHEN b =
         (λt0. ¬(b BEFORE (λt. a t ∧ b t)) t0 ∨ ALWAYS (λt. ¬b t) t0)

   [WHEN_AS_NOT_SWHEN]  Theorem

      |- (a WHEN b) t0 ⇔ ¬((λt. ¬a t) SWHEN b) t0

   [WHEN_AS_SBEFORE]  Theorem

      |- a WHEN b =
         (λt0. (b SBEFORE (λt. ¬a t ∧ b t)) t0 ∨ ALWAYS (λt. ¬b t) t0)

   [WHEN_AS_SUNTIL]  Theorem

      |- a WHEN b =
         (λt. ((λt. ¬b t) SUNTIL (λt. a t ∧ b t)) t ∨ ALWAYS (λt. ¬b t) t)

   [WHEN_AS_SWHEN]  Theorem

      |- a WHEN b = (λt. (a SWHEN b) t ∨ ALWAYS (λt. ¬b t) t)

   [WHEN_AS_UNTIL]  Theorem

      |- a WHEN b = (λt. ¬b t) UNTIL (λt. a t ∧ b t)

   [WHEN_EVENT]  Theorem

      |- a WHEN b = (λt. a t ∧ b t) WHEN b

   [WHEN_FIX]  Theorem

      |- (y = (λt. if b t then a t else y (t + 1))) ⇔
         (y = a WHEN b) ∨ (y = a SWHEN b)

   [WHEN_IDEM]  Theorem

      |- a WHEN b = (a WHEN b) WHEN b

   [WHEN_IMP]  Theorem

      |- (a WHEN b) t0 ⇔
         ∀q. (q WATCH b) t0 ⇒ ∀t. q (t + t0) ∨ (b (t + t0) ⇒ a (t + t0))

   [WHEN_INVARIANT]  Theorem

      |- (a WHEN b) t0 ⇔
         ∃J.
           J t0 ∧ (∀t. ¬b (t + t0) ∧ J (t + t0) ⇒ J (SUC (t + t0))) ∧
           ∀d. b (d + t0) ∧ J (d + t0) ⇒ a (d + t0)

   [WHEN_LINORD]  Theorem

      |- (a WHEN b) t0 ⇔
         ∀t1. t0 ≤ t1 ∧ b t1 ∧ UPTO (t0,t1,(λt. ¬b t)) ⇒ a t1

   [WHEN_NEXT]  Theorem

      |- ∀a b. NEXT (a WHEN b) = NEXT a WHEN NEXT b

   [WHEN_REC]  Theorem

      |- (a WHEN b) t0 ⇔ if b t0 then a t0 else NEXT (a WHEN b) t0

   [WHEN_SIGNAL]  Theorem

      |- (a WHEN b) t0 ⇔
         ∀delta.
           (∀t. t < delta ⇒ ¬b (t + t0)) ∧ b (delta + t0) ⇒ a (delta + t0)

   [WHEN_SIMP]  Theorem

      |- ((λt. F) WHEN b = ALWAYS (λt. ¬b t)) ∧
         ((λt. T) WHEN b = (λt. T)) ∧ (a WHEN (λt. F) = (λt. T)) ∧
         (a WHEN (λt. T) = (λt. a t)) ∧ (a WHEN a = (λt. T))

   [WHEN_SWHEN_LEMMA]  Theorem

      |- if ∀t1. ∃t2. b (t2 + t1) then ∀t0. (a WHEN b) t0 ⇔ (a SWHEN b) t0
         else ∃t1. ∀t2. (a WHEN b) (t2 + t1) ∧ ¬(a SWHEN b) (t2 + t1)


*)
end
