signature Past_Temporal_LogicTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val InitPoint : thm
    val PALWAYS : thm
    val PBEFORE : thm
    val PEVENTUAL : thm
    val PNEXT : thm
    val PSBEFORE : thm
    val PSNEXT : thm
    val PSUNTIL : thm
    val PSWHEN : thm
    val PUNTIL : thm
    val PWHEN : thm

  (*  Theorems  *)
    val BEFORE_EXPRESSIVE : thm
    val CONJUNCTIVE_NORMAL_FORM : thm
    val DISJUNCTIVE_NORMAL_FORM : thm
    val FIXPOINTS : thm
    val IMMEDIATE_EVENT : thm
    val INITIALISATION : thm
    val MORE_EVENT : thm
    val NEGATION_NORMAL_FORM : thm
    val NEXT_INWARDS_NORMAL_FORM : thm
    val NO_FUTURE_EVENT : thm
    val NO_PAST_EVENT : thm
    val PBEFORE_EXPRESSIVE : thm
    val PNEXT_INWARDS_NORMAL_FORM : thm
    val PRENEX_NEXT_NORMAL_FORM : thm
    val PSBEFORE_EXPRESSIVE : thm
    val PSUNTIL_EXPRESSIVE : thm
    val PSWHEN_EXPRESSIVE : thm
    val PUNTIL_EXPRESSIVE : thm
    val PWHEN_EXPRESSIVE : thm
    val RECURSION : thm
    val SBEFORE_EXPRESSIVE : thm
    val SEPARATE_BEFORE_THM : thm
    val SEPARATE_NEXT_THM : thm
    val SEPARATE_PNEXT_THM : thm
    val SEPARATE_PSUNTIL_THM : thm
    val SEPARATE_SUNTIL_THM : thm
    val SIMPLIFY : thm
    val SOME_FUTURE_EVENT : thm
    val SOME_PAST_EVENT : thm
    val SUNTIL_EXPRESSIVE : thm
    val SWHEN_EXPRESSIVE : thm
    val UNTIL_EXPRESSIVE : thm
    val WHEN_EXPRESSIVE : thm

  val Past_Temporal_Logic_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Temporal_Logic] Parent theory of "Past_Temporal_Logic"

   [InitPoint]  Definition

      |- InitPoint = (λt. t = 0)

   [PALWAYS]  Definition

      |- ∀a t0. PALWAYS a t0 ⇔ ∀t. t ≤ t0 ⇒ a t

   [PBEFORE]  Definition

      |- ∀a b t0.
           (a PBEFORE b) t0 ⇔
           (∀t. t ≤ t0 ⇒ ¬b t) ∨
           ∃delta. delta ≤ t0 ∧ a delta ∧ ∀t. delta ≤ t ∧ t ≤ t0 ⇒ ¬b t

   [PEVENTUAL]  Definition

      |- ∀a t0. PEVENTUAL a t0 ⇔ ∃t. t ≤ t0 ∧ a t

   [PNEXT]  Definition

      |- ∀a t0. PNEXT a t0 ⇔ (t0 = 0) ∨ a (PRE t0)

   [PSBEFORE]  Definition

      |- ∀a b t0.
           (a PSBEFORE b) t0 ⇔
           ∃delta. delta ≤ t0 ∧ a delta ∧ ∀t. delta ≤ t ∧ t ≤ t0 ⇒ ¬b t

   [PSNEXT]  Definition

      |- ∀a t0. PSNEXT a t0 ⇔ 0 < t0 ∧ a (PRE t0)

   [PSUNTIL]  Definition

      |- ∀a b t0.
           (a PSUNTIL b) t0 ⇔
           ∃delta.
             delta ≤ t0 ∧ b delta ∧ ∀t. delta < t ∧ t ≤ t0 ⇒ a t ∧ ¬b t

   [PSWHEN]  Definition

      |- ∀a b t0.
           (a PSWHEN b) t0 ⇔
           ∃delta.
             delta ≤ t0 ∧ a delta ∧ b delta ∧ ∀t. delta < t ∧ t ≤ t0 ⇒ ¬b t

   [PUNTIL]  Definition

      |- ∀a b t0.
           (a PUNTIL b) t0 ⇔
           (∀t. t ≤ t0 ⇒ a t) ∨
           ∃delta.
             delta ≤ t0 ∧ b delta ∧ ∀t. delta < t ∧ t ≤ t0 ⇒ a t ∧ ¬b t

   [PWHEN]  Definition

      |- ∀a b t0.
           (a PWHEN b) t0 ⇔
           (∀t. t ≤ t0 ⇒ ¬b t) ∨
           ∃delta.
             delta ≤ t0 ∧ a delta ∧ b delta ∧ ∀t. delta < t ∧ t ≤ t0 ⇒ ¬b t

   [BEFORE_EXPRESSIVE]  Theorem

      |- (ALWAYS a = (λt. ((λt. F) BEFORE (λt. ¬a t)) t)) ∧
         (EVENTUAL a = (λt. ¬((λt. F) BEFORE a) t)) ∧
         (a SUNTIL b = (λt. ¬((λt. ¬a t) BEFORE b) t)) ∧
         (a UNTIL b = (λt. (b BEFORE (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a SWHEN b = (λt. ¬(b BEFORE (λt. a t ∧ b t)) t)) ∧
         (a WHEN b = (λt. ((λt. a t ∧ b t) BEFORE (λt. ¬a t ∧ b t)) t)) ∧
         (a SBEFORE b = (λt. ¬(b BEFORE (λt. a t ∧ ¬b t)) t))

   [CONJUNCTIVE_NORMAL_FORM]  Theorem

      |- (NEXT (λt. a t ∧ b t) = (λt. NEXT a t ∧ NEXT b t)) ∧
         (ALWAYS (λt. a t ∧ b t) = (λt. ALWAYS a t ∧ ALWAYS b t)) ∧
         ((λt. a t ∧ b t) WHEN c = (λt. (a WHEN c) t ∧ (b WHEN c) t)) ∧
         ((λt. a t ∧ b t) SWHEN c = (λt. (a SWHEN c) t ∧ (b SWHEN c) t)) ∧
         ((λt. a t ∧ b t) UNTIL c = (λt. (a UNTIL c) t ∧ (b UNTIL c) t)) ∧
         ((λt. a t ∧ b t) SUNTIL c =
          (λt. (a SUNTIL c) t ∧ (b SUNTIL c) t)) ∧
         (c BEFORE (λt. a t ∨ b t) =
          (λt. (c BEFORE a) t ∧ (c BEFORE b) t)) ∧
         (c SBEFORE (λt. a t ∨ b t) =
          (λt. (c SBEFORE a) t ∧ (c SBEFORE b) t)) ∧
         (PNEXT (λt. a t ∧ b t) = (λt. PNEXT a t ∧ PNEXT b t)) ∧
         (PSNEXT (λt. a t ∧ b t) = (λt. PSNEXT a t ∧ PSNEXT b t)) ∧
         (PALWAYS (λt. a t ∧ b t) = (λt. PALWAYS a t ∧ PALWAYS b t)) ∧
         ((λt. a t ∧ b t) PWHEN c = (λt. (a PWHEN c) t ∧ (b PWHEN c) t)) ∧
         ((λt. a t ∧ b t) PSWHEN c =
          (λt. (a PSWHEN c) t ∧ (b PSWHEN c) t)) ∧
         ((λt. a t ∧ b t) PUNTIL c =
          (λt. (a PUNTIL c) t ∧ (b PUNTIL c) t)) ∧
         ((λt. a t ∧ b t) PSUNTIL c =
          (λt. (a PSUNTIL c) t ∧ (b PSUNTIL c) t)) ∧
         (c PBEFORE (λt. a t ∨ b t) =
          (λt. (c PBEFORE a) t ∧ (c PBEFORE b) t)) ∧
         (c PSBEFORE (λt. a t ∨ b t) =
          (λt. (c PSBEFORE a) t ∧ (c PSBEFORE b) t))

   [DISJUNCTIVE_NORMAL_FORM]  Theorem

      |- (NEXT (λt. a t ∨ b t) = (λt. NEXT a t ∨ NEXT b t)) ∧
         (EVENTUAL (λt. a t ∨ b t) = (λt. EVENTUAL a t ∨ EVENTUAL b t)) ∧
         ((λt. a t ∨ b t) WHEN c = (λt. (a WHEN c) t ∨ (b WHEN c) t)) ∧
         ((λt. a t ∨ b t) SWHEN c = (λt. (a SWHEN c) t ∨ (b SWHEN c) t)) ∧
         (a UNTIL (λt. b t ∨ c t) = (λt. (a UNTIL b) t ∨ (a UNTIL c) t)) ∧
         (a SUNTIL (λt. b t ∨ c t) =
          (λt. (a SUNTIL b) t ∨ (a SUNTIL c) t)) ∧
         ((λt. a t ∨ b t) BEFORE c =
          (λt. (a BEFORE c) t ∨ (b BEFORE c) t)) ∧
         ((λt. a t ∨ b t) SBEFORE c =
          (λt. (a SBEFORE c) t ∨ (b SBEFORE c) t)) ∧
         (PNEXT (λt. a t ∨ b t) = (λt. PNEXT a t ∨ PNEXT b t)) ∧
         (PEVENTUAL (λt. a t ∨ b t) =
          (λt. PEVENTUAL a t ∨ PEVENTUAL b t)) ∧
         ((λt. a t ∨ b t) PWHEN c = (λt. (a PWHEN c) t ∨ (b PWHEN c) t)) ∧
         ((λt. a t ∨ b t) PSWHEN c =
          (λt. (a PSWHEN c) t ∨ (b PSWHEN c) t)) ∧
         (a PUNTIL (λt. b t ∨ c t) =
          (λt. (a PUNTIL b) t ∨ (a PUNTIL c) t)) ∧
         (a PSUNTIL (λt. b t ∨ c t) =
          (λt. (a PSUNTIL b) t ∨ (a PSUNTIL c) t)) ∧
         ((λt. a t ∨ b t) PBEFORE c =
          (λt. (a PBEFORE c) t ∨ (b PBEFORE c) t)) ∧
         ((λt. a t ∨ b t) PSBEFORE c =
          (λt. (a PSBEFORE c) t ∨ (b PSBEFORE c) t))

   [FIXPOINTS]  Theorem

      |- ((y = (λt. a t ∧ NEXT y t)) ⇔ (y = ALWAYS a) ∨ (y = (λt. F))) ∧
         ((y = (λt. a t ∨ NEXT y t)) ⇔ (y = EVENTUAL a) ∨ (y = (λt. T))) ∧
         ((y = (λt. ¬b t ⇒ a t ∧ NEXT y t)) ⇔
          (y = a UNTIL b) ∨ (y = a SUNTIL b)) ∧
         ((y = (λt. if b t then a t else NEXT y t)) ⇔
          (y = a WHEN b) ∨ (y = a SWHEN b)) ∧
         ((y = (λt. ¬b t ∧ (a t ∨ NEXT y t))) ⇔
          (y = a BEFORE b) ∨ (y = a SBEFORE b)) ∧
         ((y = (λt. a t ∧ PNEXT y t)) ⇔ (y = PALWAYS a)) ∧
         ((y = (λt. a t ∨ PSNEXT y t)) ⇔ (y = PEVENTUAL a)) ∧
         ((y = (λt. b t ∨ a t ∧ PSNEXT y t)) ⇔ (y = a PSUNTIL b)) ∧
         ((y = (λt. a t ∧ b t ∨ ¬b t ∧ PSNEXT y t)) ⇔ (y = a PSWHEN b)) ∧
         ((y = (λt. ¬b t ∧ (a t ∨ PSNEXT y t))) ⇔ (y = a PSBEFORE b)) ∧
         ((y = (λt. b t ∨ a t ∧ PNEXT y t)) ⇔ (y = a PUNTIL b)) ∧
         ((y = (λt. a t ∧ b t ∨ ¬b t ∧ PNEXT y t)) ⇔ (y = a PWHEN b)) ∧
         ((y = (λt. ¬b t ∧ (a t ∨ PNEXT y t))) ⇔ (y = a PBEFORE b))

   [IMMEDIATE_EVENT]  Theorem

      |- b t ⇒
         ((a WHEN b) t ⇔ a t) ∧ ((a UNTIL b) t ⇔ T) ∧
         ((a BEFORE b) t ⇔ F) ∧ ((b BEFORE a) t ⇔ ¬a t) ∧
         ((a SWHEN b) t ⇔ a t) ∧ ((a SUNTIL b) t ⇔ T) ∧
         ((a SBEFORE b) t ⇔ F) ∧ ((b SBEFORE a) t ⇔ ¬a t) ∧
         ((a PWHEN b) t ⇔ a t) ∧ ((a PUNTIL b) t ⇔ T) ∧
         ((a PBEFORE b) t ⇔ F) ∧ ((b PBEFORE a) t ⇔ ¬a t) ∧
         ((a PSWHEN b) t ⇔ a t) ∧ ((a PSUNTIL b) t ⇔ T) ∧
         ((a PSBEFORE b) t ⇔ F) ∧ ((b PSBEFORE a) t ⇔ ¬a t)

   [INITIALISATION]  Theorem

      |- (PNEXT a 0 ⇔ T) ∧ (PSNEXT a 0 ⇔ F) ∧ (PALWAYS a 0 ⇔ a 0) ∧
         (PEVENTUAL a 0 ⇔ a 0) ∧ ((a PSUNTIL b) 0 ⇔ b 0) ∧
         ((a PSWHEN b) 0 ⇔ a 0 ∧ b 0) ∧ ((a PSBEFORE b) 0 ⇔ a 0 ∧ ¬b 0) ∧
         ((a PUNTIL b) 0 ⇔ a 0 ∨ b 0) ∧ ((a PWHEN b) 0 ⇔ a 0 ∨ ¬b 0) ∧
         ((a PBEFORE b) 0 ⇔ ¬b 0)

   [MORE_EVENT]  Theorem

      |- (a WHEN b = (λt. a t ∧ b t) WHEN b) ∧
         (a UNTIL b = (λt. a t ∧ ¬b t) UNTIL b) ∧
         (a BEFORE b = (λt. a t ∧ ¬b t) BEFORE b) ∧
         (a SWHEN b = (λt. a t ∧ b t) SWHEN b) ∧
         (a SUNTIL b = (λt. a t ∧ ¬b t) SUNTIL b) ∧
         (a SBEFORE b = (λt. a t ∧ ¬b t) SBEFORE b) ∧
         (a PWHEN b = (λt. a t ∧ b t) PWHEN b) ∧
         (a PUNTIL b = (λt. a t ∧ ¬b t) PUNTIL b) ∧
         (a PBEFORE b = (λt. a t ∧ ¬b t) PBEFORE b) ∧
         (a PSWHEN b = (λt. a t ∧ b t) PSWHEN b) ∧
         (a PSUNTIL b = (λt. a t ∧ ¬b t) PSUNTIL b) ∧
         (a PSBEFORE b = (λt. a t ∧ ¬b t) PSBEFORE b)

   [NEGATION_NORMAL_FORM]  Theorem

      |- (¬NEXT a t ⇔ NEXT (λt. ¬a t) t) ∧
         (¬ALWAYS a t ⇔ EVENTUAL (λt. ¬a t) t) ∧
         (¬EVENTUAL a t ⇔ ALWAYS (λt. ¬a t) t) ∧
         (¬(a WHEN b) t ⇔ ((λt. ¬a t) SWHEN b) t) ∧
         (¬(a UNTIL b) t ⇔ ((λt. ¬a t) SBEFORE b) t) ∧
         (¬(a BEFORE b) t ⇔ ((λt. ¬a t) SUNTIL b) t) ∧
         (¬(a SWHEN b) t ⇔ ((λt. ¬a t) WHEN b) t) ∧
         (¬(a SUNTIL b) t ⇔ ((λt. ¬a t) BEFORE b) t) ∧
         (¬(a SBEFORE b) t ⇔ ((λt. ¬a t) UNTIL b) t) ∧
         (¬PNEXT a t ⇔ PSNEXT (λt. ¬a t) t) ∧
         (¬PSNEXT a t ⇔ PNEXT (λt. ¬a t) t) ∧
         (¬PALWAYS a t ⇔ PEVENTUAL (λt. ¬a t) t) ∧
         (¬PEVENTUAL a t ⇔ PALWAYS (λt. ¬a t) t) ∧
         (¬(a PWHEN b) t ⇔ ((λt. ¬a t) PSWHEN b) t) ∧
         (¬(a PUNTIL b) t ⇔ ((λt. ¬a t) PSBEFORE b) t) ∧
         (¬(a PBEFORE b) t ⇔ ((λt. ¬a t) PSUNTIL b) t) ∧
         (¬(a PSWHEN b) t ⇔ ((λt. ¬a t) PWHEN b) t) ∧
         (¬(a PSUNTIL b) t ⇔ ((λt. ¬a t) PBEFORE b) t) ∧
         (¬(a PSBEFORE b) t ⇔ ((λt. ¬a t) PUNTIL b) t)

   [NEXT_INWARDS_NORMAL_FORM]  Theorem

      |- (NEXT (λt. ¬a t) = (λt. ¬NEXT a t)) ∧
         (NEXT (λt. a t ∧ b t) = (λt. NEXT a t ∧ NEXT b t)) ∧
         (NEXT (λt. a t ∨ b t) = (λt. NEXT a t ∨ NEXT b t)) ∧
         (NEXT (ALWAYS a) = ALWAYS (NEXT a)) ∧
         (NEXT (EVENTUAL a) = EVENTUAL (NEXT a)) ∧
         (NEXT (a SUNTIL b) = NEXT a SUNTIL NEXT b) ∧
         (NEXT (a SWHEN b) = NEXT a SWHEN NEXT b) ∧
         (NEXT (a SBEFORE b) = NEXT a SBEFORE NEXT b) ∧
         (NEXT (a UNTIL b) = NEXT a UNTIL NEXT b) ∧
         (NEXT (a WHEN b) = NEXT a WHEN NEXT b) ∧
         (NEXT (a BEFORE b) = NEXT a BEFORE NEXT b) ∧
         (NEXT (PNEXT a) = a) ∧ (NEXT (PSNEXT a) = a) ∧
         (NEXT (PALWAYS a) = (λt. PALWAYS a t ∧ NEXT a t)) ∧
         (NEXT (PEVENTUAL a) = (λt. PEVENTUAL a t ∨ NEXT a t)) ∧
         (NEXT (a PSUNTIL b) =
          (λt. NEXT b t ∨ NEXT a t ∧ (a PSUNTIL b) t)) ∧
         (NEXT (a PSWHEN b) =
          (λt. if NEXT b t then NEXT a t else (a PSWHEN b) t)) ∧
         (NEXT (a PSBEFORE b) =
          (λt. ¬NEXT b t ∧ (NEXT a t ∨ (a PSBEFORE b) t))) ∧
         (NEXT (a PUNTIL b) = (λt. NEXT b t ∨ NEXT a t ∧ (a PUNTIL b) t)) ∧
         (NEXT (a PWHEN b) =
          (λt. if NEXT b t then NEXT a t else (a PWHEN b) t)) ∧
         (NEXT (a PBEFORE b) =
          (λt. ¬NEXT b t ∧ (NEXT a t ∨ (a PBEFORE b) t)))

   [NO_FUTURE_EVENT]  Theorem

      |- ALWAYS (λt. ¬b t) t0 ⇒
         (∀a. (a WHEN b) t0 ⇔ T) ∧ (∀a. (a UNTIL b) t0 ⇔ ALWAYS a t0) ∧
         (∀a. (a BEFORE b) t0 ⇔ T) ∧ (∀a. (a SWHEN b) t0 ⇔ F) ∧
         (∀a. (a SUNTIL b) t0 ⇔ F) ∧ ∀a. (a SBEFORE b) t0 ⇔ EVENTUAL a t0

   [NO_PAST_EVENT]  Theorem

      |- PALWAYS (λt. ¬b t) t ⇒
         ((a PWHEN b) t ⇔ T) ∧ ((a PUNTIL b) t ⇔ PALWAYS a t) ∧
         ((a PBEFORE b) t ⇔ T) ∧ ((b PBEFORE a) t ⇔ PALWAYS (λt. ¬a t) t) ∧
         ((a PSWHEN b) t ⇔ F) ∧ ((a PSUNTIL b) t ⇔ F) ∧
         ((a PSBEFORE b) t ⇔ PEVENTUAL a t) ∧ ((b PSBEFORE a) t ⇔ F)

   [PBEFORE_EXPRESSIVE]  Theorem

      |- (PALWAYS a = (λt. ((λt. F) PBEFORE (λt. ¬a t)) t)) ∧
         (PEVENTUAL a = (λt. ¬((λt. F) PBEFORE a) t)) ∧
         (a PSUNTIL b = (λt. ¬((λt. ¬a t) PBEFORE b) t)) ∧
         (a PUNTIL b = (λt. (b PBEFORE (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a PSWHEN b = (λt. ¬(b PBEFORE (λt. a t ∧ b t)) t)) ∧
         (a PWHEN b = (λt. ((λt. a t ∧ b t) PBEFORE (λt. ¬a t ∧ b t)) t)) ∧
         (a PSBEFORE b = (λt. ¬(b PBEFORE (λt. a t ∧ ¬b t)) t))

   [PNEXT_INWARDS_NORMAL_FORM]  Theorem

      |- (PNEXT (λt. ¬a t) = (λt. ¬PSNEXT a t)) ∧
         (PNEXT (λt. a t ∧ b t) = (λt. PNEXT a t ∧ PNEXT b t)) ∧
         (PNEXT (λt. a t ∨ b t) = (λt. PNEXT a t ∨ PNEXT b t)) ∧
         (PNEXT (NEXT a) = (λt. InitPoint t ∨ a t)) ∧
         (PNEXT (ALWAYS a) = (λt. InitPoint t ∨ ALWAYS (PNEXT a) t)) ∧
         (PNEXT (EVENTUAL a) = (λt. InitPoint t ∨ EVENTUAL (PNEXT a) t)) ∧
         (PNEXT (a SUNTIL b) = PNEXT a SUNTIL PNEXT b) ∧
         (PNEXT (a SWHEN b) = PNEXT a SWHEN PNEXT b) ∧
         (PNEXT (a SBEFORE b) = PNEXT a SBEFORE PSNEXT b) ∧
         (PNEXT (a UNTIL b) = PNEXT a UNTIL PNEXT b) ∧
         (PNEXT (a WHEN b) = PNEXT a WHEN PNEXT b) ∧
         (PNEXT (a BEFORE b) = PNEXT a BEFORE PSNEXT b) ∧
         (PNEXT (PALWAYS a) = PALWAYS (PNEXT a)) ∧
         (PNEXT (PEVENTUAL a) =
          (λt. InitPoint t ∨ PEVENTUAL (PSNEXT a) t)) ∧
         (PNEXT (a PSUNTIL b) =
          (λt. InitPoint t ∨ (PNEXT a PSUNTIL PSNEXT b) t)) ∧
         (PNEXT (a PSWHEN b) =
          (λt. InitPoint t ∨ (PNEXT a PSWHEN PSNEXT b) t)) ∧
         (PNEXT (a PSBEFORE b) =
          (λt. InitPoint t ∨ (PSNEXT a PSBEFORE PNEXT b) t)) ∧
         (PNEXT (a PUNTIL b) = PNEXT a PUNTIL PNEXT b) ∧
         (PNEXT (a PWHEN b) = PNEXT a PWHEN PNEXT b) ∧
         (PNEXT (a PBEFORE b) = PNEXT a PBEFORE PSNEXT b)

   [PRENEX_NEXT_NORMAL_FORM]  Theorem

      |- (¬NEXT a t ⇔ NEXT (λt. ¬a t) t) ∧
         (a t ∧ NEXT b t ⇔ NEXT (λt. PNEXT a t ∧ b t) t) ∧
         (a t ∨ NEXT b t ⇔ NEXT (λt. PNEXT a t ∨ b t) t) ∧
         (ALWAYS (NEXT a) = NEXT (ALWAYS a)) ∧
         (EVENTUAL (NEXT a) = NEXT (EVENTUAL a)) ∧
         (a SUNTIL NEXT b = NEXT (PNEXT a SUNTIL b)) ∧
         (a SWHEN NEXT b = NEXT (PNEXT a SWHEN b)) ∧
         (a SBEFORE NEXT b = NEXT (PNEXT a SBEFORE b)) ∧
         (a UNTIL NEXT b = NEXT (PNEXT a UNTIL b)) ∧
         (a WHEN NEXT b = NEXT (PNEXT a WHEN b)) ∧
         (a BEFORE NEXT b = NEXT (PNEXT a BEFORE b)) ∧
         (NEXT a SUNTIL b = NEXT (a SUNTIL PNEXT b)) ∧
         (NEXT a SWHEN b = NEXT (a SWHEN PNEXT b)) ∧
         (NEXT a SBEFORE b = NEXT (a SBEFORE PNEXT b)) ∧
         (NEXT a UNTIL b = NEXT (a UNTIL PNEXT b)) ∧
         (NEXT a WHEN b = NEXT (a WHEN PNEXT b)) ∧
         (NEXT a BEFORE b = NEXT (a BEFORE PNEXT b)) ∧
         (PNEXT (NEXT a) = (λt. InitPoint t ∨ a t)) ∧
         (PSNEXT (NEXT a) = (λt. ¬InitPoint t ∧ a t)) ∧
         (PALWAYS (NEXT a) = NEXT (PALWAYS (λt. InitPoint t ∨ a t))) ∧
         (PEVENTUAL (NEXT a) = NEXT (PEVENTUAL (λt. ¬InitPoint t ∧ a t))) ∧
         (a PSUNTIL NEXT b =
          NEXT (PNEXT a PSUNTIL (λt. ¬InitPoint t ∧ b t))) ∧
         (a PSWHEN NEXT b =
          NEXT (PNEXT a PSWHEN (λt. ¬InitPoint t ∧ b t))) ∧
         (a PSBEFORE NEXT b = NEXT (PSNEXT a PSBEFORE b)) ∧
         (a PUNTIL NEXT b = NEXT (PNEXT a PUNTIL b)) ∧
         (a PWHEN NEXT b = NEXT (PNEXT a PWHEN (λt. ¬InitPoint t ∧ b t))) ∧
         (a PBEFORE NEXT b =
          NEXT (PNEXT a PBEFORE (λt. ¬InitPoint t ∧ b t))) ∧
         (NEXT a PSUNTIL b = NEXT (a PSUNTIL PSNEXT b)) ∧
         (NEXT a PSWHEN b = NEXT (a PSWHEN PSNEXT b)) ∧
         (NEXT a PSBEFORE b =
          NEXT ((λt. ¬InitPoint t ∧ a t) PSBEFORE PNEXT b)) ∧
         (NEXT a PUNTIL b =
          NEXT ((λt. InitPoint t ∨ a t) PUNTIL PNEXT b)) ∧
         (NEXT a PWHEN b = NEXT (a PWHEN PSNEXT b)) ∧
         (NEXT a PBEFORE b = NEXT (a PBEFORE PSNEXT b))

   [PSBEFORE_EXPRESSIVE]  Theorem

      |- (PALWAYS a = (λt. ¬((λt. ¬a t) PSBEFORE (λt. F)) t)) ∧
         (PEVENTUAL a = (λt. (a PSBEFORE (λt. F)) t)) ∧
         (a PSUNTIL b = (λt. (b PSBEFORE (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a PUNTIL b = (λt. ¬((λt. ¬a t) PSBEFORE b) t)) ∧
         (a PSWHEN b = (λt. (b PSBEFORE (λt. ¬a t ∧ b t)) t)) ∧
         (a PWHEN b = (λt. ¬(b PSBEFORE (λt. a t ∧ b t)) t)) ∧
         (a PBEFORE b = (λt. ¬(b PSBEFORE (λt. a t ∧ ¬b t)) t))

   [PSUNTIL_EXPRESSIVE]  Theorem

      |- (PALWAYS a = (λt. ¬((λt. T) PSUNTIL (λt. ¬a t)) t)) ∧
         (PEVENTUAL a = (λt. ((λt. T) PSUNTIL a) t)) ∧
         (a PUNTIL b = (λt. ¬((λt. ¬b t) PSUNTIL (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a PWHEN b =
          (λt. ¬((λt. ¬a t ∨ ¬b t) PSUNTIL (λt. ¬a t ∧ b t)) t)) ∧
         (a PBEFORE b = (λt. ¬((λt. ¬a t) PSUNTIL b) t)) ∧
         (a PSWHEN b = (λt. ((λt. ¬b t) PSUNTIL (λt. a t ∧ b t)) t)) ∧
         (a PSBEFORE b = (λt. ((λt. ¬b t) PSUNTIL (λt. a t ∧ ¬b t)) t))

   [PSWHEN_EXPRESSIVE]  Theorem

      |- (PALWAYS a = (λt. ¬((λt. T) PSWHEN (λt. ¬a t)) t)) ∧
         (PEVENTUAL a = (λt. ((λt. T) PSWHEN a) t)) ∧
         (a PSUNTIL b = (λt. (b PSWHEN (λt. a t ⇒ b t)) t)) ∧
         (a PUNTIL b = (λt. ¬((λt. ¬b t) PSWHEN (λt. a t ⇒ b t)) t)) ∧
         (a PWHEN b = (λt. ¬((λt. ¬a t) PSWHEN b) t)) ∧
         (a PBEFORE b = (λt. ¬(b PSWHEN (λt. a t ∨ b t)) t)) ∧
         (a PSBEFORE b = (λt. ((λt. ¬b t) PSWHEN (λt. a t ∨ b t)) t))

   [PUNTIL_EXPRESSIVE]  Theorem

      |- (PALWAYS a = (λt. (a PUNTIL (λt. F)) t)) ∧
         (PEVENTUAL a = (λt. ¬((λt. ¬a t) PUNTIL (λt. F)) t)) ∧
         (a PSUNTIL b = (λt. ¬((λt. ¬b t) PUNTIL (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a PWHEN b = (λt. ((λt. ¬b t) PUNTIL (λt. a t ∧ b t)) t)) ∧
         (a PSWHEN b =
          (λt. ¬((λt. ¬a t ∨ ¬b t) PUNTIL (λt. ¬a t ∧ b t)) t)) ∧
         (a PBEFORE b = (λt. ((λt. ¬b t) PUNTIL (λt. a t ∧ ¬b t)) t)) ∧
         (a PSBEFORE b = (λt. ¬((λt. ¬a t) PUNTIL b) t))

   [PWHEN_EXPRESSIVE]  Theorem

      |- (PALWAYS a = (λt. ((λt. F) PWHEN (λt. ¬a t)) t)) ∧
         (PEVENTUAL a = (λt. ¬((λt. F) PWHEN a) t)) ∧
         (a PSUNTIL b = (λt. ¬((λt. ¬b t) PWHEN (λt. a t ⇒ b t)) t)) ∧
         (a PUNTIL b = (λt. (b PWHEN (λt. a t ⇒ b t)) t)) ∧
         (a PSWHEN b = (λt. ¬((λt. ¬a t) PWHEN b) t)) ∧
         (a PBEFORE b = (λt. ((λt. ¬b t) PWHEN (λt. a t ∨ b t)) t)) ∧
         (a PSBEFORE b = (λt. ¬(b PWHEN (λt. a t ∨ b t)) t))

   [RECURSION]  Theorem

      |- (ALWAYS a = (λt. a t ∧ NEXT (ALWAYS a) t)) ∧
         (EVENTUAL a = (λt. a t ∨ NEXT (EVENTUAL a) t)) ∧
         (a SUNTIL b = (λt. ¬b t ⇒ a t ∧ NEXT (a SUNTIL b) t)) ∧
         (a SWHEN b = (λt. if b t then a t else NEXT (a SWHEN b) t)) ∧
         (a SBEFORE b = (λt. ¬b t ∧ (a t ∨ NEXT (a SBEFORE b) t))) ∧
         (a UNTIL b = (λt. ¬b t ⇒ a t ∧ NEXT (a UNTIL b) t)) ∧
         (a WHEN b = (λt. if b t then a t else NEXT (a WHEN b) t)) ∧
         (a BEFORE b = (λt. ¬b t ∧ (a t ∨ NEXT (a BEFORE b) t))) ∧
         (PALWAYS a = (λt. a t ∧ PNEXT (PALWAYS a) t)) ∧
         (PEVENTUAL a = (λt. a t ∨ PSNEXT (PEVENTUAL a) t)) ∧
         (a PSUNTIL b = (λt. b t ∨ a t ∧ PSNEXT (a PSUNTIL b) t)) ∧
         (a PSWHEN b = (λt. a t ∧ b t ∨ ¬b t ∧ PSNEXT (a PSWHEN b) t)) ∧
         (a PSBEFORE b = (λt. ¬b t ∧ (a t ∨ PSNEXT (a PSBEFORE b) t))) ∧
         (a PUNTIL b = (λt. b t ∨ a t ∧ PNEXT (a PUNTIL b) t)) ∧
         (a PWHEN b = (λt. a t ∧ b t ∨ ¬b t ∧ PNEXT (a PWHEN b) t)) ∧
         (a PBEFORE b = (λt. ¬b t ∧ (a t ∨ PNEXT (a PBEFORE b) t)))

   [SBEFORE_EXPRESSIVE]  Theorem

      |- (ALWAYS a = (λt. ¬((λt. ¬a t) SBEFORE (λt. F)) t)) ∧
         (EVENTUAL a = (λt. (a SBEFORE (λt. F)) t)) ∧
         (a SUNTIL b = (λt. (b SBEFORE (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a UNTIL b = (λt. ¬((λt. ¬a t) SBEFORE b) t)) ∧
         (a SWHEN b = (λt. (b SBEFORE (λt. ¬a t ∧ b t)) t)) ∧
         (a WHEN b = (λt. ¬(b SBEFORE (λt. a t ∧ b t)) t)) ∧
         (a BEFORE b = (λt. ¬(b SBEFORE (λt. a t ∧ ¬b t)) t))

   [SEPARATE_BEFORE_THM]  Theorem

      |- (a BEFORE (λt. b t ∨ c t) =
          (λt. (a BEFORE b) t ∧ (a BEFORE c) t)) ∧
         ((λt. a t ∨ b t) BEFORE c =
          (λt. (a BEFORE c) t ∨ (b BEFORE c) t)) ∧
         (a BEFORE (λt. b t ∧ PNEXT c t) =
          (λt.
             ¬(b t ∧ PNEXT c t) ∧
             (a t ∨ (NEXT a BEFORE (λt. c t ∧ NEXT b t)) t))) ∧
         (a BEFORE (λt. b t ∧ PSNEXT c t) =
          (λt.
             ¬(b t ∧ PSNEXT c t) ∧
             (a t ∨ (NEXT a BEFORE (λt. c t ∧ NEXT b t)) t))) ∧
         (a BEFORE (λt. b t ∧ (c PSUNTIL d) t) =
          (λt.
             (((λt. ¬c t) PBEFORE d) t ∨
              ((λt. a t ∨ ¬NEXT c t) BEFORE b) t) ∧
             (a BEFORE (λt. d t ∧ ((λt. ¬a t ∧ NEXT c t) SUNTIL b) t))
               t)) ∧
         (a BEFORE (λt. b t ∧ (c PBEFORE d) t) =
          (λt.
             (((λt. ¬c t) PSUNTIL d) t ∨
              ((λt. a t ∨ NEXT d t) BEFORE b) t) ∧
             (a BEFORE
              (λt. c t ∧ ¬d t ∧ ((λt. ¬a t ∧ ¬NEXT d t) SUNTIL b) t)) t)) ∧
         ((λt. a t ∧ PNEXT b t) BEFORE c =
          (λt.
             ¬c t ∧ a t ∧ PNEXT b t ∨
             ¬c t ∧ ((λt. b t ∧ NEXT a t) BEFORE NEXT c) t)) ∧
         ((λt. a t ∧ PSNEXT b t) BEFORE c =
          (λt.
             ¬c t ∧ a t ∧ PSNEXT b t ∨
             ¬c t ∧ ((λt. b t ∧ NEXT a t) BEFORE NEXT c) t)) ∧
         ((λt. a t ∧ (b PBEFORE c) t) BEFORE d =
          (λt.
             (b PBEFORE c) t ∧
             ((λt. ¬d t ∧ ¬NEXT c t) SUNTIL (λt. a t ∧ ¬d t)) t ∨
             ((λt.
                 b t ∧ ¬c t ∧
                 ((λt. ¬d t ∧ ¬NEXT c t) SUNTIL (λt. a t ∧ ¬d t)) t) BEFORE
              d) t)) ∧
         ((λt. a t ∧ (b PSUNTIL c) t) BEFORE d =
          (λt.
             (b PSUNTIL c) t ∧
             ((λt. ¬d t ∧ NEXT b t) SUNTIL (λt. a t ∧ ¬d t)) t ∨
             ((λt.
                 c t ∧
                 ((λt. ¬d t ∧ NEXT b t) SUNTIL (λt. a t ∧ ¬d t)) t) BEFORE
              d) t))

   [SEPARATE_NEXT_THM]  Theorem

      |- (NEXT (λt. a t ∧ PNEXT b t) = (λt. b t ∧ NEXT a t)) ∧
         (NEXT (λt. a t ∧ PSNEXT b t) = (λt. b t ∧ NEXT a t)) ∧
         (NEXT (λt. a t ∧ (b PSUNTIL c) t) =
          (λt.
             NEXT (λt. a t ∧ c t) t ∨
             (b PSUNTIL c) t ∧ NEXT (λt. a t ∧ b t) t)) ∧
         (NEXT (λt. a t ∧ (b PBEFORE c) t) =
          (λt.
             NEXT (λt. a t ∧ b t ∧ ¬c t) t ∨
             (b PBEFORE c) t ∧ NEXT (λt. a t ∧ ¬c t) t)) ∧
         (NEXT (λt. a t ∨ PNEXT b t) = (λt. b t ∨ NEXT a t)) ∧
         (NEXT (λt. a t ∨ PSNEXT b t) = (λt. b t ∨ NEXT a t)) ∧
         (NEXT (λt. a t ∨ (b PSUNTIL c) t) =
          (λt. NEXT (λt. a t ∨ c t) t ∨ (b PSUNTIL c) t ∧ NEXT b t)) ∧
         (NEXT (λt. a t ∨ (b PBEFORE c) t) =
          (λt.
             NEXT (λt. a t ∨ ¬c t) t ∧
             ((b PBEFORE c) t ∨ NEXT (λt. a t ∨ b t) t)))

   [SEPARATE_PNEXT_THM]  Theorem

      |- (PNEXT (λt. a t ∧ NEXT b t) =
          (λt. InitPoint t ∨ b t ∧ PNEXT a t)) ∧
         (PNEXT (λt. a t ∧ (b SUNTIL c) t) =
          (λt.
             PNEXT (λt. a t ∧ c t) t ∨
             (b SUNTIL c) t ∧ PNEXT (λt. a t ∧ b t) t)) ∧
         (PNEXT (λt. a t ∧ (b BEFORE c) t) =
          (λt.
             PNEXT (λt. a t ∧ b t ∧ ¬c t) t ∨
             (b BEFORE c) t ∧ PNEXT (λt. a t ∧ ¬c t) t)) ∧
         (PNEXT (λt. a t ∨ NEXT b t) = (λt. b t ∨ PNEXT a t)) ∧
         (PNEXT (λt. a t ∨ (b SUNTIL c) t) =
          (λt. PNEXT (λt. a t ∨ c t) t ∨ (b SUNTIL c) t ∧ PNEXT b t)) ∧
         (PNEXT (λt. a t ∨ (b BEFORE c) t) =
          (λt.
             PNEXT (λt. a t ∨ ¬c t) t ∧
             ((b BEFORE c) t ∨ PNEXT (λt. a t ∨ b t) t)))

   [SEPARATE_PSUNTIL_THM]  Theorem

      |- (a PSUNTIL (λt. b t ∨ c t) =
          (λt. (a PSUNTIL b) t ∨ (a PSUNTIL c) t)) ∧
         (a PSUNTIL (λt. b t ∧ NEXT c t) =
          (λt.
             b t ∧ NEXT c t ∨
             (a PSUNTIL (λt. a t ∧ c t ∧ PSNEXT b t)) t)) ∧
         (a PSUNTIL (λt. b t ∧ (c SUNTIL d) t) =
          (λt.
             (c SUNTIL d) t ∧ ((λt. a t ∧ PNEXT c t) PSUNTIL b) t ∨
             (a PSUNTIL (λt. d t ∧ ((λt. a t ∧ PNEXT c t) PSUNTIL b) t))
               t)) ∧
         (a PSUNTIL (λt. b t ∧ (c BEFORE d) t) =
          (λt.
             (c BEFORE d) t ∧ ((λt. a t ∧ ¬PNEXT d t) PSUNTIL b) t ∨
             (a PSUNTIL
              (λt. c t ∧ ¬d t ∧ ((λt. a t ∧ ¬PNEXT d t) PSUNTIL b) t))
               t)) ∧
         ((λt. a t ∧ b t) PSUNTIL c =
          (λt. (a PSUNTIL c) t ∧ (b PSUNTIL c) t)) ∧
         ((λt. a t ∨ NEXT b t) PSUNTIL c =
          (λt.
             c t ∨
             (a t ∨ NEXT b t) ∧
             ((λt. b t ∨ PNEXT a t) PSUNTIL PSNEXT c) t)) ∧
         ((λt. a t ∨ (b SUNTIL c) t) PSUNTIL d =
          (λt.
             ((b SUNTIL c) t ∨
              ((λt. d t ∨ PNEXT c t) PBEFORE (λt. ¬a t ∧ ¬d t)) t) ∧
             ((λt.
                 b t ∨ c t ∨
                 ((λt. d t ∨ PNEXT c t) PBEFORE (λt. ¬a t ∧ ¬d t))
                   t) PSUNTIL d) t)) ∧
         ((λt. a t ∨ (b BEFORE c) t) PSUNTIL d =
          (λt.
             ((b BEFORE c) t ∨
              ((λt. d t ∨ PSNEXT b t) PBEFORE (λt. ¬a t ∧ ¬d t)) t) ∧
             ((λt.
                 ¬c t ∨
                 ((λt. d t ∨ PSNEXT b t) PBEFORE (λt. ¬a t ∧ ¬d t))
                   t) PSUNTIL d) t))

   [SEPARATE_SUNTIL_THM]  Theorem

      |- (a SUNTIL (λt. b t ∨ c t) =
          (λt. (a SUNTIL b) t ∨ (a SUNTIL c) t)) ∧
         (a SUNTIL (λt. b t ∧ PNEXT c t) =
          (λt.
             b t ∧ PNEXT c t ∨ (a SUNTIL (λt. a t ∧ c t ∧ NEXT b t)) t)) ∧
         (a SUNTIL (λt. b t ∧ PSNEXT c t) =
          (λt.
             b t ∧ PSNEXT c t ∨ (a SUNTIL (λt. a t ∧ c t ∧ NEXT b t)) t)) ∧
         (a SUNTIL (λt. b t ∧ (c PSUNTIL d) t) =
          (λt.
             (c PSUNTIL d) t ∧ ((λt. a t ∧ NEXT c t) SUNTIL b) t ∨
             (a SUNTIL (λt. d t ∧ ((λt. a t ∧ NEXT c t) SUNTIL b) t)) t)) ∧
         (a SUNTIL (λt. b t ∧ (c PBEFORE d) t) =
          (λt.
             (c PBEFORE d) t ∧ ((λt. a t ∧ ¬NEXT d t) SUNTIL b) t ∨
             (a SUNTIL
              (λt. c t ∧ ¬d t ∧ ((λt. a t ∧ ¬NEXT d t) SUNTIL b) t)) t)) ∧
         ((λt. a t ∧ b t) SUNTIL c =
          (λt. (a SUNTIL c) t ∧ (b SUNTIL c) t)) ∧
         ((λt. a t ∨ PNEXT b t) SUNTIL c =
          (λt.
             c t ∨
             (a t ∨ PNEXT b t) ∧ ((λt. b t ∨ NEXT a t) SUNTIL NEXT c) t)) ∧
         ((λt. a t ∨ PSNEXT b t) SUNTIL c =
          (λt.
             c t ∨
             (a t ∨ PSNEXT b t) ∧
             ((λt. b t ∨ NEXT a t) SUNTIL NEXT c) t)) ∧
         ((λt. a t ∨ (b PSUNTIL c) t) SUNTIL d =
          (λt.
             ((b PSUNTIL c) t ∨
              ((λt. d t ∨ NEXT c t) BEFORE (λt. ¬a t ∧ ¬d t)) t) ∧
             ((λt.
                 b t ∨ c t ∨
                 ((λt. d t ∨ NEXT c t) BEFORE (λt. ¬a t ∧ ¬d t)) t) SUNTIL
              d) t)) ∧
         ((λt. a t ∨ (b PBEFORE c) t) SUNTIL d =
          (λt.
             ((b PBEFORE c) t ∨
              ((λt. d t ∨ NEXT b t) BEFORE (λt. ¬a t ∧ ¬d t)) t) ∧
             ((λt.
                 ¬c t ∨
                 ((λt. d t ∨ NEXT b t) BEFORE (λt. ¬a t ∧ ¬d t)) t) SUNTIL
              d) t))

   [SIMPLIFY]  Theorem

      |- (NEXT (λt. F) = (λt. F)) ∧ (NEXT (λt. T) = (λt. T)) ∧
         (ALWAYS (λt. T) = (λt. T)) ∧ (ALWAYS (λt. F) = (λt. F)) ∧
         (EVENTUAL (λt. T) = (λt. T)) ∧ (EVENTUAL (λt. F) = (λt. F)) ∧
         ((λt. F) SUNTIL b = b) ∧ ((λt. T) SUNTIL b = EVENTUAL b) ∧
         (a SUNTIL (λt. F) = (λt. F)) ∧ (a SUNTIL (λt. T) = (λt. T)) ∧
         (a SUNTIL a = a) ∧ ((λt. F) UNTIL b = b) ∧
         ((λt. T) UNTIL b = (λt. T)) ∧ (a UNTIL (λt. F) = ALWAYS a) ∧
         (a UNTIL (λt. T) = (λt. T)) ∧ (a UNTIL a = a) ∧
         ((λt. F) SWHEN b = (λt. F)) ∧ ((λt. T) SWHEN b = EVENTUAL b) ∧
         (a SWHEN (λt. F) = (λt. F)) ∧ (a SWHEN (λt. T) = a) ∧
         (a SWHEN a = EVENTUAL a) ∧ ((λt. F) WHEN b = ALWAYS (λt. ¬b t)) ∧
         ((λt. T) WHEN b = (λt. T)) ∧ (a WHEN (λt. F) = (λt. T)) ∧
         (a WHEN (λt. T) = a) ∧ (a WHEN a = (λt. T)) ∧
         ((λt. F) SBEFORE b = (λt. F)) ∧ ((λt. T) SBEFORE b = (λt. ¬b t)) ∧
         (a SBEFORE (λt. F) = EVENTUAL a) ∧ (a SBEFORE (λt. T) = (λt. F)) ∧
         (a SBEFORE a = (λt. F)) ∧ ((λt. F) BEFORE b = ALWAYS (λt. ¬b t)) ∧
         ((λt. T) BEFORE b = (λt. ¬b t)) ∧ (a BEFORE (λt. F) = (λt. T)) ∧
         (a BEFORE (λt. T) = (λt. F)) ∧ (a BEFORE a = ALWAYS (λt. ¬a t)) ∧
         (PNEXT (λt. F) = InitPoint) ∧ (PNEXT (λt. T) = (λt. T)) ∧
         (PSNEXT (λt. F) = (λt. F)) ∧
         (PSNEXT (λt. T) = (λt. ¬InitPoint t)) ∧
         (PALWAYS (λt. T) = (λt. T)) ∧ (PALWAYS (λt. F) = (λt. F)) ∧
         (PEVENTUAL (λt. T) = (λt. T)) ∧ (PEVENTUAL (λt. F) = (λt. F)) ∧
         ((λt. F) PSUNTIL b = b) ∧ ((λt. T) PSUNTIL b = PEVENTUAL b) ∧
         (a PSUNTIL (λt. F) = (λt. F)) ∧ (a PSUNTIL (λt. T) = (λt. T)) ∧
         (a PSUNTIL a = a) ∧ ((λt. F) PUNTIL b = b) ∧
         ((λt. T) PUNTIL b = (λt. T)) ∧ (a PUNTIL (λt. F) = PALWAYS a) ∧
         (a PUNTIL (λt. T) = (λt. T)) ∧ (a PUNTIL a = a) ∧
         ((λt. F) PSWHEN b = (λt. F)) ∧ ((λt. T) PSWHEN b = PEVENTUAL b) ∧
         (a PSWHEN (λt. F) = (λt. F)) ∧ (a PSWHEN (λt. T) = a) ∧
         (a PSWHEN a = PEVENTUAL a) ∧
         ((λt. F) PWHEN b = PALWAYS (λt. ¬b t)) ∧
         ((λt. T) PWHEN b = (λt. T)) ∧ (a PWHEN (λt. F) = (λt. T)) ∧
         (a PWHEN (λt. T) = a) ∧ (a PWHEN a = (λt. T)) ∧
         ((λt. F) PSBEFORE b = (λt. F)) ∧
         ((λt. T) PSBEFORE b = (λt. ¬b t)) ∧
         (a PSBEFORE (λt. F) = PEVENTUAL a) ∧
         (a PSBEFORE (λt. T) = (λt. F)) ∧ (a PSBEFORE a = (λt. F)) ∧
         ((λt. F) PBEFORE b = PALWAYS (λt. ¬b t)) ∧
         ((λt. T) PBEFORE b = (λt. ¬b t)) ∧ (a PBEFORE (λt. F) = (λt. T)) ∧
         (a PBEFORE (λt. T) = (λt. F)) ∧ (a PBEFORE a = PALWAYS (λt. ¬a t))

   [SOME_FUTURE_EVENT]  Theorem

      |- (EVENTUAL b t0 ⇔ ∀a. (a WHEN b) t0 ⇔ (a SWHEN b) t0) ∧
         (EVENTUAL b t0 ⇔ ∀a. (a UNTIL b) t0 ⇔ (a SUNTIL b) t0) ∧
         (EVENTUAL b t0 ⇔ ∀a. (a BEFORE b) t0 ⇔ (a SBEFORE b) t0)

   [SOME_PAST_EVENT]  Theorem

      |- PEVENTUAL b t ⇒
         ((a PWHEN b) t ⇔ (a PSWHEN b) t) ∧
         ((a PUNTIL b) t ⇔ (a PSUNTIL b) t) ∧
         ((a PBEFORE b) t ⇔ (a PSBEFORE b) t) ∧
         ((b PBEFORE a) t ⇔ (b PSBEFORE a) t)

   [SUNTIL_EXPRESSIVE]  Theorem

      |- (ALWAYS a = (λt. ¬((λt. T) SUNTIL (λt. ¬a t)) t)) ∧
         (EVENTUAL a = (λt. ((λt. T) SUNTIL a) t)) ∧
         (a UNTIL b = (λt. ¬((λt. ¬b t) SUNTIL (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a WHEN b =
          (λt. ¬((λt. ¬a t ∨ ¬b t) SUNTIL (λt. ¬a t ∧ b t)) t)) ∧
         (a BEFORE b = (λt. ¬((λt. ¬a t) SUNTIL b) t)) ∧
         (a SWHEN b = (λt. ((λt. ¬b t) SUNTIL (λt. a t ∧ b t)) t)) ∧
         (a SBEFORE b = (λt. ((λt. ¬b t) SUNTIL (λt. a t ∧ ¬b t)) t))

   [SWHEN_EXPRESSIVE]  Theorem

      |- (ALWAYS a = (λt. ¬((λt. T) SWHEN (λt. ¬a t)) t)) ∧
         (EVENTUAL a = (λt. ((λt. T) SWHEN a) t)) ∧
         (a SUNTIL b = (λt. (b SWHEN (λt. a t ⇒ b t)) t)) ∧
         (a UNTIL b = (λt. ¬((λt. ¬b t) SWHEN (λt. a t ⇒ b t)) t)) ∧
         (a WHEN b = (λt. ¬((λt. ¬a t) SWHEN b) t)) ∧
         (a BEFORE b = (λt. ¬(b SWHEN (λt. a t ∨ b t)) t)) ∧
         (a SBEFORE b = (λt. ((λt. ¬b t) SWHEN (λt. a t ∨ b t)) t))

   [UNTIL_EXPRESSIVE]  Theorem

      |- (ALWAYS a = (λt. (a UNTIL (λt. F)) t)) ∧
         (EVENTUAL a = (λt. ¬((λt. ¬a t) UNTIL (λt. F)) t)) ∧
         (a SUNTIL b = (λt. ¬((λt. ¬b t) UNTIL (λt. ¬a t ∧ ¬b t)) t)) ∧
         (a WHEN b = (λt. ((λt. ¬b t) UNTIL (λt. a t ∧ b t)) t)) ∧
         (a SWHEN b =
          (λt. ¬((λt. ¬a t ∨ ¬b t) UNTIL (λt. ¬a t ∧ b t)) t)) ∧
         (a BEFORE b = (λt. ((λt. ¬b t) UNTIL (λt. a t ∧ ¬b t)) t)) ∧
         (a SBEFORE b = (λt. ¬((λt. ¬a t) UNTIL b) t))

   [WHEN_EXPRESSIVE]  Theorem

      |- (ALWAYS a = (λt. ((λt. F) WHEN (λt. ¬a t)) t)) ∧
         (EVENTUAL a = (λt. ¬((λt. F) WHEN a) t)) ∧
         (a SUNTIL b = (λt. ¬((λt. ¬b t) WHEN (λt. a t ⇒ b t)) t)) ∧
         (a UNTIL b = (λt. (b WHEN (λt. a t ⇒ b t)) t)) ∧
         (a SWHEN b = (λt. ¬((λt. ¬a t) WHEN b) t)) ∧
         (a BEFORE b = (λt. ((λt. ¬b t) WHEN (λt. a t ∨ b t)) t)) ∧
         (a SBEFORE b = (λt. ¬(b WHEN (λt. a t ∨ b t)) t))


*)
end
