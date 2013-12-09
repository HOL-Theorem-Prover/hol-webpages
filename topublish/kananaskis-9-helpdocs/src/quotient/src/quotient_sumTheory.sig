signature quotient_sumTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val SUM_REL_curried_def : thm
    val SUM_REL_tupled_primitive_def : thm

  (*  Theorems  *)
    val INL_PRS : thm
    val INL_RSP : thm
    val INR_PRS : thm
    val INR_RSP : thm
    val ISL_PRS : thm
    val ISL_RSP : thm
    val ISR_PRS : thm
    val ISR_RSP : thm
    val SUM_EQUIV : thm
    val SUM_MAP_PRS : thm
    val SUM_MAP_RSP : thm
    val SUM_QUOTIENT : thm
    val SUM_REL_EQ : thm
    val SUM_REL_def : thm
    val SUM_REL_ind : thm

  val quotient_sum_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [quotient] Parent theory of "quotient_sum"

   [SUM_REL_curried_def]  Definition

      |- ∀x x1 x2 x3. (x +++ x1) x2 x3 ⇔ SUM_REL_tupled (x,x1,x2,x3)

   [SUM_REL_tupled_primitive_def]  Definition

      |- SUM_REL_tupled =
         WFREC (@R. WF R)
           (λSUM_REL_tupled a.
              case a of
                (R1,R2,INL a1,INL a2) => I (R1 a1 a2)
              | (R1,R2,INL a1,INR b2') => I F
              | (R1,R2,INR b1,INL a2') => I F
              | (R1,R2,INR b1,INR b2) => I (R2 b1 b2))

   [INL_PRS]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀a. INL a = (abs1 ++ abs2) (INL (rep1 a))

   [INL_RSP]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀a1 a2. R1 a1 a2 ⇒ (R1 +++ R2) (INL a1) (INL a2)

   [INR_PRS]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀b. INR b = (abs1 ++ abs2) (INR (rep2 b))

   [INR_RSP]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀b1 b2. R2 b1 b2 ⇒ (R1 +++ R2) (INR b1) (INR b2)

   [ISL_PRS]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒ ∀a. ISL a ⇔ ISL ((rep1 ++ rep2) a)

   [ISL_RSP]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀a1 a2. (R1 +++ R2) a1 a2 ⇒ (ISL a1 ⇔ ISL a2)

   [ISR_PRS]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒ ∀a. ISR a ⇔ ISR ((rep1 ++ rep2) a)

   [ISR_RSP]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀a1 a2. (R1 +++ R2) a1 a2 ⇒ (ISR a1 ⇔ ISR a2)

   [SUM_EQUIV]  Theorem

      |- ∀R1 R2. EQUIV R1 ⇒ EQUIV R2 ⇒ EQUIV (R1 +++ R2)

   [SUM_MAP_PRS]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀R4 abs4 rep4.
                 QUOTIENT R4 abs4 rep4 ⇒
                 ∀f g.
                   f ++ g =
                   ((rep1 ++ rep3) --> (abs2 ++ abs4))
                     ((abs1 --> rep2) f ++ (abs3 --> rep4) g)

   [SUM_MAP_RSP]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀R4 abs4 rep4.
                 QUOTIENT R4 abs4 rep4 ⇒
                 ∀f1 f2 g1 g2.
                   (R1 ===> R2) f1 f2 ∧ (R3 ===> R4) g1 g2 ⇒
                   ((R1 +++ R3) ===> (R2 +++ R4)) (f1 ++ g1) (f2 ++ g2)

   [SUM_QUOTIENT]  Theorem

      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             QUOTIENT (R1 +++ R2) (abs1 ++ abs2) (rep1 ++ rep2)

   [SUM_REL_EQ]  Theorem

      |- $= +++ $= = $=

   [SUM_REL_def]  Theorem

      |- ((R1 +++ R2) (INL a1) (INL a2) ⇔ R1 a1 a2) ∧
         ((R1 +++ R2) (INR b1) (INR b2) ⇔ R2 b1 b2) ∧
         ((R1 +++ R2) (INL a1) (INR b2) ⇔ F) ∧
         ((R1 +++ R2) (INR b1) (INL a2) ⇔ F)

   [SUM_REL_ind]  Theorem

      |- ∀P.
           (∀R1 R2 a1 a2. P R1 R2 (INL a1) (INL a2)) ∧
           (∀R1 R2 b1 b2. P R1 R2 (INR b1) (INR b2)) ∧
           (∀R1 R2 a1 b2. P R1 R2 (INL a1) (INR b2)) ∧
           (∀R1 R2 b1 a2. P R1 R2 (INR b1) (INL a2)) ⇒
           ∀v v1 v2 v3. P v v1 v2 v3


*)
end
