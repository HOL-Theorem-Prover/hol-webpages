signature inttoTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val intOrd : thm
    val intto : thm

  (*  Theorems  *)
    val BIT1_gt_neg_thm : thm
    val BIT1_nz : thm
    val BIT2_gt_neg_thm : thm
    val BIT2_nz : thm
    val ZERO_eq_neg_ZERO_thm : thm
    val apintto_thm : thm
    val gt_neg_BIT1_thm : thm
    val gt_neg_BIT2_thm : thm
    val neg_BIT1_lt_thm : thm
    val neg_BIT2_lt_thm : thm
    val neg_ZERO_eq_ZERO_thm : thm
    val neg_lt_BIT1_thm : thm
    val neg_lt_BIT2_thm : thm
    val neg_neg_thm : thm
    val pos_pos_thm : thm

  val intto_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "intto"

   [int_arith] Parent theory of "intto"

   [toto] Parent theory of "intto"

   [intOrd]  Definition

      |- intOrd = TO_of_LinearOrder $<

   [intto]  Definition

      |- intto = TO intOrd

   [BIT1_gt_neg_thm]  Theorem

      |- !m n. intOrd (&BIT1 m) (-&n) = GREATER

   [BIT1_nz]  Theorem

      |- !n. BIT1 n <> 0

   [BIT2_gt_neg_thm]  Theorem

      |- !m n. intOrd (&BIT2 m) (-&n) = GREATER

   [BIT2_nz]  Theorem

      |- !n. BIT2 n <> 0

   [ZERO_eq_neg_ZERO_thm]  Theorem

      |- intOrd (&ZERO) (-&ZERO) = EQUAL

   [apintto_thm]  Theorem

      |- apto intto = intOrd

   [gt_neg_BIT1_thm]  Theorem

      |- !m n. intOrd (&m) (-&BIT1 n) = GREATER

   [gt_neg_BIT2_thm]  Theorem

      |- !m n. intOrd (&m) (-&BIT2 n) = GREATER

   [neg_BIT1_lt_thm]  Theorem

      |- !m n. intOrd (-&BIT1 m) (&n) = LESS

   [neg_BIT2_lt_thm]  Theorem

      |- !m n. intOrd (-&BIT2 m) (&n) = LESS

   [neg_ZERO_eq_ZERO_thm]  Theorem

      |- intOrd (-&ZERO) (&ZERO) = EQUAL

   [neg_lt_BIT1_thm]  Theorem

      |- !m n. intOrd (-&m) (&BIT1 n) = LESS

   [neg_lt_BIT2_thm]  Theorem

      |- !m n. intOrd (-&m) (&BIT2 n) = LESS

   [neg_neg_thm]  Theorem

      |- !m n. intOrd (-&m) (-&n) = numOrd n m

   [pos_pos_thm]  Theorem

      |- !m n. intOrd (&m) (&n) = numOrd m n


*)
end
