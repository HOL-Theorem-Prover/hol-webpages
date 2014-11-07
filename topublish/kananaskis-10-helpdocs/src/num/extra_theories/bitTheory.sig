signature bitTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BITS_def : thm
    val BITV_def : thm
    val BITWISE_def : thm
    val BIT_MODIFY_def : thm
    val BIT_REVERSE_def : thm
    val BIT_def : thm
    val DIVMOD_2EXP_def : thm
    val DIV_2EXP_def : thm
    val LOG2_def : thm
    val LOWEST_SET_BIT_def : thm
    val MOD_2EXP_EQ_def : thm
    val MOD_2EXP_MAX_def : thm
    val MOD_2EXP_def : thm
    val SBIT_def : thm
    val SIGN_EXTEND_def : thm
    val SLICE_def : thm
    val TIMES_2EXP_def : thm

  (*  Theorems  *)
    val ADD_BIT0 : thm
    val ADD_BITS_SUC : thm
    val ADD_BIT_SUC : thm
    val BIT0_ODD : thm
    val BITSLT_THM : thm
    val BITSLT_THM2 : thm
    val BITS_COMP_THM : thm
    val BITS_COMP_THM2 : thm
    val BITS_DIV_THM : thm
    val BITS_LEQ : thm
    val BITS_LOG2_ZERO_ID : thm
    val BITS_LT_HIGH : thm
    val BITS_LT_LOW : thm
    val BITS_MUL : thm
    val BITS_SLICE_THM : thm
    val BITS_SLICE_THM2 : thm
    val BITS_SUC : thm
    val BITS_SUC_THM : thm
    val BITS_SUM : thm
    val BITS_SUM2 : thm
    val BITS_SUM3 : thm
    val BITS_THM : thm
    val BITS_THM2 : thm
    val BITS_ZERO : thm
    val BITS_ZERO2 : thm
    val BITS_ZERO3 : thm
    val BITS_ZERO4 : thm
    val BITS_ZERO5 : thm
    val BITS_ZEROL : thm
    val BITV_THM : thm
    val BITWISE_BITS : thm
    val BITWISE_COR : thm
    val BITWISE_EVAL : thm
    val BITWISE_LT_2EXP : thm
    val BITWISE_NOT_COR : thm
    val BITWISE_ONE_COMP_LEM : thm
    val BITWISE_THM : thm
    val BIT_B : thm
    val BIT_BITS_THM : thm
    val BIT_B_NEQ : thm
    val BIT_COMPLEMENT : thm
    val BIT_COMP_THM3 : thm
    val BIT_DIV2 : thm
    val BIT_EXP_SUB1 : thm
    val BIT_IMP_GE_TWOEXP : thm
    val BIT_LOG2 : thm
    val BIT_MODIFY_THM : thm
    val BIT_OF_BITS_THM : thm
    val BIT_OF_BITS_THM2 : thm
    val BIT_REVERSE_THM : thm
    val BIT_SHIFT_THM : thm
    val BIT_SHIFT_THM2 : thm
    val BIT_SHIFT_THM3 : thm
    val BIT_SHIFT_THM4 : thm
    val BIT_SHIFT_THM5 : thm
    val BIT_SIGN_EXTEND : thm
    val BIT_SLICE : thm
    val BIT_SLICE_LEM : thm
    val BIT_SLICE_THM : thm
    val BIT_SLICE_THM2 : thm
    val BIT_SLICE_THM3 : thm
    val BIT_SLICE_THM4 : thm
    val BIT_ZERO : thm
    val DIVMOD_2EXP : thm
    val DIV_GT0 : thm
    val DIV_LT : thm
    val DIV_MULT_1 : thm
    val DIV_MULT_THM : thm
    val DIV_MULT_THM2 : thm
    val DIV_SUB1 : thm
    val EXISTS_BIT_IN_RANGE : thm
    val EXISTS_BIT_LT : thm
    val EXP_SUB_LESS_EQ : thm
    val LEAST_THM : thm
    val LESS_EQ_EXP_MULT : thm
    val LESS_MULT_MONO2 : thm
    val LOG2_LE_MONO : thm
    val LOG2_TWOEXP : thm
    val LOG2_UNIQUE : thm
    val LT_TWOEXP : thm
    val MOD_2EXP_LT : thm
    val MOD_2EXP_MONO : thm
    val MOD_ADD_1 : thm
    val MOD_LEQ : thm
    val MOD_PLUS_1 : thm
    val MOD_PLUS_LEFT : thm
    val MOD_PLUS_RIGHT : thm
    val MOD_ZERO_GT : thm
    val NOT_BIT : thm
    val NOT_BITS : thm
    val NOT_BITS2 : thm
    val NOT_BIT_GT_BITWISE : thm
    val NOT_BIT_GT_LOG2 : thm
    val NOT_BIT_GT_TWOEXP : thm
    val NOT_MOD2_LEM : thm
    val NOT_MOD2_LEM2 : thm
    val NOT_ZERO_ADD1 : thm
    val ODD_MOD2_LEM : thm
    val ONE_LE_TWOEXP : thm
    val SBIT_DIV : thm
    val SBIT_MULT : thm
    val SLICELT_THM : thm
    val SLICE_COMP_RWT : thm
    val SLICE_COMP_THM : thm
    val SLICE_COMP_THM2 : thm
    val SLICE_THM : thm
    val SLICE_ZERO : thm
    val SLICE_ZERO2 : thm
    val SLICE_ZERO_THM : thm
    val SUC_SUB : thm
    val TWOEXP_DIVISION : thm
    val TWOEXP_LE_IMP_LE_LOG2 : thm
    val TWOEXP_MONO : thm
    val TWOEXP_MONO2 : thm
    val TWOEXP_NOT_ZERO : thm
    val ZERO_LT_TWOEXP : thm

  val bit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [logroot] Parent theory of "bit"

   [BITS_def]  Definition

      |- ∀h l n. BITS h l n = MOD_2EXP (SUC h − l) (DIV_2EXP l n)

   [BITV_def]  Definition

      |- ∀n b. BITV n b = BITS b b n

   [BITWISE_def]  Definition

      |- (∀op x y. BITWISE 0 op x y = 0) ∧
         ∀n op x y.
           BITWISE (SUC n) op x y =
           BITWISE n op x y + SBIT (op (BIT n x) (BIT n y)) n

   [BIT_MODIFY_def]  Definition

      |- (∀f x. BIT_MODIFY 0 f x = 0) ∧
         ∀n f x.
           BIT_MODIFY (SUC n) f x =
           BIT_MODIFY n f x + SBIT (f n (BIT n x)) n

   [BIT_REVERSE_def]  Definition

      |- (∀x. BIT_REVERSE 0 x = 0) ∧
         ∀n x.
           BIT_REVERSE (SUC n) x = BIT_REVERSE n x * 2 + SBIT (BIT n x) 0

   [BIT_def]  Definition

      |- ∀b n. BIT b n ⇔ (BITS b b n = 1)

   [DIVMOD_2EXP_def]  Definition

      |- ∀x n. DIVMOD_2EXP x n = (n DIV 2 ** x,n MOD 2 ** x)

   [DIV_2EXP_def]  Definition

      |- ∀x n. DIV_2EXP x n = n DIV 2 ** x

   [LOG2_def]  Definition

      |- LOG2 = LOG 2

   [LOWEST_SET_BIT_def]  Definition

      |- ∀n. LOWEST_SET_BIT n = LEAST i. BIT i n

   [MOD_2EXP_EQ_def]  Definition

      |- ∀n a b. MOD_2EXP_EQ n a b ⇔ (MOD_2EXP n a = MOD_2EXP n b)

   [MOD_2EXP_MAX_def]  Definition

      |- ∀n a. MOD_2EXP_MAX n a ⇔ (MOD_2EXP n a = 2 ** n − 1)

   [MOD_2EXP_def]  Definition

      |- ∀x n. MOD_2EXP x n = n MOD 2 ** x

   [SBIT_def]  Definition

      |- ∀b n. SBIT b n = if b then 2 ** n else 0

   [SIGN_EXTEND_def]  Definition

      |- ∀l h n.
           SIGN_EXTEND l h n =
           (let m = n MOD 2 ** l
            in
              if BIT (l − 1) n then 2 ** h − 2 ** l + m else m)

   [SLICE_def]  Definition

      |- ∀h l n. SLICE h l n = MOD_2EXP (SUC h) n − MOD_2EXP l n

   [TIMES_2EXP_def]  Definition

      |- ∀x n. TIMES_2EXP x n = n * 2 ** x

   [ADD_BIT0]  Theorem

      |- ∀m n. BIT 0 (m + n) ⇔ (BIT 0 m ⇎ BIT 0 n)

   [ADD_BITS_SUC]  Theorem

      |- ∀n a b.
           BITS (SUC n) (SUC n) (a + b) =
           (BITS (SUC n) (SUC n) a + BITS (SUC n) (SUC n) b +
            BITS (SUC n) (SUC n) (BITS n 0 a + BITS n 0 b)) MOD 2

   [ADD_BIT_SUC]  Theorem

      |- ∀n a b.
           BIT (SUC n) (a + b) ⇔
           if BIT (SUC n) (BITS n 0 a + BITS n 0 b) then
             BIT (SUC n) a ⇔ BIT (SUC n) b
           else BIT (SUC n) a ⇎ BIT (SUC n) b

   [BIT0_ODD]  Theorem

      |- BIT 0 = ODD

   [BITSLT_THM]  Theorem

      |- ∀h l n. BITS h l n < 2 ** (SUC h − l)

   [BITSLT_THM2]  Theorem

      |- ∀h l n. BITS h l n < 2 ** SUC h

   [BITS_COMP_THM]  Theorem

      |- ∀h1 l1 h2 l2 n.
           h2 + l1 ≤ h1 ⇒
           (BITS h2 l2 (BITS h1 l1 n) = BITS (h2 + l1) (l2 + l1) n)

   [BITS_COMP_THM2]  Theorem

      |- ∀h1 l1 h2 l2 n.
           BITS h2 l2 (BITS h1 l1 n) = BITS (MIN h1 (h2 + l1)) (l2 + l1) n

   [BITS_DIV_THM]  Theorem

      |- ∀h l x n. BITS h l x DIV 2 ** n = BITS h (l + n) x

   [BITS_LEQ]  Theorem

      |- ∀h l n. BITS h l n ≤ n

   [BITS_LOG2_ZERO_ID]  Theorem

      |- ∀n. 0 < n ⇒ (BITS (LOG2 n) 0 n = n)

   [BITS_LT_HIGH]  Theorem

      |- ∀h l n. n < 2 ** SUC h ⇒ (BITS h l n = n DIV 2 ** l)

   [BITS_LT_LOW]  Theorem

      |- ∀h l n. n < 2 ** l ⇒ (BITS h l n = 0)

   [BITS_MUL]  Theorem

      |- ∀h a b. BITS h 0 (BITS h 0 a * BITS h 0 b) = BITS h 0 (a * b)

   [BITS_SLICE_THM]  Theorem

      |- ∀h l n. BITS h l (SLICE h l n) = BITS h l n

   [BITS_SLICE_THM2]  Theorem

      |- ∀h h2 l n. h ≤ h2 ⇒ (BITS h2 l (SLICE h l n) = BITS h l n)

   [BITS_SUC]  Theorem

      |- ∀h l n.
           l ≤ SUC h ⇒
           (SBIT (BIT (SUC h) n) (SUC h − l) + BITS h l n =
            BITS (SUC h) l n)

   [BITS_SUC_THM]  Theorem

      |- ∀h l n.
           BITS (SUC h) l n =
           if SUC h < l then 0
           else SBIT (BIT (SUC h) n) (SUC h − l) + BITS h l n

   [BITS_SUM]  Theorem

      |- ∀h l a b.
           b < 2 ** l ⇒ (BITS h l (a * 2 ** l + b) = BITS h l (a * 2 ** l))

   [BITS_SUM2]  Theorem

      |- ∀h l a b. BITS h l (a * 2 ** SUC h + b) = BITS h l b

   [BITS_SUM3]  Theorem

      |- ∀h a b. BITS h 0 (BITS h 0 a + BITS h 0 b) = BITS h 0 (a + b)

   [BITS_THM]  Theorem

      |- ∀h l n. BITS h l n = (n DIV 2 ** l) MOD 2 ** (SUC h − l)

   [BITS_THM2]  Theorem

      |- ∀h l n. BITS h l n = n MOD 2 ** SUC h DIV 2 ** l

   [BITS_ZERO]  Theorem

      |- ∀h l n. h < l ⇒ (BITS h l n = 0)

   [BITS_ZERO2]  Theorem

      |- ∀h l. BITS h l 0 = 0

   [BITS_ZERO3]  Theorem

      |- ∀h n. BITS h 0 n = n MOD 2 ** SUC h

   [BITS_ZERO4]  Theorem

      |- ∀h l a. l ≤ h ⇒ (BITS h l (a * 2 ** l) = BITS (h − l) 0 a)

   [BITS_ZERO5]  Theorem

      |- ∀n m. (∀i. i ≤ n ⇒ ¬BIT i m) ⇒ (BITS n 0 m = 0)

   [BITS_ZEROL]  Theorem

      |- ∀h a. a < 2 ** SUC h ⇒ (BITS h 0 a = a)

   [BITV_THM]  Theorem

      |- ∀b n. BITV n b = SBIT (BIT b n) 0

   [BITWISE_BITS]  Theorem

      |- ∀wl op a b.
           BITWISE (SUC wl) op (BITS wl 0 a) (BITS wl 0 b) =
           BITWISE (SUC wl) op a b

   [BITWISE_COR]  Theorem

      |- ∀x n op a b.
           x < n ⇒
           op (BIT x a) (BIT x b) ⇒
           ((BITWISE n op a b DIV 2 ** x) MOD 2 = 1)

   [BITWISE_EVAL]  Theorem

      |- ∀n op a b.
           BITWISE (SUC n) op a b =
           2 * BITWISE n op (a DIV 2) (b DIV 2) +
           SBIT (op (ODD a) (ODD b)) 0

   [BITWISE_LT_2EXP]  Theorem

      |- ∀n op a b. BITWISE n op a b < 2 ** n

   [BITWISE_NOT_COR]  Theorem

      |- ∀x n op a b.
           x < n ⇒
           ¬op (BIT x a) (BIT x b) ⇒
           ((BITWISE n op a b DIV 2 ** x) MOD 2 = 0)

   [BITWISE_ONE_COMP_LEM]  Theorem

      |- ∀n a b.
           BITWISE (SUC n) (λx y. ¬x) a b = 2 ** SUC n − 1 − BITS n 0 a

   [BITWISE_THM]  Theorem

      |- ∀x n op a b.
           x < n ⇒ (BIT x (BITWISE n op a b) ⇔ op (BIT x a) (BIT x b))

   [BIT_B]  Theorem

      |- ∀b. BIT b (2 ** b)

   [BIT_BITS_THM]  Theorem

      |- ∀h l a b.
           (∀x. l ≤ x ∧ x ≤ h ⇒ (BIT x a ⇔ BIT x b)) ⇔
           (BITS h l a = BITS h l b)

   [BIT_B_NEQ]  Theorem

      |- ∀a b. a ≠ b ⇒ ¬BIT a (2 ** b)

   [BIT_COMPLEMENT]  Theorem

      |- ∀n i a.
           BIT i (2 ** n − a MOD 2 ** n) ⇔
           (a MOD 2 ** n = 0) ∧ (i = n) ∨
           a MOD 2 ** n ≠ 0 ∧ i < n ∧ ¬BIT i (a MOD 2 ** n − 1)

   [BIT_COMP_THM3]  Theorem

      |- ∀h m l n.
           SUC m ≤ h ∧ l ≤ m ⇒
           (BITS h (SUC m) n * 2 ** (SUC m − l) + BITS m l n = BITS h l n)

   [BIT_DIV2]  Theorem

      |- ∀n i. BIT n (i DIV 2) ⇔ BIT (SUC n) i

   [BIT_EXP_SUB1]  Theorem

      |- ∀b n. BIT b (2 ** n − 1) ⇔ b < n

   [BIT_IMP_GE_TWOEXP]  Theorem

      |- ∀i n. BIT i n ⇒ 2 ** i ≤ n

   [BIT_LOG2]  Theorem

      |- ∀n. n ≠ 0 ⇒ BIT (LOG2 n) n

   [BIT_MODIFY_THM]  Theorem

      |- ∀x n f a. x < n ⇒ (BIT x (BIT_MODIFY n f a) ⇔ f x (BIT x a))

   [BIT_OF_BITS_THM]  Theorem

      |- ∀n h l a. l + n ≤ h ⇒ (BIT n (BITS h l a) ⇔ BIT (l + n) a)

   [BIT_OF_BITS_THM2]  Theorem

      |- ∀h l x n. h < l + x ⇒ ¬BIT x (BITS h l n)

   [BIT_REVERSE_THM]  Theorem

      |- ∀x n a. x < n ⇒ (BIT x (BIT_REVERSE n a) ⇔ BIT (n − 1 − x) a)

   [BIT_SHIFT_THM]  Theorem

      |- ∀n a s. BIT (n + s) (a * 2 ** s) ⇔ BIT n a

   [BIT_SHIFT_THM2]  Theorem

      |- ∀n a s. s ≤ n ⇒ (BIT n (a * 2 ** s) ⇔ BIT (n − s) a)

   [BIT_SHIFT_THM3]  Theorem

      |- ∀n a s. n < s ⇒ ¬BIT n (a * 2 ** s)

   [BIT_SHIFT_THM4]  Theorem

      |- ∀n i a. BIT i (a DIV 2 ** n) ⇔ BIT (i + n) a

   [BIT_SHIFT_THM5]  Theorem

      |- ∀n m i a.
           i + n < m ∧ a < 2 ** m ⇒
           (BIT i
              (2 ** m −
               (a DIV 2 ** n + if a MOD 2 ** n = 0 then 0 else 1) MOD
               2 ** m) ⇔ BIT (i + n) (2 ** m − a MOD 2 ** m))

   [BIT_SIGN_EXTEND]  Theorem

      |- ∀l h n i.
           l ≠ 0 ⇒
           (BIT i (SIGN_EXTEND l h n) ⇔
            if l ≤ h ⇒ i < l then BIT i (n MOD 2 ** l)
            else i < h ∧ BIT (l − 1) n)

   [BIT_SLICE]  Theorem

      |- ∀n a b. (BIT n a ⇔ BIT n b) ⇔ (SLICE n n a = SLICE n n b)

   [BIT_SLICE_LEM]  Theorem

      |- ∀y x n. SBIT (BIT x n) (x + y) = SLICE x x n * 2 ** y

   [BIT_SLICE_THM]  Theorem

      |- ∀x n. SBIT (BIT x n) x = SLICE x x n

   [BIT_SLICE_THM2]  Theorem

      |- ∀b n. BIT b n ⇔ (SLICE b b n = 2 ** b)

   [BIT_SLICE_THM3]  Theorem

      |- ∀b n. ¬BIT b n ⇔ (SLICE b b n = 0)

   [BIT_SLICE_THM4]  Theorem

      |- ∀b h l n. BIT b (SLICE h l n) ⇔ l ≤ b ∧ b ≤ h ∧ BIT b n

   [BIT_ZERO]  Theorem

      |- ∀b. ¬BIT b 0

   [DIVMOD_2EXP]  Theorem

      |- ∀x n. DIVMOD_2EXP x n = (DIV_2EXP x n,MOD_2EXP x n)

   [DIV_GT0]  Theorem

      |- ∀a b. b ≤ a ∧ 0 < b ⇒ 0 < a DIV b

   [DIV_LT]  Theorem

      |- ∀n m a. n < m ∧ a < 2 ** m ⇒ a DIV 2 ** n < 2 ** m

   [DIV_MULT_1]  Theorem

      |- ∀r n. r < n ⇒ ((n + r) DIV n = 1)

   [DIV_MULT_THM]  Theorem

      |- ∀x n. n DIV 2 ** x * 2 ** x = n − n MOD 2 ** x

   [DIV_MULT_THM2]  Theorem

      |- ∀n. 2 * (n DIV 2) = n − n MOD 2

   [DIV_SUB1]  Theorem

      |- ∀a b.
           2 ** b ≤ a ∧ (a MOD 2 ** b = 0) ⇒
           (a DIV 2 ** b − 1 = (a − 1) DIV 2 ** b)

   [EXISTS_BIT_IN_RANGE]  Theorem

      |- ∀a b n.
           n ≠ 0 ∧ 2 ** a ≤ n ∧ n < 2 ** b ⇒ ∃i. a ≤ i ∧ i < b ∧ BIT i n

   [EXISTS_BIT_LT]  Theorem

      |- ∀b n. n ≠ 0 ∧ n < 2 ** b ⇒ ∃i. i < b ∧ BIT i n

   [EXP_SUB_LESS_EQ]  Theorem

      |- ∀a b. 2 ** (a − b) ≤ 2 ** a

   [LEAST_THM]  Theorem

      |- ∀n P. (∀m. m < n ⇒ ¬P m) ∧ P n ⇒ ($LEAST P = n)

   [LESS_EQ_EXP_MULT]  Theorem

      |- ∀a b. a ≤ b ⇒ ∃p. 2 ** b = p * 2 ** a

   [LESS_MULT_MONO2]  Theorem

      |- ∀a b x y. a < x ∧ b < y ⇒ a * b < x * y

   [LOG2_LE_MONO]  Theorem

      |- ∀x y. 0 < x ⇒ x ≤ y ⇒ LOG2 x ≤ LOG2 y

   [LOG2_TWOEXP]  Theorem

      |- ∀n. LOG2 (2 ** n) = n

   [LOG2_UNIQUE]  Theorem

      |- ∀n p. 2 ** p ≤ n ∧ n < 2 ** SUC p ⇒ (LOG2 n = p)

   [LT_TWOEXP]  Theorem

      |- ∀x n. x < 2 ** n ⇔ (x = 0) ∨ LOG2 x < n

   [MOD_2EXP_LT]  Theorem

      |- ∀n k. k MOD 2 ** n < 2 ** n

   [MOD_2EXP_MONO]  Theorem

      |- ∀n h l. l ≤ h ⇒ n MOD 2 ** l ≤ n MOD 2 ** SUC h

   [MOD_ADD_1]  Theorem

      |- ∀n. 0 < n ⇒ ∀x. (x + 1) MOD n ≠ 0 ⇒ ((x + 1) MOD n = x MOD n + 1)

   [MOD_LEQ]  Theorem

      |- ∀a b. 0 < b ⇒ a MOD b ≤ a

   [MOD_PLUS_1]  Theorem

      |- ∀n. 0 < n ⇒ ∀x. ((x + 1) MOD n = 0) ⇔ (x MOD n + 1 = n)

   [MOD_PLUS_LEFT]  Theorem

      |- ∀n. 0 < n ⇒ ∀j k. (k MOD n + j) MOD n = (k + j) MOD n

   [MOD_PLUS_RIGHT]  Theorem

      |- ∀n. 0 < n ⇒ ∀j k. (j + k MOD n) MOD n = (j + k) MOD n

   [MOD_ZERO_GT]  Theorem

      |- ∀n a. a ≠ 0 ∧ (a MOD 2 ** n = 0) ⇒ 2 ** n ≤ a

   [NOT_BIT]  Theorem

      |- ∀n a. ¬BIT n a ⇔ (BITS n n a = 0)

   [NOT_BITS]  Theorem

      |- ∀n a. BITS n n a ≠ 0 ⇔ (BITS n n a = 1)

   [NOT_BITS2]  Theorem

      |- ∀n a. BITS n n a ≠ 1 ⇔ (BITS n n a = 0)

   [NOT_BIT_GT_BITWISE]  Theorem

      |- ∀i n op a b. n ≤ i ⇒ ¬BIT i (BITWISE n op a b)

   [NOT_BIT_GT_LOG2]  Theorem

      |- ∀i n. LOG2 n < i ⇒ ¬BIT i n

   [NOT_BIT_GT_TWOEXP]  Theorem

      |- ∀i n. n < 2 ** i ⇒ ¬BIT i n

   [NOT_MOD2_LEM]  Theorem

      |- ∀n. n MOD 2 ≠ 0 ⇔ (n MOD 2 = 1)

   [NOT_MOD2_LEM2]  Theorem

      |- ∀n. n MOD 2 ≠ 1 ⇔ (n MOD 2 = 0)

   [NOT_ZERO_ADD1]  Theorem

      |- ∀m. m ≠ 0 ⇒ ∃p. m = SUC p

   [ODD_MOD2_LEM]  Theorem

      |- ∀n. ODD n ⇔ (n MOD 2 = 1)

   [ONE_LE_TWOEXP]  Theorem

      |- ∀n. 1 ≤ 2 ** n

   [SBIT_DIV]  Theorem

      |- ∀b m n. n < m ⇒ (SBIT b (m − n) = SBIT b m DIV 2 ** n)

   [SBIT_MULT]  Theorem

      |- ∀b m n. SBIT b n * 2 ** m = SBIT b (n + m)

   [SLICELT_THM]  Theorem

      |- ∀h l n. SLICE h l n < 2 ** SUC h

   [SLICE_COMP_RWT]  Theorem

      |- ∀h m' m l n.
           l ≤ m ∧ (m' = m + 1) ∧ m < h ⇒
           (SLICE h m' n + SLICE m l n = SLICE h l n)

   [SLICE_COMP_THM]  Theorem

      |- ∀h m l n.
           SUC m ≤ h ∧ l ≤ m ⇒
           (SLICE h (SUC m) n + SLICE m l n = SLICE h l n)

   [SLICE_COMP_THM2]  Theorem

      |- ∀h l x y n.
           h ≤ x ∧ y ≤ l ⇒ (SLICE h l (SLICE x y n) = SLICE h l n)

   [SLICE_THM]  Theorem

      |- ∀n h l. SLICE h l n = BITS h l n * 2 ** l

   [SLICE_ZERO]  Theorem

      |- ∀h l n. h < l ⇒ (SLICE h l n = 0)

   [SLICE_ZERO2]  Theorem

      |- ∀l h. SLICE h l 0 = 0

   [SLICE_ZERO_THM]  Theorem

      |- ∀n h. SLICE h 0 n = BITS h 0 n

   [SUC_SUB]  Theorem

      |- ∀a. SUC a − a = 1

   [TWOEXP_DIVISION]  Theorem

      |- ∀n k. k = k DIV 2 ** n * 2 ** n + k MOD 2 ** n

   [TWOEXP_LE_IMP_LE_LOG2]  Theorem

      |- (∀x y. 2 ** x ≤ y ⇒ x ≤ LOG2 y) ∧
         ∀y x. 0 < x ⇒ x ≤ 2 ** y ⇒ LOG2 x ≤ y

   [TWOEXP_MONO]  Theorem

      |- ∀a b. a < b ⇒ 2 ** a < 2 ** b

   [TWOEXP_MONO2]  Theorem

      |- ∀a b. a ≤ b ⇒ 2 ** a ≤ 2 ** b

   [TWOEXP_NOT_ZERO]  Theorem

      |- ∀n. 2 ** n ≠ 0

   [ZERO_LT_TWOEXP]  Theorem

      |- ∀n. 0 < 2 ** n


*)
end
