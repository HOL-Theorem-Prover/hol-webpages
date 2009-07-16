signature integerTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val INT_ABS : thm
    val INT_DIVIDES : thm
    val INT_MAX : thm
    val INT_MIN : thm
    val Num : thm
    val int_0 : thm
    val int_1 : thm
    val int_ABS_def : thm
    val int_REP_def : thm
    val int_TY_DEF : thm
    val int_add : thm
    val int_bijections : thm
    val int_div : thm
    val int_exp : thm
    val int_ge : thm
    val int_gt : thm
    val int_le : thm
    val int_lt : thm
    val int_mod : thm
    val int_mul : thm
    val int_neg : thm
    val int_quot : thm
    val int_rem : thm
    val int_sub : thm
    val tint_0 : thm
    val tint_1 : thm
    val tint_add : thm
    val tint_eq : thm
    val tint_lt : thm
    val tint_mul : thm
    val tint_neg : thm
    val tint_of_num : thm
  
  (*  Theorems  *)
    val EQ_ADDL : thm
    val EQ_LADD : thm
    val INT : thm
    val INT_0 : thm
    val INT_1 : thm
    val INT_10 : thm
    val INT_ABS_ABS : thm
    val INT_ABS_EQ : thm
    val INT_ABS_EQ0 : thm
    val INT_ABS_EQ_ID : thm
    val INT_ABS_LE : thm
    val INT_ABS_LE0 : thm
    val INT_ABS_LT : thm
    val INT_ABS_LT0 : thm
    val INT_ABS_MUL : thm
    val INT_ABS_NEG : thm
    val INT_ABS_NUM : thm
    val INT_ABS_POS : thm
    val INT_ABS_QUOT : thm
    val INT_ADD : thm
    val INT_ADD2_SUB2 : thm
    val INT_ADD_ASSOC : thm
    val INT_ADD_CALCULATE : thm
    val INT_ADD_COMM : thm
    val INT_ADD_DIV : thm
    val INT_ADD_LID : thm
    val INT_ADD_LID_UNIQ : thm
    val INT_ADD_LINV : thm
    val INT_ADD_REDUCE : thm
    val INT_ADD_RID : thm
    val INT_ADD_RID_UNIQ : thm
    val INT_ADD_RINV : thm
    val INT_ADD_SUB : thm
    val INT_ADD_SUB2 : thm
    val INT_ADD_SYM : thm
    val INT_DIFFSQ : thm
    val INT_DISCRETE : thm
    val INT_DIV : thm
    val INT_DIVIDES_0 : thm
    val INT_DIVIDES_1 : thm
    val INT_DIVIDES_LADD : thm
    val INT_DIVIDES_LMUL : thm
    val INT_DIVIDES_LSUB : thm
    val INT_DIVIDES_MOD0 : thm
    val INT_DIVIDES_MUL : thm
    val INT_DIVIDES_MUL_BOTH : thm
    val INT_DIVIDES_NEG : thm
    val INT_DIVIDES_RADD : thm
    val INT_DIVIDES_REDUCE : thm
    val INT_DIVIDES_REFL : thm
    val INT_DIVIDES_RMUL : thm
    val INT_DIVIDES_RSUB : thm
    val INT_DIVIDES_TRANS : thm
    val INT_DIVISION : thm
    val INT_DIV_0 : thm
    val INT_DIV_1 : thm
    val INT_DIV_CALCULATE : thm
    val INT_DIV_FORALL_P : thm
    val INT_DIV_ID : thm
    val INT_DIV_LMUL : thm
    val INT_DIV_MUL_ID : thm
    val INT_DIV_NEG : thm
    val INT_DIV_P : thm
    val INT_DIV_REDUCE : thm
    val INT_DIV_RMUL : thm
    val INT_DIV_UNIQUE : thm
    val INT_DOUBLE : thm
    val INT_ENTIRE : thm
    val INT_EQ_CALCULATE : thm
    val INT_EQ_IMP_LE : thm
    val INT_EQ_LADD : thm
    val INT_EQ_LMUL : thm
    val INT_EQ_LMUL2 : thm
    val INT_EQ_LMUL_IMP : thm
    val INT_EQ_NEG : thm
    val INT_EQ_RADD : thm
    val INT_EQ_REDUCE : thm
    val INT_EQ_RMUL : thm
    val INT_EQ_RMUL_IMP : thm
    val INT_EQ_SUB_LADD : thm
    val INT_EQ_SUB_RADD : thm
    val INT_EXP : thm
    val INT_EXP_ADD_EXPONENTS : thm
    val INT_EXP_CALCULATE : thm
    val INT_EXP_EQ0 : thm
    val INT_EXP_MOD : thm
    val INT_EXP_MULTIPLY_EXPONENTS : thm
    val INT_EXP_NEG : thm
    val INT_EXP_REDUCE : thm
    val INT_EXP_SUBTRACT_EXPONENTS : thm
    val INT_GE_CALCULATE : thm
    val INT_GE_REDUCE : thm
    val INT_GT_CALCULATE : thm
    val INT_GT_REDUCE : thm
    val INT_INJ : thm
    val INT_LDISTRIB : thm
    val INT_LE : thm
    val INT_LESS_MOD : thm
    val INT_LET_ADD : thm
    val INT_LET_ADD2 : thm
    val INT_LET_ANTISYM : thm
    val INT_LET_TOTAL : thm
    val INT_LET_TRANS : thm
    val INT_LE_01 : thm
    val INT_LE_ADD : thm
    val INT_LE_ADD2 : thm
    val INT_LE_ADDL : thm
    val INT_LE_ADDR : thm
    val INT_LE_ANTISYM : thm
    val INT_LE_CALCULATE : thm
    val INT_LE_DOUBLE : thm
    val INT_LE_LADD : thm
    val INT_LE_LT : thm
    val INT_LE_LT1 : thm
    val INT_LE_MONO : thm
    val INT_LE_MUL : thm
    val INT_LE_NEG : thm
    val INT_LE_NEGL : thm
    val INT_LE_NEGR : thm
    val INT_LE_NEGTOTAL : thm
    val INT_LE_RADD : thm
    val INT_LE_REDUCE : thm
    val INT_LE_REFL : thm
    val INT_LE_SQUARE : thm
    val INT_LE_SUB_LADD : thm
    val INT_LE_SUB_RADD : thm
    val INT_LE_TOTAL : thm
    val INT_LE_TRANS : thm
    val INT_LNEG_UNIQ : thm
    val INT_LT : thm
    val INT_LTE_ADD : thm
    val INT_LTE_ADD2 : thm
    val INT_LTE_ANTSYM : thm
    val INT_LTE_TOTAL : thm
    val INT_LTE_TRANS : thm
    val INT_LT_01 : thm
    val INT_LT_ADD : thm
    val INT_LT_ADD1 : thm
    val INT_LT_ADD2 : thm
    val INT_LT_ADDL : thm
    val INT_LT_ADDNEG : thm
    val INT_LT_ADDNEG2 : thm
    val INT_LT_ADDR : thm
    val INT_LT_ADD_SUB : thm
    val INT_LT_ANTISYM : thm
    val INT_LT_CALCULATE : thm
    val INT_LT_GT : thm
    val INT_LT_IMP_LE : thm
    val INT_LT_IMP_NE : thm
    val INT_LT_LADD : thm
    val INT_LT_LADD_IMP : thm
    val INT_LT_LE : thm
    val INT_LT_LE1 : thm
    val INT_LT_MONO : thm
    val INT_LT_MUL : thm
    val INT_LT_MUL2 : thm
    val INT_LT_NEG : thm
    val INT_LT_NEGTOTAL : thm
    val INT_LT_NZ : thm
    val INT_LT_RADD : thm
    val INT_LT_REDUCE : thm
    val INT_LT_REFL : thm
    val INT_LT_SUB_LADD : thm
    val INT_LT_SUB_RADD : thm
    val INT_LT_TOTAL : thm
    val INT_LT_TRANS : thm
    val INT_MAX_LT : thm
    val INT_MAX_NUM : thm
    val INT_MIN_LT : thm
    val INT_MIN_NUM : thm
    val INT_MOD : thm
    val INT_MOD0 : thm
    val INT_MOD_1 : thm
    val INT_MOD_ADD_MULTIPLES : thm
    val INT_MOD_BOUNDS : thm
    val INT_MOD_CALCULATE : thm
    val INT_MOD_COMMON_FACTOR : thm
    val INT_MOD_EQ0 : thm
    val INT_MOD_FORALL_P : thm
    val INT_MOD_ID : thm
    val INT_MOD_MINUS1 : thm
    val INT_MOD_MOD : thm
    val INT_MOD_NEG : thm
    val INT_MOD_NEG_NUMERATOR : thm
    val INT_MOD_P : thm
    val INT_MOD_PLUS : thm
    val INT_MOD_REDUCE : thm
    val INT_MOD_SUB : thm
    val INT_MOD_UNIQUE : thm
    val INT_MUL : thm
    val INT_MUL_ASSOC : thm
    val INT_MUL_CALCULATE : thm
    val INT_MUL_COMM : thm
    val INT_MUL_DIV : thm
    val INT_MUL_EQ_1 : thm
    val INT_MUL_LID : thm
    val INT_MUL_LZERO : thm
    val INT_MUL_QUOT : thm
    val INT_MUL_REDUCE : thm
    val INT_MUL_RID : thm
    val INT_MUL_RZERO : thm
    val INT_MUL_SIGN_CASES : thm
    val INT_MUL_SYM : thm
    val INT_NEGNEG : thm
    val INT_NEG_0 : thm
    val INT_NEG_ADD : thm
    val INT_NEG_EQ : thm
    val INT_NEG_EQ0 : thm
    val INT_NEG_GE0 : thm
    val INT_NEG_GT0 : thm
    val INT_NEG_LE0 : thm
    val INT_NEG_LMUL : thm
    val INT_NEG_LT0 : thm
    val INT_NEG_MINUS1 : thm
    val INT_NEG_MUL2 : thm
    val INT_NEG_RMUL : thm
    val INT_NEG_SAME_EQ : thm
    val INT_NEG_SUB : thm
    val INT_NOT_LE : thm
    val INT_NOT_LT : thm
    val INT_NUM_CASES : thm
    val INT_NZ_IMP_LT : thm
    val INT_OF_NUM : thm
    val INT_POASQ : thm
    val INT_POS : thm
    val INT_POS_NZ : thm
    val INT_QUOT : thm
    val INT_QUOT_0 : thm
    val INT_QUOT_1 : thm
    val INT_QUOT_CALCULATE : thm
    val INT_QUOT_ID : thm
    val INT_QUOT_NEG : thm
    val INT_QUOT_REDUCE : thm
    val INT_QUOT_UNIQUE : thm
    val INT_RDISTRIB : thm
    val INT_REM : thm
    val INT_REM0 : thm
    val INT_REMQUOT : thm
    val INT_REM_CALCULATE : thm
    val INT_REM_COMMON_FACTOR : thm
    val INT_REM_EQ0 : thm
    val INT_REM_EQ_MOD : thm
    val INT_REM_ID : thm
    val INT_REM_NEG : thm
    val INT_REM_REDUCE : thm
    val INT_REM_UNIQUE : thm
    val INT_RNEG_UNIQ : thm
    val INT_SUB : thm
    val INT_SUB_0 : thm
    val INT_SUB_ADD : thm
    val INT_SUB_ADD2 : thm
    val INT_SUB_CALCULATE : thm
    val INT_SUB_LDISTRIB : thm
    val INT_SUB_LE : thm
    val INT_SUB_LNEG : thm
    val INT_SUB_LT : thm
    val INT_SUB_LZERO : thm
    val INT_SUB_NEG2 : thm
    val INT_SUB_RDISTRIB : thm
    val INT_SUB_REDUCE : thm
    val INT_SUB_REFL : thm
    val INT_SUB_RNEG : thm
    val INT_SUB_RZERO : thm
    val INT_SUB_SUB : thm
    val INT_SUB_SUB2 : thm
    val INT_SUB_TRIANGLE : thm
    val INT_SUMSQ : thm
    val LE_NUM_OF_INT : thm
    val LT_ADD2 : thm
    val LT_ADDL : thm
    val LT_ADDR : thm
    val LT_LADD : thm
    val NUM_NEGINT_EXISTS : thm
    val NUM_OF_INT : thm
    val NUM_POSINT : thm
    val NUM_POSINT_EX : thm
    val NUM_POSINT_EXISTS : thm
    val NUM_POSTINT_EX : thm
    val TINT_10 : thm
    val TINT_ADD_ASSOC : thm
    val TINT_ADD_LID : thm
    val TINT_ADD_LINV : thm
    val TINT_ADD_SYM : thm
    val TINT_ADD_WELLDEF : thm
    val TINT_ADD_WELLDEFR : thm
    val TINT_EQ_AP : thm
    val TINT_EQ_EQUIV : thm
    val TINT_EQ_REFL : thm
    val TINT_EQ_SYM : thm
    val TINT_EQ_TRANS : thm
    val TINT_INJ : thm
    val TINT_LDISTRIB : thm
    val TINT_LT_ADD : thm
    val TINT_LT_MUL : thm
    val TINT_LT_REFL : thm
    val TINT_LT_TOTAL : thm
    val TINT_LT_TRANS : thm
    val TINT_LT_WELLDEF : thm
    val TINT_LT_WELLDEFL : thm
    val TINT_LT_WELLDEFR : thm
    val TINT_MUL_ASSOC : thm
    val TINT_MUL_LID : thm
    val TINT_MUL_SYM : thm
    val TINT_MUL_WELLDEF : thm
    val TINT_MUL_WELLDEFR : thm
    val TINT_NEG_WELLDEF : thm
    val int_ABS_REP_CLASS : thm
    val int_QUOTIENT : thm
    val int_of_num : thm
    val tint_of_num_eq : thm
  
  val integer_grammars : type_grammar.grammar * term_grammar.grammar
  
  val integer_rwts : simpLib.ssfrag
(*
   [divides] Parent theory of "integer"
   
   [quotient_list] Parent theory of "integer"
   
   [quotient_option] Parent theory of "integer"
   
   [quotient_pair] Parent theory of "integer"
   
   [quotient_sum] Parent theory of "integer"
   
   [INT_ABS]  Definition
      
      |- !n. ABS n = if n < 0 then -n else n
   
   [INT_DIVIDES]  Definition
      
      |- !p q. p int_divides q <=> ?m. m * p = q
   
   [INT_MAX]  Definition
      
      |- !x y. int_max x y = if x < y then y else x
   
   [INT_MIN]  Definition
      
      |- !x y. int_min x y = if x < y then x else y
   
   [Num]  Definition
      
      |- !i. Num i = @n. i = &n
   
   [int_0]  Definition
      
      |- int_0 = int_ABS tint_0
   
   [int_1]  Definition
      
      |- int_1 = int_ABS tint_1
   
   [int_ABS_def]  Definition
      
      |- !r. int_ABS r = int_ABS_CLASS ($tint_eq r)
   
   [int_REP_def]  Definition
      
      |- !a. int_REP a = $@ (int_REP_CLASS a)
   
   [int_TY_DEF]  Definition
      
      |- ?rep.
           TYPE_DEFINITION (\c. ?r. r tint_eq r /\ (c = $tint_eq r)) rep
   
   [int_add]  Definition
      
      |- !T1 T2. T1 + T2 = int_ABS (int_REP T1 tint_add int_REP T2)
   
   [int_bijections]  Definition
      
      |- (!a. int_ABS_CLASS (int_REP_CLASS a) = a) /\
         !r.
           (\c. ?r. r tint_eq r /\ (c = $tint_eq r)) r <=>
           (int_REP_CLASS (int_ABS_CLASS r) = r)
   
   [int_div]  Definition
      
      |- !i j.
           j <> 0 ==>
           (i / j =
            if 0 < j then
              if 0 <= i then
                &(Num i DIV Num j)
              else
                -&(Num (-i) DIV Num j) +
                if Num (-i) MOD Num j = 0 then 0 else -1
            else
              if 0 <= i then
                -&(Num i DIV Num (-j)) +
                if Num i MOD Num (-j) = 0 then 0 else -1
              else
                &(Num (-i) DIV Num (-j)))
   
   [int_exp]  Definition
      
      |- (!p. p ** 0 = 1) /\ !p n. p ** SUC n = p * p ** n
   
   [int_ge]  Definition
      
      |- !x y. x >= y <=> y <= x
   
   [int_gt]  Definition
      
      |- !x y. x > y <=> y < x
   
   [int_le]  Definition
      
      |- !x y. x <= y <=> ~(y < x)
   
   [int_lt]  Definition
      
      |- !T1 T2. T1 < T2 <=> int_REP T1 tint_lt int_REP T2
   
   [int_mod]  Definition
      
      |- !i j. j <> 0 ==> (i % j = i - i / j * j)
   
   [int_mul]  Definition
      
      |- !T1 T2. T1 * T2 = int_ABS (int_REP T1 tint_mul int_REP T2)
   
   [int_neg]  Definition
      
      |- !T1. -T1 = int_ABS (tint_neg (int_REP T1))
   
   [int_quot]  Definition
      
      |- !i j.
           j <> 0 ==>
           (i quot j =
            if 0 < j then
              if 0 <= i then &(Num i DIV Num j) else -&(Num (-i) DIV Num j)
            else
              if 0 <= i then
                -&(Num i DIV Num (-j))
              else
                &(Num (-i) DIV Num (-j)))
   
   [int_rem]  Definition
      
      |- !i j. j <> 0 ==> (i rem j = i - i quot j * j)
   
   [int_sub]  Definition
      
      |- !x y. x - y = x + -y
   
   [tint_0]  Definition
      
      |- tint_0 = (1,1)
   
   [tint_1]  Definition
      
      |- tint_1 = (1 + 1,1)
   
   [tint_add]  Definition
      
      |- !x1 y1 x2 y2. (x1,y1) tint_add (x2,y2) = (x1 + x2,y1 + y2)
   
   [tint_eq]  Definition
      
      |- !x1 y1 x2 y2. (x1,y1) tint_eq (x2,y2) <=> (x1 + y2 = x2 + y1)
   
   [tint_lt]  Definition
      
      |- !x1 y1 x2 y2. (x1,y1) tint_lt (x2,y2) <=> x1 + y2 < x2 + y1
   
   [tint_mul]  Definition
      
      |- !x1 y1 x2 y2.
           (x1,y1) tint_mul (x2,y2) = (x1 * x2 + y1 * y2,x1 * y2 + y1 * x2)
   
   [tint_neg]  Definition
      
      |- !x y. tint_neg (x,y) = (y,x)
   
   [tint_of_num]  Definition
      
      |- (tint_of_num 0 = tint_0) /\
         !n. tint_of_num (SUC n) = tint_of_num n tint_add tint_1
   
   [EQ_ADDL]  Theorem
      
      |- !x y. (x = x + y) <=> (y = 0)
   
   [EQ_LADD]  Theorem
      
      |- !x y z. (x + y = x + z) <=> (y = z)
   
   [INT]  Theorem
      
      |- !n. &SUC n = &n + 1
   
   [INT_0]  Theorem
      
      |- int_0 = 0
   
   [INT_1]  Theorem
      
      |- int_1 = 1
   
   [INT_10]  Theorem
      
      |- int_1 <> int_0
   
   [INT_ABS_ABS]  Theorem
      
      |- !p. ABS (ABS p) = ABS p
   
   [INT_ABS_EQ]  Theorem
      
      |- !p q.
           ((ABS p = q) <=> (p = q) /\ 0 < q \/ (p = -q) /\ 0 <= q) /\
           ((q = ABS p) <=> (p = q) /\ 0 < q \/ (p = -q) /\ 0 <= q)
   
   [INT_ABS_EQ0]  Theorem
      
      |- !p. (ABS p = 0) <=> (p = 0)
   
   [INT_ABS_EQ_ID]  Theorem
      
      |- !p. (ABS p = p) <=> 0 <= p
   
   [INT_ABS_LE]  Theorem
      
      |- !p q.
           (ABS p <= q <=> p <= q /\ -q <= p) /\
           (q <= ABS p <=> q <= p \/ p <= -q) /\
           (-ABS p <= q <=> -q <= p \/ p <= q) /\
           (q <= -ABS p <=> p <= -q /\ q <= p)
   
   [INT_ABS_LE0]  Theorem
      
      |- !p. ABS p <= 0 <=> (p = 0)
   
   [INT_ABS_LT]  Theorem
      
      |- !p q.
           (ABS p < q <=> p < q /\ -q < p) /\
           (q < ABS p <=> q < p \/ p < -q) /\
           (-ABS p < q <=> -q < p \/ p < q) /\
           (q < -ABS p <=> p < -q /\ q < p)
   
   [INT_ABS_LT0]  Theorem
      
      |- !p. ~(ABS p < 0)
   
   [INT_ABS_MUL]  Theorem
      
      |- !p q. ABS p * ABS q = ABS (p * q)
   
   [INT_ABS_NEG]  Theorem
      
      |- !p. ABS (-p) = ABS p
   
   [INT_ABS_NUM]  Theorem
      
      |- !n. ABS (&n) = &n
   
   [INT_ABS_POS]  Theorem
      
      |- !p. 0 <= ABS p
   
   [INT_ABS_QUOT]  Theorem
      
      |- !p q. q <> 0 ==> ABS (p quot q * q) <= ABS p
   
   [INT_ADD]  Theorem
      
      |- !m n. &m + &n = &(m + n)
   
   [INT_ADD2_SUB2]  Theorem
      
      |- !a b c d. a + b - (c + d) = a - c + (b - d)
   
   [INT_ADD_ASSOC]  Theorem
      
      |- !z y x. x + (y + z) = x + y + z
   
   [INT_ADD_CALCULATE]  Theorem
      
      |- !p n m.
           (0 + p = p) /\ (p + 0 = p) /\ (&n + &m = &(n + m)) /\
           (&n + -&m = if m <= n then &(n - m) else -&(m - n)) /\
           (-&n + &m = if n <= m then &(m - n) else -&(n - m)) /\
           (-&n + -&m = -&(n + m))
   
   [INT_ADD_COMM]  Theorem
      
      |- !y x. x + y = y + x
   
   [INT_ADD_DIV]  Theorem
      
      |- !i j k.
           k <> 0 /\ ((i % k = 0) \/ (j % k = 0)) ==>
           ((i + j) / k = i / k + j / k)
   
   [INT_ADD_LID]  Theorem
      
      |- !x. 0 + x = x
   
   [INT_ADD_LID_UNIQ]  Theorem
      
      |- !x y. (x + y = y) <=> (x = 0)
   
   [INT_ADD_LINV]  Theorem
      
      |- !x. -x + x = 0
   
   [INT_ADD_REDUCE]  Theorem
      
      |- !p n m.
           (0 + p = p) /\ (p + 0 = p) /\ (-0 = 0) /\ (--p = p) /\
           (&NUMERAL n + &NUMERAL m = &NUMERAL (numeral$iZ (n + m))) /\
           (&NUMERAL n + -&NUMERAL m =
            if m <= n then &NUMERAL (n - m) else -&NUMERAL (m - n)) /\
           (-&NUMERAL n + &NUMERAL m =
            if n <= m then &NUMERAL (m - n) else -&NUMERAL (n - m)) /\
           (-&NUMERAL n + -&NUMERAL m = -&NUMERAL (numeral$iZ (n + m)))
   
   [INT_ADD_RID]  Theorem
      
      |- !x. x + 0 = x
   
   [INT_ADD_RID_UNIQ]  Theorem
      
      |- !x y. (x + y = x) <=> (y = 0)
   
   [INT_ADD_RINV]  Theorem
      
      |- !x. x + -x = 0
   
   [INT_ADD_SUB]  Theorem
      
      |- !x y. x + y - x = y
   
   [INT_ADD_SUB2]  Theorem
      
      |- !x y. x - (x + y) = -y
   
   [INT_ADD_SYM]  Theorem
      
      |- !y x. x + y = y + x
   
   [INT_DIFFSQ]  Theorem
      
      |- !x y. (x + y) * (x - y) = x * x - y * y
   
   [INT_DISCRETE]  Theorem
      
      |- !x y. ~(x < y /\ y < x + 1)
   
   [INT_DIV]  Theorem
      
      |- !n m. m <> 0 ==> (&n / &m = &(n DIV m))
   
   [INT_DIVIDES_0]  Theorem
      
      |- (!x. x int_divides 0) /\ !x. 0 int_divides x <=> (x = 0)
   
   [INT_DIVIDES_1]  Theorem
      
      |- !x. 1 int_divides x /\ (x int_divides 1 <=> (x = 1) \/ (x = -1))
   
   [INT_DIVIDES_LADD]  Theorem
      
      |- !p q r.
           p int_divides q ==> (p int_divides q + r <=> p int_divides r)
   
   [INT_DIVIDES_LMUL]  Theorem
      
      |- !p q r. p int_divides q ==> p int_divides q * r
   
   [INT_DIVIDES_LSUB]  Theorem
      
      |- !p q r.
           p int_divides q ==> (p int_divides q - r <=> p int_divides r)
   
   [INT_DIVIDES_MOD0]  Theorem
      
      |- !p q.
           p int_divides q <=> (q % p = 0) /\ p <> 0 \/ (p = 0) /\ (q = 0)
   
   [INT_DIVIDES_MUL]  Theorem
      
      |- !p q. p int_divides p * q /\ p int_divides q * p
   
   [INT_DIVIDES_MUL_BOTH]  Theorem
      
      |- !p q r. p <> 0 ==> (p * q int_divides p * r <=> q int_divides r)
   
   [INT_DIVIDES_NEG]  Theorem
      
      |- !p q.
           (p int_divides -q <=> p int_divides q) /\
           (-p int_divides q <=> p int_divides q)
   
   [INT_DIVIDES_RADD]  Theorem
      
      |- !p q r.
           p int_divides q ==> (p int_divides r + q <=> p int_divides r)
   
   [INT_DIVIDES_REDUCE]  Theorem
      
      |- !n m p.
           (0 int_divides 0 <=> T) /\
           (0 int_divides &NUMERAL (BIT1 n) <=> F) /\
           (0 int_divides &NUMERAL (BIT2 n) <=> F) /\
           (p int_divides 0 <=> T) /\
           (&NUMERAL (BIT1 n) int_divides &NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
           (&NUMERAL (BIT2 n) int_divides &NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
           (&NUMERAL (BIT1 n) int_divides -&NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
           (&NUMERAL (BIT2 n) int_divides -&NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
           (-&NUMERAL (BIT1 n) int_divides &NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
           (-&NUMERAL (BIT2 n) int_divides &NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT2 n) = 0)) /\
           (-&NUMERAL (BIT1 n) int_divides -&NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT1 n) = 0)) /\
           (-&NUMERAL (BIT2 n) int_divides -&NUMERAL m <=>
            (NUMERAL m MOD NUMERAL (BIT2 n) = 0))
   
   [INT_DIVIDES_REFL]  Theorem
      
      |- !x. x int_divides x
   
   [INT_DIVIDES_RMUL]  Theorem
      
      |- !p q r. p int_divides q ==> p int_divides r * q
   
   [INT_DIVIDES_RSUB]  Theorem
      
      |- !p q r.
           p int_divides q ==> (p int_divides r - q <=> p int_divides r)
   
   [INT_DIVIDES_TRANS]  Theorem
      
      |- !x y z. x int_divides y /\ y int_divides z ==> x int_divides z
   
   [INT_DIVISION]  Theorem
      
      |- !q.
           q <> 0 ==>
           !p.
             (p = p / q * q + p % q) /\
             if q < 0 then
               q < p % q /\ p % q <= 0
             else
               0 <= p % q /\ p % q < q
   
   [INT_DIV_0]  Theorem
      
      |- !q. q <> 0 ==> (0 / q = 0)
   
   [INT_DIV_1]  Theorem
      
      |- !p. p / 1 = p
   
   [INT_DIV_CALCULATE]  Theorem
      
      |- (!n m. m <> 0 ==> (&n / &m = &(n DIV m))) /\
         (!p q. q <> 0 ==> (p / -q = -p / q)) /\
         (!m n. (&m = &n) <=> (m = n)) /\ (!x. (-x = 0) <=> (x = 0)) /\
         !x. --x = x
   
   [INT_DIV_FORALL_P]  Theorem
      
      |- !P x c.
           c <> 0 ==>
           (P (x / c) <=>
            !k r.
              (x = k * c + r) /\
              (c < 0 /\ c < r /\ r <= 0 \/ ~(c < 0) /\ 0 <= r /\ r < c) ==>
              P k)
   
   [INT_DIV_ID]  Theorem
      
      |- !p. p <> 0 ==> (p / p = 1)
   
   [INT_DIV_LMUL]  Theorem
      
      |- !i j. i <> 0 ==> (i * j / i = j)
   
   [INT_DIV_MUL_ID]  Theorem
      
      |- !p q. q <> 0 /\ (p % q = 0) ==> (p / q * q = p)
   
   [INT_DIV_NEG]  Theorem
      
      |- !p q. q <> 0 ==> (p / -q = -p / q)
   
   [INT_DIV_P]  Theorem
      
      |- !P x c.
           c <> 0 ==>
           (P (x / c) <=>
            ?k r.
              (x = k * c + r) /\
              (c < 0 /\ c < r /\ r <= 0 \/ ~(c < 0) /\ 0 <= r /\ r < c) /\
              P k)
   
   [INT_DIV_REDUCE]  Theorem
      
      |- !m n.
           (0 / &NUMERAL (BIT1 n) = 0) /\ (0 / &NUMERAL (BIT2 n) = 0) /\
           (&NUMERAL m / &NUMERAL (BIT1 n) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
           (&NUMERAL m / &NUMERAL (BIT2 n) =
            &(NUMERAL m DIV NUMERAL (BIT2 n))) /\
           (-&NUMERAL m / &NUMERAL (BIT1 n) =
            -&(NUMERAL m DIV NUMERAL (BIT1 n)) +
            if NUMERAL m MOD NUMERAL (BIT1 n) = 0 then 0 else -1) /\
           (-&NUMERAL m / &NUMERAL (BIT2 n) =
            -&(NUMERAL m DIV NUMERAL (BIT2 n)) +
            if NUMERAL m MOD NUMERAL (BIT2 n) = 0 then 0 else -1) /\
           (&NUMERAL m / -&NUMERAL (BIT1 n) =
            -&(NUMERAL m DIV NUMERAL (BIT1 n)) +
            if NUMERAL m MOD NUMERAL (BIT1 n) = 0 then 0 else -1) /\
           (&NUMERAL m / -&NUMERAL (BIT2 n) =
            -&(NUMERAL m DIV NUMERAL (BIT2 n)) +
            if NUMERAL m MOD NUMERAL (BIT2 n) = 0 then 0 else -1) /\
           (-&NUMERAL m / -&NUMERAL (BIT1 n) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
           (-&NUMERAL m / -&NUMERAL (BIT2 n) =
            &(NUMERAL m DIV NUMERAL (BIT2 n)))
   
   [INT_DIV_RMUL]  Theorem
      
      |- !i j. i <> 0 ==> (j * i / i = j)
   
   [INT_DIV_UNIQUE]  Theorem
      
      |- !i j q.
           (?r.
              (i = q * j + r) /\
              if j < 0 then j < r /\ r <= 0 else 0 <= r /\ r < j) ==>
           (i / j = q)
   
   [INT_DOUBLE]  Theorem
      
      |- !x. x + x = 2 * x
   
   [INT_ENTIRE]  Theorem
      
      |- !x y. (x * y = 0) <=> (x = 0) \/ (y = 0)
   
   [INT_EQ_CALCULATE]  Theorem
      
      |- (!m n. (&m = &n) <=> (m = n)) /\ (!x y. (-x = -y) <=> (x = y)) /\
         !n m.
           ((&n = -&m) <=> (n = 0) /\ (m = 0)) /\
           ((-&n = &m) <=> (n = 0) /\ (m = 0))
   
   [INT_EQ_IMP_LE]  Theorem
      
      |- !x y. (x = y) ==> x <= y
   
   [INT_EQ_LADD]  Theorem
      
      |- !x y z. (x + y = x + z) <=> (y = z)
   
   [INT_EQ_LMUL]  Theorem
      
      |- !x y z. (x * y = x * z) <=> (x = 0) \/ (y = z)
   
   [INT_EQ_LMUL2]  Theorem
      
      |- !x y z. x <> 0 ==> ((y = z) <=> (x * y = x * z))
   
   [INT_EQ_LMUL_IMP]  Theorem
      
      |- !x y z. x <> 0 /\ (x * y = x * z) ==> (y = z)
   
   [INT_EQ_NEG]  Theorem
      
      |- !x y. (-x = -y) <=> (x = y)
   
   [INT_EQ_RADD]  Theorem
      
      |- !x y z. (x + z = y + z) <=> (x = y)
   
   [INT_EQ_REDUCE]  Theorem
      
      |- !n m.
           ((0 = 0) <=> T) /\ ((0 = &NUMERAL (BIT1 n)) <=> F) /\
           ((0 = &NUMERAL (BIT2 n)) <=> F) /\
           ((0 = -&NUMERAL (BIT1 n)) <=> F) /\
           ((0 = -&NUMERAL (BIT2 n)) <=> F) /\
           ((&NUMERAL (BIT1 n) = 0) <=> F) /\
           ((&NUMERAL (BIT2 n) = 0) <=> F) /\
           ((-&NUMERAL (BIT1 n) = 0) <=> F) /\
           ((-&NUMERAL (BIT2 n) = 0) <=> F) /\
           ((&NUMERAL n = &NUMERAL m) <=> (n = m)) /\
           ((&NUMERAL (BIT1 n) = -&NUMERAL m) <=> F) /\
           ((&NUMERAL (BIT2 n) = -&NUMERAL m) <=> F) /\
           ((-&NUMERAL (BIT1 n) = &NUMERAL m) <=> F) /\
           ((-&NUMERAL (BIT2 n) = &NUMERAL m) <=> F) /\
           ((-&NUMERAL n = -&NUMERAL m) <=> (n = m))
   
   [INT_EQ_RMUL]  Theorem
      
      |- !x y z. (x * z = y * z) <=> (z = 0) \/ (x = y)
   
   [INT_EQ_RMUL_IMP]  Theorem
      
      |- !x y z. z <> 0 /\ (x * z = y * z) ==> (x = y)
   
   [INT_EQ_SUB_LADD]  Theorem
      
      |- !x y z. (x = y - z) <=> (x + z = y)
   
   [INT_EQ_SUB_RADD]  Theorem
      
      |- !x y z. (x - y = z) <=> (x = z + y)
   
   [INT_EXP]  Theorem
      
      |- !n m. &n ** m = &(n ** m)
   
   [INT_EXP_ADD_EXPONENTS]  Theorem
      
      |- !n m p. p ** n * p ** m = p ** (n + m)
   
   [INT_EXP_CALCULATE]  Theorem
      
      |- !p n m.
           (p ** 0 = 1) /\ (&n ** m = &(n ** m)) /\
           (-&n ** NUMERAL (BIT1 m) = -&NUMERAL (n ** NUMERAL (BIT1 m))) /\
           (-&n ** NUMERAL (BIT2 m) = &NUMERAL (n ** NUMERAL (BIT2 m)))
   
   [INT_EXP_EQ0]  Theorem
      
      |- !p n. (p ** n = 0) <=> (p = 0) /\ n <> 0
   
   [INT_EXP_MOD]  Theorem
      
      |- !m n p. n <= m /\ p <> 0 ==> (p ** m % p ** n = 0)
   
   [INT_EXP_MULTIPLY_EXPONENTS]  Theorem
      
      |- !m n p. (p ** n) ** m = p ** (n * m)
   
   [INT_EXP_NEG]  Theorem
      
      |- !n m.
           (EVEN n ==> (-&m ** n = &(m ** n))) /\
           (ODD n ==> (-&m ** n = -&(m ** n)))
   
   [INT_EXP_REDUCE]  Theorem
      
      |- !n m p.
           (p ** 0 = 1) /\ (&NUMERAL n ** NUMERAL m = &NUMERAL (n ** m)) /\
           (-&NUMERAL n ** NUMERAL (BIT1 m) = -&NUMERAL (n ** BIT1 m)) /\
           (-&NUMERAL n ** NUMERAL (BIT2 m) = &NUMERAL (n ** BIT2 m))
   
   [INT_EXP_SUBTRACT_EXPONENTS]  Theorem
      
      |- !m n p. n <= m /\ p <> 0 ==> (p ** m / p ** n = p ** (m - n))
   
   [INT_GE_CALCULATE]  Theorem
      
      |- !x y. x >= y <=> y <= x
   
   [INT_GE_REDUCE]  Theorem
      
      |- !n m.
           (0 >= 0 <=> T) /\ (&NUMERAL n >= 0 <=> T) /\
           (-&NUMERAL (BIT1 n) >= 0 <=> F) /\
           (-&NUMERAL (BIT2 n) >= 0 <=> F) /\
           (0 >= &NUMERAL (BIT1 n) <=> F) /\
           (0 >= &NUMERAL (BIT2 n) <=> F) /\
           (0 >= -&NUMERAL (BIT1 n) <=> T) /\
           (0 >= -&NUMERAL (BIT2 n) <=> T) /\
           (&NUMERAL m >= &NUMERAL n <=> n <= m) /\
           (-&NUMERAL (BIT1 m) >= &NUMERAL n <=> F) /\
           (-&NUMERAL (BIT2 m) >= &NUMERAL n <=> F) /\
           (&NUMERAL m >= -&NUMERAL n <=> T) /\
           (-&NUMERAL m >= -&NUMERAL n <=> m <= n)
   
   [INT_GT_CALCULATE]  Theorem
      
      |- !x y. x > y <=> y < x
   
   [INT_GT_REDUCE]  Theorem
      
      |- !n m.
           (&NUMERAL (BIT1 n) > 0 <=> T) /\
           (&NUMERAL (BIT2 n) > 0 <=> T) /\ (0 > 0 <=> F) /\
           (-&NUMERAL n > 0 <=> F) /\ (0 > &NUMERAL n <=> F) /\
           (0 > -&NUMERAL (BIT1 n) <=> T) /\
           (0 > -&NUMERAL (BIT2 n) <=> T) /\
           (&NUMERAL m > &NUMERAL n <=> n < m) /\
           (&NUMERAL m > -&NUMERAL (BIT1 n) <=> T) /\
           (&NUMERAL m > -&NUMERAL (BIT2 n) <=> T) /\
           (-&NUMERAL m > &NUMERAL n <=> F) /\
           (-&NUMERAL m > -&NUMERAL n <=> m < n)
   
   [INT_INJ]  Theorem
      
      |- !m n. (&m = &n) <=> (m = n)
   
   [INT_LDISTRIB]  Theorem
      
      |- !z y x. x * (y + z) = x * y + x * z
   
   [INT_LE]  Theorem
      
      |- !m n. &m <= &n <=> m <= n
   
   [INT_LESS_MOD]  Theorem
      
      |- !i j. 0 <= i /\ i < j ==> (i % j = i)
   
   [INT_LET_ADD]  Theorem
      
      |- !x y. 0 <= x /\ 0 < y ==> 0 < x + y
   
   [INT_LET_ADD2]  Theorem
      
      |- !w x y z. w <= x /\ y < z ==> w + y < x + z
   
   [INT_LET_ANTISYM]  Theorem
      
      |- !x y. ~(x < y /\ y <= x)
   
   [INT_LET_TOTAL]  Theorem
      
      |- !x y. x <= y \/ y < x
   
   [INT_LET_TRANS]  Theorem
      
      |- !x y z. x <= y /\ y < z ==> x < z
   
   [INT_LE_01]  Theorem
      
      |- 0 <= 1
   
   [INT_LE_ADD]  Theorem
      
      |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x + y
   
   [INT_LE_ADD2]  Theorem
      
      |- !w x y z. w <= x /\ y <= z ==> w + y <= x + z
   
   [INT_LE_ADDL]  Theorem
      
      |- !x y. y <= x + y <=> 0 <= x
   
   [INT_LE_ADDR]  Theorem
      
      |- !x y. x <= x + y <=> 0 <= y
   
   [INT_LE_ANTISYM]  Theorem
      
      |- !x y. x <= y /\ y <= x <=> (x = y)
   
   [INT_LE_CALCULATE]  Theorem
      
      |- !x y. x <= y <=> x < y \/ (x = y)
   
   [INT_LE_DOUBLE]  Theorem
      
      |- !x. 0 <= x + x <=> 0 <= x
   
   [INT_LE_LADD]  Theorem
      
      |- !x y z. x + y <= x + z <=> y <= z
   
   [INT_LE_LT]  Theorem
      
      |- !x y. x <= y <=> x < y \/ (x = y)
   
   [INT_LE_LT1]  Theorem
      
      |- x <= y <=> x < y + 1
   
   [INT_LE_MONO]  Theorem
      
      |- !x y z. 0 < x ==> (x * y <= x * z <=> y <= z)
   
   [INT_LE_MUL]  Theorem
      
      |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x * y
   
   [INT_LE_NEG]  Theorem
      
      |- !x y. -x <= -y <=> y <= x
   
   [INT_LE_NEGL]  Theorem
      
      |- !x. -x <= x <=> 0 <= x
   
   [INT_LE_NEGR]  Theorem
      
      |- !x. x <= -x <=> x <= 0
   
   [INT_LE_NEGTOTAL]  Theorem
      
      |- !x. 0 <= x \/ 0 <= -x
   
   [INT_LE_RADD]  Theorem
      
      |- !x y z. x + z <= y + z <=> x <= y
   
   [INT_LE_REDUCE]  Theorem
      
      |- !n m.
           (0 <= 0 <=> T) /\ (0 <= &NUMERAL n <=> T) /\
           (0 <= -&NUMERAL (BIT1 n) <=> F) /\
           (0 <= -&NUMERAL (BIT2 n) <=> F) /\
           (&NUMERAL (BIT1 n) <= 0 <=> F) /\
           (&NUMERAL (BIT2 n) <= 0 <=> F) /\
           (-&NUMERAL (BIT1 n) <= 0 <=> T) /\
           (-&NUMERAL (BIT2 n) <= 0 <=> T) /\
           (&NUMERAL n <= &NUMERAL m <=> n <= m) /\
           (&NUMERAL n <= -&NUMERAL (BIT1 m) <=> F) /\
           (&NUMERAL n <= -&NUMERAL (BIT2 m) <=> F) /\
           (-&NUMERAL n <= &NUMERAL m <=> T) /\
           (-&NUMERAL n <= -&NUMERAL m <=> m <= n)
   
   [INT_LE_REFL]  Theorem
      
      |- !x. x <= x
   
   [INT_LE_SQUARE]  Theorem
      
      |- !x. 0 <= x * x
   
   [INT_LE_SUB_LADD]  Theorem
      
      |- !x y z. x <= y - z <=> x + z <= y
   
   [INT_LE_SUB_RADD]  Theorem
      
      |- !x y z. x - y <= z <=> x <= z + y
   
   [INT_LE_TOTAL]  Theorem
      
      |- !x y. x <= y \/ y <= x
   
   [INT_LE_TRANS]  Theorem
      
      |- !x y z. x <= y /\ y <= z ==> x <= z
   
   [INT_LNEG_UNIQ]  Theorem
      
      |- !x y. (x + y = 0) <=> (x = -y)
   
   [INT_LT]  Theorem
      
      |- !m n. &m < &n <=> m < n
   
   [INT_LTE_ADD]  Theorem
      
      |- !x y. 0 < x /\ 0 <= y ==> 0 < x + y
   
   [INT_LTE_ADD2]  Theorem
      
      |- !w x y z. w < x /\ y <= z ==> w + y < x + z
   
   [INT_LTE_ANTSYM]  Theorem
      
      |- !x y. ~(x <= y /\ y < x)
   
   [INT_LTE_TOTAL]  Theorem
      
      |- !x y. x < y \/ y <= x
   
   [INT_LTE_TRANS]  Theorem
      
      |- !x y z. x < y /\ y <= z ==> x < z
   
   [INT_LT_01]  Theorem
      
      |- 0 < 1
   
   [INT_LT_ADD]  Theorem
      
      |- !x y. 0 < x /\ 0 < y ==> 0 < x + y
   
   [INT_LT_ADD1]  Theorem
      
      |- !x y. x <= y ==> x < y + 1
   
   [INT_LT_ADD2]  Theorem
      
      |- !w x y z. w < x /\ y < z ==> w + y < x + z
   
   [INT_LT_ADDL]  Theorem
      
      |- !x y. y < x + y <=> 0 < x
   
   [INT_LT_ADDNEG]  Theorem
      
      |- !x y z. y < x + -z <=> y + z < x
   
   [INT_LT_ADDNEG2]  Theorem
      
      |- !x y z. x + -y < z <=> x < z + y
   
   [INT_LT_ADDR]  Theorem
      
      |- !x y. x < x + y <=> 0 < y
   
   [INT_LT_ADD_SUB]  Theorem
      
      |- !x y z. x + y < z <=> x < z - y
   
   [INT_LT_ANTISYM]  Theorem
      
      |- !x y. ~(x < y /\ y < x)
   
   [INT_LT_CALCULATE]  Theorem
      
      |- !n m.
           (&n < &m <=> n < m) /\ (-&n < -&m <=> m < n) /\
           (-&n < &m <=> n <> 0 \/ m <> 0) /\ (&n < -&m <=> F)
   
   [INT_LT_GT]  Theorem
      
      |- !x y. x < y ==> ~(y < x)
   
   [INT_LT_IMP_LE]  Theorem
      
      |- !x y. x < y ==> x <= y
   
   [INT_LT_IMP_NE]  Theorem
      
      |- !x y. x < y ==> x <> y
   
   [INT_LT_LADD]  Theorem
      
      |- !x y z. x + y < x + z <=> y < z
   
   [INT_LT_LADD_IMP]  Theorem
      
      |- !x y z. y < z ==> x + y < x + z
   
   [INT_LT_LE]  Theorem
      
      |- !x y. x < y <=> x <= y /\ x <> y
   
   [INT_LT_LE1]  Theorem
      
      |- x < y <=> x + 1 <= y
   
   [INT_LT_MONO]  Theorem
      
      |- !x y z. 0 < x ==> (x * y < x * z <=> y < z)
   
   [INT_LT_MUL]  Theorem
      
      |- !x y. int_0 < x /\ int_0 < y ==> int_0 < x * y
   
   [INT_LT_MUL2]  Theorem
      
      |- !x1 x2 y1 y2.
           0 <= x1 /\ 0 <= y1 /\ x1 < x2 /\ y1 < y2 ==> x1 * y1 < x2 * y2
   
   [INT_LT_NEG]  Theorem
      
      |- !x y. -x < -y <=> y < x
   
   [INT_LT_NEGTOTAL]  Theorem
      
      |- !x. (x = 0) \/ 0 < x \/ 0 < -x
   
   [INT_LT_NZ]  Theorem
      
      |- !n. &n <> 0 <=> 0 < &n
   
   [INT_LT_RADD]  Theorem
      
      |- !x y z. x + z < y + z <=> x < y
   
   [INT_LT_REDUCE]  Theorem
      
      |- !n m.
           (0 < &NUMERAL (BIT1 n) <=> T) /\
           (0 < &NUMERAL (BIT2 n) <=> T) /\ (0 < 0 <=> F) /\
           (0 < -&NUMERAL n <=> F) /\ (&NUMERAL n < 0 <=> F) /\
           (-&NUMERAL (BIT1 n) < 0 <=> T) /\
           (-&NUMERAL (BIT2 n) < 0 <=> T) /\
           (&NUMERAL n < &NUMERAL m <=> n < m) /\
           (-&NUMERAL (BIT1 n) < &NUMERAL m <=> T) /\
           (-&NUMERAL (BIT2 n) < &NUMERAL m <=> T) /\
           (&NUMERAL n < -&NUMERAL m <=> F) /\
           (-&NUMERAL n < -&NUMERAL m <=> m < n)
   
   [INT_LT_REFL]  Theorem
      
      |- !x. ~(x < x)
   
   [INT_LT_SUB_LADD]  Theorem
      
      |- !x y z. x < y - z <=> x + z < y
   
   [INT_LT_SUB_RADD]  Theorem
      
      |- !x y z. x - y < z <=> x < z + y
   
   [INT_LT_TOTAL]  Theorem
      
      |- !x y. (x = y) \/ x < y \/ y < x
   
   [INT_LT_TRANS]  Theorem
      
      |- !x y z. x < y /\ y < z ==> x < z
   
   [INT_MAX_LT]  Theorem
      
      |- !x y z. int_max x y < z ==> x < z /\ y < z
   
   [INT_MAX_NUM]  Theorem
      
      |- !m n. int_max (&m) (&n) = &MAX m n
   
   [INT_MIN_LT]  Theorem
      
      |- !x y z. x < int_min y z ==> x < y /\ x < z
   
   [INT_MIN_NUM]  Theorem
      
      |- !m n. int_min (&m) (&n) = &MIN m n
   
   [INT_MOD]  Theorem
      
      |- !n m. m <> 0 ==> (&n % &m = &(n MOD m))
   
   [INT_MOD0]  Theorem
      
      |- !p. p <> 0 ==> (0 % p = 0)
   
   [INT_MOD_1]  Theorem
      
      |- !i. i % 1 = 0
   
   [INT_MOD_ADD_MULTIPLES]  Theorem
      
      |- k <> 0 ==> ((q * k + r) % k = r % k)
   
   [INT_MOD_BOUNDS]  Theorem
      
      |- !p q.
           q <> 0 ==>
           if q < 0 then
             q < p % q /\ p % q <= 0
           else
             0 <= p % q /\ p % q < q
   
   [INT_MOD_CALCULATE]  Theorem
      
      |- (!n m. m <> 0 ==> (&n % &m = &(n MOD m))) /\
         (!p q. q <> 0 ==> (p % -q = -(-p % q))) /\ (!x. --x = x) /\
         (!m n. (&m = &n) <=> (m = n)) /\ !x. (-x = 0) <=> (x = 0)
   
   [INT_MOD_COMMON_FACTOR]  Theorem
      
      |- !p. p <> 0 ==> !q. (q * p) % p = 0
   
   [INT_MOD_EQ0]  Theorem
      
      |- !q. q <> 0 ==> !p. (p % q = 0) <=> ?k. p = k * q
   
   [INT_MOD_FORALL_P]  Theorem
      
      |- !P x c.
           c <> 0 ==>
           (P (x % c) <=>
            !q r.
              (x = q * c + r) /\
              (c < 0 /\ c < r /\ r <= 0 \/ ~(c < 0) /\ 0 <= r /\ r < c) ==>
              P r)
   
   [INT_MOD_ID]  Theorem
      
      |- !i. i <> 0 ==> (i % i = 0)
   
   [INT_MOD_MINUS1]  Theorem
      
      |- !n. 0 < n ==> (-1 % n = n - 1)
   
   [INT_MOD_MOD]  Theorem
      
      |- k <> 0 ==> (j % k % k = j % k)
   
   [INT_MOD_NEG]  Theorem
      
      |- !p q. q <> 0 ==> (p % -q = -(-p % q))
   
   [INT_MOD_NEG_NUMERATOR]  Theorem
      
      |- k <> 0 ==> (-x % k = (k - x) % k)
   
   [INT_MOD_P]  Theorem
      
      |- !P x c.
           c <> 0 ==>
           (P (x % c) <=>
            ?k r.
              (x = k * c + r) /\
              (c < 0 /\ c < r /\ r <= 0 \/ ~(c < 0) /\ 0 <= r /\ r < c) /\
              P r)
   
   [INT_MOD_PLUS]  Theorem
      
      |- k <> 0 ==> ((i % k + j % k) % k = (i + j) % k)
   
   [INT_MOD_REDUCE]  Theorem
      
      |- !m n.
           (0 % &NUMERAL (BIT1 n) = 0) /\ (0 % &NUMERAL (BIT2 n) = 0) /\
           (&NUMERAL m % &NUMERAL (BIT1 n) =
            &(NUMERAL m MOD NUMERAL (BIT1 n))) /\
           (&NUMERAL m % &NUMERAL (BIT2 n) =
            &(NUMERAL m MOD NUMERAL (BIT2 n))) /\
           (x % &NUMERAL (BIT1 n) =
            x - x / &NUMERAL (BIT1 n) * &NUMERAL (BIT1 n)) /\
           (x % &NUMERAL (BIT2 n) =
            x - x / &NUMERAL (BIT2 n) * &NUMERAL (BIT2 n))
   
   [INT_MOD_SUB]  Theorem
      
      |- k <> 0 ==> ((i % k - j % k) % k = (i - j) % k)
   
   [INT_MOD_UNIQUE]  Theorem
      
      |- !i j m.
           (?q.
              (i = q * j + m) /\
              if j < 0 then j < m /\ m <= 0 else 0 <= m /\ m < j) ==>
           (i % j = m)
   
   [INT_MUL]  Theorem
      
      |- !m n. &m * &n = &(m * n)
   
   [INT_MUL_ASSOC]  Theorem
      
      |- !z y x. x * (y * z) = x * y * z
   
   [INT_MUL_CALCULATE]  Theorem
      
      |- (!m n. &m * &n = &(m * n)) /\ (!x y. -x * y = -(x * y)) /\
         (!x y. x * -y = -(x * y)) /\ !x. --x = x
   
   [INT_MUL_COMM]  Theorem
      
      |- !y x. x * y = y * x
   
   [INT_MUL_DIV]  Theorem
      
      |- !p q k. q <> 0 /\ (p % q = 0) ==> (k * p / q = k * (p / q))
   
   [INT_MUL_EQ_1]  Theorem
      
      |- !x y. (x * y = 1) <=> (x = 1) /\ (y = 1) \/ (x = -1) /\ (y = -1)
   
   [INT_MUL_LID]  Theorem
      
      |- !x. 1 * x = x
   
   [INT_MUL_LZERO]  Theorem
      
      |- !x. 0 * x = 0
   
   [INT_MUL_QUOT]  Theorem
      
      |- !p q k.
           q <> 0 /\ (p rem q = 0) ==> (k * p quot q = k * (p quot q))
   
   [INT_MUL_REDUCE]  Theorem
      
      |- !m n p.
           (p * 0 = 0) /\ (0 * p = 0) /\
           (&NUMERAL m * &NUMERAL n = &NUMERAL (m * n)) /\
           (-&NUMERAL m * &NUMERAL n = -&NUMERAL (m * n)) /\
           (&NUMERAL m * -&NUMERAL n = -&NUMERAL (m * n)) /\
           (-&NUMERAL m * -&NUMERAL n = &NUMERAL (m * n))
   
   [INT_MUL_RID]  Theorem
      
      |- !x. x * 1 = x
   
   [INT_MUL_RZERO]  Theorem
      
      |- !x. x * 0 = 0
   
   [INT_MUL_SIGN_CASES]  Theorem
      
      |- !p q.
           (0 < p * q <=> 0 < p /\ 0 < q \/ p < 0 /\ q < 0) /\
           (p * q < 0 <=> 0 < p /\ q < 0 \/ p < 0 /\ 0 < q)
   
   [INT_MUL_SYM]  Theorem
      
      |- !y x. x * y = y * x
   
   [INT_NEGNEG]  Theorem
      
      |- !x. --x = x
   
   [INT_NEG_0]  Theorem
      
      |- -0 = 0
   
   [INT_NEG_ADD]  Theorem
      
      |- !x y. -(x + y) = -x + -y
   
   [INT_NEG_EQ]  Theorem
      
      |- !x y. (-x = y) <=> (x = -y)
   
   [INT_NEG_EQ0]  Theorem
      
      |- !x. (-x = 0) <=> (x = 0)
   
   [INT_NEG_GE0]  Theorem
      
      |- !x. 0 <= -x <=> x <= 0
   
   [INT_NEG_GT0]  Theorem
      
      |- !x. 0 < -x <=> x < 0
   
   [INT_NEG_LE0]  Theorem
      
      |- !x. -x <= 0 <=> 0 <= x
   
   [INT_NEG_LMUL]  Theorem
      
      |- !x y. -(x * y) = -x * y
   
   [INT_NEG_LT0]  Theorem
      
      |- !x. -x < 0 <=> 0 < x
   
   [INT_NEG_MINUS1]  Theorem
      
      |- !x. -x = -1 * x
   
   [INT_NEG_MUL2]  Theorem
      
      |- !x y. -x * -y = x * y
   
   [INT_NEG_RMUL]  Theorem
      
      |- !x y. -(x * y) = x * -y
   
   [INT_NEG_SAME_EQ]  Theorem
      
      |- !p. (p = -p) <=> (p = 0)
   
   [INT_NEG_SUB]  Theorem
      
      |- !x y. -(x - y) = y - x
   
   [INT_NOT_LE]  Theorem
      
      |- !x y. ~(x <= y) <=> y < x
   
   [INT_NOT_LT]  Theorem
      
      |- !x y. ~(x < y) <=> y <= x
   
   [INT_NUM_CASES]  Theorem
      
      |- !p.
           (?n. (p = &n) /\ n <> 0) \/ (?n. (p = -&n) /\ n <> 0) \/ (p = 0)
   
   [INT_NZ_IMP_LT]  Theorem
      
      |- !n. n <> 0 ==> 0 < &n
   
   [INT_OF_NUM]  Theorem
      
      |- !i. (&Num i = i) <=> 0 <= i
   
   [INT_POASQ]  Theorem
      
      |- !x. 0 < x * x <=> x <> 0
   
   [INT_POS]  Theorem
      
      |- !n. 0 <= &n
   
   [INT_POS_NZ]  Theorem
      
      |- !x. 0 < x ==> x <> 0
   
   [INT_QUOT]  Theorem
      
      |- !p q. q <> 0 ==> (&p quot &q = &(p DIV q))
   
   [INT_QUOT_0]  Theorem
      
      |- !q. q <> 0 ==> (0 quot q = 0)
   
   [INT_QUOT_1]  Theorem
      
      |- !p. p quot 1 = p
   
   [INT_QUOT_CALCULATE]  Theorem
      
      |- (!p q. q <> 0 ==> (&p quot &q = &(p DIV q))) /\
         (!p q.
            q <> 0 ==>
            (-p quot q = -(p quot q)) /\ (p quot -q = -(p quot q))) /\
         (!m n. (&m = &n) <=> (m = n)) /\ (!x. (-x = 0) <=> (x = 0)) /\
         !x. --x = x
   
   [INT_QUOT_ID]  Theorem
      
      |- !p. p <> 0 ==> (p quot p = 1)
   
   [INT_QUOT_NEG]  Theorem
      
      |- !p q.
           q <> 0 ==>
           (-p quot q = -(p quot q)) /\ (p quot -q = -(p quot q))
   
   [INT_QUOT_REDUCE]  Theorem
      
      |- !m n.
           (0 quot &NUMERAL (BIT1 n) = 0) /\
           (0 quot &NUMERAL (BIT2 n) = 0) /\
           (&NUMERAL m quot &NUMERAL (BIT1 n) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
           (&NUMERAL m quot &NUMERAL (BIT2 n) =
            &(NUMERAL m DIV NUMERAL (BIT2 n))) /\
           (-&NUMERAL m quot &NUMERAL (BIT1 n) =
            -&(NUMERAL m DIV NUMERAL (BIT1 n))) /\
           (-&NUMERAL m quot &NUMERAL (BIT2 n) =
            -&(NUMERAL m DIV NUMERAL (BIT2 n))) /\
           (&NUMERAL m quot -&NUMERAL (BIT1 n) =
            -&(NUMERAL m DIV NUMERAL (BIT1 n))) /\
           (&NUMERAL m quot -&NUMERAL (BIT2 n) =
            -&(NUMERAL m DIV NUMERAL (BIT2 n))) /\
           (-&NUMERAL m quot -&NUMERAL (BIT1 n) =
            &(NUMERAL m DIV NUMERAL (BIT1 n))) /\
           (-&NUMERAL m quot -&NUMERAL (BIT2 n) =
            &(NUMERAL m DIV NUMERAL (BIT2 n)))
   
   [INT_QUOT_UNIQUE]  Theorem
      
      |- !p q k.
           (?r.
              (p = k * q + r) /\ (if 0 < p then 0 <= r else r <= 0) /\
              ABS r < ABS q) ==>
           (p quot q = k)
   
   [INT_RDISTRIB]  Theorem
      
      |- !x y z. (x + y) * z = x * z + y * z
   
   [INT_REM]  Theorem
      
      |- !p q. q <> 0 ==> (&p rem &q = &(p MOD q))
   
   [INT_REM0]  Theorem
      
      |- !q. q <> 0 ==> (0 rem q = 0)
   
   [INT_REMQUOT]  Theorem
      
      |- !q.
           q <> 0 ==>
           !p.
             (p = p quot q * q + p rem q) /\
             (if 0 < p then 0 <= p rem q else p rem q <= 0) /\
             ABS (p rem q) < ABS q
   
   [INT_REM_CALCULATE]  Theorem
      
      |- (!p q. q <> 0 ==> (&p rem &q = &(p MOD q))) /\
         (!p q.
            q <> 0 ==> (-p rem q = -(p rem q)) /\ (p rem -q = p rem q)) /\
         (!x. --x = x) /\ (!m n. (&m = &n) <=> (m = n)) /\
         !x. (-x = 0) <=> (x = 0)
   
   [INT_REM_COMMON_FACTOR]  Theorem
      
      |- !p. p <> 0 ==> !q. (q * p) rem p = 0
   
   [INT_REM_EQ0]  Theorem
      
      |- !q. q <> 0 ==> !p. (p rem q = 0) <=> ?k. p = k * q
   
   [INT_REM_EQ_MOD]  Theorem
      
      |- !i n.
           0 < n ==>
           (i rem n = if i < 0 then (i - 1) % n - n + 1 else i % n)
   
   [INT_REM_ID]  Theorem
      
      |- !p. p <> 0 ==> (p rem p = 0)
   
   [INT_REM_NEG]  Theorem
      
      |- !p q. q <> 0 ==> (-p rem q = -(p rem q)) /\ (p rem -q = p rem q)
   
   [INT_REM_REDUCE]  Theorem
      
      |- !m n.
           (0 rem &NUMERAL (BIT1 n) = 0) /\
           (0 rem &NUMERAL (BIT2 n) = 0) /\
           (&NUMERAL m rem &NUMERAL (BIT1 n) =
            &(NUMERAL m MOD NUMERAL (BIT1 n))) /\
           (&NUMERAL m rem &NUMERAL (BIT2 n) =
            &(NUMERAL m MOD NUMERAL (BIT2 n))) /\
           (-&NUMERAL m rem &NUMERAL (BIT1 n) =
            -&(NUMERAL m MOD NUMERAL (BIT1 n))) /\
           (-&NUMERAL m rem &NUMERAL (BIT2 n) =
            -&(NUMERAL m MOD NUMERAL (BIT2 n))) /\
           (&NUMERAL m rem -&NUMERAL (BIT1 n) =
            &(NUMERAL m MOD NUMERAL (BIT1 n))) /\
           (&NUMERAL m rem -&NUMERAL (BIT2 n) =
            &(NUMERAL m MOD NUMERAL (BIT2 n))) /\
           (-&NUMERAL m rem -&NUMERAL (BIT1 n) =
            -&(NUMERAL m MOD NUMERAL (BIT1 n))) /\
           (-&NUMERAL m rem -&NUMERAL (BIT2 n) =
            -&(NUMERAL m MOD NUMERAL (BIT2 n)))
   
   [INT_REM_UNIQUE]  Theorem
      
      |- !p q r.
           ABS r < ABS q /\ (if 0 < p then 0 <= r else r <= 0) /\
           (?k. p = k * q + r) ==>
           (p rem q = r)
   
   [INT_RNEG_UNIQ]  Theorem
      
      |- !x y. (x + y = 0) <=> (y = -x)
   
   [INT_SUB]  Theorem
      
      |- !n m. m <= n ==> (&n - &m = &(n - m))
   
   [INT_SUB_0]  Theorem
      
      |- !x y. (x - y = 0) <=> (x = y)
   
   [INT_SUB_ADD]  Theorem
      
      |- !x y. x - y + y = x
   
   [INT_SUB_ADD2]  Theorem
      
      |- !x y. y + (x - y) = x
   
   [INT_SUB_CALCULATE]  Theorem
      
      |- !x y. x - y = x + -y
   
   [INT_SUB_LDISTRIB]  Theorem
      
      |- !x y z. x * (y - z) = x * y - x * z
   
   [INT_SUB_LE]  Theorem
      
      |- !x y. 0 <= x - y <=> y <= x
   
   [INT_SUB_LNEG]  Theorem
      
      |- !x y. -x - y = -(x + y)
   
   [INT_SUB_LT]  Theorem
      
      |- !x y. 0 < x - y <=> y < x
   
   [INT_SUB_LZERO]  Theorem
      
      |- !x. 0 - x = -x
   
   [INT_SUB_NEG2]  Theorem
      
      |- !x y. -x - -y = y - x
   
   [INT_SUB_RDISTRIB]  Theorem
      
      |- !x y z. (x - y) * z = x * z - y * z
   
   [INT_SUB_REDUCE]  Theorem
      
      |- !m n p.
           (p - 0 = p) /\ (0 - p = -p) /\
           (&NUMERAL m - &NUMERAL n = &NUMERAL m + -&NUMERAL n) /\
           (-&NUMERAL m - &NUMERAL n = -&NUMERAL m + -&NUMERAL n) /\
           (&NUMERAL m - -&NUMERAL n = &NUMERAL m + &NUMERAL n) /\
           (-&NUMERAL m - -&NUMERAL n = -&NUMERAL m + &NUMERAL n)
   
   [INT_SUB_REFL]  Theorem
      
      |- !x. x - x = 0
   
   [INT_SUB_RNEG]  Theorem
      
      |- !x y. x - -y = x + y
   
   [INT_SUB_RZERO]  Theorem
      
      |- !x. x - 0 = x
   
   [INT_SUB_SUB]  Theorem
      
      |- !x y. x - y - x = -y
   
   [INT_SUB_SUB2]  Theorem
      
      |- !x y. x - (x - y) = y
   
   [INT_SUB_TRIANGLE]  Theorem
      
      |- !a b c. a - b + (b - c) = a - c
   
   [INT_SUMSQ]  Theorem
      
      |- !x y. (x * x + y * y = 0) <=> (x = 0) /\ (y = 0)
   
   [LE_NUM_OF_INT]  Theorem
      
      |- !n i. &n <= i ==> n <= Num i
   
   [LT_ADD2]  Theorem
      
      |- !x1 x2 y1 y2. x1 < y1 /\ x2 < y2 ==> x1 + x2 < y1 + y2
   
   [LT_ADDL]  Theorem
      
      |- !x y. x < x + y <=> 0 < y
   
   [LT_ADDR]  Theorem
      
      |- !x y. ~(x + y < x)
   
   [LT_LADD]  Theorem
      
      |- !x y z. x + y < x + z <=> y < z
   
   [NUM_NEGINT_EXISTS]  Theorem
      
      |- !i. i <= 0 ==> ?n. i = -&n
   
   [NUM_OF_INT]  Theorem
      
      |- !n. Num (&n) = n
   
   [NUM_POSINT]  Theorem
      
      |- !i. 0 <= i ==> ?!n. i = &n
   
   [NUM_POSINT_EX]  Theorem
      
      |- !t. ~(t < int_0) ==> ?n. t = &n
   
   [NUM_POSINT_EXISTS]  Theorem
      
      |- !i. 0 <= i ==> ?n. i = &n
   
   [NUM_POSTINT_EX]  Theorem
      
      |- !t. ~(t tint_lt tint_0) ==> ?n. t tint_eq tint_of_num n
   
   [TINT_10]  Theorem
      
      |- ~(tint_1 tint_eq tint_0)
   
   [TINT_ADD_ASSOC]  Theorem
      
      |- !x y z. x tint_add (y tint_add z) = x tint_add y tint_add z
   
   [TINT_ADD_LID]  Theorem
      
      |- !x. tint_0 tint_add x tint_eq x
   
   [TINT_ADD_LINV]  Theorem
      
      |- !x. tint_neg x tint_add x tint_eq tint_0
   
   [TINT_ADD_SYM]  Theorem
      
      |- !x y. x tint_add y = y tint_add x
   
   [TINT_ADD_WELLDEF]  Theorem
      
      |- !x1 x2 y1 y2.
           x1 tint_eq x2 /\ y1 tint_eq y2 ==>
           x1 tint_add y1 tint_eq x2 tint_add y2
   
   [TINT_ADD_WELLDEFR]  Theorem
      
      |- !x1 x2 y. x1 tint_eq x2 ==> x1 tint_add y tint_eq x2 tint_add y
   
   [TINT_EQ_AP]  Theorem
      
      |- !p q. (p = q) ==> p tint_eq q
   
   [TINT_EQ_EQUIV]  Theorem
      
      |- !p q. p tint_eq q <=> ($tint_eq p = $tint_eq q)
   
   [TINT_EQ_REFL]  Theorem
      
      |- !x. x tint_eq x
   
   [TINT_EQ_SYM]  Theorem
      
      |- !x y. x tint_eq y <=> y tint_eq x
   
   [TINT_EQ_TRANS]  Theorem
      
      |- !x y z. x tint_eq y /\ y tint_eq z ==> x tint_eq z
   
   [TINT_INJ]  Theorem
      
      |- !m n. tint_of_num m tint_eq tint_of_num n <=> (m = n)
   
   [TINT_LDISTRIB]  Theorem
      
      |- !x y z.
           x tint_mul (y tint_add z) = x tint_mul y tint_add x tint_mul z
   
   [TINT_LT_ADD]  Theorem
      
      |- !x y z. y tint_lt z ==> x tint_add y tint_lt x tint_add z
   
   [TINT_LT_MUL]  Theorem
      
      |- !x y.
           tint_0 tint_lt x /\ tint_0 tint_lt y ==>
           tint_0 tint_lt x tint_mul y
   
   [TINT_LT_REFL]  Theorem
      
      |- !x. ~(x tint_lt x)
   
   [TINT_LT_TOTAL]  Theorem
      
      |- !x y. x tint_eq y \/ x tint_lt y \/ y tint_lt x
   
   [TINT_LT_TRANS]  Theorem
      
      |- !x y z. x tint_lt y /\ y tint_lt z ==> x tint_lt z
   
   [TINT_LT_WELLDEF]  Theorem
      
      |- !x1 x2 y1 y2.
           x1 tint_eq x2 /\ y1 tint_eq y2 ==>
           (x1 tint_lt y1 <=> x2 tint_lt y2)
   
   [TINT_LT_WELLDEFL]  Theorem
      
      |- !x y1 y2. y1 tint_eq y2 ==> (x tint_lt y1 <=> x tint_lt y2)
   
   [TINT_LT_WELLDEFR]  Theorem
      
      |- !x1 x2 y. x1 tint_eq x2 ==> (x1 tint_lt y <=> x2 tint_lt y)
   
   [TINT_MUL_ASSOC]  Theorem
      
      |- !x y z. x tint_mul (y tint_mul z) = x tint_mul y tint_mul z
   
   [TINT_MUL_LID]  Theorem
      
      |- !x. tint_1 tint_mul x tint_eq x
   
   [TINT_MUL_SYM]  Theorem
      
      |- !x y. x tint_mul y = y tint_mul x
   
   [TINT_MUL_WELLDEF]  Theorem
      
      |- !x1 x2 y1 y2.
           x1 tint_eq x2 /\ y1 tint_eq y2 ==>
           x1 tint_mul y1 tint_eq x2 tint_mul y2
   
   [TINT_MUL_WELLDEFR]  Theorem
      
      |- !x1 x2 y. x1 tint_eq x2 ==> x1 tint_mul y tint_eq x2 tint_mul y
   
   [TINT_NEG_WELLDEF]  Theorem
      
      |- !x1 x2. x1 tint_eq x2 ==> tint_neg x1 tint_eq tint_neg x2
   
   [int_ABS_REP_CLASS]  Theorem
      
      |- (!a. int_ABS_CLASS (int_REP_CLASS a) = a) /\
         !c.
           (?r. r tint_eq r /\ (c = $tint_eq r)) <=>
           (int_REP_CLASS (int_ABS_CLASS c) = c)
   
   [int_QUOTIENT]  Theorem
      
      |- QUOTIENT $tint_eq int_ABS int_REP
   
   [int_of_num]  Theorem
      
      |- (0 = int_0) /\ !n. &SUC n = &n + int_1
   
   [tint_of_num_eq]  Theorem
      
      |- !n. FST (tint_of_num n) = SND (tint_of_num n) + n
   
   
*)
end
