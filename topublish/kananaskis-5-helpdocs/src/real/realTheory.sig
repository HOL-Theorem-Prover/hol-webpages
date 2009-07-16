signature realTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val NUM_CEILING_def : thm
    val NUM_FLOOR_def : thm
    val SUM_DEF : thm
    val abs : thm
    val inf_def : thm
    val max_def : thm
    val min_def : thm
    val pos_def : thm
    val pow : thm
    val real_div : thm
    val real_ge : thm
    val real_gt : thm
    val real_lte : thm
    val real_of_num : thm
    val real_sub : thm
    val sumc : thm
    val sup : thm
  
  (*  Theorems  *)
    val ABS_0 : thm
    val ABS_1 : thm
    val ABS_ABS : thm
    val ABS_BETWEEN : thm
    val ABS_BETWEEN1 : thm
    val ABS_BETWEEN2 : thm
    val ABS_BOUND : thm
    val ABS_BOUNDS : thm
    val ABS_CASES : thm
    val ABS_CIRCLE : thm
    val ABS_DIV : thm
    val ABS_INV : thm
    val ABS_LE : thm
    val ABS_LT_MUL2 : thm
    val ABS_MUL : thm
    val ABS_N : thm
    val ABS_NEG : thm
    val ABS_NZ : thm
    val ABS_POS : thm
    val ABS_POW2 : thm
    val ABS_REFL : thm
    val ABS_SIGN : thm
    val ABS_SIGN2 : thm
    val ABS_STILLNZ : thm
    val ABS_SUB : thm
    val ABS_SUB_ABS : thm
    val ABS_SUM : thm
    val ABS_TRIANGLE : thm
    val ABS_ZERO : thm
    val LE_NUM_CEILING : thm
    val NUM_CEILING_LE : thm
    val NUM_FLOOR_DIV : thm
    val NUM_FLOOR_DIV_LOWERBOUND : thm
    val NUM_FLOOR_EQNS : thm
    val NUM_FLOOR_LE : thm
    val NUM_FLOOR_LE2 : thm
    val NUM_FLOOR_LET : thm
    val NUM_FLOOR_LOWER_BOUND : thm
    val NUM_FLOOR_upper_bound : thm
    val POW_0 : thm
    val POW_1 : thm
    val POW_2 : thm
    val POW_2_LE1 : thm
    val POW_2_LT : thm
    val POW_ABS : thm
    val POW_ADD : thm
    val POW_EQ : thm
    val POW_INV : thm
    val POW_LE : thm
    val POW_LT : thm
    val POW_M1 : thm
    val POW_MINUS1 : thm
    val POW_MUL : thm
    val POW_NZ : thm
    val POW_ONE : thm
    val POW_PLUS1 : thm
    val POW_POS : thm
    val POW_POS_LT : thm
    val POW_ZERO : thm
    val POW_ZERO_EQ : thm
    val REAL : thm
    val REAL_0 : thm
    val REAL_1 : thm
    val REAL_10 : thm
    val REAL_ABS_0 : thm
    val REAL_ABS_MUL : thm
    val REAL_ABS_POS : thm
    val REAL_ABS_TRIANGLE : thm
    val REAL_ADD : thm
    val REAL_ADD2_SUB2 : thm
    val REAL_ADD_ASSOC : thm
    val REAL_ADD_COMM : thm
    val REAL_ADD_LDISTRIB : thm
    val REAL_ADD_LID : thm
    val REAL_ADD_LID_UNIQ : thm
    val REAL_ADD_LINV : thm
    val REAL_ADD_RAT : thm
    val REAL_ADD_RDISTRIB : thm
    val REAL_ADD_RID : thm
    val REAL_ADD_RID_UNIQ : thm
    val REAL_ADD_RINV : thm
    val REAL_ADD_SUB : thm
    val REAL_ADD_SUB2 : thm
    val REAL_ADD_SUB_ALT : thm
    val REAL_ADD_SYM : thm
    val REAL_ARCH : thm
    val REAL_ARCH_LEAST : thm
    val REAL_BIGNUM : thm
    val REAL_DIFFSQ : thm
    val REAL_DIV_ADD : thm
    val REAL_DIV_DENOM_CANCEL : thm
    val REAL_DIV_DENOM_CANCEL2 : thm
    val REAL_DIV_DENOM_CANCEL3 : thm
    val REAL_DIV_INNER_CANCEL : thm
    val REAL_DIV_INNER_CANCEL2 : thm
    val REAL_DIV_INNER_CANCEL3 : thm
    val REAL_DIV_LMUL : thm
    val REAL_DIV_LMUL_CANCEL : thm
    val REAL_DIV_LZERO : thm
    val REAL_DIV_MUL2 : thm
    val REAL_DIV_OUTER_CANCEL : thm
    val REAL_DIV_OUTER_CANCEL2 : thm
    val REAL_DIV_OUTER_CANCEL3 : thm
    val REAL_DIV_REFL : thm
    val REAL_DIV_REFL2 : thm
    val REAL_DIV_REFL3 : thm
    val REAL_DIV_RMUL : thm
    val REAL_DIV_RMUL_CANCEL : thm
    val REAL_DOUBLE : thm
    val REAL_DOWN : thm
    val REAL_DOWN2 : thm
    val REAL_ENTIRE : thm
    val REAL_EQ_IMP_LE : thm
    val REAL_EQ_LADD : thm
    val REAL_EQ_LDIV_EQ : thm
    val REAL_EQ_LMUL : thm
    val REAL_EQ_LMUL2 : thm
    val REAL_EQ_LMUL_IMP : thm
    val REAL_EQ_MUL_LCANCEL : thm
    val REAL_EQ_NEG : thm
    val REAL_EQ_RADD : thm
    val REAL_EQ_RDIV_EQ : thm
    val REAL_EQ_RMUL : thm
    val REAL_EQ_RMUL_IMP : thm
    val REAL_EQ_SUB_LADD : thm
    val REAL_EQ_SUB_RADD : thm
    val REAL_FACT_NZ : thm
    val REAL_HALF_BETWEEN : thm
    val REAL_HALF_DOUBLE : thm
    val REAL_IMP_INF_LE : thm
    val REAL_IMP_LE_INF : thm
    val REAL_IMP_LE_SUP : thm
    val REAL_IMP_MAX_LE2 : thm
    val REAL_IMP_MIN_LE2 : thm
    val REAL_IMP_SUP_LE : thm
    val REAL_INF_CLOSE : thm
    val REAL_INF_LE : thm
    val REAL_INF_LT : thm
    val REAL_INF_MIN : thm
    val REAL_INJ : thm
    val REAL_INV1 : thm
    val REAL_INVINV : thm
    val REAL_INV_0 : thm
    val REAL_INV_1OVER : thm
    val REAL_INV_EQ_0 : thm
    val REAL_INV_INJ : thm
    val REAL_INV_INV : thm
    val REAL_INV_LT1 : thm
    val REAL_INV_LT_ANTIMONO : thm
    val REAL_INV_MUL : thm
    val REAL_INV_NZ : thm
    val REAL_INV_POS : thm
    val REAL_LDISTRIB : thm
    val REAL_LE : thm
    val REAL_LE1_POW2 : thm
    val REAL_LET_ADD : thm
    val REAL_LET_ADD2 : thm
    val REAL_LET_ANTISYM : thm
    val REAL_LET_TOTAL : thm
    val REAL_LET_TRANS : thm
    val REAL_LE_01 : thm
    val REAL_LE_ADD : thm
    val REAL_LE_ADD2 : thm
    val REAL_LE_ADDL : thm
    val REAL_LE_ADDR : thm
    val REAL_LE_ANTISYM : thm
    val REAL_LE_DIV : thm
    val REAL_LE_DOUBLE : thm
    val REAL_LE_EPSILON : thm
    val REAL_LE_INV : thm
    val REAL_LE_INV_EQ : thm
    val REAL_LE_LADD : thm
    val REAL_LE_LADD_IMP : thm
    val REAL_LE_LDIV : thm
    val REAL_LE_LDIV_EQ : thm
    val REAL_LE_LMUL : thm
    val REAL_LE_LMUL_IMP : thm
    val REAL_LE_LNEG : thm
    val REAL_LE_LT : thm
    val REAL_LE_MAX : thm
    val REAL_LE_MAX1 : thm
    val REAL_LE_MAX2 : thm
    val REAL_LE_MIN : thm
    val REAL_LE_MUL : thm
    val REAL_LE_MUL2 : thm
    val REAL_LE_NEG : thm
    val REAL_LE_NEG2 : thm
    val REAL_LE_NEGL : thm
    val REAL_LE_NEGR : thm
    val REAL_LE_NEGTOTAL : thm
    val REAL_LE_POW2 : thm
    val REAL_LE_RADD : thm
    val REAL_LE_RDIV : thm
    val REAL_LE_RDIV_EQ : thm
    val REAL_LE_REFL : thm
    val REAL_LE_RMUL : thm
    val REAL_LE_RMUL_IMP : thm
    val REAL_LE_RNEG : thm
    val REAL_LE_SQUARE : thm
    val REAL_LE_SUB_CANCEL2 : thm
    val REAL_LE_SUB_LADD : thm
    val REAL_LE_SUB_RADD : thm
    val REAL_LE_SUP : thm
    val REAL_LE_TOTAL : thm
    val REAL_LE_TRANS : thm
    val REAL_LINV_UNIQ : thm
    val REAL_LIN_LE_MAX : thm
    val REAL_LNEG_UNIQ : thm
    val REAL_LT : thm
    val REAL_LT1_POW2 : thm
    val REAL_LTE_ADD : thm
    val REAL_LTE_ADD2 : thm
    val REAL_LTE_ANTSYM : thm
    val REAL_LTE_TOTAL : thm
    val REAL_LTE_TRANS : thm
    val REAL_LT_01 : thm
    val REAL_LT_1 : thm
    val REAL_LT_ADD : thm
    val REAL_LT_ADD1 : thm
    val REAL_LT_ADD2 : thm
    val REAL_LT_ADDL : thm
    val REAL_LT_ADDNEG : thm
    val REAL_LT_ADDNEG2 : thm
    val REAL_LT_ADDR : thm
    val REAL_LT_ADD_SUB : thm
    val REAL_LT_ANTISYM : thm
    val REAL_LT_DIV : thm
    val REAL_LT_FRACTION : thm
    val REAL_LT_FRACTION_0 : thm
    val REAL_LT_GT : thm
    val REAL_LT_HALF1 : thm
    val REAL_LT_HALF2 : thm
    val REAL_LT_IADD : thm
    val REAL_LT_IMP_LE : thm
    val REAL_LT_IMP_NE : thm
    val REAL_LT_INV : thm
    val REAL_LT_INV_EQ : thm
    val REAL_LT_LADD : thm
    val REAL_LT_LDIV_EQ : thm
    val REAL_LT_LE : thm
    val REAL_LT_LMUL : thm
    val REAL_LT_LMUL_0 : thm
    val REAL_LT_LMUL_IMP : thm
    val REAL_LT_MUL : thm
    val REAL_LT_MUL2 : thm
    val REAL_LT_MULTIPLE : thm
    val REAL_LT_NEG : thm
    val REAL_LT_NEGTOTAL : thm
    val REAL_LT_NZ : thm
    val REAL_LT_RADD : thm
    val REAL_LT_RDIV : thm
    val REAL_LT_RDIV_0 : thm
    val REAL_LT_RDIV_EQ : thm
    val REAL_LT_REFL : thm
    val REAL_LT_RMUL : thm
    val REAL_LT_RMUL_0 : thm
    val REAL_LT_RMUL_IMP : thm
    val REAL_LT_SUB_LADD : thm
    val REAL_LT_SUB_RADD : thm
    val REAL_LT_TOTAL : thm
    val REAL_LT_TRANS : thm
    val REAL_MAX_ADD : thm
    val REAL_MAX_ALT : thm
    val REAL_MAX_LE : thm
    val REAL_MAX_MIN : thm
    val REAL_MAX_REFL : thm
    val REAL_MAX_SUB : thm
    val REAL_MEAN : thm
    val REAL_MIDDLE1 : thm
    val REAL_MIDDLE2 : thm
    val REAL_MIN_ADD : thm
    val REAL_MIN_ALT : thm
    val REAL_MIN_LE : thm
    val REAL_MIN_LE1 : thm
    val REAL_MIN_LE2 : thm
    val REAL_MIN_LE_LIN : thm
    val REAL_MIN_MAX : thm
    val REAL_MIN_REFL : thm
    val REAL_MIN_SUB : thm
    val REAL_MUL : thm
    val REAL_MUL_ASSOC : thm
    val REAL_MUL_COMM : thm
    val REAL_MUL_LID : thm
    val REAL_MUL_LINV : thm
    val REAL_MUL_LNEG : thm
    val REAL_MUL_LZERO : thm
    val REAL_MUL_RID : thm
    val REAL_MUL_RINV : thm
    val REAL_MUL_RNEG : thm
    val REAL_MUL_RZERO : thm
    val REAL_MUL_SUB1_CANCEL : thm
    val REAL_MUL_SUB2_CANCEL : thm
    val REAL_MUL_SYM : thm
    val REAL_NEGNEG : thm
    val REAL_NEG_0 : thm
    val REAL_NEG_ADD : thm
    val REAL_NEG_EQ : thm
    val REAL_NEG_EQ0 : thm
    val REAL_NEG_GE0 : thm
    val REAL_NEG_GT0 : thm
    val REAL_NEG_HALF : thm
    val REAL_NEG_INV : thm
    val REAL_NEG_LE0 : thm
    val REAL_NEG_LMUL : thm
    val REAL_NEG_LT0 : thm
    val REAL_NEG_MINUS1 : thm
    val REAL_NEG_MUL2 : thm
    val REAL_NEG_NEG : thm
    val REAL_NEG_RMUL : thm
    val REAL_NEG_SUB : thm
    val REAL_NEG_THIRD : thm
    val REAL_NOT_LE : thm
    val REAL_NOT_LT : thm
    val REAL_NZ_IMP_LT : thm
    val REAL_OF_NUM_ADD : thm
    val REAL_OF_NUM_EQ : thm
    val REAL_OF_NUM_LE : thm
    val REAL_OF_NUM_MUL : thm
    val REAL_OF_NUM_POW : thm
    val REAL_OF_NUM_SUC : thm
    val REAL_OVER1 : thm
    val REAL_POASQ : thm
    val REAL_POS : thm
    val REAL_POS_EQ_ZERO : thm
    val REAL_POS_ID : thm
    val REAL_POS_INFLATE : thm
    val REAL_POS_LE_ZERO : thm
    val REAL_POS_MONO : thm
    val REAL_POS_NZ : thm
    val REAL_POS_POS : thm
    val REAL_POW2_ABS : thm
    val REAL_POW_ADD : thm
    val REAL_POW_DIV : thm
    val REAL_POW_INV : thm
    val REAL_POW_LT : thm
    val REAL_POW_LT2 : thm
    val REAL_POW_MONO_LT : thm
    val REAL_POW_POW : thm
    val REAL_RDISTRIB : thm
    val REAL_RINV_UNIQ : thm
    val REAL_RNEG_UNIQ : thm
    val REAL_SUB : thm
    val REAL_SUB_0 : thm
    val REAL_SUB_ABS : thm
    val REAL_SUB_ADD : thm
    val REAL_SUB_ADD2 : thm
    val REAL_SUB_INV2 : thm
    val REAL_SUB_LDISTRIB : thm
    val REAL_SUB_LE : thm
    val REAL_SUB_LNEG : thm
    val REAL_SUB_LT : thm
    val REAL_SUB_LZERO : thm
    val REAL_SUB_NEG2 : thm
    val REAL_SUB_RAT : thm
    val REAL_SUB_RDISTRIB : thm
    val REAL_SUB_REFL : thm
    val REAL_SUB_RNEG : thm
    val REAL_SUB_RZERO : thm
    val REAL_SUB_SUB : thm
    val REAL_SUB_SUB2 : thm
    val REAL_SUB_TRIANGLE : thm
    val REAL_SUMSQ : thm
    val REAL_SUP : thm
    val REAL_SUP_ALLPOS : thm
    val REAL_SUP_CONST : thm
    val REAL_SUP_EXISTS : thm
    val REAL_SUP_EXISTS_UNIQUE : thm
    val REAL_SUP_LE : thm
    val REAL_SUP_MAX : thm
    val REAL_SUP_SOMEPOS : thm
    val REAL_SUP_UBOUND : thm
    val REAL_SUP_UBOUND_LE : thm
    val REAL_THIRDS_BETWEEN : thm
    val SETOK_LE_LT : thm
    val SUM_0 : thm
    val SUM_1 : thm
    val SUM_2 : thm
    val SUM_ABS : thm
    val SUM_ABS_LE : thm
    val SUM_ADD : thm
    val SUM_BOUND : thm
    val SUM_CANCEL : thm
    val SUM_CMUL : thm
    val SUM_DIFF : thm
    val SUM_EQ : thm
    val SUM_GROUP : thm
    val SUM_LE : thm
    val SUM_NEG : thm
    val SUM_NSUB : thm
    val SUM_OFFSET : thm
    val SUM_PERMUTE_0 : thm
    val SUM_POS : thm
    val SUM_POS_GEN : thm
    val SUM_REINDEX : thm
    val SUM_SUB : thm
    val SUM_SUBST : thm
    val SUM_TWO : thm
    val SUM_ZERO : thm
    val SUP_EPSILON : thm
    val SUP_LEMMA1 : thm
    val SUP_LEMMA2 : thm
    val SUP_LEMMA3 : thm
    val add_ints : thm
    val add_rat : thm
    val add_ratl : thm
    val add_ratr : thm
    val div_rat : thm
    val div_ratl : thm
    val div_ratr : thm
    val eq_ints : thm
    val eq_rat : thm
    val eq_ratl : thm
    val eq_ratr : thm
    val le_int : thm
    val le_rat : thm
    val le_ratl : thm
    val le_ratr : thm
    val lt_int : thm
    val lt_rat : thm
    val lt_ratl : thm
    val lt_ratr : thm
    val mult_ints : thm
    val mult_rat : thm
    val mult_ratl : thm
    val mult_ratr : thm
    val neg_rat : thm
    val pow_rat : thm
    val real_lt : thm
    val sum : thm
  
  val real_grammars : type_grammar.grammar * term_grammar.grammar
  
  val real_rwts : simpLib.ssfrag
(*
   [realax] Parent theory of "real"
   
   [NUM_CEILING_def]  Definition
      
      |- !x. clg x = LEAST n. x <= &n
   
   [NUM_FLOOR_def]  Definition
      
      |- !x. flr x = LEAST n. &(n + 1) > x
   
   [SUM_DEF]  Definition
      
      |- !m n f. sum (m,n) f = sumc m n f
   
   [abs]  Definition
      
      |- !x. abs x = if 0 <= x then x else -x
   
   [inf_def]  Definition
      
      |- !p. inf p = -sup (\r. p (-r))
   
   [max_def]  Definition
      
      |- !x y. max x y = if x <= y then y else x
   
   [min_def]  Definition
      
      |- !x y. min x y = if x <= y then x else y
   
   [pos_def]  Definition
      
      |- !x. pos x = if 0 <= x then x else 0
   
   [pow]  Definition
      
      |- (!x. x pow 0 = 1) /\ !x n. x pow SUC n = x * x pow n
   
   [real_div]  Definition
      
      |- !x y. x / y = x * inv y
   
   [real_ge]  Definition
      
      |- !x y. x >= y <=> y <= x
   
   [real_gt]  Definition
      
      |- !x y. x > y <=> y < x
   
   [real_lte]  Definition
      
      |- !x y. x <= y <=> ~(y < x)
   
   [real_of_num]  Definition
      
      |- (0 = real_0) /\ !n. &SUC n = &n + real_1
   
   [real_sub]  Definition
      
      |- !x y. x - y = x + -y
   
   [sumc]  Definition
      
      |- (!n f. sumc n 0 f = 0) /\
         !n m f. sumc n (SUC m) f = sumc n m f + f (n + m)
   
   [sup]  Definition
      
      |- !P. sup P = @s. !y. (?x. P x /\ y < x) <=> y < s
   
   [ABS_0]  Theorem
      
      |- abs 0 = 0
   
   [ABS_1]  Theorem
      
      |- abs 1 = 1
   
   [ABS_ABS]  Theorem
      
      |- !x. abs (abs x) = abs x
   
   [ABS_BETWEEN]  Theorem
      
      |- !x y d. 0 < d /\ x - d < y /\ y < x + d <=> abs (y - x) < d
   
   [ABS_BETWEEN1]  Theorem
      
      |- !x y z. x < z /\ abs (y - x) < z - x ==> y < z
   
   [ABS_BETWEEN2]  Theorem
      
      |- !x0 x y0 y.
           x0 < y0 /\ abs (x - x0) < (y0 - x0) / 2 /\
           abs (y - y0) < (y0 - x0) / 2 ==>
           x < y
   
   [ABS_BOUND]  Theorem
      
      |- !x y d. abs (x - y) < d ==> y < x + d
   
   [ABS_BOUNDS]  Theorem
      
      |- !x k. abs x <= k <=> -k <= x /\ x <= k
   
   [ABS_CASES]  Theorem
      
      |- !x. (x = 0) \/ 0 < abs x
   
   [ABS_CIRCLE]  Theorem
      
      |- !x y h. abs h < abs y - abs x ==> abs (x + h) < abs y
   
   [ABS_DIV]  Theorem
      
      |- !y. y <> 0 ==> !x. abs (x / y) = abs x / abs y
   
   [ABS_INV]  Theorem
      
      |- !x. x <> 0 ==> (abs (inv x) = inv (abs x))
   
   [ABS_LE]  Theorem
      
      |- !x. x <= abs x
   
   [ABS_LT_MUL2]  Theorem
      
      |- !w x y z. abs w < y /\ abs x < z ==> abs (w * x) < y * z
   
   [ABS_MUL]  Theorem
      
      |- !x y. abs (x * y) = abs x * abs y
   
   [ABS_N]  Theorem
      
      |- !n. abs (&n) = &n
   
   [ABS_NEG]  Theorem
      
      |- !x. abs (-x) = abs x
   
   [ABS_NZ]  Theorem
      
      |- !x. x <> 0 <=> 0 < abs x
   
   [ABS_POS]  Theorem
      
      |- !x. 0 <= abs x
   
   [ABS_POW2]  Theorem
      
      |- !x. abs (x pow 2) = x pow 2
   
   [ABS_REFL]  Theorem
      
      |- !x. (abs x = x) <=> 0 <= x
   
   [ABS_SIGN]  Theorem
      
      |- !x y. abs (x - y) < y ==> 0 < x
   
   [ABS_SIGN2]  Theorem
      
      |- !x y. abs (x - y) < -y ==> x < 0
   
   [ABS_STILLNZ]  Theorem
      
      |- !x y. abs (x - y) < abs y ==> x <> 0
   
   [ABS_SUB]  Theorem
      
      |- !x y. abs (x - y) = abs (y - x)
   
   [ABS_SUB_ABS]  Theorem
      
      |- !x y. abs (abs x - abs y) <= abs (x - y)
   
   [ABS_SUM]  Theorem
      
      |- !f m n. abs (sum (m,n) f) <= sum (m,n) (\n. abs (f n))
   
   [ABS_TRIANGLE]  Theorem
      
      |- !x y. abs (x + y) <= abs x + abs y
   
   [ABS_ZERO]  Theorem
      
      |- !x. (abs x = 0) <=> (x = 0)
   
   [LE_NUM_CEILING]  Theorem
      
      |- !x. x <= &clg x
   
   [NUM_CEILING_LE]  Theorem
      
      |- !x n. x <= &n ==> clg x <= n
   
   [NUM_FLOOR_DIV]  Theorem
      
      |- 0 <= x /\ 0 < y ==> &flr (x / y) * y <= x
   
   [NUM_FLOOR_DIV_LOWERBOUND]  Theorem
      
      |- 0 <= x /\ 0 < y ==> x < &(flr (x / y) + 1) * y
   
   [NUM_FLOOR_EQNS]  Theorem
      
      |- (flr (&n) = n) /\ (0 < m ==> (flr (&n / &m) = n DIV m))
   
   [NUM_FLOOR_LE]  Theorem
      
      |- 0 <= x ==> &flr x <= x
   
   [NUM_FLOOR_LE2]  Theorem
      
      |- 0 <= y ==> (x <= flr y <=> &x <= y)
   
   [NUM_FLOOR_LET]  Theorem
      
      |- flr x <= y <=> x < &y + 1
   
   [NUM_FLOOR_LOWER_BOUND]  Theorem
      
      |- x < &n <=> flr (x + 1) <= n
   
   [NUM_FLOOR_upper_bound]  Theorem
      
      |- &n <= x <=> n < flr (x + 1)
   
   [POW_0]  Theorem
      
      |- !n. 0 pow SUC n = 0
   
   [POW_1]  Theorem
      
      |- !x. x pow 1 = x
   
   [POW_2]  Theorem
      
      |- !x. x pow 2 = x * x
   
   [POW_2_LE1]  Theorem
      
      |- !n. 1 <= 2 pow n
   
   [POW_2_LT]  Theorem
      
      |- !n. &n < 2 pow n
   
   [POW_ABS]  Theorem
      
      |- !c n. abs c pow n = abs (c pow n)
   
   [POW_ADD]  Theorem
      
      |- !c m n. c pow (m + n) = c pow m * c pow n
   
   [POW_EQ]  Theorem
      
      |- !n x y.
           0 <= x /\ 0 <= y /\ (x pow SUC n = y pow SUC n) ==> (x = y)
   
   [POW_INV]  Theorem
      
      |- !c. c <> 0 ==> !n. inv (c pow n) = inv c pow n
   
   [POW_LE]  Theorem
      
      |- !n x y. 0 <= x /\ x <= y ==> x pow n <= y pow n
   
   [POW_LT]  Theorem
      
      |- !n x y. 0 <= x /\ x < y ==> x pow SUC n < y pow SUC n
   
   [POW_M1]  Theorem
      
      |- !n. abs (-1 pow n) = 1
   
   [POW_MINUS1]  Theorem
      
      |- !n. -1 pow (2 * n) = 1
   
   [POW_MUL]  Theorem
      
      |- !n x y. (x * y) pow n = x pow n * y pow n
   
   [POW_NZ]  Theorem
      
      |- !c n. c <> 0 ==> c pow n <> 0
   
   [POW_ONE]  Theorem
      
      |- !n. 1 pow n = 1
   
   [POW_PLUS1]  Theorem
      
      |- !e. 0 < e ==> !n. 1 + &n * e <= (1 + e) pow n
   
   [POW_POS]  Theorem
      
      |- !x. 0 <= x ==> !n. 0 <= x pow n
   
   [POW_POS_LT]  Theorem
      
      |- !x n. 0 < x ==> 0 < x pow SUC n
   
   [POW_ZERO]  Theorem
      
      |- !n x. (x pow n = 0) ==> (x = 0)
   
   [POW_ZERO_EQ]  Theorem
      
      |- !n x. (x pow SUC n = 0) <=> (x = 0)
   
   [REAL]  Theorem
      
      |- !n. &SUC n = &n + 1
   
   [REAL_0]  Theorem
      
      |- real_0 = 0
   
   [REAL_1]  Theorem
      
      |- real_1 = 1
   
   [REAL_10]  Theorem
      
      |- 1 <> 0
   
   [REAL_ABS_0]  Theorem
      
      |- abs 0 = 0
   
   [REAL_ABS_MUL]  Theorem
      
      |- !x y. abs (x * y) = abs x * abs y
   
   [REAL_ABS_POS]  Theorem
      
      |- !x. 0 <= abs x
   
   [REAL_ABS_TRIANGLE]  Theorem
      
      |- !x y. abs (x + y) <= abs x + abs y
   
   [REAL_ADD]  Theorem
      
      |- !m n. &m + &n = &(m + n)
   
   [REAL_ADD2_SUB2]  Theorem
      
      |- !a b c d. a + b - (c + d) = a - c + (b - d)
   
   [REAL_ADD_ASSOC]  Theorem
      
      |- !x y z. x + (y + z) = x + y + z
   
   [REAL_ADD_COMM]  Theorem
      
      |- !x y. x + y = y + x
   
   [REAL_ADD_LDISTRIB]  Theorem
      
      |- !x y z. x * (y + z) = x * y + x * z
   
   [REAL_ADD_LID]  Theorem
      
      |- !x. 0 + x = x
   
   [REAL_ADD_LID_UNIQ]  Theorem
      
      |- !x y. (x + y = y) <=> (x = 0)
   
   [REAL_ADD_LINV]  Theorem
      
      |- !x. -x + x = 0
   
   [REAL_ADD_RAT]  Theorem
      
      |- !a b c d.
           b <> 0 /\ d <> 0 ==> (a / b + c / d = (a * d + b * c) / (b * d))
   
   [REAL_ADD_RDISTRIB]  Theorem
      
      |- !x y z. (x + y) * z = x * z + y * z
   
   [REAL_ADD_RID]  Theorem
      
      |- !x. x + 0 = x
   
   [REAL_ADD_RID_UNIQ]  Theorem
      
      |- !x y. (x + y = x) <=> (y = 0)
   
   [REAL_ADD_RINV]  Theorem
      
      |- !x. x + -x = 0
   
   [REAL_ADD_SUB]  Theorem
      
      |- !x y. x + y - x = y
   
   [REAL_ADD_SUB2]  Theorem
      
      |- !x y. x - (x + y) = -y
   
   [REAL_ADD_SUB_ALT]  Theorem
      
      |- !x y. x + y - y = x
   
   [REAL_ADD_SYM]  Theorem
      
      |- !x y. x + y = y + x
   
   [REAL_ARCH]  Theorem
      
      |- !x. 0 < x ==> !y. ?n. y < &n * x
   
   [REAL_ARCH_LEAST]  Theorem
      
      |- !y. 0 < y ==> !x. 0 <= x ==> ?n. &n * y <= x /\ x < &SUC n * y
   
   [REAL_BIGNUM]  Theorem
      
      |- !r. ?n. r < &n
   
   [REAL_DIFFSQ]  Theorem
      
      |- !x y. (x + y) * (x - y) = x * x - y * y
   
   [REAL_DIV_ADD]  Theorem
      
      |- !x y z. y / x + z / x = (y + z) / x
   
   [REAL_DIV_DENOM_CANCEL]  Theorem
      
      |- !x y z. x <> 0 ==> (y / x / (z / x) = y / z)
   
   [REAL_DIV_DENOM_CANCEL2]  Theorem
      
      |- !y z. y / 2 / (z / 2) = y / z
   
   [REAL_DIV_DENOM_CANCEL3]  Theorem
      
      |- !y z. y / 3 / (z / 3) = y / z
   
   [REAL_DIV_INNER_CANCEL]  Theorem
      
      |- !x y z. x <> 0 ==> (y / x * (x / z) = y / z)
   
   [REAL_DIV_INNER_CANCEL2]  Theorem
      
      |- !y z. y / 2 * (2 / z) = y / z
   
   [REAL_DIV_INNER_CANCEL3]  Theorem
      
      |- !y z. y / 3 * (3 / z) = y / z
   
   [REAL_DIV_LMUL]  Theorem
      
      |- !x y. y <> 0 ==> (y * (x / y) = x)
   
   [REAL_DIV_LMUL_CANCEL]  Theorem
      
      |- !c a b. c <> 0 ==> (c * a / (c * b) = a / b)
   
   [REAL_DIV_LZERO]  Theorem
      
      |- !x. 0 / x = 0
   
   [REAL_DIV_MUL2]  Theorem
      
      |- !x z. x <> 0 /\ z <> 0 ==> !y. y / z = x * y / (x * z)
   
   [REAL_DIV_OUTER_CANCEL]  Theorem
      
      |- !x y z. x <> 0 ==> (x / y * (z / x) = z / y)
   
   [REAL_DIV_OUTER_CANCEL2]  Theorem
      
      |- !y z. 2 / y * (z / 2) = z / y
   
   [REAL_DIV_OUTER_CANCEL3]  Theorem
      
      |- !y z. 3 / y * (z / 3) = z / y
   
   [REAL_DIV_REFL]  Theorem
      
      |- !x. x <> 0 ==> (x / x = 1)
   
   [REAL_DIV_REFL2]  Theorem
      
      |- 2 / 2 = 1
   
   [REAL_DIV_REFL3]  Theorem
      
      |- 3 / 3 = 1
   
   [REAL_DIV_RMUL]  Theorem
      
      |- !x y. y <> 0 ==> (x / y * y = x)
   
   [REAL_DIV_RMUL_CANCEL]  Theorem
      
      |- !c a b. c <> 0 ==> (a * c / (b * c) = a / b)
   
   [REAL_DOUBLE]  Theorem
      
      |- !x. x + x = 2 * x
   
   [REAL_DOWN]  Theorem
      
      |- !x. 0 < x ==> ?y. 0 < y /\ y < x
   
   [REAL_DOWN2]  Theorem
      
      |- !x y. 0 < x /\ 0 < y ==> ?z. 0 < z /\ z < x /\ z < y
   
   [REAL_ENTIRE]  Theorem
      
      |- !x y. (x * y = 0) <=> (x = 0) \/ (y = 0)
   
   [REAL_EQ_IMP_LE]  Theorem
      
      |- !x y. (x = y) ==> x <= y
   
   [REAL_EQ_LADD]  Theorem
      
      |- !x y z. (x + y = x + z) <=> (y = z)
   
   [REAL_EQ_LDIV_EQ]  Theorem
      
      |- !x y z. 0 < z ==> ((x / z = y) <=> (x = y * z))
   
   [REAL_EQ_LMUL]  Theorem
      
      |- !x y z. (x * y = x * z) <=> (x = 0) \/ (y = z)
   
   [REAL_EQ_LMUL2]  Theorem
      
      |- !x y z. x <> 0 ==> ((y = z) <=> (x * y = x * z))
   
   [REAL_EQ_LMUL_IMP]  Theorem
      
      |- !x y z. x <> 0 /\ (x * y = x * z) ==> (y = z)
   
   [REAL_EQ_MUL_LCANCEL]  Theorem
      
      |- !x y z. (x * y = x * z) <=> (x = 0) \/ (y = z)
   
   [REAL_EQ_NEG]  Theorem
      
      |- !x y. (-x = -y) <=> (x = y)
   
   [REAL_EQ_RADD]  Theorem
      
      |- !x y z. (x + z = y + z) <=> (x = y)
   
   [REAL_EQ_RDIV_EQ]  Theorem
      
      |- !x y z. 0 < z ==> ((x = y / z) <=> (x * z = y))
   
   [REAL_EQ_RMUL]  Theorem
      
      |- !x y z. (x * z = y * z) <=> (z = 0) \/ (x = y)
   
   [REAL_EQ_RMUL_IMP]  Theorem
      
      |- !x y z. z <> 0 /\ (x * z = y * z) ==> (x = y)
   
   [REAL_EQ_SUB_LADD]  Theorem
      
      |- !x y z. (x = y - z) <=> (x + z = y)
   
   [REAL_EQ_SUB_RADD]  Theorem
      
      |- !x y z. (x - y = z) <=> (x = z + y)
   
   [REAL_FACT_NZ]  Theorem
      
      |- !n. &FACT n <> 0
   
   [REAL_HALF_BETWEEN]  Theorem
      
      |- (0 < 1 / 2 /\ 1 / 2 < 1) /\ 0 <= 1 / 2 /\ 1 / 2 <= 1
   
   [REAL_HALF_DOUBLE]  Theorem
      
      |- !x. x / 2 + x / 2 = x
   
   [REAL_IMP_INF_LE]  Theorem
      
      |- !p r.
           (?z. !x. p x ==> z <= x) /\ (?x. p x /\ x <= r) ==> inf p <= r
   
   [REAL_IMP_LE_INF]  Theorem
      
      |- !p r. (?x. p x) /\ (!x. p x ==> r <= x) ==> r <= inf p
   
   [REAL_IMP_LE_SUP]  Theorem
      
      |- !p x.
           (?r. p r) /\ (?z. !r. p r ==> r <= z) /\ (?r. p r /\ x <= r) ==>
           x <= sup p
   
   [REAL_IMP_MAX_LE2]  Theorem
      
      |- !x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> max x1 x2 <= max y1 y2
   
   [REAL_IMP_MIN_LE2]  Theorem
      
      |- !x1 x2 y1 y2. x1 <= y1 /\ x2 <= y2 ==> min x1 x2 <= min y1 y2
   
   [REAL_IMP_SUP_LE]  Theorem
      
      |- !p x. (?r. p r) /\ (!r. p r ==> r <= x) ==> sup p <= x
   
   [REAL_INF_CLOSE]  Theorem
      
      |- !p e. (?x. p x) /\ 0 < e ==> ?x. p x /\ x < inf p + e
   
   [REAL_INF_LE]  Theorem
      
      |- !p x.
           (?y. p y) /\ (?y. !z. p z ==> y <= z) ==>
           (inf p <= x <=> !y. (!z. p z ==> y <= z) ==> y <= x)
   
   [REAL_INF_LT]  Theorem
      
      |- !p z. (?x. p x) /\ inf p < z ==> ?x. p x /\ x < z
   
   [REAL_INF_MIN]  Theorem
      
      |- !p z. p z /\ (!x. p x ==> z <= x) ==> (inf p = z)
   
   [REAL_INJ]  Theorem
      
      |- !m n. (&m = &n) <=> (m = n)
   
   [REAL_INV1]  Theorem
      
      |- inv 1 = 1
   
   [REAL_INVINV]  Theorem
      
      |- !x. x <> 0 ==> (inv (inv x) = x)
   
   [REAL_INV_0]  Theorem
      
      |- inv 0 = 0
   
   [REAL_INV_1OVER]  Theorem
      
      |- !x. inv x = 1 / x
   
   [REAL_INV_EQ_0]  Theorem
      
      |- !x. (inv x = 0) <=> (x = 0)
   
   [REAL_INV_INJ]  Theorem
      
      |- !x y. (inv x = inv y) <=> (x = y)
   
   [REAL_INV_INV]  Theorem
      
      |- !x. inv (inv x) = x
   
   [REAL_INV_LT1]  Theorem
      
      |- !x. 0 < x /\ x < 1 ==> 1 < inv x
   
   [REAL_INV_LT_ANTIMONO]  Theorem
      
      |- !x y. 0 < x /\ 0 < y ==> (inv x < inv y <=> y < x)
   
   [REAL_INV_MUL]  Theorem
      
      |- !x y. x <> 0 /\ y <> 0 ==> (inv (x * y) = inv x * inv y)
   
   [REAL_INV_NZ]  Theorem
      
      |- !x. x <> 0 ==> inv x <> 0
   
   [REAL_INV_POS]  Theorem
      
      |- !x. 0 < x ==> 0 < inv x
   
   [REAL_LDISTRIB]  Theorem
      
      |- !x y z. x * (y + z) = x * y + x * z
   
   [REAL_LE]  Theorem
      
      |- !m n. &m <= &n <=> m <= n
   
   [REAL_LE1_POW2]  Theorem
      
      |- !x. 1 <= x ==> 1 <= x pow 2
   
   [REAL_LET_ADD]  Theorem
      
      |- !x y. 0 <= x /\ 0 < y ==> 0 < x + y
   
   [REAL_LET_ADD2]  Theorem
      
      |- !w x y z. w <= x /\ y < z ==> w + y < x + z
   
   [REAL_LET_ANTISYM]  Theorem
      
      |- !x y. ~(x < y /\ y <= x)
   
   [REAL_LET_TOTAL]  Theorem
      
      |- !x y. x <= y \/ y < x
   
   [REAL_LET_TRANS]  Theorem
      
      |- !x y z. x <= y /\ y < z ==> x < z
   
   [REAL_LE_01]  Theorem
      
      |- 0 <= 1
   
   [REAL_LE_ADD]  Theorem
      
      |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x + y
   
   [REAL_LE_ADD2]  Theorem
      
      |- !w x y z. w <= x /\ y <= z ==> w + y <= x + z
   
   [REAL_LE_ADDL]  Theorem
      
      |- !x y. y <= x + y <=> 0 <= x
   
   [REAL_LE_ADDR]  Theorem
      
      |- !x y. x <= x + y <=> 0 <= y
   
   [REAL_LE_ANTISYM]  Theorem
      
      |- !x y. x <= y /\ y <= x <=> (x = y)
   
   [REAL_LE_DIV]  Theorem
      
      |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x / y
   
   [REAL_LE_DOUBLE]  Theorem
      
      |- !x. 0 <= x + x <=> 0 <= x
   
   [REAL_LE_EPSILON]  Theorem
      
      |- !x y. (!e. 0 < e ==> x <= y + e) ==> x <= y
   
   [REAL_LE_INV]  Theorem
      
      |- !x. 0 <= x ==> 0 <= inv x
   
   [REAL_LE_INV_EQ]  Theorem
      
      |- !x. 0 <= inv x <=> 0 <= x
   
   [REAL_LE_LADD]  Theorem
      
      |- !x y z. x + y <= x + z <=> y <= z
   
   [REAL_LE_LADD_IMP]  Theorem
      
      |- !x y z. y <= z ==> x + y <= x + z
   
   [REAL_LE_LDIV]  Theorem
      
      |- !x y z. 0 < x /\ y <= z * x ==> y / x <= z
   
   [REAL_LE_LDIV_EQ]  Theorem
      
      |- !x y z. 0 < z ==> (x / z <= y <=> x <= y * z)
   
   [REAL_LE_LMUL]  Theorem
      
      |- !x y z. 0 < x ==> (x * y <= x * z <=> y <= z)
   
   [REAL_LE_LMUL_IMP]  Theorem
      
      |- !x y z. 0 <= x /\ y <= z ==> x * y <= x * z
   
   [REAL_LE_LNEG]  Theorem
      
      |- !x y. -x <= y <=> 0 <= x + y
   
   [REAL_LE_LT]  Theorem
      
      |- !x y. x <= y <=> x < y \/ (x = y)
   
   [REAL_LE_MAX]  Theorem
      
      |- !z x y. z <= max x y <=> z <= x \/ z <= y
   
   [REAL_LE_MAX1]  Theorem
      
      |- !x y. x <= max x y
   
   [REAL_LE_MAX2]  Theorem
      
      |- !x y. y <= max x y
   
   [REAL_LE_MIN]  Theorem
      
      |- !z x y. z <= min x y <=> z <= x /\ z <= y
   
   [REAL_LE_MUL]  Theorem
      
      |- !x y. 0 <= x /\ 0 <= y ==> 0 <= x * y
   
   [REAL_LE_MUL2]  Theorem
      
      |- !x1 x2 y1 y2.
           0 <= x1 /\ 0 <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
           x1 * y1 <= x2 * y2
   
   [REAL_LE_NEG]  Theorem
      
      |- !x y. -x <= -y <=> y <= x
   
   [REAL_LE_NEG2]  Theorem
      
      |- !x y. -x <= -y <=> y <= x
   
   [REAL_LE_NEGL]  Theorem
      
      |- !x. -x <= x <=> 0 <= x
   
   [REAL_LE_NEGR]  Theorem
      
      |- !x. x <= -x <=> x <= 0
   
   [REAL_LE_NEGTOTAL]  Theorem
      
      |- !x. 0 <= x \/ 0 <= -x
   
   [REAL_LE_POW2]  Theorem
      
      |- !x. 0 <= x pow 2
   
   [REAL_LE_RADD]  Theorem
      
      |- !x y z. x + z <= y + z <=> x <= y
   
   [REAL_LE_RDIV]  Theorem
      
      |- !x y z. 0 < x /\ y * x <= z ==> y <= z / x
   
   [REAL_LE_RDIV_EQ]  Theorem
      
      |- !x y z. 0 < z ==> (x <= y / z <=> x * z <= y)
   
   [REAL_LE_REFL]  Theorem
      
      |- !x. x <= x
   
   [REAL_LE_RMUL]  Theorem
      
      |- !x y z. 0 < z ==> (x * z <= y * z <=> x <= y)
   
   [REAL_LE_RMUL_IMP]  Theorem
      
      |- !x y z. 0 <= x /\ y <= z ==> y * x <= z * x
   
   [REAL_LE_RNEG]  Theorem
      
      |- !x y. x <= -y <=> x + y <= 0
   
   [REAL_LE_SQUARE]  Theorem
      
      |- !x. 0 <= x * x
   
   [REAL_LE_SUB_CANCEL2]  Theorem
      
      |- !x y z. x - z <= y - z <=> x <= y
   
   [REAL_LE_SUB_LADD]  Theorem
      
      |- !x y z. x <= y - z <=> x + z <= y
   
   [REAL_LE_SUB_RADD]  Theorem
      
      |- !x y z. x - y <= z <=> x <= z + y
   
   [REAL_LE_SUP]  Theorem
      
      |- !p x.
           (?y. p y) /\ (?y. !z. p z ==> z <= y) ==>
           (x <= sup p <=> !y. (!z. p z ==> z <= y) ==> x <= y)
   
   [REAL_LE_TOTAL]  Theorem
      
      |- !x y. x <= y \/ y <= x
   
   [REAL_LE_TRANS]  Theorem
      
      |- !x y z. x <= y /\ y <= z ==> x <= z
   
   [REAL_LINV_UNIQ]  Theorem
      
      |- !x y. (x * y = 1) ==> (x = inv y)
   
   [REAL_LIN_LE_MAX]  Theorem
      
      |- !z x y. 0 <= z /\ z <= 1 ==> z * x + (1 - z) * y <= max x y
   
   [REAL_LNEG_UNIQ]  Theorem
      
      |- !x y. (x + y = 0) <=> (x = -y)
   
   [REAL_LT]  Theorem
      
      |- !m n. &m < &n <=> m < n
   
   [REAL_LT1_POW2]  Theorem
      
      |- !x. 1 < x ==> 1 < x pow 2
   
   [REAL_LTE_ADD]  Theorem
      
      |- !x y. 0 < x /\ 0 <= y ==> 0 < x + y
   
   [REAL_LTE_ADD2]  Theorem
      
      |- !w x y z. w < x /\ y <= z ==> w + y < x + z
   
   [REAL_LTE_ANTSYM]  Theorem
      
      |- !x y. ~(x <= y /\ y < x)
   
   [REAL_LTE_TOTAL]  Theorem
      
      |- !x y. x < y \/ y <= x
   
   [REAL_LTE_TRANS]  Theorem
      
      |- !x y z. x < y /\ y <= z ==> x < z
   
   [REAL_LT_01]  Theorem
      
      |- 0 < 1
   
   [REAL_LT_1]  Theorem
      
      |- !x y. 0 <= x /\ x < y ==> x / y < 1
   
   [REAL_LT_ADD]  Theorem
      
      |- !x y. 0 < x /\ 0 < y ==> 0 < x + y
   
   [REAL_LT_ADD1]  Theorem
      
      |- !x y. x <= y ==> x < y + 1
   
   [REAL_LT_ADD2]  Theorem
      
      |- !w x y z. w < x /\ y < z ==> w + y < x + z
   
   [REAL_LT_ADDL]  Theorem
      
      |- !x y. y < x + y <=> 0 < x
   
   [REAL_LT_ADDNEG]  Theorem
      
      |- !x y z. y < x + -z <=> y + z < x
   
   [REAL_LT_ADDNEG2]  Theorem
      
      |- !x y z. x + -y < z <=> x < z + y
   
   [REAL_LT_ADDR]  Theorem
      
      |- !x y. x < x + y <=> 0 < y
   
   [REAL_LT_ADD_SUB]  Theorem
      
      |- !x y z. x + y < z <=> x < z - y
   
   [REAL_LT_ANTISYM]  Theorem
      
      |- !x y. ~(x < y /\ y < x)
   
   [REAL_LT_DIV]  Theorem
      
      |- !x y. 0 < x /\ 0 < y ==> 0 < x / y
   
   [REAL_LT_FRACTION]  Theorem
      
      |- !n d. 1 < n ==> (d / &n < d <=> 0 < d)
   
   [REAL_LT_FRACTION_0]  Theorem
      
      |- !n d. n <> 0 ==> (0 < d / &n <=> 0 < d)
   
   [REAL_LT_GT]  Theorem
      
      |- !x y. x < y ==> ~(y < x)
   
   [REAL_LT_HALF1]  Theorem
      
      |- !d. 0 < d / 2 <=> 0 < d
   
   [REAL_LT_HALF2]  Theorem
      
      |- !d. d / 2 < d <=> 0 < d
   
   [REAL_LT_IADD]  Theorem
      
      |- !x y z. y < z ==> x + y < x + z
   
   [REAL_LT_IMP_LE]  Theorem
      
      |- !x y. x < y ==> x <= y
   
   [REAL_LT_IMP_NE]  Theorem
      
      |- !x y. x < y ==> x <> y
   
   [REAL_LT_INV]  Theorem
      
      |- !x y. 0 < x /\ x < y ==> inv y < inv x
   
   [REAL_LT_INV_EQ]  Theorem
      
      |- !x. 0 < inv x <=> 0 < x
   
   [REAL_LT_LADD]  Theorem
      
      |- !x y z. x + y < x + z <=> y < z
   
   [REAL_LT_LDIV_EQ]  Theorem
      
      |- !x y z. 0 < z ==> (x / z < y <=> x < y * z)
   
   [REAL_LT_LE]  Theorem
      
      |- !x y. x < y <=> x <= y /\ x <> y
   
   [REAL_LT_LMUL]  Theorem
      
      |- !x y z. 0 < x ==> (x * y < x * z <=> y < z)
   
   [REAL_LT_LMUL_0]  Theorem
      
      |- !x y. 0 < x ==> (0 < x * y <=> 0 < y)
   
   [REAL_LT_LMUL_IMP]  Theorem
      
      |- !x y z. y < z /\ 0 < x ==> x * y < x * z
   
   [REAL_LT_MUL]  Theorem
      
      |- !x y. 0 < x /\ 0 < y ==> 0 < x * y
   
   [REAL_LT_MUL2]  Theorem
      
      |- !x1 x2 y1 y2.
           0 <= x1 /\ 0 <= y1 /\ x1 < x2 /\ y1 < y2 ==> x1 * y1 < x2 * y2
   
   [REAL_LT_MULTIPLE]  Theorem
      
      |- !n d. 1 < n ==> (d < &n * d <=> 0 < d)
   
   [REAL_LT_NEG]  Theorem
      
      |- !x y. -x < -y <=> y < x
   
   [REAL_LT_NEGTOTAL]  Theorem
      
      |- !x. (x = 0) \/ 0 < x \/ 0 < -x
   
   [REAL_LT_NZ]  Theorem
      
      |- !n. &n <> 0 <=> 0 < &n
   
   [REAL_LT_RADD]  Theorem
      
      |- !x y z. x + z < y + z <=> x < y
   
   [REAL_LT_RDIV]  Theorem
      
      |- !x y z. 0 < z ==> (x / z < y / z <=> x < y)
   
   [REAL_LT_RDIV_0]  Theorem
      
      |- !y z. 0 < z ==> (0 < y / z <=> 0 < y)
   
   [REAL_LT_RDIV_EQ]  Theorem
      
      |- !x y z. 0 < z ==> (x < y / z <=> x * z < y)
   
   [REAL_LT_REFL]  Theorem
      
      |- !x. ~(x < x)
   
   [REAL_LT_RMUL]  Theorem
      
      |- !x y z. 0 < z ==> (x * z < y * z <=> x < y)
   
   [REAL_LT_RMUL_0]  Theorem
      
      |- !x y. 0 < y ==> (0 < x * y <=> 0 < x)
   
   [REAL_LT_RMUL_IMP]  Theorem
      
      |- !x y z. x < y /\ 0 < z ==> x * z < y * z
   
   [REAL_LT_SUB_LADD]  Theorem
      
      |- !x y z. x < y - z <=> x + z < y
   
   [REAL_LT_SUB_RADD]  Theorem
      
      |- !x y z. x - y < z <=> x < z + y
   
   [REAL_LT_TOTAL]  Theorem
      
      |- !x y. (x = y) \/ x < y \/ y < x
   
   [REAL_LT_TRANS]  Theorem
      
      |- !x y z. x < y /\ y < z ==> x < z
   
   [REAL_MAX_ADD]  Theorem
      
      |- !z x y. max (x + z) (y + z) = max x y + z
   
   [REAL_MAX_ALT]  Theorem
      
      |- !x y. (x <= y ==> (max x y = y)) /\ (y <= x ==> (max x y = x))
   
   [REAL_MAX_LE]  Theorem
      
      |- !z x y. max x y <= z <=> x <= z /\ y <= z
   
   [REAL_MAX_MIN]  Theorem
      
      |- !x y. max x y = -min (-x) (-y)
   
   [REAL_MAX_REFL]  Theorem
      
      |- !x. max x x = x
   
   [REAL_MAX_SUB]  Theorem
      
      |- !z x y. max (x - z) (y - z) = max x y - z
   
   [REAL_MEAN]  Theorem
      
      |- !x y. x < y ==> ?z. x < z /\ z < y
   
   [REAL_MIDDLE1]  Theorem
      
      |- !a b. a <= b ==> a <= (a + b) / 2
   
   [REAL_MIDDLE2]  Theorem
      
      |- !a b. a <= b ==> (a + b) / 2 <= b
   
   [REAL_MIN_ADD]  Theorem
      
      |- !z x y. min (x + z) (y + z) = min x y + z
   
   [REAL_MIN_ALT]  Theorem
      
      |- !x y. (x <= y ==> (min x y = x)) /\ (y <= x ==> (min x y = y))
   
   [REAL_MIN_LE]  Theorem
      
      |- !z x y. min x y <= z <=> x <= z \/ y <= z
   
   [REAL_MIN_LE1]  Theorem
      
      |- !x y. min x y <= x
   
   [REAL_MIN_LE2]  Theorem
      
      |- !x y. min x y <= y
   
   [REAL_MIN_LE_LIN]  Theorem
      
      |- !z x y. 0 <= z /\ z <= 1 ==> min x y <= z * x + (1 - z) * y
   
   [REAL_MIN_MAX]  Theorem
      
      |- !x y. min x y = -max (-x) (-y)
   
   [REAL_MIN_REFL]  Theorem
      
      |- !x. min x x = x
   
   [REAL_MIN_SUB]  Theorem
      
      |- !z x y. min (x - z) (y - z) = min x y - z
   
   [REAL_MUL]  Theorem
      
      |- !m n. &m * &n = &(m * n)
   
   [REAL_MUL_ASSOC]  Theorem
      
      |- !x y z. x * (y * z) = x * y * z
   
   [REAL_MUL_COMM]  Theorem
      
      |- !x y. x * y = y * x
   
   [REAL_MUL_LID]  Theorem
      
      |- !x. 1 * x = x
   
   [REAL_MUL_LINV]  Theorem
      
      |- !x. x <> 0 ==> (inv x * x = 1)
   
   [REAL_MUL_LNEG]  Theorem
      
      |- !x y. -x * y = -(x * y)
   
   [REAL_MUL_LZERO]  Theorem
      
      |- !x. 0 * x = 0
   
   [REAL_MUL_RID]  Theorem
      
      |- !x. x * 1 = x
   
   [REAL_MUL_RINV]  Theorem
      
      |- !x. x <> 0 ==> (x * inv x = 1)
   
   [REAL_MUL_RNEG]  Theorem
      
      |- !x y. x * -y = -(x * y)
   
   [REAL_MUL_RZERO]  Theorem
      
      |- !x. x * 0 = 0
   
   [REAL_MUL_SUB1_CANCEL]  Theorem
      
      |- !z x y. y * x + y * (z - x) = y * z
   
   [REAL_MUL_SUB2_CANCEL]  Theorem
      
      |- !z x y. x * y + (z - x) * y = z * y
   
   [REAL_MUL_SYM]  Theorem
      
      |- !x y. x * y = y * x
   
   [REAL_NEGNEG]  Theorem
      
      |- !x. --x = x
   
   [REAL_NEG_0]  Theorem
      
      |- -0 = 0
   
   [REAL_NEG_ADD]  Theorem
      
      |- !x y. -(x + y) = -x + -y
   
   [REAL_NEG_EQ]  Theorem
      
      |- !x y. (-x = y) <=> (x = -y)
   
   [REAL_NEG_EQ0]  Theorem
      
      |- !x. (-x = 0) <=> (x = 0)
   
   [REAL_NEG_GE0]  Theorem
      
      |- !x. 0 <= -x <=> x <= 0
   
   [REAL_NEG_GT0]  Theorem
      
      |- !x. 0 < -x <=> x < 0
   
   [REAL_NEG_HALF]  Theorem
      
      |- !x. x - x / 2 = x / 2
   
   [REAL_NEG_INV]  Theorem
      
      |- !x. x <> 0 ==> (-inv x = inv (-x))
   
   [REAL_NEG_LE0]  Theorem
      
      |- !x. -x <= 0 <=> 0 <= x
   
   [REAL_NEG_LMUL]  Theorem
      
      |- !x y. -(x * y) = -x * y
   
   [REAL_NEG_LT0]  Theorem
      
      |- !x. -x < 0 <=> 0 < x
   
   [REAL_NEG_MINUS1]  Theorem
      
      |- !x. -x = -1 * x
   
   [REAL_NEG_MUL2]  Theorem
      
      |- !x y. -x * -y = x * y
   
   [REAL_NEG_NEG]  Theorem
      
      |- !x. --x = x
   
   [REAL_NEG_RMUL]  Theorem
      
      |- !x y. -(x * y) = x * -y
   
   [REAL_NEG_SUB]  Theorem
      
      |- !x y. -(x - y) = y - x
   
   [REAL_NEG_THIRD]  Theorem
      
      |- !x. x - x / 3 = 2 * x / 3
   
   [REAL_NOT_LE]  Theorem
      
      |- !x y. ~(x <= y) <=> y < x
   
   [REAL_NOT_LT]  Theorem
      
      |- !x y. ~(x < y) <=> y <= x
   
   [REAL_NZ_IMP_LT]  Theorem
      
      |- !n. n <> 0 ==> 0 < &n
   
   [REAL_OF_NUM_ADD]  Theorem
      
      |- !m n. &m + &n = &(m + n)
   
   [REAL_OF_NUM_EQ]  Theorem
      
      |- !m n. (&m = &n) <=> (m = n)
   
   [REAL_OF_NUM_LE]  Theorem
      
      |- !m n. &m <= &n <=> m <= n
   
   [REAL_OF_NUM_MUL]  Theorem
      
      |- !m n. &m * &n = &(m * n)
   
   [REAL_OF_NUM_POW]  Theorem
      
      |- !x n. &x pow n = &(x ** n)
   
   [REAL_OF_NUM_SUC]  Theorem
      
      |- !n. &n + 1 = &SUC n
   
   [REAL_OVER1]  Theorem
      
      |- !x. x / 1 = x
   
   [REAL_POASQ]  Theorem
      
      |- !x. 0 < x * x <=> x <> 0
   
   [REAL_POS]  Theorem
      
      |- !n. 0 <= &n
   
   [REAL_POS_EQ_ZERO]  Theorem
      
      |- !x. (pos x = 0) <=> x <= 0
   
   [REAL_POS_ID]  Theorem
      
      |- !x. 0 <= x ==> (pos x = x)
   
   [REAL_POS_INFLATE]  Theorem
      
      |- !x. x <= pos x
   
   [REAL_POS_LE_ZERO]  Theorem
      
      |- !x. pos x <= 0 <=> x <= 0
   
   [REAL_POS_MONO]  Theorem
      
      |- !x y. x <= y ==> pos x <= pos y
   
   [REAL_POS_NZ]  Theorem
      
      |- !x. 0 < x ==> x <> 0
   
   [REAL_POS_POS]  Theorem
      
      |- !x. 0 <= pos x
   
   [REAL_POW2_ABS]  Theorem
      
      |- !x. abs x pow 2 = x pow 2
   
   [REAL_POW_ADD]  Theorem
      
      |- !x m n. x pow (m + n) = x pow m * x pow n
   
   [REAL_POW_DIV]  Theorem
      
      |- !x y n. (x / y) pow n = x pow n / y pow n
   
   [REAL_POW_INV]  Theorem
      
      |- !x n. inv x pow n = inv (x pow n)
   
   [REAL_POW_LT]  Theorem
      
      |- !x n. 0 < x ==> 0 < x pow n
   
   [REAL_POW_LT2]  Theorem
      
      |- !n x y. n <> 0 /\ 0 <= x /\ x < y ==> x pow n < y pow n
   
   [REAL_POW_MONO_LT]  Theorem
      
      |- !m n x. 1 < x /\ m < n ==> x pow m < x pow n
   
   [REAL_POW_POW]  Theorem
      
      |- !x m n. (x pow m) pow n = x pow (m * n)
   
   [REAL_RDISTRIB]  Theorem
      
      |- !x y z. (x + y) * z = x * z + y * z
   
   [REAL_RINV_UNIQ]  Theorem
      
      |- !x y. (x * y = 1) ==> (y = inv x)
   
   [REAL_RNEG_UNIQ]  Theorem
      
      |- !x y. (x + y = 0) <=> (y = -x)
   
   [REAL_SUB]  Theorem
      
      |- !m n. &m - &n = if m - n = 0 then -&(n - m) else &(m - n)
   
   [REAL_SUB_0]  Theorem
      
      |- !x y. (x - y = 0) <=> (x = y)
   
   [REAL_SUB_ABS]  Theorem
      
      |- !x y. abs x - abs y <= abs (x - y)
   
   [REAL_SUB_ADD]  Theorem
      
      |- !x y. x - y + y = x
   
   [REAL_SUB_ADD2]  Theorem
      
      |- !x y. y + (x - y) = x
   
   [REAL_SUB_INV2]  Theorem
      
      |- !x y. x <> 0 /\ y <> 0 ==> (inv x - inv y = (y - x) / (x * y))
   
   [REAL_SUB_LDISTRIB]  Theorem
      
      |- !x y z. x * (y - z) = x * y - x * z
   
   [REAL_SUB_LE]  Theorem
      
      |- !x y. 0 <= x - y <=> y <= x
   
   [REAL_SUB_LNEG]  Theorem
      
      |- !x y. -x - y = -(x + y)
   
   [REAL_SUB_LT]  Theorem
      
      |- !x y. 0 < x - y <=> y < x
   
   [REAL_SUB_LZERO]  Theorem
      
      |- !x. 0 - x = -x
   
   [REAL_SUB_NEG2]  Theorem
      
      |- !x y. -x - -y = y - x
   
   [REAL_SUB_RAT]  Theorem
      
      |- !a b c d.
           b <> 0 /\ d <> 0 ==> (a / b - c / d = (a * d - b * c) / (b * d))
   
   [REAL_SUB_RDISTRIB]  Theorem
      
      |- !x y z. (x - y) * z = x * z - y * z
   
   [REAL_SUB_REFL]  Theorem
      
      |- !x. x - x = 0
   
   [REAL_SUB_RNEG]  Theorem
      
      |- !x y. x - -y = x + y
   
   [REAL_SUB_RZERO]  Theorem
      
      |- !x. x - 0 = x
   
   [REAL_SUB_SUB]  Theorem
      
      |- !x y. x - y - x = -y
   
   [REAL_SUB_SUB2]  Theorem
      
      |- !x y. x - (x - y) = y
   
   [REAL_SUB_TRIANGLE]  Theorem
      
      |- !a b c. a - b + (b - c) = a - c
   
   [REAL_SUMSQ]  Theorem
      
      |- !x y. (x * x + y * y = 0) <=> (x = 0) /\ (y = 0)
   
   [REAL_SUP]  Theorem
      
      |- !P.
           (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
           !y. (?x. P x /\ y < x) <=> y < sup P
   
   [REAL_SUP_ALLPOS]  Theorem
      
      |- !P.
           (!x. P x ==> 0 < x) /\ (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
           ?s. !y. (?x. P x /\ y < x) <=> y < s
   
   [REAL_SUP_CONST]  Theorem
      
      |- !x. sup (\r. r = x) = x
   
   [REAL_SUP_EXISTS]  Theorem
      
      |- !P.
           (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
           ?s. !y. (?x. P x /\ y < x) <=> y < s
   
   [REAL_SUP_EXISTS_UNIQUE]  Theorem
      
      |- !p.
           (?x. p x) /\ (?z. !x. p x ==> x <= z) ==>
           ?!s. !y. (?x. p x /\ y < x) <=> y < s
   
   [REAL_SUP_LE]  Theorem
      
      |- !P.
           (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           !y. (?x. P x /\ y < x) <=> y < sup P
   
   [REAL_SUP_MAX]  Theorem
      
      |- !p z. p z /\ (!x. p x ==> x <= z) ==> (sup p = z)
   
   [REAL_SUP_SOMEPOS]  Theorem
      
      |- !P.
           (?x. P x /\ 0 < x) /\ (?z. !x. P x ==> x < z) ==>
           ?s. !y. (?x. P x /\ y < x) <=> y < s
   
   [REAL_SUP_UBOUND]  Theorem
      
      |- !P.
           (?x. P x) /\ (?z. !x. P x ==> x < z) ==> !y. P y ==> y <= sup P
   
   [REAL_SUP_UBOUND_LE]  Theorem
      
      |- !P.
           (?x. P x) /\ (?z. !x. P x ==> x <= z) ==> !y. P y ==> y <= sup P
   
   [REAL_THIRDS_BETWEEN]  Theorem
      
      |- (0 < 1 / 3 /\ 1 / 3 < 1 /\ 0 < 2 / 3 /\ 2 / 3 < 1) /\
         0 <= 1 / 3 /\ 1 / 3 <= 1 /\ 0 <= 2 / 3 /\ 2 / 3 <= 1
   
   [SETOK_LE_LT]  Theorem
      
      |- !P.
           (?x. P x) /\ (?z. !x. P x ==> x <= z) <=>
           (?x. P x) /\ ?z. !x. P x ==> x < z
   
   [SUM_0]  Theorem
      
      |- !m n. sum (m,n) (\r. 0) = 0
   
   [SUM_1]  Theorem
      
      |- !f n. sum (n,1) f = f n
   
   [SUM_2]  Theorem
      
      |- !f n. sum (n,2) f = f n + f (n + 1)
   
   [SUM_ABS]  Theorem
      
      |- !f m n.
           abs (sum (m,n) (\m. abs (f m))) = sum (m,n) (\m. abs (f m))
   
   [SUM_ABS_LE]  Theorem
      
      |- !f m n. abs (sum (m,n) f) <= sum (m,n) (\n. abs (f n))
   
   [SUM_ADD]  Theorem
      
      |- !f g m n. sum (m,n) (\n. f n + g n) = sum (m,n) f + sum (m,n) g
   
   [SUM_BOUND]  Theorem
      
      |- !f k m n.
           (!p. m <= p /\ p < m + n ==> f p <= k) ==> sum (m,n) f <= &n * k
   
   [SUM_CANCEL]  Theorem
      
      |- !f n d. sum (n,d) (\n. f (SUC n) - f n) = f (n + d) - f n
   
   [SUM_CMUL]  Theorem
      
      |- !f c m n. sum (m,n) (\n. c * f n) = c * sum (m,n) f
   
   [SUM_DIFF]  Theorem
      
      |- !f m n. sum (m,n) f = sum (0,m + n) f - sum (0,m) f
   
   [SUM_EQ]  Theorem
      
      |- !f g m n.
           (!r. m <= r /\ r < n + m ==> (f r = g r)) ==>
           (sum (m,n) f = sum (m,n) g)
   
   [SUM_GROUP]  Theorem
      
      |- !n k f. sum (0,n) (\m. sum (m * k,k) f) = sum (0,n * k) f
   
   [SUM_LE]  Theorem
      
      |- !f g m n.
           (!r. m <= r /\ r < n + m ==> f r <= g r) ==>
           sum (m,n) f <= sum (m,n) g
   
   [SUM_NEG]  Theorem
      
      |- !f n d. sum (n,d) (\n. -f n) = -sum (n,d) f
   
   [SUM_NSUB]  Theorem
      
      |- !n f c. sum (0,n) f - &n * c = sum (0,n) (\p. f p - c)
   
   [SUM_OFFSET]  Theorem
      
      |- !f n k. sum (0,n) (\m. f (m + k)) = sum (0,n + k) f - sum (0,k) f
   
   [SUM_PERMUTE_0]  Theorem
      
      |- !n p.
           (!y. y < n ==> ?!x. x < n /\ (p x = y)) ==>
           !f. sum (0,n) (\n. f (p n)) = sum (0,n) f
   
   [SUM_POS]  Theorem
      
      |- !f. (!n. 0 <= f n) ==> !m n. 0 <= sum (m,n) f
   
   [SUM_POS_GEN]  Theorem
      
      |- !f m. (!n. m <= n ==> 0 <= f n) ==> !n. 0 <= sum (m,n) f
   
   [SUM_REINDEX]  Theorem
      
      |- !f m k n. sum (m + k,n) f = sum (m,n) (\r. f (r + k))
   
   [SUM_SUB]  Theorem
      
      |- !f g m n. sum (m,n) (\n. f n - g n) = sum (m,n) f - sum (m,n) g
   
   [SUM_SUBST]  Theorem
      
      |- !f g m n.
           (!p. m <= p /\ p < m + n ==> (f p = g p)) ==>
           (sum (m,n) f = sum (m,n) g)
   
   [SUM_TWO]  Theorem
      
      |- !f n p. sum (0,n) f + sum (n,p) f = sum (0,n + p) f
   
   [SUM_ZERO]  Theorem
      
      |- !f N.
           (!n. n >= N ==> (f n = 0)) ==>
           !m n. m >= N ==> (sum (m,n) f = 0)
   
   [SUP_EPSILON]  Theorem
      
      |- !p e.
           0 < e /\ (?x. p x) /\ (?z. !x. p x ==> x <= z) ==>
           ?x. p x /\ sup p <= x + e
   
   [SUP_LEMMA1]  Theorem
      
      |- !P s d.
           (!y. (?x. (\x. P (x + d)) x /\ y < x) <=> y < s) ==>
           !y. (?x. P x /\ y < x) <=> y < s + d
   
   [SUP_LEMMA2]  Theorem
      
      |- !P. (?x. P x) ==> ?d x. (\x. P (x + d)) x /\ 0 < x
   
   [SUP_LEMMA3]  Theorem
      
      |- !d.
           (?z. !x. P x ==> x < z) ==> ?z. !x. (\x. P (x + d)) x ==> x < z
   
   [add_ints]  Theorem
      
      |- (&n + &m = &(n + m)) /\
         (-&n + &m = if n <= m then &(m - n) else -&(n - m)) /\
         (&n + -&m = if n < m then -&(m - n) else &(n - m)) /\
         (-&n + -&m = -&(n + m))
   
   [add_rat]  Theorem
      
      |- x / y + u / v =
         if y = 0 then
           unint (x / y) + u / v
         else
           if v = 0 then
             x / y + unint (u / v)
           else
             if y = v then (x + u) / v else (x * v + u * y) / (y * v)
   
   [add_ratl]  Theorem
      
      |- x / y + z = if y = 0 then unint (x / y) + z else (x + z * y) / y
   
   [add_ratr]  Theorem
      
      |- x + y / z = if z = 0 then x + unint (y / z) else (x * z + y) / z
   
   [div_rat]  Theorem
      
      |- x / y / (u / v) =
         if (u = 0) \/ (v = 0) then
           x / y / unint (u / v)
         else
           if y = 0 then unint (x / y) / (u / v) else x * v / (y * u)
   
   [div_ratl]  Theorem
      
      |- x / y / z =
         if y = 0 then
           unint (x / y) / z
         else
           if z = 0 then unint (x / y / z) else x / (y * z)
   
   [div_ratr]  Theorem
      
      |- x / (y / z) =
         if (y = 0) \/ (z = 0) then x / unint (y / z) else x * z / y
   
   [eq_ints]  Theorem
      
      |- ((&n = &m) <=> (n = m)) /\ ((-&n = &m) <=> (n = 0) /\ (m = 0)) /\
         ((&n = -&m) <=> (n = 0) /\ (m = 0)) /\ ((-&n = -&m) <=> (n = m))
   
   [eq_rat]  Theorem
      
      |- (x / y = u / v) <=>
         if y = 0 then
           unint (x / y) = u / v
         else
           if v = 0 then
             x / y = unint (u / v)
           else
             if y = v then x = u else x * v = y * u
   
   [eq_ratl]  Theorem
      
      |- (x / y = z) <=> if y = 0 then unint (x / y) = z else x = y * z
   
   [eq_ratr]  Theorem
      
      |- (z = x / y) <=> if y = 0 then z = unint (x / y) else y * z = x
   
   [le_int]  Theorem
      
      |- (&n <= &m <=> n <= m) /\ (-&n <= &m <=> T) /\
         (&n <= -&m <=> (n = 0) /\ (m = 0)) /\ (-&n <= -&m <=> m <= n)
   
   [le_rat]  Theorem
      
      |- x / &n <= u / &m <=>
         if n = 0 then
           unint (x / 0) <= u / &m
         else
           if m = 0 then x / &n <= unint (u / 0) else &m * x <= &n * u
   
   [le_ratl]  Theorem
      
      |- x / &n <= u <=> if n = 0 then unint (x / 0) <= u else x <= &n * u
   
   [le_ratr]  Theorem
      
      |- x <= u / &m <=> if m = 0 then x <= unint (u / 0) else &m * x <= u
   
   [lt_int]  Theorem
      
      |- (&n < &m <=> n < m) /\ (-&n < &m <=> n <> 0 \/ m <> 0) /\
         (&n < -&m <=> F) /\ (-&n < -&m <=> m < n)
   
   [lt_rat]  Theorem
      
      |- x / &n < u / &m <=>
         if n = 0 then
           unint (x / 0) < u / &m
         else
           if m = 0 then x / &n < unint (u / 0) else &m * x < &n * u
   
   [lt_ratl]  Theorem
      
      |- x / &n < u <=> if n = 0 then unint (x / 0) < u else x < &n * u
   
   [lt_ratr]  Theorem
      
      |- x < u / &m <=> if m = 0 then x < unint (u / 0) else &m * x < u
   
   [mult_ints]  Theorem
      
      |- (&a * &b = &(a * b)) /\ (-&a * &b = -&(a * b)) /\
         (&a * -&b = -&(a * b)) /\ (-&a * -&b = &(a * b))
   
   [mult_rat]  Theorem
      
      |- x / y * (u / v) =
         if y = 0 then
           unint (x / y) * (u / v)
         else
           if v = 0 then x / y * unint (u / v) else x * u / (y * v)
   
   [mult_ratl]  Theorem
      
      |- x / y * z = if y = 0 then unint (x / y) * z else x * z / y
   
   [mult_ratr]  Theorem
      
      |- x * (y / z) = if z = 0 then x * unint (y / z) else x * y / z
   
   [neg_rat]  Theorem
      
      |- (-(x / y) = if y = 0 then -unint (x / y) else -x / y) /\
         (x / -y = if y = 0 then unint (x / y) else -x / y)
   
   [pow_rat]  Theorem
      
      |- (x pow 0 = 1) /\ (0 pow NUMERAL (BIT1 n) = 0) /\
         (0 pow NUMERAL (BIT2 n) = 0) /\
         (&NUMERAL a pow NUMERAL n = &(NUMERAL a ** NUMERAL n)) /\
         (-&NUMERAL a pow NUMERAL n =
          (if ODD (NUMERAL n) then numeric_negate else (\x. x))
            (&(NUMERAL a ** NUMERAL n))) /\
         ((x / y) pow n = x pow n / y pow n)
   
   [real_lt]  Theorem
      
      |- !y x. x < y <=> ~(y <= x)
   
   [sum]  Theorem
      
      |- !f n m.
           (sum (n,0) f = 0) /\ (sum (n,SUC m) f = sum (n,m) f + f (n + m))
   
   
*)
end
