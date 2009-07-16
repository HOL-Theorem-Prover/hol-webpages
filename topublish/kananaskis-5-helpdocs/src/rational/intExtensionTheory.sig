signature intExtensionTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val SGN_def : thm
  
  (*  Theorems  *)
    val INT_ABS_CALCULATE_0 : thm
    val INT_ABS_CALCULATE_NEG : thm
    val INT_ABS_CALCULATE_POS : thm
    val INT_ABS_NOT0POS : thm
    val INT_EQ_RMUL_EXP : thm
    val INT_GT0_IMP_NOT0 : thm
    val INT_GT_RMUL_EXP : thm
    val INT_LT_ADD_NEG : thm
    val INT_LT_RMUL_EXP : thm
    val INT_MUL_POS_SIGN : thm
    val INT_NE_IMP_LTGT : thm
    val INT_NOT0_MUL : thm
    val INT_NOT0_SGNNOT0 : thm
    val INT_NOTGT_IMP_EQLT : thm
    val INT_NOTLTEQ_GT : thm
    val INT_NOTPOS0_NEG : thm
    val INT_NO_ZERODIV : thm
    val INT_SGN_CASES : thm
    val INT_SGN_CLAUSES : thm
    val INT_SGN_MUL : thm
    val INT_SGN_MUL2 : thm
    val INT_SGN_NOTPOSNEG : thm
    val INT_SGN_TOTAL : thm
    val LESS_IMP_NOT_0 : thm
  
  val intExtension_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [Omega] Parent theory of "intExtension"
   
   [int_arith] Parent theory of "intExtension"
   
   [integerRing] Parent theory of "intExtension"
   
   [numRing] Parent theory of "intExtension"
   
   [SGN_def]  Definition
      
      |- !x. SGN x = if x = 0 then 0 else if x < 0 then -1 else 1
   
   [INT_ABS_CALCULATE_0]  Theorem
      
      |- ABS 0 = 0
   
   [INT_ABS_CALCULATE_NEG]  Theorem
      
      |- !a. a < 0 ==> (ABS a = -a)
   
   [INT_ABS_CALCULATE_POS]  Theorem
      
      |- !a. 0 < a ==> (ABS a = a)
   
   [INT_ABS_NOT0POS]  Theorem
      
      |- !x. x <> 0 ==> 0 < ABS x
   
   [INT_EQ_RMUL_EXP]  Theorem
      
      |- !a b n. 0 < n ==> ((a = b) <=> (a * n = b * n))
   
   [INT_GT0_IMP_NOT0]  Theorem
      
      |- !a. 0 < a ==> a <> 0
   
   [INT_GT_RMUL_EXP]  Theorem
      
      |- !a b n. 0 < n ==> (a > b <=> a * n > b * n)
   
   [INT_LT_ADD_NEG]  Theorem
      
      |- !x y. x < 0 /\ y < 0 ==> x + y < 0
   
   [INT_LT_RMUL_EXP]  Theorem
      
      |- !a b n. 0 < n ==> (a < b <=> a * n < b * n)
   
   [INT_MUL_POS_SIGN]  Theorem
      
      |- !a b. 0 < a ==> 0 < b ==> 0 < a * b
   
   [INT_NE_IMP_LTGT]  Theorem
      
      |- !x. x <> 0 <=> 0 < x \/ x < 0
   
   [INT_NOT0_MUL]  Theorem
      
      |- !a b. a <> 0 ==> b <> 0 ==> a * b <> 0
   
   [INT_NOT0_SGNNOT0]  Theorem
      
      |- !x. x <> 0 ==> SGN x <> 0
   
   [INT_NOTGT_IMP_EQLT]  Theorem
      
      |- !n. ~(n < 0) <=> (0 = n) \/ 0 < n
   
   [INT_NOTLTEQ_GT]  Theorem
      
      |- !a. ~(a < 0) ==> a <> 0 ==> 0 < a
   
   [INT_NOTPOS0_NEG]  Theorem
      
      |- !a. ~(0 < a) ==> a <> 0 ==> 0 < -a
   
   [INT_NO_ZERODIV]  Theorem
      
      |- !x y. (x = 0) \/ (y = 0) <=> (x * y = 0)
   
   [INT_SGN_CASES]  Theorem
      
      |- !a P.
           ((SGN a = -1) ==> P) /\ ((SGN a = 0) ==> P) /\
           ((SGN a = 1) ==> P) ==>
           P
   
   [INT_SGN_CLAUSES]  Theorem
      
      |- !x.
           ((SGN x = -1) <=> x < 0) /\ ((SGN x = 0) <=> (x = 0)) /\
           ((SGN x = 1) <=> x > 0)
   
   [INT_SGN_MUL]  Theorem
      
      |- !x1 x2 y1 y2.
           (SGN x1 = y1) ==> (SGN x2 = y2) ==> (SGN (x1 * x2) = y1 * y2)
   
   [INT_SGN_MUL2]  Theorem
      
      |- !x y. SGN (x * y) = SGN x * SGN y
   
   [INT_SGN_NOTPOSNEG]  Theorem
      
      |- !x. SGN x <> -1 ==> SGN x <> 1 ==> (SGN x = 0)
   
   [INT_SGN_TOTAL]  Theorem
      
      |- !a. (SGN a = -1) \/ (SGN a = 0) \/ (SGN a = 1)
   
   [LESS_IMP_NOT_0]  Theorem
      
      |- !n. 0 < n ==> n <> 0
   
   
*)
end
