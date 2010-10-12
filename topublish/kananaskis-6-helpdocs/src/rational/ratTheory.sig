signature ratTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val abs_rat_def : thm
    val rat_0_def : thm
    val rat_1_def : thm
    val rat_TY_DEF : thm
    val rat_add_def : thm
    val rat_ainv_def : thm
    val rat_bijections : thm
    val rat_cons_def : thm
    val rat_div_def : thm
    val rat_dnm_def : thm
    val rat_equiv_def : thm
    val rat_geq_def : thm
    val rat_gre_def : thm
    val rat_leq_def : thm
    val rat_les_def : thm
    val rat_minv_def : thm
    val rat_mul_def : thm
    val rat_nmr_def : thm
    val rat_of_num_primitive_def : thm
    val rat_sgn_def : thm
    val rat_sub_def : thm
    val rep_rat_def : thm
  
  (*  Theorems  *)
    val RAT : thm
    val RAT_0 : thm
    val RAT_0LEQ_NMR : thm
    val RAT_0LES_0LEQ_ADD : thm
    val RAT_0LES_0LES_ADD : thm
    val RAT_0LES_NMR : thm
    val RAT_1 : thm
    val RAT_1_NOT_0 : thm
    val RAT_ABS_EQUIV : thm
    val RAT_ADD_ASSOC : thm
    val RAT_ADD_CALCULATE : thm
    val RAT_ADD_COMM : thm
    val RAT_ADD_CONG : thm
    val RAT_ADD_CONG1 : thm
    val RAT_ADD_CONG2 : thm
    val RAT_ADD_LID : thm
    val RAT_ADD_LINV : thm
    val RAT_ADD_NUM_CALCULATE : thm
    val RAT_ADD_ONE_ONE : thm
    val RAT_ADD_RID : thm
    val RAT_ADD_RINV : thm
    val RAT_AINV_0 : thm
    val RAT_AINV_ADD : thm
    val RAT_AINV_AINV : thm
    val RAT_AINV_CALCULATE : thm
    val RAT_AINV_CONG : thm
    val RAT_AINV_EQ : thm
    val RAT_AINV_LES : thm
    val RAT_AINV_LMUL : thm
    val RAT_AINV_MINV : thm
    val RAT_AINV_ONE_ONE : thm
    val RAT_AINV_RMUL : thm
    val RAT_AINV_SUB : thm
    val RAT_CONS_TO_NUM : thm
    val RAT_DENSE_THM : thm
    val RAT_DIV_CALCULATE : thm
    val RAT_DIV_CONG : thm
    val RAT_DIV_CONG1 : thm
    val RAT_DIV_CONG2 : thm
    val RAT_DIV_MULMINV : thm
    val RAT_EQ : thm
    val RAT_EQ0_NMR : thm
    val RAT_EQUIV : thm
    val RAT_EQUIV_ALT : thm
    val RAT_EQUIV_REF : thm
    val RAT_EQUIV_SYM : thm
    val RAT_EQUIV_TRANS : thm
    val RAT_EQ_0SUB : thm
    val RAT_EQ_AINV : thm
    val RAT_EQ_ALT : thm
    val RAT_EQ_CALCULATE : thm
    val RAT_EQ_LADD : thm
    val RAT_EQ_LMUL : thm
    val RAT_EQ_NUM_CALCULATE : thm
    val RAT_EQ_RADD : thm
    val RAT_EQ_RMUL : thm
    val RAT_EQ_SUB0 : thm
    val RAT_LDISTRIB : thm
    val RAT_LDIV_EQ : thm
    val RAT_LDIV_LES_NEG : thm
    val RAT_LDIV_LES_POS : thm
    val RAT_LEQ0_NMR : thm
    val RAT_LEQ_ANTISYM : thm
    val RAT_LEQ_LES : thm
    val RAT_LEQ_LES_TRANS : thm
    val RAT_LEQ_REF : thm
    val RAT_LEQ_TRANS : thm
    val RAT_LES0_LEQ0_ADD : thm
    val RAT_LES0_LES0_ADD : thm
    val RAT_LES0_NMR : thm
    val RAT_LES_01 : thm
    val RAT_LES_0SUB : thm
    val RAT_LES_AINV : thm
    val RAT_LES_ANTISYM : thm
    val RAT_LES_CALCULATE : thm
    val RAT_LES_IMP_LEQ : thm
    val RAT_LES_IMP_NEQ : thm
    val RAT_LES_LADD : thm
    val RAT_LES_LEQ : thm
    val RAT_LES_LEQ2 : thm
    val RAT_LES_LEQ_TRANS : thm
    val RAT_LES_LMUL_NEG : thm
    val RAT_LES_LMUL_POS : thm
    val RAT_LES_RADD : thm
    val RAT_LES_REF : thm
    val RAT_LES_RMUL_NEG : thm
    val RAT_LES_RMUL_POS : thm
    val RAT_LES_SUB0 : thm
    val RAT_LES_TOTAL : thm
    val RAT_LES_TRANS : thm
    val RAT_LSUB_EQ : thm
    val RAT_LSUB_LES : thm
    val RAT_MINV_CALCULATE : thm
    val RAT_MINV_CONG : thm
    val RAT_MINV_LES : thm
    val RAT_MUL_ASSOC : thm
    val RAT_MUL_CALCULATE : thm
    val RAT_MUL_COMM : thm
    val RAT_MUL_CONG : thm
    val RAT_MUL_CONG1 : thm
    val RAT_MUL_CONG2 : thm
    val RAT_MUL_LID : thm
    val RAT_MUL_LINV : thm
    val RAT_MUL_LZERO : thm
    val RAT_MUL_NUM_CALCULATE : thm
    val RAT_MUL_ONE_ONE : thm
    val RAT_MUL_RID : thm
    val RAT_MUL_RINV : thm
    val RAT_MUL_RZERO : thm
    val RAT_MUL_SIGN_CASES : thm
    val RAT_NMRDNM_EQ : thm
    val RAT_NMREQ0_CONG : thm
    val RAT_NMRGT0_CONG : thm
    val RAT_NMRLT0_CONG : thm
    val RAT_NO_IDDIV : thm
    val RAT_NO_ZERODIV : thm
    val RAT_NO_ZERODIV_NEG : thm
    val RAT_OF_NUM : thm
    val RAT_OF_NUM_CALCULATE : thm
    val RAT_RDISTRIB : thm
    val RAT_RDIV_EQ : thm
    val RAT_RDIV_LES_NEG : thm
    val RAT_RDIV_LES_POS : thm
    val RAT_RSUB_EQ : thm
    val RAT_RSUB_LES : thm
    val RAT_SAVE : thm
    val RAT_SAVE_MINV : thm
    val RAT_SAVE_NUM : thm
    val RAT_SAVE_TO_CONS : thm
    val RAT_SGN_0 : thm
    val RAT_SGN_AINV : thm
    val RAT_SGN_CALCULATE : thm
    val RAT_SGN_CLAUSES : thm
    val RAT_SGN_COMPLEMENT : thm
    val RAT_SGN_CONG : thm
    val RAT_SGN_MINV : thm
    val RAT_SGN_MUL : thm
    val RAT_SGN_TOTAL : thm
    val RAT_SUB_ADDAINV : thm
    val RAT_SUB_CALCULATE : thm
    val RAT_SUB_CONG : thm
    val RAT_SUB_CONG1 : thm
    val RAT_SUB_CONG2 : thm
    val RAT_SUB_ID : thm
    val RAT_SUB_LDISTRIB : thm
    val RAT_SUB_LID : thm
    val RAT_SUB_RDISTRIB : thm
    val RAT_SUB_RID : thm
    val rat_0 : thm
    val rat_1 : thm
    val rat_ABS_REP_CLASS : thm
    val rat_QUOTIENT : thm
    val rat_def : thm
    val rat_of_num_def : thm
    val rat_of_num_ind : thm
  
  val rat_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [frac] Parent theory of "rat"
   
   [abs_rat_def]  Definition
      
      |- ∀r. abs_rat r = abs_rat_CLASS (rat_equiv r)
   
   [rat_0_def]  Definition
      
      |- rat_0 = abs_rat frac_0
   
   [rat_1_def]  Definition
      
      |- rat_1 = abs_rat frac_1
   
   [rat_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION (λc. ∃r. rat_equiv r r ∧ (c = rat_equiv r)) rep
   
   [rat_add_def]  Definition
      
      |- ∀r1 r2. r1 + r2 = abs_rat (frac_add (rep_rat r1) (rep_rat r2))
   
   [rat_ainv_def]  Definition
      
      |- ∀r1. -r1 = abs_rat (frac_ainv (rep_rat r1))
   
   [rat_bijections]  Definition
      
      |- (∀a. abs_rat_CLASS (rep_rat_CLASS a) = a) ∧
         ∀r.
           (λc. ∃r. rat_equiv r r ∧ (c = rat_equiv r)) r ⇔
           (rep_rat_CLASS (abs_rat_CLASS r) = r)
   
   [rat_cons_def]  Definition
      
      |- ∀nmr dnm.
           nmr // dnm = abs_rat (abs_frac (SGN nmr * SGN dnm * ABS nmr,ABS dnm))
   
   [rat_div_def]  Definition
      
      |- ∀r1 r2. r1 / r2 = abs_rat (frac_div (rep_rat r1) (rep_rat r2))
   
   [rat_dnm_def]  Definition
      
      |- ∀r. rat_dnm r = frac_dnm (rep_rat r)
   
   [rat_equiv_def]  Definition
      
      |- ∀f1 f2.
           rat_equiv f1 f2 ⇔ (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)
   
   [rat_geq_def]  Definition
      
      |- ∀r1 r2. r1 ≥ r2 ⇔ r2 ≤ r1
   
   [rat_gre_def]  Definition
      
      |- ∀r1 r2. r1 > r2 ⇔ r2 < r1
   
   [rat_leq_def]  Definition
      
      |- ∀r1 r2. r1 ≤ r2 ⇔ r1 < r2 ∨ (r1 = r2)
   
   [rat_les_def]  Definition
      
      |- ∀r1 r2. r1 < r2 ⇔ (rat_sgn (r2 − r1) = 1)
   
   [rat_minv_def]  Definition
      
      |- ∀r1. rat_minv r1 = abs_rat (frac_minv (rep_rat r1))
   
   [rat_mul_def]  Definition
      
      |- ∀r1 r2. r1 * r2 = abs_rat (frac_mul (rep_rat r1) (rep_rat r2))
   
   [rat_nmr_def]  Definition
      
      |- ∀r. rat_nmr r = frac_nmr (rep_rat r)
   
   [rat_of_num_primitive_def]  Definition
      
      |- $& =
         WFREC (@R. WF R ∧ ∀n. R (SUC n) (SUC (SUC n)))
           (λrat_of_num a.
              case a of
                 0 -> I rat_0
              || SUC 0 -> I rat_1
              || SUC (SUC n) -> I (rat_of_num (SUC n) + rat_1))
   
   [rat_sgn_def]  Definition
      
      |- ∀r. rat_sgn r = frac_sgn (rep_rat r)
   
   [rat_sub_def]  Definition
      
      |- ∀r1 r2. r1 − r2 = abs_rat (frac_sub (rep_rat r1) (rep_rat r2))
   
   [rep_rat_def]  Definition
      
      |- ∀a. rep_rat a = $@ (rep_rat_CLASS a)
   
   [RAT]  Theorem
      
      |- ∀r. abs_rat (rep_rat r) = r
   
   [RAT_0]  Theorem
      
      |- rat_0 = 0
   
   [RAT_0LEQ_NMR]  Theorem
      
      |- ∀r1. 0 ≤ r1 ⇔ 0 ≤ rat_nmr r1
   
   [RAT_0LES_0LEQ_ADD]  Theorem
      
      |- ∀r1 r2. 0 < r1 ⇒ 0 ≤ r2 ⇒ 0 < r1 + r2
   
   [RAT_0LES_0LES_ADD]  Theorem
      
      |- ∀r1 r2. 0 < r1 ⇒ 0 < r2 ⇒ 0 < r1 + r2
   
   [RAT_0LES_NMR]  Theorem
      
      |- ∀r1. 0 < r1 ⇔ 0 < rat_nmr r1
   
   [RAT_1]  Theorem
      
      |- rat_1 = 1
   
   [RAT_1_NOT_0]  Theorem
      
      |- 1 ≠ 0
   
   [RAT_ABS_EQUIV]  Theorem
      
      |- ∀f1 f2. (abs_rat f1 = abs_rat f2) ⇔ rat_equiv f1 f2
   
   [RAT_ADD_ASSOC]  Theorem
      
      |- ∀a b c. a + (b + c) = a + b + c
   
   [RAT_ADD_CALCULATE]  Theorem
      
      |- ∀f1 f2. abs_rat f1 + abs_rat f2 = abs_rat (frac_add f1 f2)
   
   [RAT_ADD_COMM]  Theorem
      
      |- ∀a b. a + b = b + a
   
   [RAT_ADD_CONG]  Theorem
      
      |- (∀x y.
            abs_rat (frac_add (rep_rat (abs_rat x)) y) = abs_rat (frac_add x y)) ∧
         ∀x y. abs_rat (frac_add x (rep_rat (abs_rat y))) = abs_rat (frac_add x y)
   
   [RAT_ADD_CONG1]  Theorem
      
      |- ∀x y. abs_rat (frac_add (rep_rat (abs_rat x)) y) = abs_rat (frac_add x y)
   
   [RAT_ADD_CONG2]  Theorem
      
      |- ∀x y. abs_rat (frac_add x (rep_rat (abs_rat y))) = abs_rat (frac_add x y)
   
   [RAT_ADD_LID]  Theorem
      
      |- ∀a. 0 + a = a
   
   [RAT_ADD_LINV]  Theorem
      
      |- ∀a. -a + a = 0
   
   [RAT_ADD_NUM_CALCULATE]  Theorem
      
      |- (∀n m. &n + &m = &(n + m)) ∧
         (∀n m. -&n + &m = if n ≤ m then &(m − n) else -&(n − m)) ∧
         (∀n m. &n + -&m = if m ≤ n then &(n − m) else -&(m − n)) ∧
         ∀n m. -&n + -&m = -&(n + m)
   
   [RAT_ADD_ONE_ONE]  Theorem
      
      |- ∀r1. ONE_ONE ($+ r1)
   
   [RAT_ADD_RID]  Theorem
      
      |- ∀a. a + 0 = a
   
   [RAT_ADD_RINV]  Theorem
      
      |- ∀a. a + -a = 0
   
   [RAT_AINV_0]  Theorem
      
      |- -0 = 0
   
   [RAT_AINV_ADD]  Theorem
      
      |- ∀r1 r2. -(r1 + r2) = -r1 + -r2
   
   [RAT_AINV_AINV]  Theorem
      
      |- ∀r1. --r1 = r1
   
   [RAT_AINV_CALCULATE]  Theorem
      
      |- ∀f1. -abs_rat f1 = abs_rat (frac_ainv f1)
   
   [RAT_AINV_CONG]  Theorem
      
      |- ∀x. abs_rat (frac_ainv (rep_rat (abs_rat x))) = abs_rat (frac_ainv x)
   
   [RAT_AINV_EQ]  Theorem
      
      |- ∀r1 r2. (-r1 = r2) ⇔ (r1 = -r2)
   
   [RAT_AINV_LES]  Theorem
      
      |- ∀r1 r2. -r1 < r2 ⇔ -r2 < r1
   
   [RAT_AINV_LMUL]  Theorem
      
      |- ∀r1 r2. -(r1 * r2) = -r1 * r2
   
   [RAT_AINV_MINV]  Theorem
      
      |- ∀r1. r1 ≠ 0 ⇒ (-rat_minv r1 = rat_minv (-r1))
   
   [RAT_AINV_ONE_ONE]  Theorem
      
      |- ONE_ONE numeric_negate
   
   [RAT_AINV_RMUL]  Theorem
      
      |- ∀r1 r2. -(r1 * r2) = r1 * -r2
   
   [RAT_AINV_SUB]  Theorem
      
      |- ∀r1 r2. -(r1 − r2) = r2 − r1
   
   [RAT_CONS_TO_NUM]  Theorem
      
      |- ∀n. (&n // 1 = &n) ∧ (-&n // 1 = -&n)
   
   [RAT_DENSE_THM]  Theorem
      
      |- ∀r1 r3. r1 < r3 ⇒ ∃r2. r1 < r2 ∧ r2 < r3
   
   [RAT_DIV_CALCULATE]  Theorem
      
      |- ∀f1 f2.
           frac_nmr f2 ≠ 0 ⇒ (abs_rat f1 / abs_rat f2 = abs_rat (frac_div f1 f2))
   
   [RAT_DIV_CONG]  Theorem
      
      |- (∀x y.
            frac_nmr y ≠ 0 ⇒
            (abs_rat (frac_div (rep_rat (abs_rat x)) y) = abs_rat (frac_div x y))) ∧
         ∀x y.
           frac_nmr y ≠ 0 ⇒
           (abs_rat (frac_div x (rep_rat (abs_rat y))) = abs_rat (frac_div x y))
   
   [RAT_DIV_CONG1]  Theorem
      
      |- ∀x y.
           frac_nmr y ≠ 0 ⇒
           (abs_rat (frac_div (rep_rat (abs_rat x)) y) = abs_rat (frac_div x y))
   
   [RAT_DIV_CONG2]  Theorem
      
      |- ∀x y.
           frac_nmr y ≠ 0 ⇒
           (abs_rat (frac_div x (rep_rat (abs_rat y))) = abs_rat (frac_div x y))
   
   [RAT_DIV_MULMINV]  Theorem
      
      |- ∀r1 r2. r1 / r2 = r1 * rat_minv r2
   
   [RAT_EQ]  Theorem
      
      |- ∀f1 f2.
           (abs_rat f1 = abs_rat f2) ⇔
           (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)
   
   [RAT_EQ0_NMR]  Theorem
      
      |- ∀r1. (r1 = 0) ⇔ (rat_nmr r1 = 0)
   
   [RAT_EQUIV]  Theorem
      
      |- ∀f1 f2. rat_equiv f1 f2 ⇔ (rat_equiv f1 = rat_equiv f2)
   
   [RAT_EQUIV_ALT]  Theorem
      
      |- ∀a.
           rat_equiv a =
           (λx.
              ∃b c.
                0 < b ∧ 0 < c ∧
                (frac_mul a (abs_frac (b,b)) = frac_mul x (abs_frac (c,c))))
   
   [RAT_EQUIV_REF]  Theorem
      
      |- ∀a. rat_equiv a a
   
   [RAT_EQUIV_SYM]  Theorem
      
      |- ∀a b. rat_equiv a b ⇔ rat_equiv b a
   
   [RAT_EQUIV_TRANS]  Theorem
      
      |- ∀a b c. rat_equiv a b ∧ rat_equiv b c ⇒ rat_equiv a c
   
   [RAT_EQ_0SUB]  Theorem
      
      |- ∀r1 r2. (0 = r1 − r2) ⇔ (r1 = r2)
   
   [RAT_EQ_AINV]  Theorem
      
      |- ∀r1 r2. (-r1 = -r2) ⇔ (r1 = r2)
   
   [RAT_EQ_ALT]  Theorem
      
      |- ∀r1 r2. (r1 = r2) ⇔ (rat_nmr r1 * rat_dnm r2 = rat_nmr r2 * rat_dnm r1)
   
   [RAT_EQ_CALCULATE]  Theorem
      
      |- ∀f1 f2.
           (abs_rat f1 = abs_rat f2) ⇔
           (frac_nmr f1 * frac_dnm f2 = frac_nmr f2 * frac_dnm f1)
   
   [RAT_EQ_LADD]  Theorem
      
      |- ∀r1 r2 r3. (r3 + r1 = r3 + r2) ⇔ (r1 = r2)
   
   [RAT_EQ_LMUL]  Theorem
      
      |- ∀r1 r2 r3. r3 ≠ 0 ⇒ ((r3 * r1 = r3 * r2) ⇔ (r1 = r2))
   
   [RAT_EQ_NUM_CALCULATE]  Theorem
      
      |- (∀n m. (&n = &m) ⇔ (n = m)) ∧ (∀n m. (&n = -&m) ⇔ (n = 0) ∧ (m = 0)) ∧
         (∀n m. (-&n = &m) ⇔ (n = 0) ∧ (m = 0)) ∧ ∀n m. (-&n = -&m) ⇔ (n = m)
   
   [RAT_EQ_RADD]  Theorem
      
      |- ∀r1 r2 r3. (r1 + r3 = r2 + r3) ⇔ (r1 = r2)
   
   [RAT_EQ_RMUL]  Theorem
      
      |- ∀r1 r2 r3. r3 ≠ 0 ⇒ ((r1 * r3 = r2 * r3) ⇔ (r1 = r2))
   
   [RAT_EQ_SUB0]  Theorem
      
      |- ∀r1 r2. (r1 − r2 = 0) ⇔ (r1 = r2)
   
   [RAT_LDISTRIB]  Theorem
      
      |- ∀a b c. c * (a + b) = c * a + c * b
   
   [RAT_LDIV_EQ]  Theorem
      
      |- ∀r1 r2 r3. r2 ≠ 0 ⇒ ((r1 / r2 = r3) ⇔ (r1 = r2 * r3))
   
   [RAT_LDIV_LES_NEG]  Theorem
      
      |- ∀r1 r2 r3. r2 < 0 ⇒ (r1 / r2 < r3 ⇔ r2 * r3 < r1)
   
   [RAT_LDIV_LES_POS]  Theorem
      
      |- ∀r1 r2 r3. 0 < r2 ⇒ (r1 / r2 < r3 ⇔ r1 < r2 * r3)
   
   [RAT_LEQ0_NMR]  Theorem
      
      |- ∀r1. r1 ≤ 0 ⇔ rat_nmr r1 ≤ 0
   
   [RAT_LEQ_ANTISYM]  Theorem
      
      |- ∀r1 r2. r1 ≤ r2 ∧ r2 ≤ r1 ⇒ (r1 = r2)
   
   [RAT_LEQ_LES]  Theorem
      
      |- ∀r1 r2. ¬(r2 < r1) ⇔ r1 ≤ r2
   
   [RAT_LEQ_LES_TRANS]  Theorem
      
      |- ∀a b c. a ≤ b ∧ b < c ⇒ a < c
   
   [RAT_LEQ_REF]  Theorem
      
      |- ∀r1. r1 ≤ r1
   
   [RAT_LEQ_TRANS]  Theorem
      
      |- ∀r1 r2 r3. r1 ≤ r2 ∧ r2 ≤ r3 ⇒ r1 ≤ r3
   
   [RAT_LES0_LEQ0_ADD]  Theorem
      
      |- ∀r1 r2. r1 < 0 ⇒ r2 ≤ 0 ⇒ r1 + r2 < 0
   
   [RAT_LES0_LES0_ADD]  Theorem
      
      |- ∀r1 r2. r1 < 0 ⇒ r2 < 0 ⇒ r1 + r2 < 0
   
   [RAT_LES0_NMR]  Theorem
      
      |- ∀r1. r1 < 0 ⇔ rat_nmr r1 < 0
   
   [RAT_LES_01]  Theorem
      
      |- 0 < 1
   
   [RAT_LES_0SUB]  Theorem
      
      |- ∀r1 r2. 0 < r1 − r2 ⇔ r2 < r1
   
   [RAT_LES_AINV]  Theorem
      
      |- ∀r1 r2. -r1 < -r2 ⇔ r2 < r1
   
   [RAT_LES_ANTISYM]  Theorem
      
      |- ∀r1 r2. r1 < r2 ⇒ ¬(r2 < r1)
   
   [RAT_LES_CALCULATE]  Theorem
      
      |- ∀f1 f2.
           abs_rat f1 < abs_rat f2 ⇔
           frac_nmr f1 * frac_dnm f2 < frac_nmr f2 * frac_dnm f1
   
   [RAT_LES_IMP_LEQ]  Theorem
      
      |- ∀r1 r2. r1 < r2 ⇒ r1 ≤ r2
   
   [RAT_LES_IMP_NEQ]  Theorem
      
      |- ∀r1 r2. r1 < r2 ⇒ r1 ≠ r2
   
   [RAT_LES_LADD]  Theorem
      
      |- ∀r1 r2 r3. r3 + r1 < r3 + r2 ⇔ r1 < r2
   
   [RAT_LES_LEQ]  Theorem
      
      |- ∀r1 r2. ¬(r2 ≤ r1) ⇔ r1 < r2
   
   [RAT_LES_LEQ2]  Theorem
      
      |- ∀r1 r2. r1 < r2 ⇔ r1 ≤ r2 ∧ ¬(r2 ≤ r1)
   
   [RAT_LES_LEQ_TRANS]  Theorem
      
      |- ∀a b c. a < b ∧ b ≤ c ⇒ a < c
   
   [RAT_LES_LMUL_NEG]  Theorem
      
      |- ∀r1 r2 r3. r3 < 0 ⇒ (r3 * r2 < r3 * r1 ⇔ r1 < r2)
   
   [RAT_LES_LMUL_POS]  Theorem
      
      |- ∀r1 r2 r3. 0 < r3 ⇒ (r3 * r1 < r3 * r2 ⇔ r1 < r2)
   
   [RAT_LES_RADD]  Theorem
      
      |- ∀r1 r2 r3. r1 + r3 < r2 + r3 ⇔ r1 < r2
   
   [RAT_LES_REF]  Theorem
      
      |- ∀r1. ¬(r1 < r1)
   
   [RAT_LES_RMUL_NEG]  Theorem
      
      |- ∀r1 r2 r3. r3 < 0 ⇒ (r2 * r3 < r1 * r3 ⇔ r1 < r2)
   
   [RAT_LES_RMUL_POS]  Theorem
      
      |- ∀r1 r2 r3. 0 < r3 ⇒ (r1 * r3 < r2 * r3 ⇔ r1 < r2)
   
   [RAT_LES_SUB0]  Theorem
      
      |- ∀r1 r2. r1 − r2 < 0 ⇔ r1 < r2
   
   [RAT_LES_TOTAL]  Theorem
      
      |- ∀r1 r2. r1 < r2 ∨ (r1 = r2) ∨ r2 < r1
   
   [RAT_LES_TRANS]  Theorem
      
      |- ∀r1 r2 r3. r1 < r2 ∧ r2 < r3 ⇒ r1 < r3
   
   [RAT_LSUB_EQ]  Theorem
      
      |- ∀r1 r2 r3. (r1 − r2 = r3) ⇔ (r1 = r2 + r3)
   
   [RAT_LSUB_LES]  Theorem
      
      |- ∀r1 r2 r3. r1 − r2 < r3 ⇔ r1 < r2 + r3
   
   [RAT_MINV_CALCULATE]  Theorem
      
      |- ∀f1. 0 ≠ frac_nmr f1 ⇒ (rat_minv (abs_rat f1) = abs_rat (frac_minv f1))
   
   [RAT_MINV_CONG]  Theorem
      
      |- ∀x.
           frac_nmr x ≠ 0 ⇒
           (abs_rat (frac_minv (rep_rat (abs_rat x))) = abs_rat (frac_minv x))
   
   [RAT_MINV_LES]  Theorem
      
      |- ∀r1. 0 < r1 ⇒ (rat_minv r1 < 0 ⇔ r1 < 0) ∧ (0 < rat_minv r1 ⇔ 0 < r1)
   
   [RAT_MUL_ASSOC]  Theorem
      
      |- ∀a b c. a * (b * c) = a * b * c
   
   [RAT_MUL_CALCULATE]  Theorem
      
      |- ∀f1 f2. abs_rat f1 * abs_rat f2 = abs_rat (frac_mul f1 f2)
   
   [RAT_MUL_COMM]  Theorem
      
      |- ∀a b. a * b = b * a
   
   [RAT_MUL_CONG]  Theorem
      
      |- (∀x y.
            abs_rat (frac_mul (rep_rat (abs_rat x)) y) = abs_rat (frac_mul x y)) ∧
         ∀x y. abs_rat (frac_mul x (rep_rat (abs_rat y))) = abs_rat (frac_mul x y)
   
   [RAT_MUL_CONG1]  Theorem
      
      |- ∀x y. abs_rat (frac_mul (rep_rat (abs_rat x)) y) = abs_rat (frac_mul x y)
   
   [RAT_MUL_CONG2]  Theorem
      
      |- ∀x y. abs_rat (frac_mul x (rep_rat (abs_rat y))) = abs_rat (frac_mul x y)
   
   [RAT_MUL_LID]  Theorem
      
      |- ∀a. 1 * a = a
   
   [RAT_MUL_LINV]  Theorem
      
      |- ∀a. a ≠ 0 ⇒ (rat_minv a * a = 1)
   
   [RAT_MUL_LZERO]  Theorem
      
      |- ∀r1. 0 * r1 = 0
   
   [RAT_MUL_NUM_CALCULATE]  Theorem
      
      |- (∀n m. &n * &m = &(n * m)) ∧ (∀n m. -&n * &m = -&(n * m)) ∧
         (∀n m. &n * -&m = -&(n * m)) ∧ ∀n m. -&n * -&m = &(n * m)
   
   [RAT_MUL_ONE_ONE]  Theorem
      
      |- ∀r1. r1 ≠ 0 ⇔ ONE_ONE ($* r1)
   
   [RAT_MUL_RID]  Theorem
      
      |- ∀a. a * 1 = a
   
   [RAT_MUL_RINV]  Theorem
      
      |- ∀a. a ≠ 0 ⇒ (a * rat_minv a = 1)
   
   [RAT_MUL_RZERO]  Theorem
      
      |- ∀r1. r1 * 0 = 0
   
   [RAT_MUL_SIGN_CASES]  Theorem
      
      |- ∀p q.
           (0 < p * q ⇔ 0 < p ∧ 0 < q ∨ p < 0 ∧ q < 0) ∧
           (p * q < 0 ⇔ 0 < p ∧ q < 0 ∨ p < 0 ∧ 0 < q)
   
   [RAT_NMRDNM_EQ]  Theorem
      
      |- (abs_rat (abs_frac (frac_nmr f1,frac_dnm f1)) = 1) ⇔
         (frac_nmr f1 = frac_dnm f1)
   
   [RAT_NMREQ0_CONG]  Theorem
      
      |- ∀f1. (frac_nmr (rep_rat (abs_rat f1)) = 0) ⇔ (frac_nmr f1 = 0)
   
   [RAT_NMRGT0_CONG]  Theorem
      
      |- ∀f1. frac_nmr (rep_rat (abs_rat f1)) > 0 ⇔ frac_nmr f1 > 0
   
   [RAT_NMRLT0_CONG]  Theorem
      
      |- ∀f1. frac_nmr (rep_rat (abs_rat f1)) < 0 ⇔ frac_nmr f1 < 0
   
   [RAT_NO_IDDIV]  Theorem
      
      |- ∀r1 r2. (r1 * r2 = r2) ⇔ (r1 = 1) ∨ (r2 = 0)
   
   [RAT_NO_ZERODIV]  Theorem
      
      |- ∀r1 r2. (r1 = 0) ∨ (r2 = 0) ⇔ (r1 * r2 = 0)
   
   [RAT_NO_ZERODIV_NEG]  Theorem
      
      |- ∀r1 r2. r1 * r2 ≠ 0 ⇔ r1 ≠ 0 ∧ r2 ≠ 0
   
   [RAT_OF_NUM]  Theorem
      
      |- ∀n. (0 = rat_0) ∧ ∀n. &SUC n = &n + rat_1
   
   [RAT_OF_NUM_CALCULATE]  Theorem
      
      |- ∀n1. &n1 = abs_rat (abs_frac (&n1,1))
   
   [RAT_RDISTRIB]  Theorem
      
      |- ∀a b c. (a + b) * c = a * c + b * c
   
   [RAT_RDIV_EQ]  Theorem
      
      |- ∀r1 r2 r3. r3 ≠ 0 ⇒ ((r1 = r2 / r3) ⇔ (r1 * r3 = r2))
   
   [RAT_RDIV_LES_NEG]  Theorem
      
      |- ∀r1 r2 r3. r3 < 0 ⇒ (r1 < r2 / r3 ⇔ r2 < r1 * r3)
   
   [RAT_RDIV_LES_POS]  Theorem
      
      |- ∀r1 r2 r3. 0 < r3 ⇒ (r1 < r2 / r3 ⇔ r1 * r3 < r2)
   
   [RAT_RSUB_EQ]  Theorem
      
      |- ∀r1 r2 r3. (r1 = r2 − r3) ⇔ (r1 + r3 = r2)
   
   [RAT_RSUB_LES]  Theorem
      
      |- ∀r1 r2 r3. r1 < r2 − r3 ⇔ r1 + r3 < r2
   
   [RAT_SAVE]  Theorem
      
      |- ∀r1. ∃a1 b1. r1 = abs_rat (frac_save a1 b1)
   
   [RAT_SAVE_MINV]  Theorem
      
      |- ∀a1 b1.
           abs_rat (frac_save a1 b1) ≠ 0 ⇒
           (rat_minv (abs_rat (frac_save a1 b1)) =
            abs_rat (frac_save (SGN a1 * (&b1 + 1)) (Num (ABS a1 − 1))))
   
   [RAT_SAVE_NUM]  Theorem
      
      |- ∀n. &n = abs_rat (frac_save (&n) 0)
   
   [RAT_SAVE_TO_CONS]  Theorem
      
      |- ∀a1 b1. abs_rat (frac_save a1 b1) = a1 // (&b1 + 1)
   
   [RAT_SGN_0]  Theorem
      
      |- rat_sgn 0 = 0
   
   [RAT_SGN_AINV]  Theorem
      
      |- ∀r1. -rat_sgn (-r1) = rat_sgn r1
   
   [RAT_SGN_CALCULATE]  Theorem
      
      |- rat_sgn (abs_rat f1) = frac_sgn f1
   
   [RAT_SGN_CLAUSES]  Theorem
      
      |- ∀r1.
           ((rat_sgn r1 = -1) ⇔ r1 < 0) ∧ ((rat_sgn r1 = 0) ⇔ (r1 = 0)) ∧
           ((rat_sgn r1 = 1) ⇔ r1 > 0)
   
   [RAT_SGN_COMPLEMENT]  Theorem
      
      |- ∀r1.
           (rat_sgn r1 ≠ -1 ⇔ (rat_sgn r1 = 0) ∨ (rat_sgn r1 = 1)) ∧
           (rat_sgn r1 ≠ 0 ⇔ (rat_sgn r1 = -1) ∨ (rat_sgn r1 = 1)) ∧
           (rat_sgn r1 ≠ 1 ⇔ (rat_sgn r1 = -1) ∨ (rat_sgn r1 = 0))
   
   [RAT_SGN_CONG]  Theorem
      
      |- ∀f1. frac_sgn (rep_rat (abs_rat f1)) = frac_sgn f1
   
   [RAT_SGN_MINV]  Theorem
      
      |- ∀r1. r1 ≠ 0 ⇒ (rat_sgn (rat_minv r1) = rat_sgn r1)
   
   [RAT_SGN_MUL]  Theorem
      
      |- ∀r1 r2. rat_sgn (r1 * r2) = rat_sgn r1 * rat_sgn r2
   
   [RAT_SGN_TOTAL]  Theorem
      
      |- ∀r1. (rat_sgn r1 = -1) ∨ (rat_sgn r1 = 0) ∨ (rat_sgn r1 = 1)
   
   [RAT_SUB_ADDAINV]  Theorem
      
      |- ∀r1 r2. r1 − r2 = r1 + -r2
   
   [RAT_SUB_CALCULATE]  Theorem
      
      |- ∀f1 f2. abs_rat f1 − abs_rat f2 = abs_rat (frac_sub f1 f2)
   
   [RAT_SUB_CONG]  Theorem
      
      |- (∀x y.
            abs_rat (frac_sub (rep_rat (abs_rat x)) y) = abs_rat (frac_sub x y)) ∧
         ∀x y. abs_rat (frac_sub x (rep_rat (abs_rat y))) = abs_rat (frac_sub x y)
   
   [RAT_SUB_CONG1]  Theorem
      
      |- ∀x y. abs_rat (frac_sub (rep_rat (abs_rat x)) y) = abs_rat (frac_sub x y)
   
   [RAT_SUB_CONG2]  Theorem
      
      |- ∀x y. abs_rat (frac_sub x (rep_rat (abs_rat y))) = abs_rat (frac_sub x y)
   
   [RAT_SUB_ID]  Theorem
      
      |- ∀r. r − r = 0
   
   [RAT_SUB_LDISTRIB]  Theorem
      
      |- ∀a b c. c * (a − b) = c * a − c * b
   
   [RAT_SUB_LID]  Theorem
      
      |- ∀r1. 0 − r1 = -r1
   
   [RAT_SUB_RDISTRIB]  Theorem
      
      |- ∀a b c. (a − b) * c = a * c − b * c
   
   [RAT_SUB_RID]  Theorem
      
      |- ∀r1. r1 − 0 = r1
   
   [rat_0]  Theorem
      
      |- 0 = abs_rat frac_0
   
   [rat_1]  Theorem
      
      |- 1 = abs_rat frac_1
   
   [rat_ABS_REP_CLASS]  Theorem
      
      |- (∀a. abs_rat_CLASS (rep_rat_CLASS a) = a) ∧
         ∀c.
           (∃r. rat_equiv r r ∧ (c = rat_equiv r)) ⇔
           (rep_rat_CLASS (abs_rat_CLASS c) = c)
   
   [rat_QUOTIENT]  Theorem
      
      |- QUOTIENT rat_equiv abs_rat rep_rat
   
   [rat_def]  Theorem
      
      |- QUOTIENT rat_equiv abs_rat rep_rat
   
   [rat_of_num_def]  Theorem
      
      |- (0 = rat_0) ∧ (&SUC 0 = rat_1) ∧ ∀n. &SUC (SUC n) = &SUC n + rat_1
   
   [rat_of_num_ind]  Theorem
      
      |- ∀P. P 0 ∧ P (SUC 0) ∧ (∀n. P (SUC n) ⇒ P (SUC (SUC n))) ⇒ ∀v. P v
   
   
*)
end
