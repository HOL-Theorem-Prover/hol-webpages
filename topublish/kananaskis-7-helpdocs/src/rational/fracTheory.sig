signature fracTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val frac_0_def : thm
    val frac_1_def : thm
    val frac_TY_DEF : thm
    val frac_add_def : thm
    val frac_ainv_def : thm
    val frac_div_def : thm
    val frac_dnm_def : thm
    val frac_minv_def : thm
    val frac_mul_def : thm
    val frac_nmr_def : thm
    val frac_save_def : thm
    val frac_sgn_def : thm
    val frac_sub_def : thm
    val frac_tybij : thm
    val les_abs_def : thm
  
  (*  Theorems  *)
    val DNM : thm
    val FRAC : thm
    val FRAC_0_SAVE : thm
    val FRAC_1_0 : thm
    val FRAC_1_SAVE : thm
    val FRAC_ABS_SGN : thm
    val FRAC_ADD_ASSOC : thm
    val FRAC_ADD_CALCULATE : thm
    val FRAC_ADD_COMM : thm
    val FRAC_ADD_RID : thm
    val FRAC_ADD_SAVE : thm
    val FRAC_AINV_0 : thm
    val FRAC_AINV_ADD : thm
    val FRAC_AINV_AINV : thm
    val FRAC_AINV_CALCULATE : thm
    val FRAC_AINV_LMUL : thm
    val FRAC_AINV_ONEONE : thm
    val FRAC_AINV_ONTO : thm
    val FRAC_AINV_RMUL : thm
    val FRAC_AINV_SAVE : thm
    val FRAC_AINV_SUB : thm
    val FRAC_DIV_CALCULATE : thm
    val FRAC_DNMPOS : thm
    val FRAC_DNM_SAVE : thm
    val FRAC_EQ : thm
    val FRAC_EQ_ALT : thm
    val FRAC_MINV_CALCULATE : thm
    val FRAC_MINV_SAVE : thm
    val FRAC_MULT_CALCULATE : thm
    val FRAC_MUL_ASSOC : thm
    val FRAC_MUL_COMM : thm
    val FRAC_MUL_RID : thm
    val FRAC_MUL_SAVE : thm
    val FRAC_NMR_SAVE : thm
    val FRAC_NOT_EQ : thm
    val FRAC_SGN_AINV : thm
    val FRAC_SGN_CALCULATE : thm
    val FRAC_SGN_CASES : thm
    val FRAC_SGN_IMP_EQGT : thm
    val FRAC_SGN_MUL : thm
    val FRAC_SGN_MUL2 : thm
    val FRAC_SGN_NEG : thm
    val FRAC_SGN_NOT_NEG : thm
    val FRAC_SGN_POS : thm
    val FRAC_SGN_TOTAL : thm
    val FRAC_SUB_ADD : thm
    val FRAC_SUB_CALCULATE : thm
    val FRAC_SUB_SUB : thm
    val NMR : thm
    val frac_bij : thm
  
  val frac_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [intExtension] Parent theory of "frac"
   
   [frac_0_def]  Definition
      
      |- frac_0 = abs_frac (0,1)
   
   [frac_1_def]  Definition
      
      |- frac_1 = abs_frac (1,1)
   
   [frac_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION (λf. 0 < SND f) rep
   
   [frac_add_def]  Definition
      
      |- ∀f1 f2.
           frac_add f1 f2 =
           abs_frac
             (frac_nmr f1 * frac_dnm f2 + frac_nmr f2 * frac_dnm f1,
              frac_dnm f1 * frac_dnm f2)
   
   [frac_ainv_def]  Definition
      
      |- ∀f1. frac_ainv f1 = abs_frac (-frac_nmr f1,frac_dnm f1)
   
   [frac_div_def]  Definition
      
      |- ∀f1 f2. frac_div f1 f2 = frac_mul f1 (frac_minv f2)
   
   [frac_dnm_def]  Definition
      
      |- ∀f. frac_dnm f = SND (rep_frac f)
   
   [frac_minv_def]  Definition
      
      |- ∀f1.
           frac_minv f1 =
           abs_frac (frac_sgn f1 * frac_dnm f1,ABS (frac_nmr f1))
   
   [frac_mul_def]  Definition
      
      |- ∀f1 f2.
           frac_mul f1 f2 =
           abs_frac (frac_nmr f1 * frac_nmr f2,frac_dnm f1 * frac_dnm f2)
   
   [frac_nmr_def]  Definition
      
      |- ∀f. frac_nmr f = FST (rep_frac f)
   
   [frac_save_def]  Definition
      
      |- ∀nmr dnm. frac_save nmr dnm = abs_frac (nmr,&dnm + 1)
   
   [frac_sgn_def]  Definition
      
      |- ∀f1. frac_sgn f1 = SGN (frac_nmr f1)
   
   [frac_sub_def]  Definition
      
      |- ∀f1 f2. frac_sub f1 f2 = frac_add f1 (frac_ainv f2)
   
   [frac_tybij]  Definition
      
      |- (∀a. abs_frac (rep_frac a) = a) ∧
         ∀r. (λf. 0 < SND f) r ⇔ (rep_frac (abs_frac r) = r)
   
   [les_abs_def]  Definition
      
      |- ∀f1 f2.
           les_abs f1 f2 ⇔
           frac_nmr f1 * frac_dnm f2 < frac_nmr f2 * frac_dnm f1
   
   [DNM]  Theorem
      
      |- ∀a b. 0 < b ⇒ (frac_dnm (abs_frac (a,b)) = b)
   
   [FRAC]  Theorem
      
      |- ∀f. abs_frac (frac_nmr f,frac_dnm f) = f
   
   [FRAC_0_SAVE]  Theorem
      
      |- frac_0 = frac_save 0 0
   
   [FRAC_1_0]  Theorem
      
      |- frac_1 ≠ frac_0
   
   [FRAC_1_SAVE]  Theorem
      
      |- frac_1 = frac_save 1 0
   
   [FRAC_ABS_SGN]  Theorem
      
      |- ∀f1. frac_nmr f1 ≠ 0 ⇒ (ABS (frac_sgn f1) = 1)
   
   [FRAC_ADD_ASSOC]  Theorem
      
      |- ∀a b c. frac_add a (frac_add b c) = frac_add (frac_add a b) c
   
   [FRAC_ADD_CALCULATE]  Theorem
      
      |- ∀a1 b1 a2 b2.
           0 < b1 ⇒
           0 < b2 ⇒
           (frac_add (abs_frac (a1,b1)) (abs_frac (a2,b2)) =
            abs_frac (a1 * b2 + a2 * b1,b1 * b2))
   
   [FRAC_ADD_COMM]  Theorem
      
      |- ∀a b. frac_add a b = frac_add b a
   
   [FRAC_ADD_RID]  Theorem
      
      |- ∀a. frac_add a frac_0 = a
   
   [FRAC_ADD_SAVE]  Theorem
      
      |- ∀a1 b1 a2 b2.
           frac_add (frac_save a1 b1) (frac_save a2 b2) =
           frac_save (a1 * &b2 + a2 * &b1 + a1 + a2) (b1 * b2 + b1 + b2)
   
   [FRAC_AINV_0]  Theorem
      
      |- frac_ainv frac_0 = frac_0
   
   [FRAC_AINV_ADD]  Theorem
      
      |- ∀f1 f2.
           frac_ainv (frac_add f1 f2) =
           frac_add (frac_ainv f1) (frac_ainv f2)
   
   [FRAC_AINV_AINV]  Theorem
      
      |- ∀f1. frac_ainv (frac_ainv f1) = f1
   
   [FRAC_AINV_CALCULATE]  Theorem
      
      |- ∀a1 b1.
           0 < b1 ⇒ (frac_ainv (abs_frac (a1,b1)) = abs_frac (-a1,b1))
   
   [FRAC_AINV_LMUL]  Theorem
      
      |- ∀f1 f2. frac_ainv (frac_mul f1 f2) = frac_mul (frac_ainv f1) f2
   
   [FRAC_AINV_ONEONE]  Theorem
      
      |- ONE_ONE frac_ainv
   
   [FRAC_AINV_ONTO]  Theorem
      
      |- ONTO frac_ainv
   
   [FRAC_AINV_RMUL]  Theorem
      
      |- ∀f1 f2. frac_ainv (frac_mul f1 f2) = frac_mul f1 (frac_ainv f2)
   
   [FRAC_AINV_SAVE]  Theorem
      
      |- ∀a1 b1. frac_ainv (frac_save a1 b1) = frac_save (-a1) b1
   
   [FRAC_AINV_SUB]  Theorem
      
      |- ∀f1 f2. frac_ainv (frac_sub f2 f1) = frac_sub f1 f2
   
   [FRAC_DIV_CALCULATE]  Theorem
      
      |- ∀a1 b1 a2 b2.
           0 < b1 ⇒
           0 < b2 ⇒
           a2 ≠ 0 ⇒
           (frac_div (abs_frac (a1,b1)) (abs_frac (a2,b2)) =
            abs_frac (a1 * SGN a2 * b2,b1 * ABS a2))
   
   [FRAC_DNMPOS]  Theorem
      
      |- ∀f. 0 < frac_dnm f
   
   [FRAC_DNM_SAVE]  Theorem
      
      |- ∀a1 b1. frac_dnm (frac_save a1 b1) = &b1 + 1
   
   [FRAC_EQ]  Theorem
      
      |- ∀a1 b1 a2 b2.
           0 < b1 ⇒
           0 < b2 ⇒
           ((abs_frac (a1,b1) = abs_frac (a2,b2)) ⇔ (a1 = a2) ∧ (b1 = b2))
   
   [FRAC_EQ_ALT]  Theorem
      
      |- ∀f1 f2.
           (f1 = f2) ⇔
           (frac_nmr f1 = frac_nmr f2) ∧ (frac_dnm f1 = frac_dnm f2)
   
   [FRAC_MINV_CALCULATE]  Theorem
      
      |- ∀a1 b1.
           0 < b1 ⇒
           a1 ≠ 0 ⇒
           (frac_minv (abs_frac (a1,b1)) = abs_frac (SGN a1 * b1,ABS a1))
   
   [FRAC_MINV_SAVE]  Theorem
      
      |- ∀a1 b1.
           a1 ≠ 0 ⇒
           (frac_minv (frac_save a1 b1) =
            frac_save (SGN a1 * (&b1 + 1)) (Num (ABS a1 − 1)))
   
   [FRAC_MULT_CALCULATE]  Theorem
      
      |- ∀a1 b1 a2 b2.
           0 < b1 ⇒
           0 < b2 ⇒
           (frac_mul (abs_frac (a1,b1)) (abs_frac (a2,b2)) =
            abs_frac (a1 * a2,b1 * b2))
   
   [FRAC_MUL_ASSOC]  Theorem
      
      |- ∀a b c. frac_mul a (frac_mul b c) = frac_mul (frac_mul a b) c
   
   [FRAC_MUL_COMM]  Theorem
      
      |- ∀a b. frac_mul a b = frac_mul b a
   
   [FRAC_MUL_RID]  Theorem
      
      |- ∀a. frac_mul a frac_1 = a
   
   [FRAC_MUL_SAVE]  Theorem
      
      |- ∀a1 b1 a2 b2.
           frac_mul (frac_save a1 b1) (frac_save a2 b2) =
           frac_save (a1 * a2) (b1 * b2 + b1 + b2)
   
   [FRAC_NMR_SAVE]  Theorem
      
      |- ∀a1 b1. frac_nmr (frac_save a1 b1) = a1
   
   [FRAC_NOT_EQ]  Theorem
      
      |- ∀a1 b1 a2 b2.
           0 < b1 ⇒
           0 < b2 ⇒
           (a1,b1) ≠ (a2,b2) ⇒
           abs_frac (a1,b1) ≠ abs_frac (a2,b2)
   
   [FRAC_SGN_AINV]  Theorem
      
      |- ∀f1. -frac_sgn (frac_ainv f1) = frac_sgn f1
   
   [FRAC_SGN_CALCULATE]  Theorem
      
      |- ∀a1 b1. 0 < b1 ⇒ (frac_sgn (abs_frac (a1,b1)) = SGN a1)
   
   [FRAC_SGN_CASES]  Theorem
      
      |- ∀f1 P.
           ((frac_sgn f1 = -1) ⇒ P) ∧ ((frac_sgn f1 = 0) ⇒ P) ∧
           ((frac_sgn f1 = 1) ⇒ P) ⇒
           P
   
   [FRAC_SGN_IMP_EQGT]  Theorem
      
      |- ∀f1. frac_sgn f1 ≠ -1 ⇔ (frac_sgn f1 = 0) ∨ (frac_sgn f1 = 1)
   
   [FRAC_SGN_MUL]  Theorem
      
      |- ∀f1 f2. frac_sgn (frac_mul f1 f2) = frac_sgn f1 * frac_sgn f2
   
   [FRAC_SGN_MUL2]  Theorem
      
      |- ∀f1 f2. frac_sgn (frac_mul f1 f2) = frac_sgn f1 * frac_sgn f2
   
   [FRAC_SGN_NEG]  Theorem
      
      |- ∀f. -frac_sgn (frac_ainv f) = frac_sgn f
   
   [FRAC_SGN_NOT_NEG]  Theorem
      
      |- ∀f1. frac_sgn f1 ≠ -1 ⇔ (0 = frac_nmr f1) ∨ 0 < frac_nmr f1
   
   [FRAC_SGN_POS]  Theorem
      
      |- ∀f1. (frac_sgn f1 = 1) ⇔ 0 < frac_nmr f1
   
   [FRAC_SGN_TOTAL]  Theorem
      
      |- ∀f1. (frac_sgn f1 = -1) ∨ (frac_sgn f1 = 0) ∨ (frac_sgn f1 = 1)
   
   [FRAC_SUB_ADD]  Theorem
      
      |- ∀a b c. frac_sub a (frac_add b c) = frac_sub (frac_sub a b) c
   
   [FRAC_SUB_CALCULATE]  Theorem
      
      |- ∀a1 b1 a2 b2.
           0 < b1 ⇒
           0 < b2 ⇒
           (frac_sub (abs_frac (a1,b1)) (abs_frac (a2,b2)) =
            abs_frac (a1 * b2 − a2 * b1,b1 * b2))
   
   [FRAC_SUB_SUB]  Theorem
      
      |- ∀a b c. frac_sub a (frac_sub b c) = frac_add (frac_sub a b) c
   
   [NMR]  Theorem
      
      |- ∀a b. 0 < b ⇒ (frac_nmr (abs_frac (a,b)) = a)
   
   [frac_bij]  Theorem
      
      |- (∀a. abs_frac (rep_frac a) = a) ∧
         ∀r. (λf. 0 < SND f) r ⇔ (rep_frac (abs_frac r) = r)
   
   
*)
end
