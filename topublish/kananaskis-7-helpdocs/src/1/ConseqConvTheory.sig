signature ConseqConvTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ASM_MARKER_DEF : thm
  
  (*  Theorems  *)
    val AND_CLAUSES_FX : thm
    val AND_CLAUSES_TX : thm
    val AND_CLAUSES_XF : thm
    val AND_CLAUSES_XT : thm
    val AND_CLAUSES_XX : thm
    val ASM_MARKER_THM : thm
    val COND_CLAUSES_CF : thm
    val COND_CLAUSES_CT : thm
    val COND_CLAUSES_FF : thm
    val COND_CLAUSES_FT : thm
    val COND_CLAUSES_ID : thm
    val COND_CLAUSES_TF : thm
    val COND_CLAUSES_TT : thm
    val IMP_CLAUSES_FX : thm
    val IMP_CLAUSES_TX : thm
    val IMP_CLAUSES_XF : thm
    val IMP_CLAUSES_XT : thm
    val IMP_CLAUSES_XX : thm
    val IMP_CONG_cond : thm
    val IMP_CONG_cond_simple : thm
    val IMP_CONG_conj_strengthen : thm
    val IMP_CONG_conj_weaken : thm
    val IMP_CONG_disj_strengthen : thm
    val IMP_CONG_disj_weaken : thm
    val IMP_CONG_imp_strengthen : thm
    val IMP_CONG_imp_weaken : thm
    val IMP_CONG_simple_imp_strengthen : thm
    val IMP_CONG_simple_imp_weaken : thm
    val NOT_CLAUSES_F : thm
    val NOT_CLAUSES_T : thm
    val NOT_CLAUSES_X : thm
    val OR_CLAUSES_FX : thm
    val OR_CLAUSES_TX : thm
    val OR_CLAUSES_XF : thm
    val OR_CLAUSES_XT : thm
    val OR_CLAUSES_XX : thm
    val exists_eq_thm : thm
    val false_imp : thm
    val forall_eq_thm : thm
    val true_imp : thm
  
  val ConseqConv_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bool] Parent theory of "ConseqConv"
   
   [ASM_MARKER_DEF]  Definition
      
      |- ASM_MARKER = (λy x. x)
   
   [AND_CLAUSES_FX]  Theorem
      
      |- ∀t. F ∧ t ⇔ F
   
   [AND_CLAUSES_TX]  Theorem
      
      |- ∀t. T ∧ t ⇔ t
   
   [AND_CLAUSES_XF]  Theorem
      
      |- ∀t. t ∧ F ⇔ F
   
   [AND_CLAUSES_XT]  Theorem
      
      |- ∀t. t ∧ T ⇔ t
   
   [AND_CLAUSES_XX]  Theorem
      
      |- ∀t. t ∧ t ⇔ t
   
   [ASM_MARKER_THM]  Theorem
      
      |- ∀y x. ASM_MARKER y x ⇔ x
   
   [COND_CLAUSES_CF]  Theorem
      
      |- ∀t1 t2. (if F then t1 else t2) = t2
   
   [COND_CLAUSES_CT]  Theorem
      
      |- ∀t1 t2. (if T then t1 else t2) = t1
   
   [COND_CLAUSES_FF]  Theorem
      
      |- ∀c x. (if c then x else F) ⇔ c ∧ x
   
   [COND_CLAUSES_FT]  Theorem
      
      |- ∀c x. (if c then x else T) ⇔ c ⇒ x
   
   [COND_CLAUSES_ID]  Theorem
      
      |- ∀b t. (if b then t else t) = t
   
   [COND_CLAUSES_TF]  Theorem
      
      |- ∀c x. (if c then F else x) ⇔ ¬c ∧ x
   
   [COND_CLAUSES_TT]  Theorem
      
      |- ∀c x. (if c then T else x) ⇔ ¬c ⇒ x
   
   [IMP_CLAUSES_FX]  Theorem
      
      |- ∀t. F ⇒ t ⇔ T
   
   [IMP_CLAUSES_TX]  Theorem
      
      |- ∀t. T ⇒ t ⇔ t
   
   [IMP_CLAUSES_XF]  Theorem
      
      |- ∀t. t ⇒ F ⇔ ¬t
   
   [IMP_CLAUSES_XT]  Theorem
      
      |- ∀t. t ⇒ T ⇔ T
   
   [IMP_CLAUSES_XX]  Theorem
      
      |- ∀t. t ⇒ t ⇔ T
   
   [IMP_CONG_cond]  Theorem
      
      |- ∀c x x' y y'.
           (c ⇒ x' ⇒ x) ∧ (¬c ⇒ y' ⇒ y) ⇒
           (if c then x' else y') ⇒
           if c then x else y
   
   [IMP_CONG_cond_simple]  Theorem
      
      |- ∀c x x' y y'.
           (x' ⇒ x) ∧ (y' ⇒ y) ⇒
           (if c then x' else y') ⇒
           if c then x else y
   
   [IMP_CONG_conj_strengthen]  Theorem
      
      |- ∀x x' y y'. (y ⇒ x' ⇒ x) ∧ (x' ⇒ y' ⇒ y) ⇒ x' ∧ y' ⇒ x ∧ y
   
   [IMP_CONG_conj_weaken]  Theorem
      
      |- ∀x x' y y'. (y ⇒ x ⇒ x') ∧ (x' ⇒ y ⇒ y') ⇒ x ∧ y ⇒ x' ∧ y'
   
   [IMP_CONG_disj_strengthen]  Theorem
      
      |- ∀x x' y y'. (¬y ⇒ x' ⇒ x) ∧ (¬x' ⇒ y' ⇒ y) ⇒ x' ∨ y' ⇒ x ∨ y
   
   [IMP_CONG_disj_weaken]  Theorem
      
      |- ∀x x' y y'. (¬y ⇒ x ⇒ x') ∧ (¬x' ⇒ y ⇒ y') ⇒ x ∨ y ⇒ x' ∨ y'
   
   [IMP_CONG_imp_strengthen]  Theorem
      
      |- ∀x x' y y'. (x ⇒ y' ⇒ y) ∧ (¬y' ⇒ x ⇒ x') ⇒ (x' ⇒ y') ⇒ x ⇒ y
   
   [IMP_CONG_imp_weaken]  Theorem
      
      |- ∀x x' y y'. (x ⇒ y ⇒ y') ∧ (¬y' ⇒ x' ⇒ x) ⇒ (x ⇒ y) ⇒ x' ⇒ y'
   
   [IMP_CONG_simple_imp_strengthen]  Theorem
      
      |- ∀x x' y y'. (x ⇒ x') ∧ (x' ⇒ y' ⇒ y) ⇒ (x' ⇒ y') ⇒ x ⇒ y
   
   [IMP_CONG_simple_imp_weaken]  Theorem
      
      |- ∀x x' y y'. (x' ⇒ x) ∧ (x' ⇒ y ⇒ y') ⇒ (x ⇒ y) ⇒ x' ⇒ y'
   
   [NOT_CLAUSES_F]  Theorem
      
      |- ¬F ⇔ T
   
   [NOT_CLAUSES_T]  Theorem
      
      |- ¬T ⇔ F
   
   [NOT_CLAUSES_X]  Theorem
      
      |- ∀t. ¬ ¬t ⇔ t
   
   [OR_CLAUSES_FX]  Theorem
      
      |- ∀t. F ∨ t ⇔ t
   
   [OR_CLAUSES_TX]  Theorem
      
      |- ∀t. T ∨ t ⇔ T
   
   [OR_CLAUSES_XF]  Theorem
      
      |- ∀t. t ∨ F ⇔ t
   
   [OR_CLAUSES_XT]  Theorem
      
      |- ∀t. t ∨ T ⇔ T
   
   [OR_CLAUSES_XX]  Theorem
      
      |- ∀t. t ∨ t ⇔ t
   
   [exists_eq_thm]  Theorem
      
      |- (∀s. P s ⇔ Q s) ⇒ ((∃s. P s) ⇔ ∃s. Q s)
   
   [false_imp]  Theorem
      
      |- ∀t. F ⇒ t
   
   [forall_eq_thm]  Theorem
      
      |- (∀s. P s ⇔ Q s) ⇒ ((∀s. P s) ⇔ ∀s. Q s)
   
   [true_imp]  Theorem
      
      |- ∀t. t ⇒ T
   
   
*)
end
