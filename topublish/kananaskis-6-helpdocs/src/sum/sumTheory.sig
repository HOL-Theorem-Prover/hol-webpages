signature sumTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val INL_DEF : thm
    val INR_DEF : thm
    val ISL : thm
    val ISR : thm
    val IS_SUM_REP : thm
    val OUTL : thm
    val OUTR : thm
    val SUM_MAP_def : thm
    val sum_ISO_DEF : thm
    val sum_TY_DEF : thm
    val sum_case_def : thm
  
  (*  Theorems  *)
    val FORALL_SUM : thm
    val INL : thm
    val INR : thm
    val INR_INL_11 : thm
    val INR_neq_INL : thm
    val ISL_OR_ISR : thm
    val SUM_MAP : thm
    val SUM_MAP_CASE : thm
    val SUM_MAP_I : thm
    val sum_Axiom : thm
    val sum_CASES : thm
    val sum_INDUCT : thm
    val sum_axiom : thm
    val sum_case_cong : thm
    val sum_distinct : thm
    val sum_distinct1 : thm
  
  val sum_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [combin] Parent theory of "sum"
   
   [sat] Parent theory of "sum"
   
   [INL_DEF]  Definition
      
      |- ∀e. INL e = ABS_sum (λb x y. (x = e) ∧ b)
   
   [INR_DEF]  Definition
      
      |- ∀e. INR e = ABS_sum (λb x y. (y = e) ∧ ¬b)
   
   [ISL]  Definition
      
      |- (∀x. ISL (INL x)) ∧ ∀y. ¬ISL (INR y)
   
   [ISR]  Definition
      
      |- (∀x. ISR (INR x)) ∧ ∀y. ¬ISR (INL y)
   
   [IS_SUM_REP]  Definition
      
      |- ∀f.
           IS_SUM_REP f ⇔
           ∃v1 v2. (f = (λb x y. (x = v1) ∧ b)) ∨ (f = (λb x y. (y = v2) ∧ ¬b))
   
   [OUTL]  Definition
      
      |- ∀x. OUTL (INL x) = x
   
   [OUTR]  Definition
      
      |- ∀x. OUTR (INR x) = x
   
   [SUM_MAP_def]  Definition
      
      |- (∀f g a. (f ++ g) (INL a) = INL (f a)) ∧
         ∀f g b. (f ++ g) (INR b) = INR (g b)
   
   [sum_ISO_DEF]  Definition
      
      |- (∀a. ABS_sum (REP_sum a) = a) ∧ ∀r. IS_SUM_REP r ⇔ (REP_sum (ABS_sum r) = r)
   
   [sum_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION IS_SUM_REP rep
   
   [sum_case_def]  Definition
      
      |- (∀f g x. sum_case f g (INL x) = f x) ∧ ∀f g y. sum_case f g (INR y) = g y
   
   [FORALL_SUM]  Theorem
      
      |- (∀s. P s) ⇔ (∀x. P (INL x)) ∧ ∀y. P (INR y)
   
   [INL]  Theorem
      
      |- ∀x. ISL x ⇒ (INL (OUTL x) = x)
   
   [INR]  Theorem
      
      |- ∀x. ISR x ⇒ (INR (OUTR x) = x)
   
   [INR_INL_11]  Theorem
      
      |- (∀y x. (INL x = INL y) ⇔ (x = y)) ∧ ∀y x. (INR x = INR y) ⇔ (x = y)
   
   [INR_neq_INL]  Theorem
      
      |- ∀v1 v2. INR v2 ≠ INL v1
   
   [ISL_OR_ISR]  Theorem
      
      |- ∀x. ISL x ∨ ISR x
   
   [SUM_MAP]  Theorem
      
      |- ∀f g z. (f ++ g) z = if ISL z then INL (f (OUTL z)) else INR (g (OUTR z))
   
   [SUM_MAP_CASE]  Theorem
      
      |- ∀f g z. (f ++ g) z = sum_case (INL o f) (INR o g) z
   
   [SUM_MAP_I]  Theorem
      
      |- I ++ I = I
   
   [sum_Axiom]  Theorem
      
      |- ∀f g. ∃h. (∀x. h (INL x) = f x) ∧ ∀y. h (INR y) = g y
   
   [sum_CASES]  Theorem
      
      |- ∀ss. (∃x. ss = INL x) ∨ ∃y. ss = INR y
   
   [sum_INDUCT]  Theorem
      
      |- ∀P. (∀x. P (INL x)) ∧ (∀y. P (INR y)) ⇒ ∀s. P s
   
   [sum_axiom]  Theorem
      
      |- ∀f g. ∃!h. (h o INL = f) ∧ (h o INR = g)
   
   [sum_case_cong]  Theorem
      
      |- ∀M M' f g.
           (M = M') ∧ (∀x. (M' = INL x) ⇒ (f x = f' x)) ∧
           (∀y. (M' = INR y) ⇒ (g y = g' y)) ⇒
           (sum_case f g M = sum_case f' g' M')
   
   [sum_distinct]  Theorem
      
      |- ∀x y. INL x ≠ INR y
   
   [sum_distinct1]  Theorem
      
      |- ∀x y. INR y ≠ INL x
   
   
*)
end
