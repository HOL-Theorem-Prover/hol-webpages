signature pairTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ABS_REP_prod : thm
    val COMMA_DEF : thm
    val CURRY_DEF : thm
    val LEX_DEF : thm
    val PAIR : thm
    val PAIR_MAP : thm
    val RPROD_DEF : thm
    val UNCURRY : thm
    val pair_case_def : thm
    val prod_TY_DEF : thm
  
  (*  Theorems  *)
    val ABS_PAIR_THM : thm
    val CLOSED_PAIR_EQ : thm
    val CURRY_ONE_ONE_THM : thm
    val CURRY_UNCURRY_THM : thm
    val C_UNCURRY_L : thm
    val ELIM_PEXISTS : thm
    val ELIM_PEXISTS_EVAL : thm
    val ELIM_PFORALL : thm
    val ELIM_PFORALL_EVAL : thm
    val ELIM_UNCURRY : thm
    val EXISTS_PROD : thm
    val FORALL_PROD : thm
    val FORALL_UNCURRY : thm
    val FST : thm
    val FST_PAIR_MAP : thm
    val LAMBDA_PROD : thm
    val LET2_RAND : thm
    val LET2_RATOR : thm
    val LEX_DEF_THM : thm
    val PAIR_EQ : thm
    val PAIR_FST_SND_EQ : thm
    val PAIR_FUN_THM : thm
    val PAIR_MAP_THM : thm
    val PEXISTS_THM : thm
    val PFORALL_THM : thm
    val SND : thm
    val SND_PAIR_MAP : thm
    val S_UNCURRY_R : thm
    val UNCURRY_CONG : thm
    val UNCURRY_CURRY_THM : thm
    val UNCURRY_DEF : thm
    val UNCURRY_ONE_ONE_THM : thm
    val UNCURRY_VAR : thm
    val WF_LEX : thm
    val WF_RPROD : thm
    val o_UNCURRY_R : thm
    val pair_Axiom : thm
    val pair_CASES : thm
    val pair_case_cong : thm
    val pair_case_thm : thm
    val pair_induction : thm
  
  val pair_grammars : type_grammar.grammar * term_grammar.grammar
  
  val pair_rws : thm list
  
  
  type hol_type = Abbrev.hol_type
  type term     = Abbrev.term
  type conv     = Abbrev.conv
  
  val uncurry_tm       : term
  val comma_tm         : term
  val dest_pair        : term -> term * term
  val strip_pair       : term -> term list
  val spine_pair       : term -> term list
  val is_vstruct       : term -> bool
  val mk_pabs          : term * term -> term
  val PAIRED_BETA_CONV : conv
  
(*
   [relation] Parent theory of "pair"
   
   [ABS_REP_prod]  Definition
      
      |- (∀a. ABS_prod (REP_prod a) = a) ∧
         ∀r.
           (λp. ∃x y. p = (λa b. (a = x) ∧ (b = y))) r ⇔ (REP_prod (ABS_prod r) = r)
   
   [COMMA_DEF]  Definition
      
      |- ∀x y. (x,y) = ABS_prod (λa b. (a = x) ∧ (b = y))
   
   [CURRY_DEF]  Definition
      
      |- ∀f x y. CURRY f x y = f (x,y)
   
   [LEX_DEF]  Definition
      
      |- ∀R1 R2. R1 LEX R2 = (λ(s,t) (u,v). R1 s u ∨ (s = u) ∧ R2 t v)
   
   [PAIR]  Definition
      
      |- ∀x. (FST x,SND x) = x
   
   [PAIR_MAP]  Definition
      
      |- ∀f g p. (f ## g) p = (f (FST p),g (SND p))
   
   [RPROD_DEF]  Definition
      
      |- ∀R1 R2. RPROD R1 R2 = (λ(s,t) (u,v). R1 s u ∧ R2 t v)
   
   [UNCURRY]  Definition
      
      |- ∀f v. UNCURRY f v = f (FST v) (SND v)
   
   [pair_case_def]  Definition
      
      |- pair_case = UNCURRY
   
   [prod_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION (λp. ∃x y. p = (λa b. (a = x) ∧ (b = y))) rep
   
   [ABS_PAIR_THM]  Theorem
      
      |- ∀x. ∃q r. x = (q,r)
   
   [CLOSED_PAIR_EQ]  Theorem
      
      |- ∀x y a b. ((x,y) = (a,b)) ⇔ (x = a) ∧ (y = b)
   
   [CURRY_ONE_ONE_THM]  Theorem
      
      |- (CURRY f = CURRY g) ⇔ (f = g)
   
   [CURRY_UNCURRY_THM]  Theorem
      
      |- ∀f. CURRY (UNCURRY f) = f
   
   [C_UNCURRY_L]  Theorem
      
      |- combin$C (UNCURRY f) x = UNCURRY (combin$C (combin$C o f) x)
   
   [ELIM_PEXISTS]  Theorem
      
      |- (∃p. P (FST p) (SND p)) ⇔ ∃p1 p2. P p1 p2
   
   [ELIM_PEXISTS_EVAL]  Theorem
      
      |- $? (UNCURRY (λx. P x)) ⇔ ∃x. $? (P x)
   
   [ELIM_PFORALL]  Theorem
      
      |- (∀p. P (FST p) (SND p)) ⇔ ∀p1 p2. P p1 p2
   
   [ELIM_PFORALL_EVAL]  Theorem
      
      |- $! (UNCURRY (λx. P x)) ⇔ ∀x. $! (P x)
   
   [ELIM_UNCURRY]  Theorem
      
      |- ∀f. UNCURRY f = (λx. f (FST x) (SND x))
   
   [EXISTS_PROD]  Theorem
      
      |- (∃p. P p) ⇔ ∃p_1 p_2. P (p_1,p_2)
   
   [FORALL_PROD]  Theorem
      
      |- (∀p. P p) ⇔ ∀p_1 p_2. P (p_1,p_2)
   
   [FORALL_UNCURRY]  Theorem
      
      |- $! (UNCURRY f) ⇔ $! ($! o f)
   
   [FST]  Theorem
      
      |- ∀x y. FST (x,y) = x
   
   [FST_PAIR_MAP]  Theorem
      
      |- ∀p f g. FST ((f ## g) p) = f (FST p)
   
   [LAMBDA_PROD]  Theorem
      
      |- ∀P. (λp. P p) = (λ(p1,p2). P (p1,p2))
   
   [LET2_RAND]  Theorem
      
      |- ∀P M N. P (let (x,y) = M in N x y) = (let (x,y) = M in P (N x y))
   
   [LET2_RATOR]  Theorem
      
      |- ∀M N b. (let (x,y) = M in N x y) b = (let (x,y) = M in N x y b)
   
   [LEX_DEF_THM]  Theorem
      
      |- (R1 LEX R2) (a,b) (c,d) ⇔ R1 a c ∨ (a = c) ∧ R2 b d
   
   [PAIR_EQ]  Theorem
      
      |- ((x,y) = (a,b)) ⇔ (x = a) ∧ (y = b)
   
   [PAIR_FST_SND_EQ]  Theorem
      
      |- ∀p q. (p = q) ⇔ (FST p = FST q) ∧ (SND p = SND q)
   
   [PAIR_FUN_THM]  Theorem
      
      |- ∀P. (∃!f. P f) ⇔ ∃!p. P (λa. (FST p a,SND p a))
   
   [PAIR_MAP_THM]  Theorem
      
      |- ∀f g x y. (f ## g) (x,y) = (f x,g y)
   
   [PEXISTS_THM]  Theorem
      
      |- ∀P. (∃x y. P x y) ⇔ ∃(x,y). P x y
   
   [PFORALL_THM]  Theorem
      
      |- ∀P. (∀x y. P x y) ⇔ ∀(x,y). P x y
   
   [SND]  Theorem
      
      |- ∀x y. SND (x,y) = y
   
   [SND_PAIR_MAP]  Theorem
      
      |- ∀p f g. SND ((f ## g) p) = g (SND p)
   
   [S_UNCURRY_R]  Theorem
      
      |- S f (UNCURRY g) = UNCURRY (S (S o $o f o $,) g)
   
   [UNCURRY_CONG]  Theorem
      
      |- ∀M M' f.
           (M = M') ∧ (∀x y. (M' = (x,y)) ⇒ (f x y = f' x y)) ⇒
           (UNCURRY f M = UNCURRY f' M')
   
   [UNCURRY_CURRY_THM]  Theorem
      
      |- ∀f. UNCURRY (CURRY f) = f
   
   [UNCURRY_DEF]  Theorem
      
      |- ∀f x y. UNCURRY f (x,y) = f x y
   
   [UNCURRY_ONE_ONE_THM]  Theorem
      
      |- (UNCURRY f = UNCURRY g) ⇔ (f = g)
   
   [UNCURRY_VAR]  Theorem
      
      |- ∀f v. UNCURRY f v = f (FST v) (SND v)
   
   [WF_LEX]  Theorem
      
      |- ∀R Q. WF R ∧ WF Q ⇒ WF (R LEX Q)
   
   [WF_RPROD]  Theorem
      
      |- ∀R Q. WF R ∧ WF Q ⇒ WF (RPROD R Q)
   
   [o_UNCURRY_R]  Theorem
      
      |- f o UNCURRY g = UNCURRY ($o f o g)
   
   [pair_Axiom]  Theorem
      
      |- ∀f. ∃fn. ∀x y. fn (x,y) = f x y
   
   [pair_CASES]  Theorem
      
      |- ∀x. ∃q r. x = (q,r)
   
   [pair_case_cong]  Theorem
      
      |- ∀M M' f.
           (M = M') ∧ (∀x y. (M' = (x,y)) ⇒ (f x y = f' x y)) ⇒
           (pair_case f M = pair_case f' M')
   
   [pair_case_thm]  Theorem
      
      |- pair_case f (x,y) = f x y
   
   [pair_induction]  Theorem
      
      |- (∀p_1 p_2. P (p_1,p_2)) ⇒ ∀p. P p
   
   
*)
end
