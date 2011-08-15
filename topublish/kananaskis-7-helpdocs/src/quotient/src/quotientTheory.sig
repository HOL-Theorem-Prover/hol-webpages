signature quotientTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ?!! : thm
    val EQUIV_def : thm
    val FUN_MAP : thm
    val FUN_REL : thm
    val PARTIAL_EQUIV_def : thm
    val QUOTIENT_def : thm
    val RES_EXISTS_EQUIV_DEF : thm
    val respects_def : thm
  
  (*  Theorems  *)
    val ABSTRACT_PRS : thm
    val ABSTRACT_RES_ABSTRACT : thm
    val APPLY_PRS : thm
    val APPLY_RSP : thm
    val COND_PRS : thm
    val COND_RSP : thm
    val CONJ_IMPLIES : thm
    val C_PRS : thm
    val C_RSP : thm
    val DISJ_IMPLIES : thm
    val EQUALS_EQUIV_IMPLIES : thm
    val EQUALS_IMPLIES : thm
    val EQUALS_PRS : thm
    val EQUALS_RSP : thm
    val EQUIV_IMP_PARTIAL_EQUIV : thm
    val EQUIV_REFL_SYM_TRANS : thm
    val EQUIV_RES_ABSTRACT_LEFT : thm
    val EQUIV_RES_ABSTRACT_RIGHT : thm
    val EQUIV_RES_EXISTS : thm
    val EQUIV_RES_EXISTS_UNIQUE : thm
    val EQUIV_RES_FORALL : thm
    val EQ_IMPLIES : thm
    val EXISTS_PRS : thm
    val EXISTS_REGULAR : thm
    val EXISTS_UNIQUE_PRS : thm
    val EXISTS_UNIQUE_REGULAR : thm
    val FORALL_PRS : thm
    val FORALL_REGULAR : thm
    val FUN_MAP_I : thm
    val FUN_MAP_THM : thm
    val FUN_QUOTIENT : thm
    val FUN_REL_EQ : thm
    val FUN_REL_EQUALS : thm
    val FUN_REL_EQ_REL : thm
    val FUN_REL_IMP : thm
    val FUN_REL_MP : thm
    val IDENTITY_EQUIV : thm
    val IDENTITY_QUOTIENT : thm
    val IMP_IMPLIES : thm
    val IN_FUN : thm
    val IN_RESPECTS : thm
    val I_PRS : thm
    val I_RSP : thm
    val K_PRS : thm
    val K_RSP : thm
    val LAMBDA_PRS : thm
    val LAMBDA_PRS1 : thm
    val LAMBDA_REP_ABS_RSP : thm
    val LAMBDA_RSP : thm
    val LEFT_RES_EXISTS_REGULAR : thm
    val LEFT_RES_FORALL_REGULAR : thm
    val LET_PRS : thm
    val LET_RES_ABSTRACT : thm
    val LET_RSP : thm
    val NOT_IMPLIES : thm
    val QUOTIENT_ABS_REP : thm
    val QUOTIENT_REL : thm
    val QUOTIENT_REL_ABS : thm
    val QUOTIENT_REL_ABS_EQ : thm
    val QUOTIENT_REL_REP : thm
    val QUOTIENT_REP_ABS : thm
    val QUOTIENT_REP_REFL : thm
    val QUOTIENT_SYM : thm
    val QUOTIENT_TRANS : thm
    val REP_ABS_RSP : thm
    val RESPECTS : thm
    val RESPECTS_MP : thm
    val RESPECTS_REP_ABS : thm
    val RESPECTS_THM : thm
    val RESPECTS_o : thm
    val RES_ABSTRACT_ABSTRACT : thm
    val RES_ABSTRACT_RSP : thm
    val RES_EXISTS_EQUIV : thm
    val RES_EXISTS_EQUIV_RSP : thm
    val RES_EXISTS_PRS : thm
    val RES_EXISTS_REGULAR : thm
    val RES_EXISTS_RSP : thm
    val RES_EXISTS_UNIQUE_REGULAR : thm
    val RES_EXISTS_UNIQUE_REGULAR_SAME : thm
    val RES_EXISTS_UNIQUE_RESPECTS_REGULAR : thm
    val RES_FORALL_PRS : thm
    val RES_FORALL_REGULAR : thm
    val RES_FORALL_RSP : thm
    val RIGHT_RES_EXISTS_REGULAR : thm
    val RIGHT_RES_FORALL_REGULAR : thm
    val W_PRS : thm
    val W_RSP : thm
    val literal_case_PRS : thm
    val literal_case_RSP : thm
    val o_PRS : thm
    val o_RSP : thm
  
  val quotient_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [res_quan] Parent theory of "quotient"
   
   [?!!]  Definition
      
      |- ∀P. $?!! P ⇔ $?! P
   
   [EQUIV_def]  Definition
      
      |- ∀E. EQUIV E ⇔ ∀x y. E x y ⇔ (E x = E y)
   
   [FUN_MAP]  Definition
      
      |- ∀f g. f --> g = (λh x. g (h (f x)))
   
   [FUN_REL]  Definition
      
      |- ∀R1 R2 f g. (R1 ===> R2) f g ⇔ ∀x y. R1 x y ⇒ R2 (f x) (g y)
   
   [PARTIAL_EQUIV_def]  Definition
      
      |- ∀R.
           PARTIAL_EQUIV R ⇔
           (∃x. R x x) ∧ ∀x y. R x y ⇔ R x x ∧ R y y ∧ (R x = R y)
   
   [QUOTIENT_def]  Definition
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇔
           (∀a. abs (rep a) = a) ∧ (∀a. R (rep a) (rep a)) ∧
           ∀r s. R r s ⇔ R r r ∧ R s s ∧ (abs r = abs s)
   
   [RES_EXISTS_EQUIV_DEF]  Definition
      
      |- RES_EXISTS_EQUIV =
         (λR P.
            (∃x::respects R. P x) ∧ ∀x y::respects R. P x ∧ P y ⇒ R x y)
   
   [respects_def]  Definition
      
      |- respects = W
   
   [ABSTRACT_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f.
               f =
               (rep1 --> abs2)
                 (RES_ABSTRACT (respects R1) ((abs1 --> rep2) f))
   
   [ABSTRACT_RES_ABSTRACT]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 f g.
             (R1 ===> R2) f g ⇒
             (R1 ===> R2) f (RES_ABSTRACT (respects R1) g)
   
   [APPLY_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f x. f x = abs2 ((abs1 --> rep2) f (rep1 x))
   
   [APPLY_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f g x y. (R1 ===> R2) f g ∧ R1 x y ⇒ R2 (f x) (g y)
   
   [COND_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀a b c. (if a then b else c) = abs (if a then rep b else rep c)
   
   [COND_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀a1 a2 b1 b2 c1 c2.
             (a1 ⇔ a2) ∧ R b1 b2 ∧ R c1 c2 ⇒
             R (if a1 then b1 else c1) (if a2 then b2 else c2)
   
   [CONJ_IMPLIES]  Theorem
      
      |- ∀P P' Q Q'. (P ⇒ Q) ∧ (P' ⇒ Q') ⇒ P ∧ P' ⇒ Q ∧ Q'
   
   [C_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f x y.
                 combin$C f x y =
                 abs3
                   (combin$C ((abs1 --> abs2 --> rep3) f) (rep2 x)
                      (rep1 y))
   
   [C_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f1 f2 x1 x2 y1 y2.
                 (R1 ===> R2 ===> R3) f1 f2 ∧ R2 x1 x2 ∧ R1 y1 y2 ⇒
                 R3 (combin$C f1 x1 y1) (combin$C f2 x2 y2)
   
   [DISJ_IMPLIES]  Theorem
      
      |- ∀P P' Q Q'. (P ⇒ Q) ∧ (P' ⇒ Q') ⇒ P ∨ P' ⇒ Q ∨ Q'
   
   [EQUALS_EQUIV_IMPLIES]  Theorem
      
      |- ∀R. EQUIV R ⇒ R a1 a2 ∧ R b1 b2 ⇒ (a1 = b1) ⇒ R a2 b2
   
   [EQUALS_IMPLIES]  Theorem
      
      |- ∀P P' Q Q'. (P = Q) ∧ (P' = Q') ⇒ (P = P') ⇒ (Q = Q')
   
   [EQUALS_PRS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀x y. (x = y) ⇔ R (rep x) (rep y)
   
   [EQUALS_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀x1 x2 y1 y2. R x1 x2 ∧ R y1 y2 ⇒ (R x1 y1 ⇔ R x2 y2)
   
   [EQUIV_IMP_PARTIAL_EQUIV]  Theorem
      
      |- ∀R. EQUIV R ⇒ PARTIAL_EQUIV R
   
   [EQUIV_REFL_SYM_TRANS]  Theorem
      
      |- ∀R.
           (∀x y. R x y ⇔ (R x = R y)) ⇔
           (∀x. R x x) ∧ (∀x y. R x y ⇒ R y x) ∧
           ∀x y z. R x y ∧ R y z ⇒ R x z
   
   [EQUIV_RES_ABSTRACT_LEFT]  Theorem
      
      |- ∀R1 R2 f1 f2 x1 x2.
           R2 (f1 x1) (f2 x2) ∧ R1 x1 x1 ⇒
           R2 (RES_ABSTRACT (respects R1) f1 x1) (f2 x2)
   
   [EQUIV_RES_ABSTRACT_RIGHT]  Theorem
      
      |- ∀R1 R2 f1 f2 x1 x2.
           R2 (f1 x1) (f2 x2) ∧ R1 x2 x2 ⇒
           R2 (f1 x1) (RES_ABSTRACT (respects R1) f2 x2)
   
   [EQUIV_RES_EXISTS]  Theorem
      
      |- ∀E P. EQUIV E ⇒ (RES_EXISTS (respects E) P ⇔ $? P)
   
   [EQUIV_RES_EXISTS_UNIQUE]  Theorem
      
      |- ∀E P. EQUIV E ⇒ (RES_EXISTS_UNIQUE (respects E) P ⇔ $?! P)
   
   [EQUIV_RES_FORALL]  Theorem
      
      |- ∀E P. EQUIV E ⇒ (RES_FORALL (respects E) P ⇔ $! P)
   
   [EQ_IMPLIES]  Theorem
      
      |- ∀P Q. (P ⇔ Q) ⇒ P ⇒ Q
   
   [EXISTS_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀f. $? f ⇔ RES_EXISTS (respects R) ((abs --> I) f)
   
   [EXISTS_REGULAR]  Theorem
      
      |- ∀P Q. (∀x. P x ⇒ Q x) ⇒ $? P ⇒ $? Q
   
   [EXISTS_UNIQUE_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀f. $?! f ⇔ RES_EXISTS_EQUIV R ((abs --> I) f)
   
   [EXISTS_UNIQUE_REGULAR]  Theorem
      
      |- ∀P E Q.
           (∀x. P x ⇒ respects E x ∧ Q x) ∧
           (∀x y. respects E x ∧ Q x ∧ respects E y ∧ Q y ⇒ E x y) ⇒
           $?! P ⇒
           RES_EXISTS_EQUIV E Q
   
   [FORALL_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀f. $! f ⇔ RES_FORALL (respects R) ((abs --> I) f)
   
   [FORALL_REGULAR]  Theorem
      
      |- ∀P Q. (∀x. P x ⇒ Q x) ⇒ $! P ⇒ $! Q
   
   [FUN_MAP_I]  Theorem
      
      |- I --> I = I
   
   [FUN_MAP_THM]  Theorem
      
      |- ∀f g h x. (f --> g) h x = g (h (f x))
   
   [FUN_QUOTIENT]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             QUOTIENT (R1 ===> R2) (rep1 --> abs2) (abs1 --> rep2)
   
   [FUN_REL_EQ]  Theorem
      
      |- $= ===> $= = $=
   
   [FUN_REL_EQUALS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f g.
               respects (R1 ===> R2) f ∧ respects (R1 ===> R2) g ⇒
               (((rep1 --> abs2) f = (rep1 --> abs2) g) ⇔
                ∀x y. R1 x y ⇒ R2 (f x) (g y))
   
   [FUN_REL_EQ_REL]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f g.
               (R1 ===> R2) f g ⇔
               respects (R1 ===> R2) f ∧ respects (R1 ===> R2) g ∧
               ((rep1 --> abs2) f = (rep1 --> abs2) g)
   
   [FUN_REL_IMP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f g.
               respects (R1 ===> R2) f ∧ respects (R1 ===> R2) g ∧
               ((rep1 --> abs2) f = (rep1 --> abs2) g) ⇒
               ∀x y. R1 x y ⇒ R2 (f x) (g y)
   
   [FUN_REL_MP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f g x y. (R1 ===> R2) f g ∧ R1 x y ⇒ R2 (f x) (g y)
   
   [IDENTITY_EQUIV]  Theorem
      
      |- EQUIV $=
   
   [IDENTITY_QUOTIENT]  Theorem
      
      |- QUOTIENT $= I I
   
   [IMP_IMPLIES]  Theorem
      
      |- ∀P P' Q Q'. (Q ⇒ P) ∧ (P' ⇒ Q') ⇒ (P ⇒ P') ⇒ Q ⇒ Q'
   
   [IN_FUN]  Theorem
      
      |- ∀f g s x. x ∈ (f --> g) s ⇔ g (f x ∈ s)
   
   [IN_RESPECTS]  Theorem
      
      |- ∀R x. x ∈ respects R ⇔ R x x
   
   [I_PRS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀e. I e = abs (I (rep e))
   
   [I_RSP]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀e1 e2. R e1 e2 ⇒ R (I e1) (I e2)
   
   [K_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀x y. K x y = abs1 (K (rep1 x) (rep2 y))
   
   [K_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀x1 x2 y1 y2. R1 x1 x2 ∧ R2 y1 y2 ⇒ R1 (K x1 y1) (K x2 y2)
   
   [LAMBDA_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f. (λx. f x) = (rep1 --> abs2) (λx. rep2 (f (abs1 x)))
   
   [LAMBDA_PRS1]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f. (λx. f x) = (rep1 --> abs2) (λx. (abs1 --> rep2) f x)
   
   [LAMBDA_REP_ABS_RSP]  Theorem
      
      |- ∀REL1 abs1 rep1 REL2 abs2 rep2 f1 f2.
           ((∀r r'. REL1 r r' ⇒ REL1 r (rep1 (abs1 r'))) ∧
            ∀r r'. REL2 r r' ⇒ REL2 r (rep2 (abs2 r'))) ∧
           (REL1 ===> REL2) f1 f2 ⇒
           (REL1 ===> REL2) f1 ((abs1 --> rep2) ((rep1 --> abs2) f2))
   
   [LAMBDA_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f1 f2.
               (R1 ===> R2) f1 f2 ⇒ (R1 ===> R2) (λx. f1 x) (λy. f2 y)
   
   [LEFT_RES_EXISTS_REGULAR]  Theorem
      
      |- ∀P R Q. (∀x. R x ⇒ Q x ⇒ P x) ⇒ RES_EXISTS R Q ⇒ $? P
   
   [LEFT_RES_FORALL_REGULAR]  Theorem
      
      |- ∀P R Q. (∀x. R x ∧ (Q x ⇒ P x)) ⇒ RES_FORALL R Q ⇒ $! P
   
   [LET_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f x. LET f x = abs2 (LET ((abs1 --> rep2) f) (rep1 x))
   
   [LET_RES_ABSTRACT]  Theorem
      
      |- ∀r lam v. v ∈ r ⇒ (LET (RES_ABSTRACT r lam) v = LET lam v)
   
   [LET_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f g x y. (R1 ===> R2) f g ∧ R1 x y ⇒ R2 (LET f x) (LET g y)
   
   [NOT_IMPLIES]  Theorem
      
      |- ∀P Q. (Q ⇒ P) ⇒ ¬P ⇒ ¬Q
   
   [QUOTIENT_ABS_REP]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀a. abs (rep a) = a
   
   [QUOTIENT_REL]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀r s. R r s ⇔ R r r ∧ R s s ∧ (abs r = abs s)
   
   [QUOTIENT_REL_ABS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀r s. R r s ⇒ (abs r = abs s)
   
   [QUOTIENT_REL_ABS_EQ]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀r s. R r r ⇒ R s s ⇒ (R r s ⇔ (abs r = abs s))
   
   [QUOTIENT_REL_REP]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀a b. R (rep a) (rep b) ⇔ (a = b)
   
   [QUOTIENT_REP_ABS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀r. R r r ⇒ R (rep (abs r)) r
   
   [QUOTIENT_REP_REFL]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀a. R (rep a) (rep a)
   
   [QUOTIENT_SYM]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀x y. R x y ⇒ R y x
   
   [QUOTIENT_TRANS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀x y z. R x y ∧ R y z ⇒ R x z
   
   [REP_ABS_RSP]  Theorem
      
      |- ∀REL abs rep.
           QUOTIENT REL abs rep ⇒ ∀x1 x2. REL x1 x2 ⇒ REL x1 (rep (abs x2))
   
   [RESPECTS]  Theorem
      
      |- ∀R x. respects R x ⇔ R x x
   
   [RESPECTS_MP]  Theorem
      
      |- ∀R1 R2 f x y. respects (R1 ===> R2) f ∧ R1 x y ⇒ R2 (f x) (f y)
   
   [RESPECTS_REP_ABS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 f x.
             respects (R1 ===> R2) f ∧ R1 x x ⇒
             R2 (f (rep1 (abs1 x))) (f x)
   
   [RESPECTS_THM]  Theorem
      
      |- ∀R1 R2 f. respects (R1 ===> R2) f ⇔ ∀x y. R1 x y ⇒ R2 (f x) (f y)
   
   [RESPECTS_o]  Theorem
      
      |- ∀R1 R2 R3 f g.
           respects (R2 ===> R3) f ∧ respects (R1 ===> R2) g ⇒
           respects (R1 ===> R3) (f o g)
   
   [RES_ABSTRACT_ABSTRACT]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 f g.
             (R1 ===> R2) f g ⇒
             (R1 ===> R2) (RES_ABSTRACT (respects R1) f) g
   
   [RES_ABSTRACT_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f1 f2.
               (R1 ===> R2) f1 f2 ⇒
               (R1 ===> R2) (RES_ABSTRACT (respects R1) f1)
                 (RES_ABSTRACT (respects R1) f2)
   
   [RES_EXISTS_EQUIV]  Theorem
      
      |- ∀R m.
           RES_EXISTS_EQUIV R m ⇔
           (∃x::respects R. m x) ∧ ∀x y::respects R. m x ∧ m y ⇒ R x y
   
   [RES_EXISTS_EQUIV_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀f g.
             (R ===> $<=>) f g ⇒
             (RES_EXISTS_EQUIV R f ⇔ RES_EXISTS_EQUIV R g)
   
   [RES_EXISTS_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀P f.
             RES_EXISTS P f ⇔ RES_EXISTS ((abs --> I) P) ((abs --> I) f)
   
   [RES_EXISTS_REGULAR]  Theorem
      
      |- ∀P Q R. (∀x. R x ⇒ P x ⇒ Q x) ⇒ RES_EXISTS R P ⇒ RES_EXISTS R Q
   
   [RES_EXISTS_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀f g.
             (R ===> $<=>) f g ⇒
             (RES_EXISTS (respects R) f ⇔ RES_EXISTS (respects R) g)
   
   [RES_EXISTS_UNIQUE_REGULAR]  Theorem
      
      |- ∀P R Q.
           (∀x. P x ⇒ Q x) ∧
           (∀x y. respects R x ∧ Q x ∧ respects R y ∧ Q y ⇒ R x y) ⇒
           RES_EXISTS_UNIQUE (respects R) P ⇒
           RES_EXISTS_EQUIV R Q
   
   [RES_EXISTS_UNIQUE_REGULAR_SAME]  Theorem
      
      |- ∀R P Q.
           (R ===> $<=>) P Q ⇒
           RES_EXISTS_UNIQUE (respects R) P ⇒
           RES_EXISTS_EQUIV R Q
   
   [RES_EXISTS_UNIQUE_RESPECTS_REGULAR]  Theorem
      
      |- ∀R P. RES_EXISTS_UNIQUE (respects R) P ⇒ RES_EXISTS_EQUIV R P
   
   [RES_FORALL_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀P f.
             RES_FORALL P f ⇔ RES_FORALL ((abs --> I) P) ((abs --> I) f)
   
   [RES_FORALL_REGULAR]  Theorem
      
      |- ∀P Q R. (∀x. R x ⇒ P x ⇒ Q x) ⇒ RES_FORALL R P ⇒ RES_FORALL R Q
   
   [RES_FORALL_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀f g.
             (R ===> $<=>) f g ⇒
             (RES_FORALL (respects R) f ⇔ RES_FORALL (respects R) g)
   
   [RIGHT_RES_EXISTS_REGULAR]  Theorem
      
      |- ∀P R Q. (∀x. R x ∧ (P x ⇒ Q x)) ⇒ $? P ⇒ RES_EXISTS R Q
   
   [RIGHT_RES_FORALL_REGULAR]  Theorem
      
      |- ∀P R Q. (∀x. R x ⇒ P x ⇒ Q x) ⇒ $! P ⇒ RES_FORALL R Q
   
   [W_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f x. W f x = abs2 (W ((abs1 --> abs1 --> rep2) f) (rep1 x))
   
   [W_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f1 f2 x1 x2.
               (R1 ===> R1 ===> R2) f1 f2 ∧ R1 x1 x2 ⇒
               R2 (W f1 x1) (W f2 x2)
   
   [literal_case_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f x.
               literal_case f x =
               abs2 (literal_case ((abs1 --> rep2) f) (rep1 x))
   
   [literal_case_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀f g x y.
               (R1 ===> R2) f g ∧ R1 x y ⇒
               R2 (literal_case f x) (literal_case g y)
   
   [o_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f g.
                 f o g =
                 (rep1 --> abs3) ((abs2 --> rep3) f o (abs1 --> rep2) g)
   
   [o_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f1 f2 g1 g2.
                 (R2 ===> R3) f1 f2 ∧ (R1 ===> R2) g1 g2 ⇒
                 (R1 ===> R3) (f1 o g1) (f2 o g2)
   
   
*)
end
