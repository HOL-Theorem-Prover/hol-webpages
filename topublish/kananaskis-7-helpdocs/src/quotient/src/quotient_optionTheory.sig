signature quotient_optionTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val OPTION_REL_curried_def : thm
    val OPTION_REL_tupled_primitive_def : thm
  
  (*  Theorems  *)
    val IS_NONE_PRS : thm
    val IS_NONE_RSP : thm
    val IS_SOME_PRS : thm
    val IS_SOME_RSP : thm
    val NONE_PRS : thm
    val NONE_RSP : thm
    val OPTION_EQUIV : thm
    val OPTION_MAP_I : thm
    val OPTION_MAP_PRS : thm
    val OPTION_MAP_RSP : thm
    val OPTION_QUOTIENT : thm
    val OPTION_REL_EQ : thm
    val OPTION_REL_def : thm
    val OPTION_REL_ind : thm
    val SOME_PRS : thm
    val SOME_RSP : thm
  
  val quotient_option_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [quotient] Parent theory of "quotient_option"
   
   [OPTION_REL_curried_def]  Definition
      
      |- ∀x x1 x2. OPTION_REL x x1 x2 ⇔ OPTION_REL_tupled (x,x1,x2)
   
   [OPTION_REL_tupled_primitive_def]  Definition
      
      |- OPTION_REL_tupled =
         WFREC (@R'. WF R')
           (λOPTION_REL_tupled a.
              case a of
                 (R,NONE,NONE) -> I T
              || (R,NONE,SOME y) -> I F
              || (R,SOME x,NONE) -> I F
              || (R,SOME x,SOME y') -> I (R x y'))
   
   [IS_NONE_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀x. IS_NONE x ⇔ IS_NONE (OPTION_MAP rep x)
   
   [IS_NONE_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀x y. OPTION_REL R x y ⇒ (IS_NONE x ⇔ IS_NONE y)
   
   [IS_SOME_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀x. IS_SOME x ⇔ IS_SOME (OPTION_MAP rep x)
   
   [IS_SOME_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀x y. OPTION_REL R x y ⇒ (IS_SOME x ⇔ IS_SOME y)
   
   [NONE_PRS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ (NONE = OPTION_MAP abs NONE)
   
   [NONE_RSP]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ OPTION_REL R NONE NONE
   
   [OPTION_EQUIV]  Theorem
      
      |- ∀R. EQUIV R ⇒ EQUIV (OPTION_REL R)
   
   [OPTION_MAP_I]  Theorem
      
      |- OPTION_MAP I = I
   
   [OPTION_MAP_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀a f.
               OPTION_MAP f a =
               OPTION_MAP abs2
                 (OPTION_MAP ((abs1 --> rep2) f) (OPTION_MAP rep1 a))
   
   [OPTION_MAP_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀a1 a2 f1 f2.
               (R1 ===> R2) f1 f2 ∧ OPTION_REL R1 a1 a2 ⇒
               OPTION_REL R2 (OPTION_MAP f1 a1) (OPTION_MAP f2 a2)
   
   [OPTION_QUOTIENT]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           QUOTIENT (OPTION_REL R) (OPTION_MAP abs) (OPTION_MAP rep)
   
   [OPTION_REL_EQ]  Theorem
      
      |- OPTION_REL $= = $=
   
   [OPTION_REL_def]  Theorem
      
      |- (OPTION_REL R NONE NONE ⇔ T) ∧ (OPTION_REL R (SOME x) NONE ⇔ F) ∧
         (OPTION_REL R NONE (SOME y) ⇔ F) ∧
         (OPTION_REL R (SOME x) (SOME y) ⇔ R x y)
   
   [OPTION_REL_ind]  Theorem
      
      |- ∀P.
           (∀R. P R NONE NONE) ∧ (∀R x. P R (SOME x) NONE) ∧
           (∀R y. P R NONE (SOME y)) ∧ (∀R x y. P R (SOME x) (SOME y)) ⇒
           ∀v v1 v2. P v v1 v2
   
   [SOME_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀x. SOME x = OPTION_MAP abs (SOME (rep x))
   
   [SOME_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀x y. R x y ⇒ OPTION_REL R (SOME x) (SOME y)
   
   
*)
end
