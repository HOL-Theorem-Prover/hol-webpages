signature quotient_pairTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val PAIR_REL : thm
  
  (*  Theorems  *)
    val COMMA_PRS : thm
    val COMMA_RSP : thm
    val CURRY_PRS : thm
    val CURRY_RSP : thm
    val FST_PRS : thm
    val FST_RSP : thm
    val PAIR_EQUIV : thm
    val PAIR_MAP_I : thm
    val PAIR_MAP_PRS : thm
    val PAIR_MAP_RSP : thm
    val PAIR_QUOTIENT : thm
    val PAIR_REL_EQ : thm
    val PAIR_REL_REFL : thm
    val PAIR_REL_THM : thm
    val SND_PRS : thm
    val SND_RSP : thm
    val UNCURRY_PRS : thm
    val UNCURRY_RSP : thm
  
  val quotient_pair_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [quotient] Parent theory of "quotient_pair"
   
   [PAIR_REL]  Definition
      
      |- ∀R1 R2. R1 ### R2 = (λ(a,b) (c,d). R1 a c ∧ R2 b d)
   
   [COMMA_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒ ∀a b. (a,b) = (abs1 ## abs2) (rep1 a,rep2 b)
   
   [COMMA_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀a1 a2 b1 b2. R1 a1 b1 ∧ R2 a2 b2 ⇒ (R1 ### R2) (a1,a2) (b1,b2)
   
   [CURRY_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f a b.
                 CURRY f a b =
                 abs3 (CURRY (((abs1 ## abs2) --> rep3) f) (rep1 a) (rep2 b))
   
   [CURRY_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f1 f2.
                 ((R1 ### R2) ===> R3) f1 f2 ⇒
                 (R1 ===> R2 ===> R3) (CURRY f1) (CURRY f2)
   
   [FST_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒ ∀p. FST p = abs1 (FST ((rep1 ## rep2) p))
   
   [FST_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒ ∀p1 p2. (R1 ### R2) p1 p2 ⇒ R1 (FST p1) (FST p2)
   
   [PAIR_EQUIV]  Theorem
      
      |- ∀R1 R2. EQUIV R1 ⇒ EQUIV R2 ⇒ EQUIV (R1 ### R2)
   
   [PAIR_MAP_I]  Theorem
      
      |- I ## I = I
   
   [PAIR_MAP_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀R4 abs4 rep4.
                 QUOTIENT R4 abs4 rep4 ⇒
                 ∀f g.
                   f ## g =
                   ((rep1 ## rep3) --> abs2 ## abs4)
                     ((abs1 --> rep2) f ## (abs3 --> rep4) g)
   
   [PAIR_MAP_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀R4 abs4 rep4.
                 QUOTIENT R4 abs4 rep4 ⇒
                 ∀f1 f2 g1 g2.
                   (R1 ===> R2) f1 f2 ∧ (R3 ===> R4) g1 g2 ⇒
                   ((R1 ### R3) ===> R2 ### R4) (f1 ## g1) (f2 ## g2)
   
   [PAIR_QUOTIENT]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             QUOTIENT (R1 ### R2) (abs1 ## abs2) (rep1 ## rep2)
   
   [PAIR_REL_EQ]  Theorem
      
      |- $= ### $= = $=
   
   [PAIR_REL_REFL]  Theorem
      
      |- ∀R1 R2.
           (∀x y. R1 x y ⇔ (R1 x = R1 y)) ∧ (∀x y. R2 x y ⇔ (R2 x = R2 y)) ⇒
           ∀x. (R1 ### R2) x x
   
   [PAIR_REL_THM]  Theorem
      
      |- ∀R1 R2 a b c d. (R1 ### R2) (a,b) (c,d) ⇔ R1 a c ∧ R2 b d
   
   [SND_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒ ∀p. SND p = abs2 (SND ((rep1 ## rep2) p))
   
   [SND_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒ ∀p1 p2. (R1 ### R2) p1 p2 ⇒ R2 (SND p1) (SND p2)
   
   [UNCURRY_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f p.
                 UNCURRY f p =
                 abs3 (UNCURRY ((abs1 --> abs2 --> rep3) f) ((rep1 ## rep2) p))
   
   [UNCURRY_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀R3 abs3 rep3.
               QUOTIENT R3 abs3 rep3 ⇒
               ∀f1 f2.
                 (R1 ===> R2 ===> R3) f1 f2 ⇒
                 ((R1 ### R2) ===> R3) (UNCURRY f1) (UNCURRY f2)
   
   
*)
end
