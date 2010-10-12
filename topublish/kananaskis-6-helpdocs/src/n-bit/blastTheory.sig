signature blastTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val BCARRY_def : thm
    val BSUM_def : thm
    val bcarry_def : thm
    val bsum_def : thm
  
  (*  Theorems  *)
    val BCARRY_EQ : thm
    val BCARRY_LEM : thm
    val BITWISE_ADD : thm
    val BITWISE_LO : thm
    val BITWISE_SUB : thm
    val BSUM_EQ : thm
    val BSUM_LEM : thm
  
  val blast_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [words] Parent theory of "blast"
   
   [BCARRY_def]  Definition
      
      |- (∀x y c. BCARRY 0 x y c ⇔ c) ∧
         ∀i x y c. BCARRY (SUC i) x y c ⇔ bcarry (x i) (y i) (BCARRY i x y c)
   
   [BSUM_def]  Definition
      
      |- ∀i x y c. BSUM i x y c ⇔ bsum (x i) (y i) (BCARRY i x y c)
   
   [bcarry_def]  Definition
      
      |- ∀x y c. bcarry x y c ⇔ x ∧ y ∨ (x ∨ y) ∧ c
   
   [bsum_def]  Definition
      
      |- ∀x y c. bsum x y c ⇔ ((x ⇔ ¬y) ⇔ ¬c)
   
   [BCARRY_EQ]  Theorem
      
      |- ∀n c x1 x2 y1 y2.
           (∀i. i < n ⇒ (x1 i ⇔ x2 i) ∧ (y1 i ⇔ y2 i)) ⇒
           (BCARRY n x1 y1 c ⇔ BCARRY n x2 y2 c)
   
   [BCARRY_LEM]  Theorem
      
      |- ∀i x y c.
           0 < i ⇒
           (BCARRY i (λi. BIT i x) (λi. BIT i y) c ⇔
            BIT i (BITS (i − 1) 0 x + BITS (i − 1) 0 y + if c then 1 else 0))
   
   [BITWISE_ADD]  Theorem
      
      |- ∀x y. x + y = FCP i. BSUM i ($' x) ($' y) F
   
   [BITWISE_LO]  Theorem
      
      |- ∀x y. x <₊ y ⇔ ¬BCARRY (dimindex (:α)) ($' x) ($~ o $' y) T
   
   [BITWISE_SUB]  Theorem
      
      |- ∀x y. x − y = FCP i. BSUM i ($' x) ($~ o $' y) T
   
   [BSUM_EQ]  Theorem
      
      |- ∀n c x1 x2 y1 y2.
           (∀i. i ≤ n ⇒ (x1 i ⇔ x2 i) ∧ (y1 i ⇔ y2 i)) ⇒
           (BSUM n x1 y1 c ⇔ BSUM n x2 y2 c)
   
   [BSUM_LEM]  Theorem
      
      |- ∀i x y c.
           BSUM i (λi. BIT i x) (λi. BIT i y) c ⇔ BIT i (x + y + if c then 1 else 0)
   
   
*)
end
