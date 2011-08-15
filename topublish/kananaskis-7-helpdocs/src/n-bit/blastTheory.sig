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
    val BITWISE_MUL : thm
    val BITWISE_SUB : thm
    val BSUM_EQ : thm
    val BSUM_LEM : thm
    val word_asr_bv_expand : thm
    val word_lsl_bv_expand : thm
    val word_lsr_bv_expand : thm
    val word_rol_bv_expand : thm
    val word_ror_bv_expand : thm
  
  val blast_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [words] Parent theory of "blast"
   
   [BCARRY_def]  Definition
      
      |- (∀x y c. BCARRY 0 x y c ⇔ c) ∧
         ∀i x y c.
           BCARRY (SUC i) x y c ⇔ bcarry (x i) (y i) (BCARRY i x y c)
   
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
            BIT i
              (BITS (i − 1) 0 x + BITS (i − 1) 0 y + if c then 1 else 0))
   
   [BITWISE_ADD]  Theorem
      
      |- ∀x y. x + y = FCP i. BSUM i ($' x) ($' y) F
   
   [BITWISE_LO]  Theorem
      
      |- ∀x y. x <₊ y ⇔ ¬BCARRY (dimindex (:α)) ($' x) ($~ o $' y) T
   
   [BITWISE_MUL]  Theorem
      
      |- ∀w m.
           w * m =
           FOLDL (λa j. a + FCP i. w ' j ∧ j ≤ i ∧ m ' (i − j)) 0w
             (COUNT_LIST (dimindex (:α)))
   
   [BITWISE_SUB]  Theorem
      
      |- ∀x y. x − y = FCP i. BSUM i ($' x) ($~ o $' y) T
   
   [BSUM_EQ]  Theorem
      
      |- ∀n c x1 x2 y1 y2.
           (∀i. i ≤ n ⇒ (x1 i ⇔ x2 i) ∧ (y1 i ⇔ y2 i)) ⇒
           (BSUM n x1 y1 c ⇔ BSUM n x2 y2 c)
   
   [BSUM_LEM]  Theorem
      
      |- ∀i x y c.
           BSUM i (λi. BIT i x) (λi. BIT i y) c ⇔
           BIT i (x + y + if c then 1 else 0)
   
   [word_asr_bv_expand]  Theorem
      
      |- ∀w m.
           w >>~ m =
           if dimindex (:α) = 1 then
             $FCP (K (w ' 0))
           else
             FCP k.
               FOLDL
                 (λa j.
                    a ∨
                    ((LOG2 (dimindex (:α) − 1) -- 0) m = n2w j) ∧
                    (w ≫ j) ' k) F (COUNT_LIST (dimindex (:α))) ∧
               ((dimindex (:α) − 1 -- LOG2 (dimindex (:α) − 1) + 1) m =
                0w) ∨
               n2w (dimindex (:α) − 1) <₊ m ∧ w ' (dimindex (:α) − 1)
   
   [word_lsl_bv_expand]  Theorem
      
      |- ∀w m.
           w <<~ m =
           if dimindex (:α) = 1 then
             $FCP (K (¬m ' 0 ∧ w ' 0))
           else
             FCP k.
               FOLDL
                 (λa j.
                    a ∨
                    ((LOG2 (dimindex (:α) − 1) -- 0) m = n2w j) ∧ j ≤ k ∧
                    w ' (k − j)) F (COUNT_LIST (dimindex (:α))) ∧
               ((dimindex (:α) − 1 -- LOG2 (dimindex (:α) − 1) + 1) m = 0w)
   
   [word_lsr_bv_expand]  Theorem
      
      |- ∀w m.
           w >>>~ m =
           if dimindex (:α) = 1 then
             $FCP (K (¬m ' 0 ∧ w ' 0))
           else
             FCP k.
               FOLDL
                 (λa j.
                    a ∨
                    ((LOG2 (dimindex (:α) − 1) -- 0) m = n2w j) ∧
                    k + j < dimindex (:α) ∧ w ' (k + j)) F
                 (COUNT_LIST (dimindex (:α))) ∧
               ((dimindex (:α) − 1 -- LOG2 (dimindex (:α) − 1) + 1) m = 0w)
   
   [word_rol_bv_expand]  Theorem
      
      |- ∀w m.
           w #<<~ m =
           FCP k.
             FOLDL
               (λa j.
                  a ∨
                  (word_mod m (n2w (dimindex (:α))) = n2w j) ∧
                  w '
                  ((k + (dimindex (:α) − j) MOD dimindex (:α)) MOD
                   dimindex (:α))) F (COUNT_LIST (dimindex (:α)))
   
   [word_ror_bv_expand]  Theorem
      
      |- ∀w m.
           w #>>~ m =
           FCP k.
             FOLDL
               (λa j.
                  a ∨
                  (word_mod m (n2w (dimindex (:α))) = n2w j) ∧
                  w ' ((j + k) MOD dimindex (:α))) F
               (COUNT_LIST (dimindex (:α)))
   
   
*)
end
