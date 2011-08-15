signature seqTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val cauchy : thm
    val convergent : thm
    val lim : thm
    val mono : thm
    val subseq : thm
    val suminf : thm
    val summable : thm
    val sums : thm
    val tends_num_real : thm
  
  (*  Theorems  *)
    val ABS_NEG_LEMMA : thm
    val BOLZANO_LEMMA : thm
    val GP : thm
    val GP_FINITE : thm
    val LE_SEQ_IMP_LE_LIM : thm
    val MAX_LEMMA : thm
    val MONO_SUC : thm
    val NEST_LEMMA : thm
    val NEST_LEMMA_UNIQ : thm
    val SEQ : thm
    val SEQ_ABS : thm
    val SEQ_ABS_IMP : thm
    val SEQ_ADD : thm
    val SEQ_BCONV : thm
    val SEQ_BOUNDED : thm
    val SEQ_BOUNDED_2 : thm
    val SEQ_CAUCHY : thm
    val SEQ_CBOUNDED : thm
    val SEQ_CONST : thm
    val SEQ_DIRECT : thm
    val SEQ_DIV : thm
    val SEQ_ICONV : thm
    val SEQ_INV : thm
    val SEQ_INV0 : thm
    val SEQ_LE : thm
    val SEQ_LE_IMP_LIM_LE : thm
    val SEQ_LE_MONO : thm
    val SEQ_LIM : thm
    val SEQ_MONOSUB : thm
    val SEQ_MONO_LE : thm
    val SEQ_MUL : thm
    val SEQ_NEG : thm
    val SEQ_NEG_BOUNDED : thm
    val SEQ_NEG_CONV : thm
    val SEQ_POWER : thm
    val SEQ_POWER_ABS : thm
    val SEQ_SBOUNDED : thm
    val SEQ_SUB : thm
    val SEQ_SUBLE : thm
    val SEQ_SUC : thm
    val SEQ_UNIQ : thm
    val SER_0 : thm
    val SER_ABS : thm
    val SER_ACONV : thm
    val SER_ADD : thm
    val SER_CAUCHY : thm
    val SER_CDIV : thm
    val SER_CMUL : thm
    val SER_COMPAR : thm
    val SER_COMPARA : thm
    val SER_GROUP : thm
    val SER_LE : thm
    val SER_LE2 : thm
    val SER_NEG : thm
    val SER_OFFSET : thm
    val SER_PAIR : thm
    val SER_POS_LE : thm
    val SER_POS_LT : thm
    val SER_POS_LT_PAIR : thm
    val SER_RATIO : thm
    val SER_SUB : thm
    val SER_ZERO : thm
    val SUBSEQ_SUC : thm
    val SUMMABLE_SUM : thm
    val SUM_SUMMABLE : thm
    val SUM_UNIQ : thm
  
  val seq_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [nets] Parent theory of "seq"
   
   [cauchy]  Definition
      
      |- ∀f.
           cauchy f ⇔
           ∀e. 0 < e ⇒ ∃N. ∀m n. m ≥ N ∧ n ≥ N ⇒ abs (f m − f n) < e
   
   [convergent]  Definition
      
      |- ∀f. convergent f ⇔ ∃l. f --> l
   
   [lim]  Definition
      
      |- ∀f. lim f = @l. f --> l
   
   [mono]  Definition
      
      |- ∀f. mono f ⇔ (∀m n. m ≤ n ⇒ f m ≤ f n) ∨ ∀m n. m ≤ n ⇒ f m ≥ f n
   
   [subseq]  Definition
      
      |- ∀f. subseq f ⇔ ∀m n. m < n ⇒ f m < f n
   
   [suminf]  Definition
      
      |- ∀f. suminf f = @s. f sums s
   
   [summable]  Definition
      
      |- ∀f. summable f ⇔ ∃s. f sums s
   
   [sums]  Definition
      
      |- ∀f s. f sums s ⇔ (λn. sum (0,n) f) --> s
   
   [tends_num_real]  Definition
      
      |- ∀x x0. x --> x0 ⇔ (x tends x0) (mtop mr1,$>=)
   
   [ABS_NEG_LEMMA]  Theorem
      
      |- ∀c. c ≤ 0 ⇒ ∀x y. abs x ≤ c * abs y ⇒ (x = 0)
   
   [BOLZANO_LEMMA]  Theorem
      
      |- ∀P.
           (∀a b c. a ≤ b ∧ b ≤ c ∧ P (a,b) ∧ P (b,c) ⇒ P (a,c)) ∧
           (∀x. ∃d. 0 < d ∧ ∀a b. a ≤ x ∧ x ≤ b ∧ b − a < d ⇒ P (a,b)) ⇒
           ∀a b. a ≤ b ⇒ P (a,b)
   
   [GP]  Theorem
      
      |- ∀x. abs x < 1 ⇒ (λn. x pow n) sums inv (1 − x)
   
   [GP_FINITE]  Theorem
      
      |- ∀x. x ≠ 1 ⇒ ∀n. sum (0,n) (λn. x pow n) = (x pow n − 1) / (x − 1)
   
   [LE_SEQ_IMP_LE_LIM]  Theorem
      
      |- ∀x y f. (∀n. x ≤ f n) ∧ f --> y ⇒ x ≤ y
   
   [MAX_LEMMA]  Theorem
      
      |- ∀s N. ∃k. ∀n. n < N ⇒ abs (s n) < k
   
   [MONO_SUC]  Theorem
      
      |- ∀f. mono f ⇔ (∀n. f (SUC n) ≥ f n) ∨ ∀n. f (SUC n) ≤ f n
   
   [NEST_LEMMA]  Theorem
      
      |- ∀f g.
           (∀n. f (SUC n) ≥ f n) ∧ (∀n. g (SUC n) ≤ g n) ∧
           (∀n. f n ≤ g n) ⇒
           ∃l m.
             l ≤ m ∧ ((∀n. f n ≤ l) ∧ f --> l) ∧ (∀n. m ≤ g n) ∧ g --> m
   
   [NEST_LEMMA_UNIQ]  Theorem
      
      |- ∀f g.
           (∀n. f (SUC n) ≥ f n) ∧ (∀n. g (SUC n) ≤ g n) ∧
           (∀n. f n ≤ g n) ∧ (λn. f n − g n) --> 0 ⇒
           ∃l. ((∀n. f n ≤ l) ∧ f --> l) ∧ (∀n. l ≤ g n) ∧ g --> l
   
   [SEQ]  Theorem
      
      |- ∀x x0. x --> x0 ⇔ ∀e. 0 < e ⇒ ∃N. ∀n. n ≥ N ⇒ abs (x n − x0) < e
   
   [SEQ_ABS]  Theorem
      
      |- ∀f. (λn. abs (f n)) --> 0 ⇔ f --> 0
   
   [SEQ_ABS_IMP]  Theorem
      
      |- ∀f l. f --> l ⇒ (λn. abs (f n)) --> abs l
   
   [SEQ_ADD]  Theorem
      
      |- ∀x x0 y y0. x --> x0 ∧ y --> y0 ⇒ (λn. x n + y n) --> (x0 + y0)
   
   [SEQ_BCONV]  Theorem
      
      |- ∀f. bounded (mr1,$>=) f ∧ mono f ⇒ convergent f
   
   [SEQ_BOUNDED]  Theorem
      
      |- ∀s. bounded (mr1,$>=) s ⇔ ∃k. ∀n. abs (s n) < k
   
   [SEQ_BOUNDED_2]  Theorem
      
      |- ∀f k k'. (∀n. k ≤ f n ∧ f n ≤ k') ⇒ bounded (mr1,$>=) f
   
   [SEQ_CAUCHY]  Theorem
      
      |- ∀f. cauchy f ⇔ convergent f
   
   [SEQ_CBOUNDED]  Theorem
      
      |- ∀f. cauchy f ⇒ bounded (mr1,$>=) f
   
   [SEQ_CONST]  Theorem
      
      |- ∀k. (λx. k) --> k
   
   [SEQ_DIRECT]  Theorem
      
      |- ∀f. subseq f ⇒ ∀N1 N2. ∃n. n ≥ N1 ∧ f n ≥ N2
   
   [SEQ_DIV]  Theorem
      
      |- ∀x x0 y y0.
           x --> x0 ∧ y --> y0 ∧ y0 ≠ 0 ⇒ (λn. x n / y n) --> (x0 / y0)
   
   [SEQ_ICONV]  Theorem
      
      |- ∀f. bounded (mr1,$>=) f ∧ (∀m n. m ≥ n ⇒ f m ≥ f n) ⇒ convergent f
   
   [SEQ_INV]  Theorem
      
      |- ∀x x0. x --> x0 ∧ x0 ≠ 0 ⇒ (λn. inv (x n)) --> inv x0
   
   [SEQ_INV0]  Theorem
      
      |- ∀f. (∀y. ∃N. ∀n. n ≥ N ⇒ f n > y) ⇒ (λn. inv (f n)) --> 0
   
   [SEQ_LE]  Theorem
      
      |- ∀f g l m. f --> l ∧ g --> m ∧ (∃N. ∀n. n ≥ N ⇒ f n ≤ g n) ⇒ l ≤ m
   
   [SEQ_LE_IMP_LIM_LE]  Theorem
      
      |- ∀x y f. (∀n. f n ≤ x) ∧ f --> y ⇒ y ≤ x
   
   [SEQ_LE_MONO]  Theorem
      
      |- ∀f x n. (∀n. f (n + 1) ≤ f n) ∧ f --> x ⇒ x ≤ f n
   
   [SEQ_LIM]  Theorem
      
      |- ∀f. convergent f ⇔ f --> lim f
   
   [SEQ_MONOSUB]  Theorem
      
      |- ∀s. ∃f. subseq f ∧ mono (λn. s (f n))
   
   [SEQ_MONO_LE]  Theorem
      
      |- ∀f x n. (∀n. f n ≤ f (n + 1)) ∧ f --> x ⇒ f n ≤ x
   
   [SEQ_MUL]  Theorem
      
      |- ∀x x0 y y0. x --> x0 ∧ y --> y0 ⇒ (λn. x n * y n) --> (x0 * y0)
   
   [SEQ_NEG]  Theorem
      
      |- ∀x x0. x --> x0 ⇔ (λn. -x n) --> -x0
   
   [SEQ_NEG_BOUNDED]  Theorem
      
      |- ∀f. bounded (mr1,$>=) (λn. -f n) ⇔ bounded (mr1,$>=) f
   
   [SEQ_NEG_CONV]  Theorem
      
      |- ∀f. convergent f ⇔ convergent (λn. -f n)
   
   [SEQ_POWER]  Theorem
      
      |- ∀c. abs c < 1 ⇒ (λn. c pow n) --> 0
   
   [SEQ_POWER_ABS]  Theorem
      
      |- ∀c. abs c < 1 ⇒ (λn. abs c pow n) --> 0
   
   [SEQ_SBOUNDED]  Theorem
      
      |- ∀s f. bounded (mr1,$>=) s ⇒ bounded (mr1,$>=) (λn. s (f n))
   
   [SEQ_SUB]  Theorem
      
      |- ∀x x0 y y0. x --> x0 ∧ y --> y0 ⇒ (λn. x n − y n) --> (x0 − y0)
   
   [SEQ_SUBLE]  Theorem
      
      |- ∀f. subseq f ⇒ ∀n. n ≤ f n
   
   [SEQ_SUC]  Theorem
      
      |- ∀f l. f --> l ⇔ (λn. f (SUC n)) --> l
   
   [SEQ_UNIQ]  Theorem
      
      |- ∀x x1 x2. x --> x1 ∧ x --> x2 ⇒ (x1 = x2)
   
   [SER_0]  Theorem
      
      |- ∀f n. (∀m. n ≤ m ⇒ (f m = 0)) ⇒ f sums sum (0,n) f
   
   [SER_ABS]  Theorem
      
      |- ∀f.
           summable (λn. abs (f n)) ⇒
           abs (suminf f) ≤ suminf (λn. abs (f n))
   
   [SER_ACONV]  Theorem
      
      |- ∀f. summable (λn. abs (f n)) ⇒ summable f
   
   [SER_ADD]  Theorem
      
      |- ∀x x0 y y0. x sums x0 ∧ y sums y0 ⇒ (λn. x n + y n) sums (x0 + y0)
   
   [SER_CAUCHY]  Theorem
      
      |- ∀f.
           summable f ⇔ ∀e. 0 < e ⇒ ∃N. ∀m n. m ≥ N ⇒ abs (sum (m,n) f) < e
   
   [SER_CDIV]  Theorem
      
      |- ∀x x0 c. x sums x0 ⇒ (λn. x n / c) sums (x0 / c)
   
   [SER_CMUL]  Theorem
      
      |- ∀x x0 c. x sums x0 ⇒ (λn. c * x n) sums (c * x0)
   
   [SER_COMPAR]  Theorem
      
      |- ∀f g. (∃N. ∀n. n ≥ N ⇒ abs (f n) ≤ g n) ∧ summable g ⇒ summable f
   
   [SER_COMPARA]  Theorem
      
      |- ∀f g.
           (∃N. ∀n. n ≥ N ⇒ abs (f n) ≤ g n) ∧ summable g ⇒
           summable (λk. abs (f k))
   
   [SER_GROUP]  Theorem
      
      |- ∀f k. summable f ∧ 0 < k ⇒ (λn. sum (n * k,k) f) sums suminf f
   
   [SER_LE]  Theorem
      
      |- ∀f g.
           (∀n. f n ≤ g n) ∧ summable f ∧ summable g ⇒ suminf f ≤ suminf g
   
   [SER_LE2]  Theorem
      
      |- ∀f g.
           (∀n. abs (f n) ≤ g n) ∧ summable g ⇒
           summable f ∧ suminf f ≤ suminf g
   
   [SER_NEG]  Theorem
      
      |- ∀x x0. x sums x0 ⇒ (λn. -x n) sums -x0
   
   [SER_OFFSET]  Theorem
      
      |- ∀f. summable f ⇒ ∀k. (λn. f (n + k)) sums (suminf f − sum (0,k) f)
   
   [SER_PAIR]  Theorem
      
      |- ∀f. summable f ⇒ (λn. sum (2 * n,2) f) sums suminf f
   
   [SER_POS_LE]  Theorem
      
      |- ∀f n. summable f ∧ (∀m. n ≤ m ⇒ 0 ≤ f m) ⇒ sum (0,n) f ≤ suminf f
   
   [SER_POS_LT]  Theorem
      
      |- ∀f n. summable f ∧ (∀m. n ≤ m ⇒ 0 < f m) ⇒ sum (0,n) f < suminf f
   
   [SER_POS_LT_PAIR]  Theorem
      
      |- ∀f n.
           summable f ∧ (∀d. 0 < f (n + 2 * d) + f (n + (2 * d + 1))) ⇒
           sum (0,n) f < suminf f
   
   [SER_RATIO]  Theorem
      
      |- ∀f c N.
           c < 1 ∧ (∀n. n ≥ N ⇒ abs (f (SUC n)) ≤ c * abs (f n)) ⇒
           summable f
   
   [SER_SUB]  Theorem
      
      |- ∀x x0 y y0. x sums x0 ∧ y sums y0 ⇒ (λn. x n − y n) sums (x0 − y0)
   
   [SER_ZERO]  Theorem
      
      |- ∀f. summable f ⇒ f --> 0
   
   [SUBSEQ_SUC]  Theorem
      
      |- ∀f. subseq f ⇔ ∀n. f n < f (SUC n)
   
   [SUMMABLE_SUM]  Theorem
      
      |- ∀f. summable f ⇒ f sums suminf f
   
   [SUM_SUMMABLE]  Theorem
      
      |- ∀f l. f sums l ⇒ summable f
   
   [SUM_UNIQ]  Theorem
      
      |- ∀f x. f sums x ⇒ (x = suminf f)
   
   
*)
end
