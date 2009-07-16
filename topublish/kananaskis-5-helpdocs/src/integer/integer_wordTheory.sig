signature integer_wordTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val INT_MAX_def : thm
    val INT_MIN_def : thm
    val UINT_MAX_def : thm
    val i2w_def : thm
    val w2i_def : thm
  
  (*  Theorems  *)
    val INT_MAX_32 : thm
    val INT_MIN_32 : thm
    val ONE_LE_TWOEXP : thm
    val UINT_MAX_32 : thm
    val WORD_GEi : thm
    val WORD_GTi : thm
    val WORD_LEi : thm
    val WORD_LTi : thm
    val i2w_w2i : thm
    val w2i_11 : thm
    val w2i_i2w : thm
    val w2i_n2w_neg : thm
    val w2i_n2w_pos : thm
    val word_add_i2w : thm
    val word_add_i2w_w2n : thm
    val word_msb_i2w : thm
    val word_sub_i2w : thm
    val word_sub_i2w_w2n : thm
  
  val integer_word_grammars : type_grammar.grammar * term_grammar.grammar
  
  val integer_word_rwts : simpLib.ssfrag
(*
   [Omega] Parent theory of "integer_word"
   
   [int_arith] Parent theory of "integer_word"
   
   [words] Parent theory of "integer_word"
   
   [INT_MAX_def]  Definition
      
      |- INT_MAX (:'a) = &INT_MIN (:'a) - 1
   
   [INT_MIN_def]  Definition
      
      |- INT_MIN (:'a) = -INT_MAX (:'a) - 1
   
   [UINT_MAX_def]  Definition
      
      |- UINT_MAX (:'a) = &dimword (:'a) - 1
   
   [i2w_def]  Definition
      
      |- !i. i2w i = if i < 0 then -n2w (Num (-i)) else n2w (Num i)
   
   [w2i_def]  Definition
      
      |- !w. w2i w = if word_msb w then -&w2n (-w) else &w2n w
   
   [INT_MAX_32]  Theorem
      
      |- INT_MAX (:32) = 2147483647
   
   [INT_MIN_32]  Theorem
      
      |- INT_MIN (:32) = -2147483648
   
   [ONE_LE_TWOEXP]  Theorem
      
      |- 1 <= 2 ** m
   
   [UINT_MAX_32]  Theorem
      
      |- UINT_MAX (:32) = 4294967295
   
   [WORD_GEi]  Theorem
      
      |- !a b. a >= b <=> w2i a >= w2i b
   
   [WORD_GTi]  Theorem
      
      |- !a b. a > b <=> w2i a > w2i b
   
   [WORD_LEi]  Theorem
      
      |- !a b. a <= b <=> w2i a <= w2i b
   
   [WORD_LTi]  Theorem
      
      |- !a b. a < b <=> w2i a < w2i b
   
   [i2w_w2i]  Theorem
      
      |- i2w (w2i w) = w
   
   [w2i_11]  Theorem
      
      |- !v w. (w2i v = w2i w) <=> (v = w)
   
   [w2i_i2w]  Theorem
      
      |- INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a) ==> (w2i (i2w i) = i)
   
   [w2i_n2w_neg]  Theorem
      
      |- INT_MIN (:'a) <= n /\ n < dimword (:'a) ==>
         (w2i (n2w n) = -&(dimword (:'a) - n))
   
   [w2i_n2w_pos]  Theorem
      
      |- n < INT_MIN (:'a) ==> (w2i (n2w n) = &n)
   
   [word_add_i2w]  Theorem
      
      |- !a b. i2w (w2i a + w2i b) = a + b
   
   [word_add_i2w_w2n]  Theorem
      
      |- !a b. i2w (&w2n a + &w2n b) = a + b
   
   [word_msb_i2w]  Theorem
      
      |- word_msb (i2w i) <=> &INT_MIN (:'a) <= i % &dimword (:'a)
   
   [word_sub_i2w]  Theorem
      
      |- !a b. i2w (w2i a - w2i b) = a - b
   
   [word_sub_i2w_w2n]  Theorem
      
      |- !a b. i2w (&w2n a - &w2n b) = a - b
   
   
*)
end
