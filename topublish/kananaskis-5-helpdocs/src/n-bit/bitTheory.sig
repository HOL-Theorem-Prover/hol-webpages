signature bitTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val BITS_def : thm
    val BITV_def : thm
    val BITWISE_def : thm
    val BIT_MODIFY_def : thm
    val BIT_REVERSE_def : thm
    val BIT_def : thm
    val DIVMOD_2EXP_def : thm
    val HEX_primitive_def : thm
    val LOG2_def : thm
    val LOWEST_SET_BIT_def : thm
    val LSB_def : thm
    val MOD_2EXP_EQ_def : thm
    val MOD_2EXP_MAX_def : thm
    val SBIT_def : thm
    val SIGN_EXTEND_def : thm
    val SLICE_def : thm
    val TIMES_2EXP_def : thm
    val UNHEX_primitive_def : thm
    val l2n_def : thm
    val n2l_curried_def : thm
    val n2l_tupled_primitive_def : thm
    val n2s_def : thm
    val num_from_bin_list_def : thm
    val num_from_bin_string_def : thm
    val num_from_dec_list_def : thm
    val num_from_dec_string_def : thm
    val num_from_hex_list_def : thm
    val num_from_hex_string_def : thm
    val num_from_oct_list_def : thm
    val num_from_oct_string_def : thm
    val num_to_bin_list_def : thm
    val num_to_bin_string_def : thm
    val num_to_dec_list_def : thm
    val num_to_dec_string_def : thm
    val num_to_hex_list_def : thm
    val num_to_hex_string_def : thm
    val num_to_oct_list_def : thm
    val num_to_oct_string_def : thm
    val s2n_def : thm
  
  (*  Theorems  *)
    val ADD_BIT0 : thm
    val ADD_BITS_SUC : thm
    val ADD_BIT_SUC : thm
    val BITSLT_THM : thm
    val BITS_COMP_THM : thm
    val BITS_COMP_THM2 : thm
    val BITS_DIV_THM : thm
    val BITS_LT_HIGH : thm
    val BITS_LT_LOW : thm
    val BITS_SLICE_THM : thm
    val BITS_SLICE_THM2 : thm
    val BITS_SUC : thm
    val BITS_SUC_THM : thm
    val BITS_SUM : thm
    val BITS_SUM2 : thm
    val BITS_SUM3 : thm
    val BITS_THM : thm
    val BITS_THM2 : thm
    val BITS_ZERO : thm
    val BITS_ZERO2 : thm
    val BITS_ZERO3 : thm
    val BITS_ZERO4 : thm
    val BITS_ZEROL : thm
    val BITV_THM : thm
    val BITWISE_BITS : thm
    val BITWISE_COR : thm
    val BITWISE_EVAL : thm
    val BITWISE_LT_2EXP : thm
    val BITWISE_NOT_COR : thm
    val BITWISE_ONE_COMP_LEM : thm
    val BITWISE_THM : thm
    val BIT_B : thm
    val BIT_BITS_THM : thm
    val BIT_B_NEQ : thm
    val BIT_COMP_THM3 : thm
    val BIT_DIV2 : thm
    val BIT_EXP_SUB1 : thm
    val BIT_LOG2 : thm
    val BIT_MODIFY_THM : thm
    val BIT_OF_BITS_THM : thm
    val BIT_OF_BITS_THM2 : thm
    val BIT_REVERSE_THM : thm
    val BIT_SHIFT_THM : thm
    val BIT_SHIFT_THM2 : thm
    val BIT_SHIFT_THM3 : thm
    val BIT_SIGN_EXTEND : thm
    val BIT_SLICE : thm
    val BIT_SLICE_LEM : thm
    val BIT_SLICE_THM : thm
    val BIT_SLICE_THM2 : thm
    val BIT_SLICE_THM3 : thm
    val BIT_SLICE_THM4 : thm
    val BIT_ZERO : thm
    val BIT_num_from_bin_list : thm
    val BIT_num_from_bin_string : thm
    val DEC_UNDEC : thm
    val DIVMOD_2EXP : thm
    val DIV_0_IMP_LT : thm
    val DIV_MULT_1 : thm
    val DIV_MULT_THM : thm
    val DIV_MULT_THM2 : thm
    val EL_TAKE : thm
    val EL_n2l : thm
    val EL_num_to_bin_list : thm
    val EXP_SUB_LESS_EQ : thm
    val HEX_UNHEX : thm
    val HEX_def : thm
    val HEX_ind : thm
    val LEAST_THM : thm
    val LENGTH_l2n : thm
    val LENGTH_n2l : thm
    val LESS_EQ_EXP_MULT : thm
    val LOG2_UNIQUE : thm
    val LOG_RWT : thm
    val LSB_ODD : thm
    val LT_TWOEXP : thm
    val MOD_2EXP_LT : thm
    val MOD_2EXP_MONO : thm
    val MOD_ADD_1 : thm
    val MOD_PLUS_1 : thm
    val MOD_PLUS_RIGHT : thm
    val NOT_BIT : thm
    val NOT_BITS : thm
    val NOT_BITS2 : thm
    val NOT_BIT_GT_BITWISE : thm
    val NOT_BIT_GT_LOG2 : thm
    val NOT_BIT_GT_TWOEXP : thm
    val NOT_MOD2_LEM : thm
    val NOT_MOD2_LEM2 : thm
    val NOT_ZERO_ADD1 : thm
    val ODD_MOD2_LEM : thm
    val SBIT_DIV : thm
    val SBIT_MULT : thm
    val SLICELT_THM : thm
    val SLICE_COMP_RWT : thm
    val SLICE_COMP_THM : thm
    val SLICE_COMP_THM2 : thm
    val SLICE_THM : thm
    val SLICE_ZERO : thm
    val SLICE_ZERO2 : thm
    val SLICE_ZERO_THM : thm
    val SUB_num_to_bin_string : thm
    val SUC_SUB : thm
    val TWOEXP_DIVISION : thm
    val TWOEXP_MONO : thm
    val TWOEXP_MONO2 : thm
    val TWOEXP_NOT_ZERO : thm
    val UNHEX_HEX : thm
    val UNHEX_def : thm
    val UNHEX_ind : thm
    val ZERO_LT_TWOEXP : thm
    val l2n_DIGIT : thm
    val l2n_n2l : thm
    val n2l_BOUND : thm
    val n2l_def : thm
    val n2l_ind : thm
    val n2l_l2n : thm
    val n2s_compute : thm
    val n2s_s2n : thm
    val num_bin_list : thm
    val num_bin_string : thm
    val num_dec_list : thm
    val num_dec_string : thm
    val num_hex_list : thm
    val num_hex_string : thm
    val num_oct_list : thm
    val num_oct_string : thm
    val s2n_compute : thm
    val s2n_n2s : thm
  
  val bit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [logroot] Parent theory of "bit"
   
   [string] Parent theory of "bit"
   
   [BITS_def]  Definition
      
      |- !h l n. BITS h l n = MOD_2EXP (SUC h - l) (DIV_2EXP l n)
   
   [BITV_def]  Definition
      
      |- !n b. BITV n b = BITS b b n
   
   [BITWISE_def]  Definition
      
      |- (!op x y. BITWISE 0 op x y = 0) /\
         !n op x y.
           BITWISE (SUC n) op x y =
           BITWISE n op x y + SBIT (op (BIT n x) (BIT n y)) n
   
   [BIT_MODIFY_def]  Definition
      
      |- (!f x. BIT_MODIFY 0 f x = 0) /\
         !n f x.
           BIT_MODIFY (SUC n) f x =
           BIT_MODIFY n f x + SBIT (f n (BIT n x)) n
   
   [BIT_REVERSE_def]  Definition
      
      |- (!x. BIT_REVERSE 0 x = 0) /\
         !n x.
           BIT_REVERSE (SUC n) x = BIT_REVERSE n x * 2 + SBIT (BIT n x) 0
   
   [BIT_def]  Definition
      
      |- !b n. BIT b n <=> (BITS b b n = 1)
   
   [DIVMOD_2EXP_def]  Definition
      
      |- !x n. DIVMOD_2EXP x n = (n DIV 2 ** x,n MOD 2 ** x)
   
   [HEX_primitive_def]  Definition
      
      |- HEX =
         WFREC (@R. WF R)
           (\HEX a.
              case a of
                 0 -> I #"0"
              || 1 -> I #"1"
              || 2 -> I #"2"
              || 3 -> I #"3"
              || 4 -> I #"4"
              || 5 -> I #"5"
              || 6 -> I #"6"
              || 7 -> I #"7"
              || 8 -> I #"8"
              || 9 -> I #"9"
              || 10 -> I #"A"
              || 11 -> I #"B"
              || 12 -> I #"C"
              || 13 -> I #"D"
              || 14 -> I #"E"
              || 15 -> I #"F"
              || v -> ARB)
   
   [LOG2_def]  Definition
      
      |- LOG2 = LOG 2
   
   [LOWEST_SET_BIT_def]  Definition
      
      |- !n. LOWEST_SET_BIT n = LEAST i. BIT i n
   
   [LSB_def]  Definition
      
      |- LSB = BIT 0
   
   [MOD_2EXP_EQ_def]  Definition
      
      |- !n a b. MOD_2EXP_EQ n a b <=> (MOD_2EXP n a = MOD_2EXP n b)
   
   [MOD_2EXP_MAX_def]  Definition
      
      |- !n a. MOD_2EXP_MAX n a <=> (MOD_2EXP n a = 2 ** n - 1)
   
   [SBIT_def]  Definition
      
      |- !b n. SBIT b n = if b then 2 ** n else 0
   
   [SIGN_EXTEND_def]  Definition
      
      |- !l h n.
           SIGN_EXTEND l h n =
           (let m = n MOD 2 ** l in
              if BIT (l - 1) n then 2 ** h - 2 ** l + m else m)
   
   [SLICE_def]  Definition
      
      |- !h l n. SLICE h l n = MOD_2EXP (SUC h) n - MOD_2EXP l n
   
   [TIMES_2EXP_def]  Definition
      
      |- !x n. TIMES_2EXP x n = n * 2 ** x
   
   [UNHEX_primitive_def]  Definition
      
      |- UNHEX =
         WFREC (@R. WF R)
           (\UNHEX a.
              case a of
                 #"0" -> I 0
              || #"1" -> I 1
              || #"2" -> I 2
              || #"3" -> I 3
              || #"4" -> I 4
              || #"5" -> I 5
              || #"6" -> I 6
              || #"7" -> I 7
              || #"8" -> I 8
              || #"9" -> I 9
              || #"a" -> I 10
              || #"b" -> I 11
              || #"c" -> I 12
              || #"d" -> I 13
              || #"e" -> I 14
              || #"f" -> I 15
              || #"A" -> I 10
              || #"B" -> I 11
              || #"C" -> I 12
              || #"D" -> I 13
              || #"E" -> I 14
              || #"F" -> I 15
              || v -> ARB)
   
   [l2n_def]  Definition
      
      |- (!b. l2n b [] = 0) /\ !b h t. l2n b (h::t) = h MOD b + b * l2n b t
   
   [n2l_curried_def]  Definition
      
      |- !x x1. n2l x x1 = n2l_tupled (x,x1)
   
   [n2l_tupled_primitive_def]  Definition
      
      |- n2l_tupled =
         WFREC
           (@R. WF R /\ !b n. ~(n < b \/ b < 2) ==> R (b,n DIV b) (b,n))
           (\n2l_tupled a.
              case a of
                 (b,n) ->
                   I
                     (if n < b \/ b < 2 then
                        [n MOD b]
                      else
                        n MOD b::n2l_tupled (b,n DIV b)))
   
   [n2s_def]  Definition
      
      |- !b f n. n2s b f n = REVERSE (MAP f (n2l b n))
   
   [num_from_bin_list_def]  Definition
      
      |- num_from_bin_list = l2n 2
   
   [num_from_bin_string_def]  Definition
      
      |- num_from_bin_string = s2n 2 UNHEX
   
   [num_from_dec_list_def]  Definition
      
      |- num_from_dec_list = l2n 10
   
   [num_from_dec_string_def]  Definition
      
      |- num_from_dec_string = s2n 10 UNHEX
   
   [num_from_hex_list_def]  Definition
      
      |- num_from_hex_list = l2n 16
   
   [num_from_hex_string_def]  Definition
      
      |- num_from_hex_string = s2n 16 UNHEX
   
   [num_from_oct_list_def]  Definition
      
      |- num_from_oct_list = l2n 8
   
   [num_from_oct_string_def]  Definition
      
      |- num_from_oct_string = s2n 8 UNHEX
   
   [num_to_bin_list_def]  Definition
      
      |- num_to_bin_list = n2l 2
   
   [num_to_bin_string_def]  Definition
      
      |- num_to_bin_string = n2s 2 HEX
   
   [num_to_dec_list_def]  Definition
      
      |- num_to_dec_list = n2l 10
   
   [num_to_dec_string_def]  Definition
      
      |- num_to_dec_string = n2s 10 HEX
   
   [num_to_hex_list_def]  Definition
      
      |- num_to_hex_list = n2l 16
   
   [num_to_hex_string_def]  Definition
      
      |- num_to_hex_string = n2s 16 HEX
   
   [num_to_oct_list_def]  Definition
      
      |- num_to_oct_list = n2l 8
   
   [num_to_oct_string_def]  Definition
      
      |- num_to_oct_string = n2s 8 HEX
   
   [s2n_def]  Definition
      
      |- !b f s. s2n b f s = l2n b (MAP f (REVERSE s))
   
   [ADD_BIT0]  Theorem
      
      |- !m n. BIT 0 (m + n) <=> (BIT 0 m <=/=> BIT 0 n)
   
   [ADD_BITS_SUC]  Theorem
      
      |- !n a b.
           BITS (SUC n) (SUC n) (a + b) =
           (BITS (SUC n) (SUC n) a + BITS (SUC n) (SUC n) b +
            BITS (SUC n) (SUC n) (BITS n 0 a + BITS n 0 b)) MOD 2
   
   [ADD_BIT_SUC]  Theorem
      
      |- !n a b.
           BIT (SUC n) (a + b) <=>
           if BIT (SUC n) (BITS n 0 a + BITS n 0 b) then
             BIT (SUC n) a <=> BIT (SUC n) b
           else
             BIT (SUC n) a <=/=> BIT (SUC n) b
   
   [BITSLT_THM]  Theorem
      
      |- !h l n. BITS h l n < 2 ** (SUC h - l)
   
   [BITS_COMP_THM]  Theorem
      
      |- !h1 l1 h2 l2 n.
           h2 + l1 <= h1 ==>
           (BITS h2 l2 (BITS h1 l1 n) = BITS (h2 + l1) (l2 + l1) n)
   
   [BITS_COMP_THM2]  Theorem
      
      |- !h1 l1 h2 l2 n.
           BITS h2 l2 (BITS h1 l1 n) = BITS (MIN h1 (h2 + l1)) (l2 + l1) n
   
   [BITS_DIV_THM]  Theorem
      
      |- !h l x n. BITS h l x DIV 2 ** n = BITS h (l + n) x
   
   [BITS_LT_HIGH]  Theorem
      
      |- !h l n. n < 2 ** SUC h ==> (BITS h l n = n DIV 2 ** l)
   
   [BITS_LT_LOW]  Theorem
      
      |- !h l n. n < 2 ** l ==> (BITS h l n = 0)
   
   [BITS_SLICE_THM]  Theorem
      
      |- !h l n. BITS h l (SLICE h l n) = BITS h l n
   
   [BITS_SLICE_THM2]  Theorem
      
      |- !h l n. h <= h2 ==> (BITS h2 l (SLICE h l n) = BITS h l n)
   
   [BITS_SUC]  Theorem
      
      |- !h l n.
           l <= SUC h ==>
           (SBIT (BIT (SUC h) n) (SUC h - l) + BITS h l n =
            BITS (SUC h) l n)
   
   [BITS_SUC_THM]  Theorem
      
      |- !h l n.
           BITS (SUC h) l n =
           if SUC h < l then
             0
           else
             SBIT (BIT (SUC h) n) (SUC h - l) + BITS h l n
   
   [BITS_SUM]  Theorem
      
      |- !h l a b.
           b < 2 ** l ==>
           (BITS h l (a * 2 ** l + b) = BITS h l (a * 2 ** l))
   
   [BITS_SUM2]  Theorem
      
      |- !h l a b. BITS h l (a * 2 ** SUC h + b) = BITS h l b
   
   [BITS_SUM3]  Theorem
      
      |- !h a b. BITS h 0 (BITS h 0 a + BITS h 0 b) = BITS h 0 (a + b)
   
   [BITS_THM]  Theorem
      
      |- !h l n. BITS h l n = (n DIV 2 ** l) MOD 2 ** (SUC h - l)
   
   [BITS_THM2]  Theorem
      
      |- !h l n. BITS h l n = n MOD 2 ** SUC h DIV 2 ** l
   
   [BITS_ZERO]  Theorem
      
      |- !h l n. h < l ==> (BITS h l n = 0)
   
   [BITS_ZERO2]  Theorem
      
      |- !h l. BITS h l 0 = 0
   
   [BITS_ZERO3]  Theorem
      
      |- !h n. BITS h 0 n = n MOD 2 ** SUC h
   
   [BITS_ZERO4]  Theorem
      
      |- !h l n. l <= h ==> (BITS h l (a * 2 ** l) = BITS (h - l) 0 a)
   
   [BITS_ZEROL]  Theorem
      
      |- !h a. a < 2 ** SUC h ==> (BITS h 0 a = a)
   
   [BITV_THM]  Theorem
      
      |- !b n. BITV n b = SBIT (BIT b n) 0
   
   [BITWISE_BITS]  Theorem
      
      |- !wl op a b.
           BITWISE (SUC wl) op (BITS wl 0 a) (BITS wl 0 b) =
           BITWISE (SUC wl) op a b
   
   [BITWISE_COR]  Theorem
      
      |- !x n op a b.
           x < n ==>
           op (BIT x a) (BIT x b) ==>
           ((BITWISE n op a b DIV 2 ** x) MOD 2 = 1)
   
   [BITWISE_EVAL]  Theorem
      
      |- !n op a b.
           BITWISE (SUC n) op a b =
           2 * BITWISE n op (a DIV 2) (b DIV 2) +
           SBIT (op (LSB a) (LSB b)) 0
   
   [BITWISE_LT_2EXP]  Theorem
      
      |- !n op a b. BITWISE n op a b < 2 ** n
   
   [BITWISE_NOT_COR]  Theorem
      
      |- !x n op a b.
           x < n ==>
           ~op (BIT x a) (BIT x b) ==>
           ((BITWISE n op a b DIV 2 ** x) MOD 2 = 0)
   
   [BITWISE_ONE_COMP_LEM]  Theorem
      
      |- !n a b.
           BITWISE (SUC n) (\x y. ~x) a b = 2 ** SUC n - 1 - BITS n 0 a
   
   [BITWISE_THM]  Theorem
      
      |- !x n op a b.
           x < n ==> (BIT x (BITWISE n op a b) <=> op (BIT x a) (BIT x b))
   
   [BIT_B]  Theorem
      
      |- !b. BIT b (2 ** b)
   
   [BIT_BITS_THM]  Theorem
      
      |- !h l a b.
           (!x. l <= x /\ x <= h ==> (BIT x a <=> BIT x b)) <=>
           (BITS h l a = BITS h l b)
   
   [BIT_B_NEQ]  Theorem
      
      |- !a b. a <> b ==> ~BIT a (2 ** b)
   
   [BIT_COMP_THM3]  Theorem
      
      |- !h m l n.
           SUC m <= h /\ l <= m ==>
           (BITS h (SUC m) n * 2 ** (SUC m - l) + BITS m l n = BITS h l n)
   
   [BIT_DIV2]  Theorem
      
      |- !n i. BIT n (i DIV 2) <=> BIT (SUC n) i
   
   [BIT_EXP_SUB1]  Theorem
      
      |- !b n. BIT b (2 ** n - 1) <=> b < n
   
   [BIT_LOG2]  Theorem
      
      |- !n. n <> 0 ==> BIT (LOG2 n) n
   
   [BIT_MODIFY_THM]  Theorem
      
      |- !x n f a. x < n ==> (BIT x (BIT_MODIFY n f a) <=> f x (BIT x a))
   
   [BIT_OF_BITS_THM]  Theorem
      
      |- !n h l a. l + n <= h ==> (BIT n (BITS h l a) <=> BIT (l + n) a)
   
   [BIT_OF_BITS_THM2]  Theorem
      
      |- !h l x n. h < l + x ==> ~BIT x (BITS h l n)
   
   [BIT_REVERSE_THM]  Theorem
      
      |- !x n a. x < n ==> (BIT x (BIT_REVERSE n a) <=> BIT (n - 1 - x) a)
   
   [BIT_SHIFT_THM]  Theorem
      
      |- !n a s. BIT (n + s) (a * 2 ** s) <=> BIT n a
   
   [BIT_SHIFT_THM2]  Theorem
      
      |- !n a s. s <= n ==> (BIT n (a * 2 ** s) <=> BIT (n - s) a)
   
   [BIT_SHIFT_THM3]  Theorem
      
      |- !n a s. n < s ==> ~BIT n (a * 2 ** s)
   
   [BIT_SIGN_EXTEND]  Theorem
      
      |- !l h n i.
           l <> 0 ==>
           (BIT i (SIGN_EXTEND l h n) <=>
            if l <= h ==> i < l then
              BIT i (n MOD 2 ** l)
            else
              i < h /\ BIT (l - 1) n)
   
   [BIT_SLICE]  Theorem
      
      |- !n a b. (BIT n a <=> BIT n b) <=> (SLICE n n a = SLICE n n b)
   
   [BIT_SLICE_LEM]  Theorem
      
      |- !y x n. SBIT (BIT x n) (x + y) = SLICE x x n * 2 ** y
   
   [BIT_SLICE_THM]  Theorem
      
      |- !x n. SBIT (BIT x n) x = SLICE x x n
   
   [BIT_SLICE_THM2]  Theorem
      
      |- !b n. BIT b n <=> (SLICE b b n = 2 ** b)
   
   [BIT_SLICE_THM3]  Theorem
      
      |- !b n. ~BIT b n <=> (SLICE b b n = 0)
   
   [BIT_SLICE_THM4]  Theorem
      
      |- !b h l n. BIT b (SLICE h l n) <=> l <= b /\ b <= h /\ BIT b n
   
   [BIT_ZERO]  Theorem
      
      |- !b. ~BIT b 0
   
   [BIT_num_from_bin_list]  Theorem
      
      |- !x l.
           EVERY ($> 2) l /\ x < LENGTH l ==>
           (BIT x (num_from_bin_list l) <=> (EL x l = 1))
   
   [BIT_num_from_bin_string]  Theorem
      
      |- !x s.
           EVERY ($> 2 o UNHEX) s /\ x < STRLEN s ==>
           (BIT x (num_from_bin_string s) <=>
            (UNHEX (SUB (s,PRE (STRLEN s - x))) = 1))
   
   [DEC_UNDEC]  Theorem
      
      |- !c. isDigit c ==> (HEX (UNHEX c) = c)
   
   [DIVMOD_2EXP]  Theorem
      
      |- !x n. DIVMOD_2EXP x n = (DIV_2EXP x n,MOD_2EXP x n)
   
   [DIV_0_IMP_LT]  Theorem
      
      |- !b n. 1 < b /\ (n DIV b = 0) ==> n < b
   
   [DIV_MULT_1]  Theorem
      
      |- !r n. r < n ==> ((n + r) DIV n = 1)
   
   [DIV_MULT_THM]  Theorem
      
      |- !x n. n DIV 2 ** x * 2 ** x = n - n MOD 2 ** x
   
   [DIV_MULT_THM2]  Theorem
      
      |- !n. 2 * (n DIV 2) = n - n MOD 2
   
   [EL_TAKE]  Theorem
      
      |- !x n l. x < n /\ n <= LENGTH l ==> (EL x (TAKE n l) = EL x l)
   
   [EL_n2l]  Theorem
      
      |- !b x n.
           1 < b /\ x < LENGTH (n2l b n) ==>
           (EL x (n2l b n) = (n DIV b ** x) MOD b)
   
   [EL_num_to_bin_list]  Theorem
      
      |- !x n.
           x < LENGTH (num_to_bin_list n) ==>
           (EL x (num_to_bin_list n) = BITV n x)
   
   [EXP_SUB_LESS_EQ]  Theorem
      
      |- !a b. 2 ** (a - b) <= 2 ** a
   
   [HEX_UNHEX]  Theorem
      
      |- !c. isHexDigit c ==> (HEX (UNHEX c) = toUpper c)
   
   [HEX_def]  Theorem
      
      |- (HEX 0 = #"0") /\ (HEX 1 = #"1") /\ (HEX 2 = #"2") /\
         (HEX 3 = #"3") /\ (HEX 4 = #"4") /\ (HEX 5 = #"5") /\
         (HEX 6 = #"6") /\ (HEX 7 = #"7") /\ (HEX 8 = #"8") /\
         (HEX 9 = #"9") /\ (HEX 10 = #"A") /\ (HEX 11 = #"B") /\
         (HEX 12 = #"C") /\ (HEX 13 = #"D") /\ (HEX 14 = #"E") /\
         (HEX 15 = #"F")
   
   [HEX_ind]  Theorem
      
      |- !P.
           P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\
           P 9 /\ P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\
           (!v18. P v18) ==>
           !v. P v
   
   [LEAST_THM]  Theorem
      
      |- !n. (!m. m < n ==> ~P m) /\ P n ==> ($LEAST P = n)
   
   [LENGTH_l2n]  Theorem
      
      |- !b l.
           1 < b /\ EVERY ($> b) l /\ l2n b l <> 0 ==>
           SUC (LOG b (l2n b l)) <= LENGTH l
   
   [LENGTH_n2l]  Theorem
      
      |- !b n.
           1 < b ==>
           (LENGTH (n2l b n) = if n = 0 then 1 else SUC (LOG b n))
   
   [LESS_EQ_EXP_MULT]  Theorem
      
      |- !a b. a <= b ==> ?p. 2 ** b = p * 2 ** a
   
   [LOG2_UNIQUE]  Theorem
      
      |- !n p. 2 ** p <= n /\ n < 2 ** SUC p ==> (LOG2 n = p)
   
   [LOG_RWT]  Theorem
      
      |- !m n.
           1 < m /\ 0 < n ==>
           (LOG m n = if n < m then 0 else SUC (LOG m (n DIV m)))
   
   [LSB_ODD]  Theorem
      
      |- LSB = ODD
   
   [LT_TWOEXP]  Theorem
      
      |- !x n. x < 2 ** n <=> (x = 0) \/ LOG2 x < n
   
   [MOD_2EXP_LT]  Theorem
      
      |- !n k. k MOD 2 ** n < 2 ** n
   
   [MOD_2EXP_MONO]  Theorem
      
      |- !n h l. l <= h ==> n MOD 2 ** l <= n MOD 2 ** SUC h
   
   [MOD_ADD_1]  Theorem
      
      |- !n.
           0 < n ==>
           !x. (x + 1) MOD n <> 0 ==> ((x + 1) MOD n = x MOD n + 1)
   
   [MOD_PLUS_1]  Theorem
      
      |- !n. 0 < n ==> !x. ((x + 1) MOD n = 0) <=> (x MOD n + 1 = n)
   
   [MOD_PLUS_RIGHT]  Theorem
      
      |- !n. 0 < n ==> !j k. (j + k MOD n) MOD n = (j + k) MOD n
   
   [NOT_BIT]  Theorem
      
      |- !n a. ~BIT n a <=> (BITS n n a = 0)
   
   [NOT_BITS]  Theorem
      
      |- !n a. BITS n n a <> 0 <=> (BITS n n a = 1)
   
   [NOT_BITS2]  Theorem
      
      |- !n a. BITS n n a <> 1 <=> (BITS n n a = 0)
   
   [NOT_BIT_GT_BITWISE]  Theorem
      
      |- !i n op a b. n <= i ==> ~BIT i (BITWISE n op a b)
   
   [NOT_BIT_GT_LOG2]  Theorem
      
      |- !i n. LOG2 n < i ==> ~BIT i n
   
   [NOT_BIT_GT_TWOEXP]  Theorem
      
      |- !i n. n < 2 ** i ==> ~BIT i n
   
   [NOT_MOD2_LEM]  Theorem
      
      |- !n. n MOD 2 <> 0 <=> (n MOD 2 = 1)
   
   [NOT_MOD2_LEM2]  Theorem
      
      |- !n a. n MOD 2 <> 1 <=> (n MOD 2 = 0)
   
   [NOT_ZERO_ADD1]  Theorem
      
      |- !m. m <> 0 ==> ?p. m = SUC p
   
   [ODD_MOD2_LEM]  Theorem
      
      |- !n. ODD n <=> (n MOD 2 = 1)
   
   [SBIT_DIV]  Theorem
      
      |- !b m n. n < m ==> (SBIT b (m - n) = SBIT b m DIV 2 ** n)
   
   [SBIT_MULT]  Theorem
      
      |- !b m n. SBIT b n * 2 ** m = SBIT b (n + m)
   
   [SLICELT_THM]  Theorem
      
      |- !h l n. SLICE h l n < 2 ** SUC h
   
   [SLICE_COMP_RWT]  Theorem
      
      |- !h m' m l n.
           l <= m /\ (m' = m + 1) /\ m < h ==>
           (SLICE h m' n + SLICE m l n = SLICE h l n)
   
   [SLICE_COMP_THM]  Theorem
      
      |- !h m l n.
           SUC m <= h /\ l <= m ==>
           (SLICE h (SUC m) n + SLICE m l n = SLICE h l n)
   
   [SLICE_COMP_THM2]  Theorem
      
      |- !h l x y n.
           h <= x /\ y <= l ==> (SLICE h l (SLICE x y n) = SLICE h l n)
   
   [SLICE_THM]  Theorem
      
      |- !n h l. SLICE h l n = BITS h l n * 2 ** l
   
   [SLICE_ZERO]  Theorem
      
      |- !h l n. h < l ==> (SLICE h l n = 0)
   
   [SLICE_ZERO2]  Theorem
      
      |- SLICE h l 0 = 0
   
   [SLICE_ZERO_THM]  Theorem
      
      |- !n h. SLICE h 0 n = BITS h 0 n
   
   [SUB_num_to_bin_string]  Theorem
      
      |- !x n.
           x < STRLEN (num_to_bin_string n) ==>
           (SUB (num_to_bin_string n,x) =
            HEX (BITV n (PRE (STRLEN (num_to_bin_string n) - x))))
   
   [SUC_SUB]  Theorem
      
      |- SUC a - a = 1
   
   [TWOEXP_DIVISION]  Theorem
      
      |- !n k. k = k DIV 2 ** n * 2 ** n + k MOD 2 ** n
   
   [TWOEXP_MONO]  Theorem
      
      |- !a b. a < b ==> 2 ** a < 2 ** b
   
   [TWOEXP_MONO2]  Theorem
      
      |- !a b. a <= b ==> 2 ** a <= 2 ** b
   
   [TWOEXP_NOT_ZERO]  Theorem
      
      |- !n. 2 ** n <> 0
   
   [UNHEX_HEX]  Theorem
      
      |- !n. n < 16 ==> (UNHEX (HEX n) = n)
   
   [UNHEX_def]  Theorem
      
      |- (UNHEX #"0" = 0) /\ (UNHEX #"1" = 1) /\ (UNHEX #"2" = 2) /\
         (UNHEX #"3" = 3) /\ (UNHEX #"4" = 4) /\ (UNHEX #"5" = 5) /\
         (UNHEX #"6" = 6) /\ (UNHEX #"7" = 7) /\ (UNHEX #"8" = 8) /\
         (UNHEX #"9" = 9) /\ (UNHEX #"a" = 10) /\ (UNHEX #"b" = 11) /\
         (UNHEX #"c" = 12) /\ (UNHEX #"d" = 13) /\ (UNHEX #"e" = 14) /\
         (UNHEX #"f" = 15) /\ (UNHEX #"A" = 10) /\ (UNHEX #"B" = 11) /\
         (UNHEX #"C" = 12) /\ (UNHEX #"D" = 13) /\ (UNHEX #"E" = 14) /\
         (UNHEX #"F" = 15)
   
   [UNHEX_ind]  Theorem
      
      |- !P.
           P #"0" /\ P #"1" /\ P #"2" /\ P #"3" /\ P #"4" /\ P #"5" /\
           P #"6" /\ P #"7" /\ P #"8" /\ P #"9" /\ P #"a" /\ P #"b" /\
           P #"c" /\ P #"d" /\ P #"e" /\ P #"f" /\ P #"A" /\ P #"B" /\
           P #"C" /\ P #"D" /\ P #"E" /\ P #"F" /\ (!v24. P v24) ==>
           !v. P v
   
   [ZERO_LT_TWOEXP]  Theorem
      
      |- !n. 0 < 2 ** n
   
   [l2n_DIGIT]  Theorem
      
      |- !b l x.
           1 < b /\ EVERY ($> b) l /\ x < LENGTH l ==>
           ((l2n b l DIV b ** x) MOD b = EL x l)
   
   [l2n_n2l]  Theorem
      
      |- !b n. 1 < b ==> (l2n b (n2l b n) = n)
   
   [n2l_BOUND]  Theorem
      
      |- !b n. 0 < b ==> EVERY ($> b) (n2l b n)
   
   [n2l_def]  Theorem
      
      |- !n b.
           n2l b n =
           if n < b \/ b < 2 then [n MOD b] else n MOD b::n2l b (n DIV b)
   
   [n2l_ind]  Theorem
      
      |- !P.
           (!b n. (~(n < b \/ b < 2) ==> P b (n DIV b)) ==> P b n) ==>
           !v v1. P v v1
   
   [n2l_l2n]  Theorem
      
      |- !b l.
           1 < b /\ EVERY ($> b) l ==>
           (n2l b (l2n b l) =
            if l2n b l = 0 then [0] else TAKE (SUC (LOG b (l2n b l))) l)
   
   [n2s_compute]  Theorem
      
      |- n2s b f n = IMPLODE (REVERSE (MAP f (n2l b n)))
   
   [n2s_s2n]  Theorem
      
      |- !c2n n2c b s.
           1 < b /\ EVERY ($> b o c2n) s ==>
           (n2s b n2c (s2n b c2n s) =
            if s2n b c2n s = 0 then
              STRING (n2c 0) ""
            else
              MAP (n2c o c2n) (LASTN (SUC (LOG b (s2n b c2n s))) s))
   
   [num_bin_list]  Theorem
      
      |- num_from_bin_list o num_to_bin_list = I
   
   [num_bin_string]  Theorem
      
      |- num_from_bin_string o num_to_bin_string = I
   
   [num_dec_list]  Theorem
      
      |- num_from_dec_list o num_to_dec_list = I
   
   [num_dec_string]  Theorem
      
      |- num_from_dec_string o num_to_dec_string = I
   
   [num_hex_list]  Theorem
      
      |- num_from_hex_list o num_to_hex_list = I
   
   [num_hex_string]  Theorem
      
      |- num_from_hex_string o num_to_hex_string = I
   
   [num_oct_list]  Theorem
      
      |- num_from_oct_list o num_to_oct_list = I
   
   [num_oct_string]  Theorem
      
      |- num_from_oct_string o num_to_oct_string = I
   
   [s2n_compute]  Theorem
      
      |- s2n b f s = l2n b (MAP f (REVERSE (EXPLODE s)))
   
   [s2n_n2s]  Theorem
      
      |- !c2n n2c b n.
           1 < b /\ (!x. x < b ==> (c2n (n2c x) = x)) ==>
           (s2n b c2n (n2s b n2c n) = n)
   
   
*)
end
