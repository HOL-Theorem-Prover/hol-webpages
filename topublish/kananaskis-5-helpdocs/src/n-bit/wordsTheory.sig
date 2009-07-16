signature wordsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val BIT_SET_curried_def : thm
    val BIT_SET_tupled_primitive_def : thm
    val INT_MAX_def : thm
    val INT_MIN_def : thm
    val UINT_MAX_def : thm
    val dimword_def : thm
    val l2w_def : thm
    val n2w_def : thm
    val n2w_itself_primitive_def : thm
    val nzcv_def : thm
    val s2w_def : thm
    val sw2sw_def : thm
    val w2l_def : thm
    val w2n_def : thm
    val w2s_def : thm
    val w2w_def : thm
    val word_1comp_def : thm
    val word_2comp_def : thm
    val word_H_def : thm
    val word_L2_def : thm
    val word_L_def : thm
    val word_T_def : thm
    val word_add_def : thm
    val word_and_def : thm
    val word_asr_def : thm
    val word_bit_def : thm
    val word_bits_def : thm
    val word_concat_def : thm
    val word_div_def : thm
    val word_extract_def : thm
    val word_from_bin_list_def : thm
    val word_from_bin_string_def : thm
    val word_from_dec_list_def : thm
    val word_from_dec_string_def : thm
    val word_from_hex_list_def : thm
    val word_from_hex_string_def : thm
    val word_from_oct_list_def : thm
    val word_from_oct_string_def : thm
    val word_ge_def : thm
    val word_gt_def : thm
    val word_hi_def : thm
    val word_hs_def : thm
    val word_join_def : thm
    val word_le_def : thm
    val word_len_def : thm
    val word_lo_def : thm
    val word_log2_def : thm
    val word_ls_def : thm
    val word_lsb_def : thm
    val word_lsl_def : thm
    val word_lsr_def : thm
    val word_lt_def : thm
    val word_mod_def : thm
    val word_modify_def : thm
    val word_msb_def : thm
    val word_mul_def : thm
    val word_or_def : thm
    val word_reverse_def : thm
    val word_rol_def : thm
    val word_ror_def : thm
    val word_rrx_def : thm
    val word_sdiv_def : thm
    val word_signed_bits_def : thm
    val word_slice_def : thm
    val word_sub_def : thm
    val word_to_bin_list_def : thm
    val word_to_bin_string_def : thm
    val word_to_dec_list_def : thm
    val word_to_dec_string_def : thm
    val word_to_hex_list_def : thm
    val word_to_hex_string_def : thm
    val word_to_oct_list_def : thm
    val word_to_oct_string_def : thm
    val word_xor_def : thm
  
  (*  Theorems  *)
    val ASR_ADD : thm
    val ASR_LIMIT : thm
    val ASR_UINT_MAX : thm
    val BIT_SET : thm
    val BIT_SET_def : thm
    val BIT_SET_ind : thm
    val BIT_UPDATE : thm
    val CONCAT_EXTRACT : thm
    val DIMINDEX_GT_0 : thm
    val EXISTS_HB : thm
    val EXTRACT_ALL_BITS : thm
    val EXTRACT_CONCAT : thm
    val EXTRACT_JOIN : thm
    val EXTRACT_JOIN_ADD : thm
    val EXTRACT_JOIN_ADD_LSL : thm
    val EXTRACT_JOIN_LSL : thm
    val INT_MIN_12 : thm
    val INT_MIN_16 : thm
    val INT_MIN_2 : thm
    val INT_MIN_20 : thm
    val INT_MIN_24 : thm
    val INT_MIN_28 : thm
    val INT_MIN_3 : thm
    val INT_MIN_30 : thm
    val INT_MIN_32 : thm
    val INT_MIN_4 : thm
    val INT_MIN_5 : thm
    val INT_MIN_6 : thm
    val INT_MIN_64 : thm
    val INT_MIN_7 : thm
    val INT_MIN_8 : thm
    val INT_MIN_SUM : thm
    val LSL_ADD : thm
    val LSL_BITWISE : thm
    val LSL_LIMIT : thm
    val LSL_ONE : thm
    val LSL_UINT_MAX : thm
    val LSR_ADD : thm
    val LSR_BITWISE : thm
    val LSR_LESS : thm
    val LSR_LIMIT : thm
    val MOD_2EXP_DIMINDEX : thm
    val MOD_COMPLEMENT : thm
    val MOD_DIMINDEX : thm
    val NOT_INT_MIN_ZERO : thm
    val ONE_LT_dimword : thm
    val ROL_ADD : thm
    val ROL_BITWISE : thm
    val ROL_MOD : thm
    val ROR_ADD : thm
    val ROR_BITWISE : thm
    val ROR_CYCLE : thm
    val ROR_MOD : thm
    val ROR_ROL : thm
    val ROR_UINT_MAX : thm
    val SHIFT_ZERO : thm
    val SUC_WORD_PRED : thm
    val TWO_COMP_NEG : thm
    val TWO_COMP_POS : thm
    val TWO_COMP_POS_NEG : thm
    val WORD_0_LS : thm
    val WORD_0_POS : thm
    val WORD_2COMP_LSL : thm
    val WORD_ADD_0 : thm
    val WORD_ADD_ASSOC : thm
    val WORD_ADD_BIT : thm
    val WORD_ADD_BIT0 : thm
    val WORD_ADD_COMM : thm
    val WORD_ADD_EQ_SUB : thm
    val WORD_ADD_INV_0_EQ : thm
    val WORD_ADD_LEFT_LO : thm
    val WORD_ADD_LEFT_LO2 : thm
    val WORD_ADD_LEFT_LS : thm
    val WORD_ADD_LEFT_LS2 : thm
    val WORD_ADD_LID_UNIQ : thm
    val WORD_ADD_LINV : thm
    val WORD_ADD_LSL : thm
    val WORD_ADD_OR : thm
    val WORD_ADD_RID_UNIQ : thm
    val WORD_ADD_RIGHT_LO : thm
    val WORD_ADD_RIGHT_LO2 : thm
    val WORD_ADD_RIGHT_LS : thm
    val WORD_ADD_RIGHT_LS2 : thm
    val WORD_ADD_RINV : thm
    val WORD_ADD_SUB : thm
    val WORD_ADD_SUB2 : thm
    val WORD_ADD_SUB3 : thm
    val WORD_ADD_SUB_ASSOC : thm
    val WORD_ADD_SUB_SYM : thm
    val WORD_ALL_BITS : thm
    val WORD_AND_ABSORD : thm
    val WORD_AND_ASSOC : thm
    val WORD_AND_CLAUSES : thm
    val WORD_AND_COMM : thm
    val WORD_AND_COMP : thm
    val WORD_AND_EXP_SUB1 : thm
    val WORD_AND_IDEM : thm
    val WORD_BITS_COMP_THM : thm
    val WORD_BITS_EXTRACT : thm
    val WORD_BITS_LSL : thm
    val WORD_BITS_LSR : thm
    val WORD_BITS_LT : thm
    val WORD_BITS_MIN_HIGH : thm
    val WORD_BITS_OVER_BITWISE : thm
    val WORD_BITS_SLICE_THM : thm
    val WORD_BITS_ZERO : thm
    val WORD_BITS_ZERO2 : thm
    val WORD_BITS_ZERO3 : thm
    val WORD_BIT_BITS : thm
    val WORD_DE_MORGAN_THM : thm
    val WORD_DIVISION : thm
    val WORD_EQ : thm
    val WORD_EQ_ADD_LCANCEL : thm
    val WORD_EQ_ADD_RCANCEL : thm
    val WORD_EQ_NEG : thm
    val WORD_EQ_SUB_LADD : thm
    val WORD_EQ_SUB_RADD : thm
    val WORD_EQ_SUB_ZERO : thm
    val WORD_EXTRACT_BITS_COMP : thm
    val WORD_EXTRACT_COMP_THM : thm
    val WORD_EXTRACT_LSL : thm
    val WORD_EXTRACT_MIN_HIGH : thm
    val WORD_EXTRACT_OVER_ADD : thm
    val WORD_EXTRACT_OVER_BITWISE : thm
    val WORD_EXTRACT_ZERO : thm
    val WORD_EXTRACT_ZERO2 : thm
    val WORD_EXTRACT_ZERO3 : thm
    val WORD_GE : thm
    val WORD_GREATER : thm
    val WORD_GREATER_EQ : thm
    val WORD_GREATER_OR_EQ : thm
    val WORD_GT : thm
    val WORD_HI : thm
    val WORD_HIGHER : thm
    val WORD_HIGHER_EQ : thm
    val WORD_HIGHER_OR_EQ : thm
    val WORD_HS : thm
    val WORD_H_POS : thm
    val WORD_H_WORD_L : thm
    val WORD_INDUCT : thm
    val WORD_LCANCEL_SUB : thm
    val WORD_LE : thm
    val WORD_LEFT_ADD_DISTRIB : thm
    val WORD_LEFT_AND_OVER_OR : thm
    val WORD_LEFT_AND_OVER_XOR : thm
    val WORD_LEFT_OR_OVER_AND : thm
    val WORD_LEFT_SUB_DISTRIB : thm
    val WORD_LESS_0_word_T : thm
    val WORD_LESS_ANTISYM : thm
    val WORD_LESS_CASES : thm
    val WORD_LESS_CASES_IMP : thm
    val WORD_LESS_EQUAL_ANTISYM : thm
    val WORD_LESS_EQ_ANTISYM : thm
    val WORD_LESS_EQ_CASES : thm
    val WORD_LESS_EQ_H : thm
    val WORD_LESS_EQ_LESS_TRANS : thm
    val WORD_LESS_EQ_REFL : thm
    val WORD_LESS_EQ_TRANS : thm
    val WORD_LESS_IMP_LESS_OR_EQ : thm
    val WORD_LESS_LESS_CASES : thm
    val WORD_LESS_LESS_EQ_TRANS : thm
    val WORD_LESS_NEG_LEFT : thm
    val WORD_LESS_NEG_RIGHT : thm
    val WORD_LESS_NOT_EQ : thm
    val WORD_LESS_OR_EQ : thm
    val WORD_LESS_REFL : thm
    val WORD_LESS_TRANS : thm
    val WORD_LE_EQ_LS : thm
    val WORD_LE_LS : thm
    val WORD_LITERAL_ADD : thm
    val WORD_LITERAL_AND : thm
    val WORD_LITERAL_MULT : thm
    val WORD_LITERAL_OR : thm
    val WORD_LITERAL_XOR : thm
    val WORD_LO : thm
    val WORD_LOWER_ANTISYM : thm
    val WORD_LOWER_CASES : thm
    val WORD_LOWER_CASES_IMP : thm
    val WORD_LOWER_EQUAL_ANTISYM : thm
    val WORD_LOWER_EQ_ANTISYM : thm
    val WORD_LOWER_EQ_CASES : thm
    val WORD_LOWER_EQ_LOWER_TRANS : thm
    val WORD_LOWER_EQ_REFL : thm
    val WORD_LOWER_EQ_TRANS : thm
    val WORD_LOWER_IMP_LOWER_OR_EQ : thm
    val WORD_LOWER_LOWER_CASES : thm
    val WORD_LOWER_LOWER_EQ_TRANS : thm
    val WORD_LOWER_NOT_EQ : thm
    val WORD_LOWER_OR_EQ : thm
    val WORD_LOWER_REFL : thm
    val WORD_LOWER_TRANS : thm
    val WORD_LO_word_0 : thm
    val WORD_LO_word_T : thm
    val WORD_LS : thm
    val WORD_LS_T : thm
    val WORD_LS_word_0 : thm
    val WORD_LS_word_T : thm
    val WORD_LT : thm
    val WORD_LT_EQ_LO : thm
    val WORD_LT_LO : thm
    val WORD_LT_SUB_UPPER : thm
    val WORD_L_LESS_EQ : thm
    val WORD_L_LESS_H : thm
    val WORD_L_NEG : thm
    val WORD_L_PLUS_H : thm
    val WORD_MSB_1COMP : thm
    val WORD_MSB_INT_MIN_LS : thm
    val WORD_MULT_ASSOC : thm
    val WORD_MULT_CLAUSES : thm
    val WORD_MULT_COMM : thm
    val WORD_MULT_SUC : thm
    val WORD_MUL_LSL : thm
    val WORD_NEG : thm
    val WORD_NEG_0 : thm
    val WORD_NEG_1 : thm
    val WORD_NEG_ADD : thm
    val WORD_NEG_EQ : thm
    val WORD_NEG_EQ_0 : thm
    val WORD_NEG_L : thm
    val WORD_NEG_LMUL : thm
    val WORD_NEG_MUL : thm
    val WORD_NEG_NEG : thm
    val WORD_NEG_RMUL : thm
    val WORD_NEG_SUB : thm
    val WORD_NEG_T : thm
    val WORD_NOT : thm
    val WORD_NOT_0 : thm
    val WORD_NOT_GREATER : thm
    val WORD_NOT_HIGHER : thm
    val WORD_NOT_LESS : thm
    val WORD_NOT_LESS_EQ : thm
    val WORD_NOT_LESS_EQUAL : thm
    val WORD_NOT_LOWER : thm
    val WORD_NOT_LOWER_EQ : thm
    val WORD_NOT_LOWER_EQUAL : thm
    val WORD_NOT_NOT : thm
    val WORD_NOT_T : thm
    val WORD_NOT_XOR : thm
    val WORD_OR_ABSORB : thm
    val WORD_OR_ASSOC : thm
    val WORD_OR_CLAUSES : thm
    val WORD_OR_COMM : thm
    val WORD_OR_COMP : thm
    val WORD_OR_IDEM : thm
    val WORD_PRED_THM : thm
    val WORD_RCANCEL_SUB : thm
    val WORD_RIGHT_ADD_DISTRIB : thm
    val WORD_RIGHT_AND_OVER_OR : thm
    val WORD_RIGHT_AND_OVER_XOR : thm
    val WORD_RIGHT_OR_OVER_AND : thm
    val WORD_RIGHT_SUB_DISTRIB : thm
    val WORD_SLICE_BITS_THM : thm
    val WORD_SLICE_COMP_THM : thm
    val WORD_SLICE_OVER_BITWISE : thm
    val WORD_SLICE_THM : thm
    val WORD_SLICE_ZERO : thm
    val WORD_SLICE_ZERO2 : thm
    val WORD_SUB : thm
    val WORD_SUB_ADD : thm
    val WORD_SUB_ADD2 : thm
    val WORD_SUB_LE : thm
    val WORD_SUB_LNEG : thm
    val WORD_SUB_LT : thm
    val WORD_SUB_LZERO : thm
    val WORD_SUB_NEG : thm
    val WORD_SUB_PLUS : thm
    val WORD_SUB_REFL : thm
    val WORD_SUB_RNEG : thm
    val WORD_SUB_RZERO : thm
    val WORD_SUB_SUB : thm
    val WORD_SUB_SUB2 : thm
    val WORD_SUB_SUB3 : thm
    val WORD_SUB_TRIANGLE : thm
    val WORD_XOR : thm
    val WORD_XOR_ASSOC : thm
    val WORD_XOR_CLAUSES : thm
    val WORD_XOR_COMM : thm
    val WORD_XOR_COMP : thm
    val WORD_ZERO_LE : thm
    val WORD_w2w_EXTRACT : thm
    val WORD_w2w_OVER_ADD : thm
    val WORD_w2w_OVER_BITWISE : thm
    val WORD_w2w_OVER_MUL : thm
    val ZERO_LO_INT_MIN : thm
    val ZERO_LT_dimword : thm
    val ZERO_SHIFT : thm
    val dimindex_12 : thm
    val dimindex_16 : thm
    val dimindex_2 : thm
    val dimindex_20 : thm
    val dimindex_24 : thm
    val dimindex_28 : thm
    val dimindex_3 : thm
    val dimindex_30 : thm
    val dimindex_32 : thm
    val dimindex_4 : thm
    val dimindex_5 : thm
    val dimindex_6 : thm
    val dimindex_64 : thm
    val dimindex_7 : thm
    val dimindex_8 : thm
    val dimword_12 : thm
    val dimword_16 : thm
    val dimword_2 : thm
    val dimword_20 : thm
    val dimword_24 : thm
    val dimword_28 : thm
    val dimword_3 : thm
    val dimword_30 : thm
    val dimword_32 : thm
    val dimword_4 : thm
    val dimword_5 : thm
    val dimword_6 : thm
    val dimword_64 : thm
    val dimword_7 : thm
    val dimword_8 : thm
    val dimword_IS_TWICE_INT_MIN : thm
    val fcp_n2w : thm
    val finite_12 : thm
    val finite_16 : thm
    val finite_2 : thm
    val finite_20 : thm
    val finite_24 : thm
    val finite_28 : thm
    val finite_3 : thm
    val finite_30 : thm
    val finite_32 : thm
    val finite_4 : thm
    val finite_5 : thm
    val finite_6 : thm
    val finite_64 : thm
    val finite_7 : thm
    val finite_8 : thm
    val l2n_n2l : thm
    val lsr_1_word_T : thm
    val n2w_11 : thm
    val n2w_SUC : thm
    val n2w_itself_def : thm
    val n2w_itself_ind : thm
    val n2w_mod : thm
    val n2w_w2n : thm
    val ranged_word_nchotomy : thm
    val s2w_w2s : thm
    val sw2sw : thm
    val sw2sw_0 : thm
    val sw2sw_id : thm
    val sw2sw_sw2sw : thm
    val sw2sw_w2w : thm
    val sw2sw_word_T : thm
    val w2l_l2w : thm
    val w2n_11 : thm
    val w2n_eq_0 : thm
    val w2n_lsr : thm
    val w2n_lt : thm
    val w2n_n2w : thm
    val w2n_w2w : thm
    val w2s_s2w : thm
    val w2w : thm
    val w2w_0 : thm
    val w2w_LSL : thm
    val w2w_id : thm
    val w2w_n2w : thm
    val w2w_w2w : thm
    val word_0 : thm
    val word_0_n2w : thm
    val word_1_n2w : thm
    val word_1comp_n2w : thm
    val word_2comp_n2w : thm
    val word_H : thm
    val word_L : thm
    val word_L2 : thm
    val word_L2_MULT : thm
    val word_L_MULT : thm
    val word_L_MULT_NEG : thm
    val word_T : thm
    val word_T_not_zero : thm
    val word_add_n2w : thm
    val word_and_n2w : thm
    val word_asr : thm
    val word_asr_n2w : thm
    val word_bin_list : thm
    val word_bin_string : thm
    val word_bit : thm
    val word_bit_0 : thm
    val word_bit_0_word_T : thm
    val word_bit_n2w : thm
    val word_bits_n2w : thm
    val word_bits_w2w : thm
    val word_concat_0 : thm
    val word_concat_word_T : thm
    val word_dec_list : thm
    val word_dec_string : thm
    val word_div_1 : thm
    val word_eq_n2w : thm
    val word_extract_n2w : thm
    val word_extract_w2w : thm
    val word_ge_n2w : thm
    val word_gt_n2w : thm
    val word_hex_list : thm
    val word_hex_string : thm
    val word_hi_n2w : thm
    val word_hs_n2w : thm
    val word_index_n2w : thm
    val word_join_0 : thm
    val word_join_word_T : thm
    val word_le_n2w : thm
    val word_lo_n2w : thm
    val word_log2_1 : thm
    val word_log2_n2w : thm
    val word_ls_n2w : thm
    val word_lsb : thm
    val word_lsb_n2w : thm
    val word_lsb_word_T : thm
    val word_lsl_n2w : thm
    val word_lsr_n2w : thm
    val word_lt_n2w : thm
    val word_modify_n2w : thm
    val word_msb : thm
    val word_msb_n2w : thm
    val word_msb_n2w_numeric : thm
    val word_msb_word_T : thm
    val word_mul_n2w : thm
    val word_nchotomy : thm
    val word_oct_list : thm
    val word_oct_string : thm
    val word_or_n2w : thm
    val word_reverse_0 : thm
    val word_reverse_n2w : thm
    val word_reverse_word_T : thm
    val word_ror : thm
    val word_ror_n2w : thm
    val word_rrx_0 : thm
    val word_rrx_n2w : thm
    val word_rrx_word_T : thm
    val word_signed_bits_n2w : thm
    val word_slice_n2w : thm
    val word_sub_w2n : thm
    val word_xor_n2w : thm
  
  val words_grammars : type_grammar.grammar * term_grammar.grammar
  
  val words_rwts : simpLib.ssfrag
(*
   [fcp] Parent theory of "words"
   
   [numeral_bit] Parent theory of "words"
   
   [sum_num] Parent theory of "words"
   
   [BIT_SET_curried_def]  Definition
      
      |- !x x1. BIT_SET x x1 = BIT_SET_tupled (x,x1)
   
   [BIT_SET_tupled_primitive_def]  Definition
      
      |- BIT_SET_tupled =
         WFREC
           (@R.
              WF R /\
              (!i n. n <> 0 /\ ODD n ==> R (SUC i,n DIV 2) (i,n)) /\
              !i n. n <> 0 /\ ~ODD n ==> R (SUC i,n DIV 2) (i,n))
           (\BIT_SET_tupled a.
              case a of
                 (i,n) ->
                   I
                     (if n = 0 then
                        {}
                      else
                        if ODD n then
                          i INSERT BIT_SET_tupled (SUC i,n DIV 2)
                        else
                          BIT_SET_tupled (SUC i,n DIV 2)))
   
   [INT_MAX_def]  Definition
      
      |- INT_MAX (:'a) = INT_MIN (:'a) - 1
   
   [INT_MIN_def]  Definition
      
      |- INT_MIN (:'a) = 2 ** (dimindex (:'a) - 1)
   
   [UINT_MAX_def]  Definition
      
      |- UINT_MAX (:'a) = dimword (:'a) - 1
   
   [dimword_def]  Definition
      
      |- dimword (:'a) = 2 ** dimindex (:'a)
   
   [l2w_def]  Definition
      
      |- !b l. l2w b l = n2w (l2n b l)
   
   [n2w_def]  Definition
      
      |- !n. n2w n = FCP i. BIT i n
   
   [n2w_itself_primitive_def]  Definition
      
      |- n2w_itself =
         WFREC (@R. WF R) (\n2w_itself a. case a of (n,(:'a)) -> I (n2w n))
   
   [nzcv_def]  Definition
      
      |- !a b.
           nzcv a b =
           (let q = w2n a + w2n (-b) in
            let r = n2w q in
              (word_msb r,r = 0w,BIT (dimindex (:'a)) q \/ (b = 0w),
               (word_msb a <=/=> word_msb b) /\
               (word_msb r <=/=> word_msb a)))
   
   [s2w_def]  Definition
      
      |- !b f s. s2w b f s = n2w (s2n b f s)
   
   [sw2sw_def]  Definition
      
      |- !w.
           sw2sw w =
           n2w (SIGN_EXTEND (dimindex (:'a)) (dimindex (:'b)) (w2n w))
   
   [w2l_def]  Definition
      
      |- !b w. w2l b w = n2l b (w2n w)
   
   [w2n_def]  Definition
      
      |- !w. w2n w = SUM (dimindex (:'a)) (\i. SBIT (w ' i) i)
   
   [w2s_def]  Definition
      
      |- !b f w. w2s b f w = n2s b f (w2n w)
   
   [w2w_def]  Definition
      
      |- !w. w2w w = n2w (w2n w)
   
   [word_1comp_def]  Definition
      
      |- !w. ~w = FCP i. ~w ' i
   
   [word_2comp_def]  Definition
      
      |- !w. -w = n2w (dimword (:'a) - w2n w)
   
   [word_H_def]  Definition
      
      |- INT_MAXw = n2w (INT_MAX (:'a))
   
   [word_L2_def]  Definition
      
      |- INT_MINw2 = INT_MINw * INT_MINw
   
   [word_L_def]  Definition
      
      |- INT_MINw = n2w (INT_MIN (:'a))
   
   [word_T_def]  Definition
      
      |- UINT_MAXw = n2w (UINT_MAX (:'a))
   
   [word_add_def]  Definition
      
      |- !v w. v + w = n2w (w2n v + w2n w)
   
   [word_and_def]  Definition
      
      |- !v w. v && w = FCP i. v ' i /\ w ' i
   
   [word_asr_def]  Definition
      
      |- !w n.
           w >> n =
           FCP i.
             if dimindex (:'a) <= i + n then word_msb w else w ' (i + n)
   
   [word_bit_def]  Definition
      
      |- !b w. word_bit b w <=> b <= dimindex (:'a) - 1 /\ w ' b
   
   [word_bits_def]  Definition
      
      |- !h l.
           h -- l =
           (\w. FCP i. i + l <= MIN h (dimindex (:'a) - 1) /\ w ' (i + l))
   
   [word_concat_def]  Definition
      
      |- !v w. v @@ w = w2w (word_join v w)
   
   [word_div_def]  Definition
      
      |- !v w. v // w = n2w (w2n v DIV w2n w)
   
   [word_extract_def]  Definition
      
      |- !h l. h >< l = w2w o (h -- l)
   
   [word_from_bin_list_def]  Definition
      
      |- word_from_bin_list = l2w 2
   
   [word_from_bin_string_def]  Definition
      
      |- word_from_bin_string = s2w 2 UNHEX
   
   [word_from_dec_list_def]  Definition
      
      |- word_from_dec_list = l2w 10
   
   [word_from_dec_string_def]  Definition
      
      |- word_from_dec_string = s2w 10 UNHEX
   
   [word_from_hex_list_def]  Definition
      
      |- word_from_hex_list = l2w 16
   
   [word_from_hex_string_def]  Definition
      
      |- word_from_hex_string = s2w 16 UNHEX
   
   [word_from_oct_list_def]  Definition
      
      |- word_from_oct_list = l2w 8
   
   [word_from_oct_string_def]  Definition
      
      |- word_from_oct_string = s2w 8 UNHEX
   
   [word_ge_def]  Definition
      
      |- !a b. a >= b <=> (let (n,z,c,v) = nzcv a b in n <=> v)
   
   [word_gt_def]  Definition
      
      |- !a b. a > b <=> (let (n,z,c,v) = nzcv a b in ~z /\ (n <=> v))
   
   [word_hi_def]  Definition
      
      |- !a b. a >+ b <=> (let (n,z,c,v) = nzcv a b in c /\ ~z)
   
   [word_hs_def]  Definition
      
      |- !a b. a >=+ b <=> (let (n,z,c,v) = nzcv a b in c)
   
   [word_join_def]  Definition
      
      |- !v w.
           word_join v w =
           (let cv = w2w v and cw = w2w w in cv << dimindex (:'b) !! cw)
   
   [word_le_def]  Definition
      
      |- !a b. a <= b <=> (let (n,z,c,v) = nzcv a b in z \/ (n <=/=> v))
   
   [word_len_def]  Definition
      
      |- !w. word_len w = dimindex (:'a)
   
   [word_lo_def]  Definition
      
      |- !a b. a <+ b <=> (let (n,z,c,v) = nzcv a b in ~c)
   
   [word_log2_def]  Definition
      
      |- !w. word_log2 w = n2w (LOG2 (w2n w))
   
   [word_ls_def]  Definition
      
      |- !a b. a <=+ b <=> (let (n,z,c,v) = nzcv a b in ~c \/ z)
   
   [word_lsb_def]  Definition
      
      |- !w. word_lsb w <=> w ' 0
   
   [word_lsl_def]  Definition
      
      |- !w n. w << n = FCP i. i < dimindex (:'a) /\ n <= i /\ w ' (i - n)
   
   [word_lsr_def]  Definition
      
      |- !w n. w >>> n = FCP i. i + n < dimindex (:'a) /\ w ' (i + n)
   
   [word_lt_def]  Definition
      
      |- !a b. a < b <=> (let (n,z,c,v) = nzcv a b in n <=/=> v)
   
   [word_mod_def]  Definition
      
      |- !v w. word_mod v w = n2w (w2n v MOD w2n w)
   
   [word_modify_def]  Definition
      
      |- !f w. word_modify f w = FCP i. f i (w ' i)
   
   [word_msb_def]  Definition
      
      |- !w. word_msb w <=> w ' (dimindex (:'a) - 1)
   
   [word_mul_def]  Definition
      
      |- !v w. v * w = n2w (w2n v * w2n w)
   
   [word_or_def]  Definition
      
      |- !v w. v !! w = FCP i. v ' i \/ w ' i
   
   [word_reverse_def]  Definition
      
      |- !w. word_reverse w = FCP i. w ' (dimindex (:'a) - 1 - i)
   
   [word_rol_def]  Definition
      
      |- !w n. w #<< n = w #>> (dimindex (:'a) - n MOD dimindex (:'a))
   
   [word_ror_def]  Definition
      
      |- !w n. w #>> n = FCP i. w ' ((i + n) MOD dimindex (:'a))
   
   [word_rrx_def]  Definition
      
      |- !c w.
           word_rrx (c,w) =
           (word_lsb w,
            FCP i. if i = dimindex (:'a) - 1 then c else (w >>> 1) ' i)
   
   [word_sdiv_def]  Definition
      
      |- !a b.
           a / b =
           if word_msb a then
             if word_msb b then -a // -b else -(-a // b)
           else
             if word_msb b then -(a // -b) else a // b
   
   [word_signed_bits_def]  Definition
      
      |- !h l.
           h --- l =
           (\w.
              FCP i.
                l <= MIN h (dimindex (:'a) - 1) /\
                w ' (MIN (i + l) (MIN h (dimindex (:'a) - 1))))
   
   [word_slice_def]  Definition
      
      |- !h l.
           h <> l =
           (\w. FCP i. l <= i /\ i <= MIN h (dimindex (:'a) - 1) /\ w ' i)
   
   [word_sub_def]  Definition
      
      |- !v w. v - w = v + -w
   
   [word_to_bin_list_def]  Definition
      
      |- word_to_bin_list = w2l 2
   
   [word_to_bin_string_def]  Definition
      
      |- word_to_bin_string = w2s 2 HEX
   
   [word_to_dec_list_def]  Definition
      
      |- word_to_dec_list = w2l 10
   
   [word_to_dec_string_def]  Definition
      
      |- word_to_dec_string = w2s 10 HEX
   
   [word_to_hex_list_def]  Definition
      
      |- word_to_hex_list = w2l 16
   
   [word_to_hex_string_def]  Definition
      
      |- word_to_hex_string = w2s 16 HEX
   
   [word_to_oct_list_def]  Definition
      
      |- word_to_oct_list = w2l 8
   
   [word_to_oct_string_def]  Definition
      
      |- word_to_oct_string = w2s 8 HEX
   
   [word_xor_def]  Definition
      
      |- !v w. v ?? w = FCP i. v ' i <=/=> w ' i
   
   [ASR_ADD]  Theorem
      
      |- !w m n. w >> m >> n = w >> (m + n)
   
   [ASR_LIMIT]  Theorem
      
      |- !w n.
           dimindex (:'a) <= n ==>
           (w >> n = if word_msb w then UINT_MAXw else 0w)
   
   [ASR_UINT_MAX]  Theorem
      
      |- !w n. UINT_MAXw >> n = UINT_MAXw
   
   [BIT_SET]  Theorem
      
      |- !i n. BIT i n <=> i IN BIT_SET 0 n
   
   [BIT_SET_def]  Theorem
      
      |- !n i.
           BIT_SET i n =
           if n = 0 then
             {}
           else
             if ODD n then
               i INSERT BIT_SET (SUC i) (n DIV 2)
             else
               BIT_SET (SUC i) (n DIV 2)
   
   [BIT_SET_ind]  Theorem
      
      |- !P.
           (!i n.
              (n <> 0 /\ ODD n ==> P (SUC i) (n DIV 2)) /\
              (n <> 0 /\ ~ODD n ==> P (SUC i) (n DIV 2)) ==>
              P i n) ==>
           !v v1. P v v1
   
   [BIT_UPDATE]  Theorem
      
      |- !n x. n :+ x = word_modify (\i b. if i = n then x else b)
   
   [CONCAT_EXTRACT]  Theorem
      
      |- !h m l w.
           (h - m = dimindex (:'b)) /\ (m + 1 - l = dimindex (:'c)) /\
           (h + 1 - l = dimindex (:'d)) /\ dimindex (:'b + 'c) <> 1 ==>
           ((h >< m + 1) w @@ (m >< l) w = (h >< l) w)
   
   [DIMINDEX_GT_0]  Theorem
      
      |- 0 < dimindex (:'a)
   
   [EXISTS_HB]  Theorem
      
      |- ?m. dimindex (:'a) = SUC m
   
   [EXTRACT_ALL_BITS]  Theorem
      
      |- !h w. dimindex (:'a) - 1 <= h ==> ((h >< 0) w = w2w w)
   
   [EXTRACT_CONCAT]  Theorem
      
      |- !v w.
           FINITE UNIV /\ FINITE UNIV /\
           dimindex (:'a) + dimindex (:'b) <= dimindex (:'c) ==>
           ((dimindex (:'b) - 1 >< 0) (v @@ w) = w) /\
           ((dimindex (:'a) + dimindex (:'b) - 1 >< dimindex (:'b))
              (v @@ w) =
            v)
   
   [EXTRACT_JOIN]  Theorem
      
      |- !h m l w.
           l <= m /\ m' <= h /\ (m' = m + 1) /\ (s = m' - l) ==>
           ((h >< m') w << s !! (m >< l) w =
            (MIN h (MIN (dimindex (:'b) + l - 1) (dimindex (:'a) - 1)) ><
             l) w)
   
   [EXTRACT_JOIN_ADD]  Theorem
      
      |- !h m l w.
           l <= m /\ m' <= h /\ (m' = m + 1) /\ (s = m' - l) ==>
           ((h >< m') w << s + (m >< l) w =
            (MIN h (MIN (dimindex (:'b) + l - 1) (dimindex (:'a) - 1)) ><
             l) w)
   
   [EXTRACT_JOIN_ADD_LSL]  Theorem
      
      |- !h m l w.
           l <= m /\ m' <= h /\ (m' = m + 1) /\ (s = m' - l + n) ==>
           ((h >< m') w << s + (m >< l) w << n =
            (MIN h (MIN (dimindex (:'b) + l - 1) (dimindex (:'a) - 1)) ><
             l) w << n)
   
   [EXTRACT_JOIN_LSL]  Theorem
      
      |- !h m l w.
           l <= m /\ m' <= h /\ (m' = m + 1) /\ (s = m' - l + n) ==>
           ((h >< m') w << s !! (m >< l) w << n =
            (MIN h (MIN (dimindex (:'b) + l - 1) (dimindex (:'a) - 1)) ><
             l) w << n)
   
   [INT_MIN_12]  Theorem
      
      |- INT_MIN (:12) = 2048
   
   [INT_MIN_16]  Theorem
      
      |- INT_MIN (:16) = 32768
   
   [INT_MIN_2]  Theorem
      
      |- INT_MIN (:2) = 2
   
   [INT_MIN_20]  Theorem
      
      |- INT_MIN (:20) = 524288
   
   [INT_MIN_24]  Theorem
      
      |- INT_MIN (:24) = 8388608
   
   [INT_MIN_28]  Theorem
      
      |- INT_MIN (:28) = 134217728
   
   [INT_MIN_3]  Theorem
      
      |- INT_MIN (:3) = 4
   
   [INT_MIN_30]  Theorem
      
      |- INT_MIN (:30) = 536870912
   
   [INT_MIN_32]  Theorem
      
      |- INT_MIN (:32) = 2147483648
   
   [INT_MIN_4]  Theorem
      
      |- INT_MIN (:4) = 8
   
   [INT_MIN_5]  Theorem
      
      |- INT_MIN (:5) = 16
   
   [INT_MIN_6]  Theorem
      
      |- INT_MIN (:6) = 32
   
   [INT_MIN_64]  Theorem
      
      |- INT_MIN (:64) = 9223372036854775808
   
   [INT_MIN_7]  Theorem
      
      |- INT_MIN (:7) = 64
   
   [INT_MIN_8]  Theorem
      
      |- INT_MIN (:8) = 128
   
   [INT_MIN_SUM]  Theorem
      
      |- INT_MIN (:'a + 'b) =
         if FINITE UNIV /\ FINITE UNIV then
           dimword (:'a) * INT_MIN (:'b)
         else
           INT_MIN (:'a + 'b)
   
   [LSL_ADD]  Theorem
      
      |- !w m n. w << m << n = w << (m + n)
   
   [LSL_BITWISE]  Theorem
      
      |- (!n v w. w << n && v << n = (w && v) << n) /\
         (!n v w. w << n !! v << n = (w !! v) << n) /\
         !n v w. w << n ?? v << n = (w ?? v) << n
   
   [LSL_LIMIT]  Theorem
      
      |- !w n. dimindex (:'a) <= n ==> (w << n = 0w)
   
   [LSL_ONE]  Theorem
      
      |- !w. w << 1 = w + w
   
   [LSL_UINT_MAX]  Theorem
      
      |- !n. UINT_MAXw << n = n2w (dimword (:'a) - 2 ** n)
   
   [LSR_ADD]  Theorem
      
      |- !w m n. w >>> m >>> n = w >>> (m + n)
   
   [LSR_BITWISE]  Theorem
      
      |- (!n v w. w >>> n && v >>> n = (w && v) >>> n) /\
         (!n v w. w >>> n !! v >>> n = (w !! v) >>> n) /\
         !n v w. w >>> n ?? v >>> n = (w ?? v) >>> n
   
   [LSR_LESS]  Theorem
      
      |- !m y. y <> 0w /\ 0 < m ==> w2n (y >>> m) < w2n y
   
   [LSR_LIMIT]  Theorem
      
      |- !w n. dimindex (:'a) <= n ==> (w >>> n = 0w)
   
   [MOD_2EXP_DIMINDEX]  Theorem
      
      |- !n. n MOD dimword (:'a) = MOD_2EXP (dimindex (:'a)) n
   
   [MOD_COMPLEMENT]  Theorem
      
      |- !n q a.
           0 < n /\ 0 < q /\ a < q * n ==>
           ((q * n - a) MOD n = (n - a MOD n) MOD n)
   
   [MOD_DIMINDEX]  Theorem
      
      |- !n. n MOD dimword (:'a) = BITS (dimindex (:'a) - 1) 0 n
   
   [NOT_INT_MIN_ZERO]  Theorem
      
      |- INT_MINw <> 0w
   
   [ONE_LT_dimword]  Theorem
      
      |- 1 < dimword (:'a)
   
   [ROL_ADD]  Theorem
      
      |- !w m n. w #<< m #<< n = w #<< (m + n)
   
   [ROL_BITWISE]  Theorem
      
      |- (!n v w. w #<< n && v #<< n = (w && v) #<< n) /\
         (!n v w. w #<< n !! v #<< n = (w !! v) #<< n) /\
         !n v w. w #<< n ?? v #<< n = (w ?? v) #<< n
   
   [ROL_MOD]  Theorem
      
      |- !w n. w #<< (n MOD dimindex (:'a)) = w #<< n
   
   [ROR_ADD]  Theorem
      
      |- !w m n. w #>> m #>> n = w #>> (m + n)
   
   [ROR_BITWISE]  Theorem
      
      |- (!n v w. w #>> n && v #>> n = (w && v) #>> n) /\
         (!n v w. w #>> n !! v #>> n = (w !! v) #>> n) /\
         !n v w. w #>> n ?? v #>> n = (w ?? v) #>> n
   
   [ROR_CYCLE]  Theorem
      
      |- !w n. w #>> (n * dimindex (:'a)) = w
   
   [ROR_MOD]  Theorem
      
      |- !w n. w #>> (n MOD dimindex (:'a)) = w #>> n
   
   [ROR_ROL]  Theorem
      
      |- !w n. (w #>> n #<< n = w) /\ (w #<< n #>> n = w)
   
   [ROR_UINT_MAX]  Theorem
      
      |- !n. UINT_MAXw #>> n = UINT_MAXw
   
   [SHIFT_ZERO]  Theorem
      
      |- (!a. a << 0 = a) /\ (!a. a >> 0 = a) /\ (!a. a >>> 0 = a) /\
         (!a. a #<< 0 = a) /\ !a. a #>> 0 = a
   
   [SUC_WORD_PRED]  Theorem
      
      |- !x. x <> 0w ==> (SUC (w2n (x - 1w)) = w2n x)
   
   [TWO_COMP_NEG]  Theorem
      
      |- !a.
           word_msb a ==>
           if (dimindex (:'a) - 1 = 0) \/ (a = INT_MINw) then
             word_msb (-a)
           else
             ~word_msb (-a)
   
   [TWO_COMP_POS]  Theorem
      
      |- ~word_msb a ==> (a = 0w) \/ word_msb (-a)
   
   [TWO_COMP_POS_NEG]  Theorem
      
      |- !a.
           ~((dimindex (:'a) - 1 = 0) \/ (a = 0w) \/ (a = INT_MINw)) ==>
           (~word_msb a <=> word_msb (-a))
   
   [WORD_0_LS]  Theorem
      
      |- !w. 0w <=+ w
   
   [WORD_0_POS]  Theorem
      
      |- ~word_msb 0w
   
   [WORD_2COMP_LSL]  Theorem
      
      |- !n a b. -a << n = -(a << n)
   
   [WORD_ADD_0]  Theorem
      
      |- (!w. w + 0w = w) /\ !w. 0w + w = w
   
   [WORD_ADD_ASSOC]  Theorem
      
      |- !v w x. v + (w + x) = v + w + x
   
   [WORD_ADD_BIT]  Theorem
      
      |- !n a b.
           n < dimindex (:'a) ==>
           ((a + b) ' n <=>
            if n = 0 then
              a ' 0 <=/=> b ' 0
            else
              if ((n - 1 -- 0) a + (n - 1 -- 0) b) ' n then
                a ' n <=> b ' n
              else
                a ' n <=/=> b ' n)
   
   [WORD_ADD_BIT0]  Theorem
      
      |- !a b. (a + b) ' 0 <=> (a ' 0 <=/=> b ' 0)
   
   [WORD_ADD_COMM]  Theorem
      
      |- !v w. v + w = w + v
   
   [WORD_ADD_EQ_SUB]  Theorem
      
      |- !v w x. (v + w = x) <=> (v = x - w)
   
   [WORD_ADD_INV_0_EQ]  Theorem
      
      |- !v w. (v + w = v) <=> (w = 0w)
   
   [WORD_ADD_LEFT_LO]  Theorem
      
      |- !b c a.
           a + b <+ c <=>
           if b <=+ c then
             (let x = n2w (w2n c - w2n b) in
                a <+ x \/ b <> 0w /\ -c + x <=+ a)
           else
             -b <=+ a /\ a <+ -b + c
   
   [WORD_ADD_LEFT_LO2]  Theorem
      
      |- !c a. c + a <+ a <=> a <> 0w /\ (c <> 0w /\ -c <+ a \/ (a = -c))
   
   [WORD_ADD_LEFT_LS]  Theorem
      
      |- !b c a.
           a + b <=+ c <=>
           if b <=+ c then
             (let x = n2w (w2n c - w2n b) in
                a <=+ x \/ b <> 0w /\ -c + x <=+ a)
           else
             -b <=+ a /\ a <=+ -b + c
   
   [WORD_ADD_LEFT_LS2]  Theorem
      
      |- !c a. c + a <=+ a <=> (c = 0w) \/ a <> 0w /\ (-c <+ a \/ (a = -c))
   
   [WORD_ADD_LID_UNIQ]  Theorem
      
      |- !v w. (v + w = w) <=> (v = 0w)
   
   [WORD_ADD_LINV]  Theorem
      
      |- !w. -w + w = 0w
   
   [WORD_ADD_LSL]  Theorem
      
      |- !n a b. (a + b) << n = a << n + b << n
   
   [WORD_ADD_OR]  Theorem
      
      |- !a b. (a && b = 0w) ==> (a + b = a !! b)
   
   [WORD_ADD_RID_UNIQ]  Theorem
      
      |- !v w. (v + w = v) <=> (w = 0w)
   
   [WORD_ADD_RIGHT_LO]  Theorem
      
      |- !c a b.
           a <+ b + c <=>
           if c <=+ a then
             (let x = n2w (w2n a - w2n c) in
                x <+ b /\ ((c = 0w) \/ b <+ -a + x))
           else
             b <+ -c \/ -c + a <+ b
   
   [WORD_ADD_RIGHT_LO2]  Theorem
      
      |- !c a. a <+ c + a <=> c <> 0w /\ ((a = 0w) \/ a <+ -c)
   
   [WORD_ADD_RIGHT_LS]  Theorem
      
      |- !c a b.
           a <=+ b + c <=>
           if c <=+ a then
             (let x = n2w (w2n a - w2n c) in
                x <=+ b /\ ((c = 0w) \/ b <+ -a + x))
           else
             b <+ -c \/ -c + a <=+ b
   
   [WORD_ADD_RIGHT_LS2]  Theorem
      
      |- !c a. a <=+ c + a <=> (a = 0w) \/ (c = 0w) \/ a <+ -c
   
   [WORD_ADD_RINV]  Theorem
      
      |- !w. w + -w = 0w
   
   [WORD_ADD_SUB]  Theorem
      
      |- !v w. v + w - w = v
   
   [WORD_ADD_SUB2]  Theorem
      
      |- !v w. w + v - w = v
   
   [WORD_ADD_SUB3]  Theorem
      
      |- !v x. v - (v + x) = -x
   
   [WORD_ADD_SUB_ASSOC]  Theorem
      
      |- !v w x. v + w - x = v + (w - x)
   
   [WORD_ADD_SUB_SYM]  Theorem
      
      |- !v w x. v + w - x = v - x + w
   
   [WORD_ALL_BITS]  Theorem
      
      |- !w. dimindex (:'a) - 1 <= h ==> ((h -- 0) w = w)
   
   [WORD_AND_ABSORD]  Theorem
      
      |- !a b. a !! a && b = a
   
   [WORD_AND_ASSOC]  Theorem
      
      |- !a b c. (a && b) && c = a && b && c
   
   [WORD_AND_CLAUSES]  Theorem
      
      |- !a.
           (UINT_MAXw && a = a) /\ (a && UINT_MAXw = a) /\
           (0w && a = 0w) /\ (a && 0w = 0w) /\ (a && a = a)
   
   [WORD_AND_COMM]  Theorem
      
      |- !a b. a && b = b && a
   
   [WORD_AND_COMP]  Theorem
      
      |- !a. a && ~a = 0w
   
   [WORD_AND_EXP_SUB1]  Theorem
      
      |- !m n. n2w n && n2w (2 ** m - 1) = n2w (n MOD 2 ** m)
   
   [WORD_AND_IDEM]  Theorem
      
      |- !a. a && a = a
   
   [WORD_BITS_COMP_THM]  Theorem
      
      |- !h1 l1 h2 l2 w.
           (h2 -- l2) ((h1 -- l1) w) = (MIN h1 (h2 + l1) -- l2 + l1) w
   
   [WORD_BITS_EXTRACT]  Theorem
      
      |- !h l w. (h -- l) w = (h >< l) w
   
   [WORD_BITS_LSL]  Theorem
      
      |- !h l n w.
           h < dimindex (:'a) ==>
           ((h -- l) (w << n) =
            if n <= h then (h - n -- l - n) w << (n - l) else 0w)
   
   [WORD_BITS_LSR]  Theorem
      
      |- !h l w. (h -- l) w >>> n = (h -- l + n) w
   
   [WORD_BITS_LT]  Theorem
      
      |- !h l w. w2n ((h -- l) w) < 2 ** (SUC h - l)
   
   [WORD_BITS_MIN_HIGH]  Theorem
      
      |- !w.
           dimindex (:'a) - 1 < h ==>
           ((h -- l) w = (dimindex (:'a) - 1 -- l) w)
   
   [WORD_BITS_OVER_BITWISE]  Theorem
      
      |- (!h l v w. (h -- l) v && (h -- l) w = (h -- l) (v && w)) /\
         (!h l v w. (h -- l) v !! (h -- l) w = (h -- l) (v !! w)) /\
         !h l v w. (h -- l) v ?? (h -- l) w = (h -- l) (v ?? w)
   
   [WORD_BITS_SLICE_THM]  Theorem
      
      |- !h l w. (h -- l) ((h <> l) w) = (h -- l) w
   
   [WORD_BITS_ZERO]  Theorem
      
      |- !h l w. h < l ==> ((h -- l) w = 0w)
   
   [WORD_BITS_ZERO2]  Theorem
      
      |- !h l. (h -- l) 0w = 0w
   
   [WORD_BITS_ZERO3]  Theorem
      
      |- !h l w. dimindex (:'a) <= l ==> ((h -- l) w = 0w)
   
   [WORD_BIT_BITS]  Theorem
      
      |- !b w. word_bit b w <=> ((b -- b) w = 1w)
   
   [WORD_DE_MORGAN_THM]  Theorem
      
      |- !a b. (~(a && b) = ~a !! ~b) /\ (~(a !! b) = ~a && ~b)
   
   [WORD_DIVISION]  Theorem
      
      |- !w.
           w <> 0w ==>
           !v. (v = v // w * w + word_mod v w) /\ word_mod v w <+ w
   
   [WORD_EQ]  Theorem
      
      |- !v w.
           (!x. x < dimindex (:'a) ==> (word_bit x v <=> word_bit x w)) <=>
           (v = w)
   
   [WORD_EQ_ADD_LCANCEL]  Theorem
      
      |- !v w x. (v + w = v + x) <=> (w = x)
   
   [WORD_EQ_ADD_RCANCEL]  Theorem
      
      |- !v w x. (v + w = x + w) <=> (v = x)
   
   [WORD_EQ_NEG]  Theorem
      
      |- !v w. (-v = -w) <=> (v = w)
   
   [WORD_EQ_SUB_LADD]  Theorem
      
      |- !v w x. (v = w - x) <=> (v + x = w)
   
   [WORD_EQ_SUB_RADD]  Theorem
      
      |- !v w x. (v - w = x) <=> (v = x + w)
   
   [WORD_EQ_SUB_ZERO]  Theorem
      
      |- !w v. (v - w = 0w) <=> (v = w)
   
   [WORD_EXTRACT_BITS_COMP]  Theorem
      
      |- (j >< k) ((h -- l) n) = (MIN h (j + l) >< k + l) n
   
   [WORD_EXTRACT_COMP_THM]  Theorem
      
      |- !w.
           (h >< l) ((m >< n) w) =
           (MIN m
              (MIN (h + n)
                 (MIN (dimindex (:'c) - 1) (dimindex (:'b) + n - 1))) ><
            l + n) w
   
   [WORD_EXTRACT_LSL]  Theorem
      
      |- !h l n w.
           h < dimindex (:'a) ==>
           ((h >< l) (w << n) =
            if n <= h then (h - n >< l - n) w << (n - l) else 0w)
   
   [WORD_EXTRACT_MIN_HIGH]  Theorem
      
      |- (!h l w.
            dimindex (:'a) <= dimindex (:'b) + l /\ dimindex (:'a) <= h ==>
            ((h >< l) w = (dimindex (:'a) - 1 >< l) w)) /\
         !h l w.
           dimindex (:'b) + l < dimindex (:'a) /\
           dimindex (:'b) + l <= h ==>
           ((h >< l) w = (dimindex (:'b) + l - 1 >< l) w)
   
   [WORD_EXTRACT_OVER_ADD]  Theorem
      
      |- !a b.
           dimindex (:'b) - 1 <= h /\ dimindex (:'b) <= dimindex (:'a) ==>
           ((h >< 0) (a + b) = (h >< 0) a + (h >< 0) b)
   
   [WORD_EXTRACT_OVER_BITWISE]  Theorem
      
      |- (!h l v w. (h >< l) v && (h >< l) w = (h >< l) (v && w)) /\
         (!h l v w. (h >< l) v !! (h >< l) w = (h >< l) (v !! w)) /\
         !h l v w. (h >< l) v ?? (h >< l) w = (h >< l) (v ?? w)
   
   [WORD_EXTRACT_ZERO]  Theorem
      
      |- !h l w. h < l ==> ((h >< l) w = 0w)
   
   [WORD_EXTRACT_ZERO2]  Theorem
      
      |- !h l. (h >< l) 0w = 0w
   
   [WORD_EXTRACT_ZERO3]  Theorem
      
      |- !h l w. dimindex (:'a) <= l ==> ((h >< l) w = 0w)
   
   [WORD_GE]  Theorem
      
      |- !a b.
           a >= b <=>
           (word_msb b <=> word_msb a) /\ w2n a >= w2n b \/
           word_msb b /\ ~word_msb a
   
   [WORD_GREATER]  Theorem
      
      |- !a b. a > b <=> b < a
   
   [WORD_GREATER_EQ]  Theorem
      
      |- !a b. a >= b <=> b <= a
   
   [WORD_GREATER_OR_EQ]  Theorem
      
      |- !a b. a >= b <=> a > b \/ (a = b)
   
   [WORD_GT]  Theorem
      
      |- !a b.
           a > b <=>
           (word_msb b <=> word_msb a) /\ w2n a > w2n b \/
           word_msb b /\ ~word_msb a
   
   [WORD_HI]  Theorem
      
      |- !a b. a >+ b <=> w2n a > w2n b
   
   [WORD_HIGHER]  Theorem
      
      |- !a b. a >+ b <=> b <+ a
   
   [WORD_HIGHER_EQ]  Theorem
      
      |- !a b. a >=+ b <=> b <=+ a
   
   [WORD_HIGHER_OR_EQ]  Theorem
      
      |- !a b. a >=+ b <=> a >+ b \/ (a = b)
   
   [WORD_HS]  Theorem
      
      |- !a b. a >=+ b <=> w2n a >= w2n b
   
   [WORD_H_POS]  Theorem
      
      |- ~word_msb INT_MAXw
   
   [WORD_H_WORD_L]  Theorem
      
      |- INT_MAXw = INT_MINw - 1w
   
   [WORD_INDUCT]  Theorem
      
      |- !P.
           P 0w /\
           (!n.
              SUC n < dimword (:'a) ==> P (n2w n) ==> P (n2w (SUC n))) ==>
           !x. P x
   
   [WORD_LCANCEL_SUB]  Theorem
      
      |- !v w x. (v - w = x - w) <=> (v = x)
   
   [WORD_LE]  Theorem
      
      |- !a b.
           a <= b <=>
           (word_msb a <=> word_msb b) /\ w2n a <= w2n b \/
           word_msb a /\ ~word_msb b
   
   [WORD_LEFT_ADD_DISTRIB]  Theorem
      
      |- !v w x. v * (w + x) = v * w + v * x
   
   [WORD_LEFT_AND_OVER_OR]  Theorem
      
      |- !a b c. a && (b !! c) = a && b !! a && c
   
   [WORD_LEFT_AND_OVER_XOR]  Theorem
      
      |- !a b c. a && (b ?? c) = a && b ?? a && c
   
   [WORD_LEFT_OR_OVER_AND]  Theorem
      
      |- !a b c. a !! b && c = (a !! b) && (a !! c)
   
   [WORD_LEFT_SUB_DISTRIB]  Theorem
      
      |- !v w x. v * (w - x) = v * w - v * x
   
   [WORD_LESS_0_word_T]  Theorem
      
      |- ~(0w < -1w) /\ ~(0w <= -1w) /\ -1w < 0w /\ -1w <= 0w
   
   [WORD_LESS_ANTISYM]  Theorem
      
      |- !a b. ~(a < b /\ b < a)
   
   [WORD_LESS_CASES]  Theorem
      
      |- !a b. a < b \/ b <= a
   
   [WORD_LESS_CASES_IMP]  Theorem
      
      |- !a b. ~(a < b) /\ a <> b ==> b < a
   
   [WORD_LESS_EQUAL_ANTISYM]  Theorem
      
      |- !a b. a <= b /\ b <= a ==> (a = b)
   
   [WORD_LESS_EQ_ANTISYM]  Theorem
      
      |- !a b. ~(a < b /\ b <= a)
   
   [WORD_LESS_EQ_CASES]  Theorem
      
      |- !a b. a <= b \/ b <= a
   
   [WORD_LESS_EQ_H]  Theorem
      
      |- !a. a <= INT_MAXw
   
   [WORD_LESS_EQ_LESS_TRANS]  Theorem
      
      |- !a b c. a <= b /\ b < c ==> a < c
   
   [WORD_LESS_EQ_REFL]  Theorem
      
      |- !a. a <= a
   
   [WORD_LESS_EQ_TRANS]  Theorem
      
      |- !a b c. a <= b /\ b <= c ==> a <= c
   
   [WORD_LESS_IMP_LESS_OR_EQ]  Theorem
      
      |- !a b. a < b ==> a <= b
   
   [WORD_LESS_LESS_CASES]  Theorem
      
      |- !a b. (a = b) \/ a < b \/ b < a
   
   [WORD_LESS_LESS_EQ_TRANS]  Theorem
      
      |- !a b c. a < b /\ b <= c ==> a < c
   
   [WORD_LESS_NEG_LEFT]  Theorem
      
      |- !a b. -a <+ b <=> b <> 0w /\ ((a = 0w) \/ -b <+ a)
   
   [WORD_LESS_NEG_RIGHT]  Theorem
      
      |- !a b. a <+ -b <=> b <> 0w /\ ((a = 0w) \/ b <+ -a)
   
   [WORD_LESS_NOT_EQ]  Theorem
      
      |- !a b. a < b ==> a <> b
   
   [WORD_LESS_OR_EQ]  Theorem
      
      |- !a b. a <= b <=> a < b \/ (a = b)
   
   [WORD_LESS_REFL]  Theorem
      
      |- !a. ~(a < a)
   
   [WORD_LESS_TRANS]  Theorem
      
      |- !a b c. a < b /\ b < c ==> a < c
   
   [WORD_LE_EQ_LS]  Theorem
      
      |- !x y. 0w <= x /\ 0w <= y ==> (x <= y <=> x <=+ y)
   
   [WORD_LE_LS]  Theorem
      
      |- !a b.
           a <= b <=>
           INT_MINw <=+ a /\ (b <+ INT_MINw \/ a <=+ b) \/
           a <+ INT_MINw /\ b <+ INT_MINw /\ a <=+ b
   
   [WORD_LITERAL_ADD]  Theorem
      
      |- (!m n. -n2w m + -n2w n = -n2w (m + n)) /\
         !m n.
           n2w m + -n2w n = if n <= m then n2w (m - n) else -n2w (n - m)
   
   [WORD_LITERAL_AND]  Theorem
      
      |- (!n m.
            n2w n && n2w m =
            n2w (BITWISE (SUC (MIN (LOG2 n) (LOG2 m))) $/\ n m)) /\
         (!n m.
            n2w n && ~n2w m =
            n2w (BITWISE (SUC (LOG2 n)) (\a b. a /\ ~b) n m)) /\
         (!n m.
            ~n2w m && n2w n =
            n2w (BITWISE (SUC (LOG2 n)) (\a b. a /\ ~b) n m)) /\
         !n m.
           ~n2w n && ~n2w m =
           ~n2w (BITWISE (SUC (MAX (LOG2 n) (LOG2 m))) $\/ n m)
   
   [WORD_LITERAL_MULT]  Theorem
      
      |- (!m n. n2w m * -n2w n = -n2w (m * n)) /\
         !m n. -n2w m * -n2w n = n2w (m * n)
   
   [WORD_LITERAL_OR]  Theorem
      
      |- (!n m.
            n2w n !! n2w m =
            n2w (BITWISE (SUC (MAX (LOG2 n) (LOG2 m))) $\/ n m)) /\
         (!n m.
            n2w n !! ~n2w m =
            ~n2w (BITWISE (SUC (LOG2 m)) (\a b. a /\ ~b) m n)) /\
         (!n m.
            ~n2w m !! n2w n =
            ~n2w (BITWISE (SUC (LOG2 m)) (\a b. a /\ ~b) m n)) /\
         !n m.
           ~n2w n !! ~n2w m =
           ~n2w (BITWISE (SUC (MIN (LOG2 n) (LOG2 m))) $/\ n m)
   
   [WORD_LITERAL_XOR]  Theorem
      
      |- !n m.
           n2w n ?? n2w m =
           n2w
             (BITWISE (SUC (MAX (LOG2 n) (LOG2 m))) (\x y. x <=/=> y) n m)
   
   [WORD_LO]  Theorem
      
      |- !a b. a <+ b <=> w2n a < w2n b
   
   [WORD_LOWER_ANTISYM]  Theorem
      
      |- !a b. ~(a <+ b /\ b <+ a)
   
   [WORD_LOWER_CASES]  Theorem
      
      |- !a b. a <+ b \/ b <=+ a
   
   [WORD_LOWER_CASES_IMP]  Theorem
      
      |- !a b. ~(a <+ b) /\ a <> b ==> b <+ a
   
   [WORD_LOWER_EQUAL_ANTISYM]  Theorem
      
      |- !a b. a <=+ b /\ b <=+ a ==> (a = b)
   
   [WORD_LOWER_EQ_ANTISYM]  Theorem
      
      |- !a b. ~(a <+ b /\ b <=+ a)
   
   [WORD_LOWER_EQ_CASES]  Theorem
      
      |- !a b. a <=+ b \/ b <=+ a
   
   [WORD_LOWER_EQ_LOWER_TRANS]  Theorem
      
      |- !a b c. a <=+ b /\ b <+ c ==> a <+ c
   
   [WORD_LOWER_EQ_REFL]  Theorem
      
      |- !a. a <=+ a
   
   [WORD_LOWER_EQ_TRANS]  Theorem
      
      |- !a b c. a <=+ b /\ b <=+ c ==> a <=+ c
   
   [WORD_LOWER_IMP_LOWER_OR_EQ]  Theorem
      
      |- !a b. a <+ b ==> a <=+ b
   
   [WORD_LOWER_LOWER_CASES]  Theorem
      
      |- !a b. (a = b) \/ a <+ b \/ b <+ a
   
   [WORD_LOWER_LOWER_EQ_TRANS]  Theorem
      
      |- !a b c. a <+ b /\ b <=+ c ==> a <+ c
   
   [WORD_LOWER_NOT_EQ]  Theorem
      
      |- !a b. a <+ b ==> a <> b
   
   [WORD_LOWER_OR_EQ]  Theorem
      
      |- !a b. a <=+ b <=> a <+ b \/ (a = b)
   
   [WORD_LOWER_REFL]  Theorem
      
      |- !a. ~(a <+ a)
   
   [WORD_LOWER_TRANS]  Theorem
      
      |- !a b c. a <+ b /\ b <+ c ==> a <+ c
   
   [WORD_LO_word_0]  Theorem
      
      |- (!n. 0w <+ n <=> n <> 0w) /\ !n. ~(n <+ 0w)
   
   [WORD_LO_word_T]  Theorem
      
      |- (!n. ~(-1w <+ n)) /\ !n. n <+ -1w <=> n <> -1w
   
   [WORD_LS]  Theorem
      
      |- !a b. a <=+ b <=> w2n a <= w2n b
   
   [WORD_LS_T]  Theorem
      
      |- !w. w <=+ UINT_MAXw
   
   [WORD_LS_word_0]  Theorem
      
      |- !n. n <=+ 0w <=> (n = 0w)
   
   [WORD_LS_word_T]  Theorem
      
      |- (!n. -1w <=+ n <=> (n = -1w)) /\ !n. n <=+ -1w
   
   [WORD_LT]  Theorem
      
      |- !a b.
           a < b <=>
           (word_msb a <=> word_msb b) /\ w2n a < w2n b \/
           word_msb a /\ ~word_msb b
   
   [WORD_LT_EQ_LO]  Theorem
      
      |- !x y. 0w <= x /\ 0w <= y ==> (x < y <=> x <+ y)
   
   [WORD_LT_LO]  Theorem
      
      |- !a b.
           a < b <=>
           INT_MINw <=+ a /\ (b <+ INT_MINw \/ a <+ b) \/
           a <+ INT_MINw /\ b <+ INT_MINw /\ a <+ b
   
   [WORD_LT_SUB_UPPER]  Theorem
      
      |- !x y. 0w < y /\ y < x ==> x - y < x
   
   [WORD_L_LESS_EQ]  Theorem
      
      |- !a. INT_MINw <= a
   
   [WORD_L_LESS_H]  Theorem
      
      |- INT_MINw < INT_MAXw
   
   [WORD_L_NEG]  Theorem
      
      |- word_msb INT_MINw
   
   [WORD_L_PLUS_H]  Theorem
      
      |- INT_MINw + INT_MAXw = UINT_MAXw
   
   [WORD_MSB_1COMP]  Theorem
      
      |- !w. word_msb (~w) <=> ~word_msb w
   
   [WORD_MSB_INT_MIN_LS]  Theorem
      
      |- !a. word_msb a <=> INT_MINw <=+ a
   
   [WORD_MULT_ASSOC]  Theorem
      
      |- !v w x. v * (w * x) = v * w * x
   
   [WORD_MULT_CLAUSES]  Theorem
      
      |- !v w.
           (0w * v = 0w) /\ (v * 0w = 0w) /\ (1w * v = v) /\
           (v * 1w = v) /\ ((v + 1w) * w = v * w + w) /\
           (v * (w + 1w) = v + v * w)
   
   [WORD_MULT_COMM]  Theorem
      
      |- !v w. v * w = w * v
   
   [WORD_MULT_SUC]  Theorem
      
      |- !v n. v * n2w (n + 1) = v * n2w n + v
   
   [WORD_MUL_LSL]  Theorem
      
      |- !a n. a << n = n2w (2 ** n) * a
   
   [WORD_NEG]  Theorem
      
      |- !w. -w = ~w + 1w
   
   [WORD_NEG_0]  Theorem
      
      |- -0w = 0w
   
   [WORD_NEG_1]  Theorem
      
      |- -1w = UINT_MAXw
   
   [WORD_NEG_ADD]  Theorem
      
      |- !v w. -(v + w) = -v + -w
   
   [WORD_NEG_EQ]  Theorem
      
      |- (-v = w) <=> (v = -w)
   
   [WORD_NEG_EQ_0]  Theorem
      
      |- (-v = 0w) <=> (v = 0w)
   
   [WORD_NEG_L]  Theorem
      
      |- -INT_MINw = INT_MINw
   
   [WORD_NEG_LMUL]  Theorem
      
      |- !v w. -(v * w) = -v * w
   
   [WORD_NEG_MUL]  Theorem
      
      |- !w. -w = -1w * w
   
   [WORD_NEG_NEG]  Theorem
      
      |- !w. - -w = w
   
   [WORD_NEG_RMUL]  Theorem
      
      |- !v w. -(v * w) = v * -w
   
   [WORD_NEG_SUB]  Theorem
      
      |- -(v - w) = w - v
   
   [WORD_NEG_T]  Theorem
      
      |- -UINT_MAXw = 1w
   
   [WORD_NOT]  Theorem
      
      |- !w. ~w = -w - 1w
   
   [WORD_NOT_0]  Theorem
      
      |- ~0w = UINT_MAXw
   
   [WORD_NOT_GREATER]  Theorem
      
      |- !a b. ~(a > b) <=> a <= b
   
   [WORD_NOT_HIGHER]  Theorem
      
      |- !a b. ~(a >+ b) <=> a <=+ b
   
   [WORD_NOT_LESS]  Theorem
      
      |- !a b. ~(a < b) <=> b <= a
   
   [WORD_NOT_LESS_EQ]  Theorem
      
      |- !a b. (a = b) ==> ~(a < b)
   
   [WORD_NOT_LESS_EQUAL]  Theorem
      
      |- !a b. ~(a <= b) <=> b < a
   
   [WORD_NOT_LOWER]  Theorem
      
      |- !a b. ~(a <+ b) <=> b <=+ a
   
   [WORD_NOT_LOWER_EQ]  Theorem
      
      |- !a b. (a = b) ==> ~(a <+ b)
   
   [WORD_NOT_LOWER_EQUAL]  Theorem
      
      |- !a b. ~(a <=+ b) <=> b <+ a
   
   [WORD_NOT_NOT]  Theorem
      
      |- !a. ~~a = a
   
   [WORD_NOT_T]  Theorem
      
      |- ~UINT_MAXw = 0w
   
   [WORD_NOT_XOR]  Theorem
      
      |- !a b.
           (~a ?? ~b = a ?? b) /\ (a ?? ~b = ~(a ?? b)) /\
           (~a ?? b = ~(a ?? b))
   
   [WORD_OR_ABSORB]  Theorem
      
      |- !a b. a && (a !! b) = a
   
   [WORD_OR_ASSOC]  Theorem
      
      |- !a b c. (a !! b) !! c = a !! b !! c
   
   [WORD_OR_CLAUSES]  Theorem
      
      |- !a.
           (UINT_MAXw !! a = UINT_MAXw) /\ (a !! UINT_MAXw = UINT_MAXw) /\
           (0w !! a = a) /\ (a !! 0w = a) /\ (a !! a = a)
   
   [WORD_OR_COMM]  Theorem
      
      |- !a b. a !! b = b !! a
   
   [WORD_OR_COMP]  Theorem
      
      |- !a. a !! ~a = UINT_MAXw
   
   [WORD_OR_IDEM]  Theorem
      
      |- !a. a !! a = a
   
   [WORD_PRED_THM]  Theorem
      
      |- !m. m <> 0w ==> w2n (m - 1w) < w2n m
   
   [WORD_RCANCEL_SUB]  Theorem
      
      |- !v w x. (v - w = v - x) <=> (w = x)
   
   [WORD_RIGHT_ADD_DISTRIB]  Theorem
      
      |- !v w x. (v + w) * x = v * x + w * x
   
   [WORD_RIGHT_AND_OVER_OR]  Theorem
      
      |- !a b c. (a !! b) && c = a && c !! b && c
   
   [WORD_RIGHT_AND_OVER_XOR]  Theorem
      
      |- !a b c. (a ?? b) && c = a && c ?? b && c
   
   [WORD_RIGHT_OR_OVER_AND]  Theorem
      
      |- !a b c. a && b !! c = (a !! c) && (b !! c)
   
   [WORD_RIGHT_SUB_DISTRIB]  Theorem
      
      |- !v w x. (w - x) * v = w * v - x * v
   
   [WORD_SLICE_BITS_THM]  Theorem
      
      |- !h w. (h <> 0) w = (h -- 0) w
   
   [WORD_SLICE_COMP_THM]  Theorem
      
      |- !h m' m l w.
           l <= m /\ (m' = m + 1) /\ m < h ==>
           ((h <> m') w !! (m <> l) w = (h <> l) w)
   
   [WORD_SLICE_OVER_BITWISE]  Theorem
      
      |- (!h l v w. (h <> l) v && (h <> l) w = (h <> l) (v && w)) /\
         (!h l v w. (h <> l) v !! (h <> l) w = (h <> l) (v !! w)) /\
         !h l v w. (h <> l) v ?? (h <> l) w = (h <> l) (v ?? w)
   
   [WORD_SLICE_THM]  Theorem
      
      |- !h l w. (h <> l) w = (h -- l) w << l
   
   [WORD_SLICE_ZERO]  Theorem
      
      |- !h l w. h < l ==> ((h <> l) w = 0w)
   
   [WORD_SLICE_ZERO2]  Theorem
      
      |- (h <> l) 0w = 0w
   
   [WORD_SUB]  Theorem
      
      |- !v w. -w + v = v - w
   
   [WORD_SUB_ADD]  Theorem
      
      |- !v w. v - w + w = v
   
   [WORD_SUB_ADD2]  Theorem
      
      |- !v w. v + (w - v) = w
   
   [WORD_SUB_LE]  Theorem
      
      |- !x y. 0w <= y /\ y <= x ==> 0w <= x - y /\ x - y <= x
   
   [WORD_SUB_LNEG]  Theorem
      
      |- !v w. -v - w = -(v + w)
   
   [WORD_SUB_LT]  Theorem
      
      |- !x y. 0w < y /\ y < x ==> 0w < x - y /\ x - y < x
   
   [WORD_SUB_LZERO]  Theorem
      
      |- !w. 0w - w = -w
   
   [WORD_SUB_NEG]  Theorem
      
      |- !v w. -v - -w = w - v
   
   [WORD_SUB_PLUS]  Theorem
      
      |- !v w x. v - (w + x) = v - w - x
   
   [WORD_SUB_REFL]  Theorem
      
      |- !w. w - w = 0w
   
   [WORD_SUB_RNEG]  Theorem
      
      |- !v w. v - -w = v + w
   
   [WORD_SUB_RZERO]  Theorem
      
      |- !w. w - 0w = w
   
   [WORD_SUB_SUB]  Theorem
      
      |- !v w x. v - (w - x) = v + x - w
   
   [WORD_SUB_SUB2]  Theorem
      
      |- !v w. v - (v - w) = w
   
   [WORD_SUB_SUB3]  Theorem
      
      |- v - w - v = -w
   
   [WORD_SUB_TRIANGLE]  Theorem
      
      |- !v w x. v - w + (w - x) = v - x
   
   [WORD_XOR]  Theorem
      
      |- !a b. a ?? b = a && ~b !! b && ~a
   
   [WORD_XOR_ASSOC]  Theorem
      
      |- !a b c. (a ?? b) ?? c = a ?? b ?? c
   
   [WORD_XOR_CLAUSES]  Theorem
      
      |- !a.
           (UINT_MAXw ?? a = ~a) /\ (a ?? UINT_MAXw = ~a) /\
           (0w ?? a = a) /\ (a ?? 0w = a) /\ (a ?? a = 0w)
   
   [WORD_XOR_COMM]  Theorem
      
      |- !a b. a ?? b = b ?? a
   
   [WORD_XOR_COMP]  Theorem
      
      |- !a. a ?? ~a = UINT_MAXw
   
   [WORD_ZERO_LE]  Theorem
      
      |- !w. 0w <= w <=> w2n w < INT_MIN (:'a)
   
   [WORD_w2w_EXTRACT]  Theorem
      
      |- !w. w2w w = (dimindex (:'a) - 1 >< 0) w
   
   [WORD_w2w_OVER_ADD]  Theorem
      
      |- !a b. w2w (a + b) = (dimindex (:'a) - 1 -- 0) (w2w a + w2w b)
   
   [WORD_w2w_OVER_BITWISE]  Theorem
      
      |- (!v w. w2w v && w2w w = w2w (v && w)) /\
         (!v w. w2w v !! w2w w = w2w (v !! w)) /\
         !v w. w2w v ?? w2w w = w2w (v ?? w)
   
   [WORD_w2w_OVER_MUL]  Theorem
      
      |- !a b. w2w (a * b) = (dimindex (:'a) - 1 -- 0) (w2w a * w2w b)
   
   [ZERO_LO_INT_MIN]  Theorem
      
      |- 0w <+ INT_MINw
   
   [ZERO_LT_dimword]  Theorem
      
      |- 0 < dimword (:'a)
   
   [ZERO_SHIFT]  Theorem
      
      |- (!n. 0w << n = 0w) /\ (!n. 0w >> n = 0w) /\ (!n. 0w >>> n = 0w) /\
         (!n. 0w #<< n = 0w) /\ !n. 0w #>> n = 0w
   
   [dimindex_12]  Theorem
      
      |- dimindex (:12) = 12
   
   [dimindex_16]  Theorem
      
      |- dimindex (:16) = 16
   
   [dimindex_2]  Theorem
      
      |- dimindex (:2) = 2
   
   [dimindex_20]  Theorem
      
      |- dimindex (:20) = 20
   
   [dimindex_24]  Theorem
      
      |- dimindex (:24) = 24
   
   [dimindex_28]  Theorem
      
      |- dimindex (:28) = 28
   
   [dimindex_3]  Theorem
      
      |- dimindex (:3) = 3
   
   [dimindex_30]  Theorem
      
      |- dimindex (:30) = 30
   
   [dimindex_32]  Theorem
      
      |- dimindex (:32) = 32
   
   [dimindex_4]  Theorem
      
      |- dimindex (:4) = 4
   
   [dimindex_5]  Theorem
      
      |- dimindex (:5) = 5
   
   [dimindex_6]  Theorem
      
      |- dimindex (:6) = 6
   
   [dimindex_64]  Theorem
      
      |- dimindex (:64) = 64
   
   [dimindex_7]  Theorem
      
      |- dimindex (:7) = 7
   
   [dimindex_8]  Theorem
      
      |- dimindex (:8) = 8
   
   [dimword_12]  Theorem
      
      |- dimword (:12) = 4096
   
   [dimword_16]  Theorem
      
      |- dimword (:16) = 65536
   
   [dimword_2]  Theorem
      
      |- dimword (:2) = 4
   
   [dimword_20]  Theorem
      
      |- dimword (:20) = 1048576
   
   [dimword_24]  Theorem
      
      |- dimword (:24) = 16777216
   
   [dimword_28]  Theorem
      
      |- dimword (:28) = 268435456
   
   [dimword_3]  Theorem
      
      |- dimword (:3) = 8
   
   [dimword_30]  Theorem
      
      |- dimword (:30) = 1073741824
   
   [dimword_32]  Theorem
      
      |- dimword (:32) = 4294967296
   
   [dimword_4]  Theorem
      
      |- dimword (:4) = 16
   
   [dimword_5]  Theorem
      
      |- dimword (:5) = 32
   
   [dimword_6]  Theorem
      
      |- dimword (:6) = 64
   
   [dimword_64]  Theorem
      
      |- dimword (:64) = 18446744073709551616
   
   [dimword_7]  Theorem
      
      |- dimword (:7) = 128
   
   [dimword_8]  Theorem
      
      |- dimword (:8) = 256
   
   [dimword_IS_TWICE_INT_MIN]  Theorem
      
      |- dimword (:'a) = 2 * INT_MIN (:'a)
   
   [fcp_n2w]  Theorem
      
      |- !f. $FCP f = word_modify (\i b. f i) 0w
   
   [finite_12]  Theorem
      
      |- FINITE UNIV
   
   [finite_16]  Theorem
      
      |- FINITE UNIV
   
   [finite_2]  Theorem
      
      |- FINITE UNIV
   
   [finite_20]  Theorem
      
      |- FINITE UNIV
   
   [finite_24]  Theorem
      
      |- FINITE UNIV
   
   [finite_28]  Theorem
      
      |- FINITE UNIV
   
   [finite_3]  Theorem
      
      |- FINITE UNIV
   
   [finite_30]  Theorem
      
      |- FINITE UNIV
   
   [finite_32]  Theorem
      
      |- FINITE UNIV
   
   [finite_4]  Theorem
      
      |- FINITE UNIV
   
   [finite_5]  Theorem
      
      |- FINITE UNIV
   
   [finite_6]  Theorem
      
      |- FINITE UNIV
   
   [finite_64]  Theorem
      
      |- FINITE UNIV
   
   [finite_7]  Theorem
      
      |- FINITE UNIV
   
   [finite_8]  Theorem
      
      |- FINITE UNIV
   
   [l2n_n2l]  Theorem
      
      |- !b w. 1 < b ==> (l2w b (w2l b w) = w)
   
   [lsr_1_word_T]  Theorem
      
      |- -1w >>> 1 = INT_MAXw
   
   [n2w_11]  Theorem
      
      |- !m n.
           (n2w m = n2w n) <=> (m MOD dimword (:'a) = n MOD dimword (:'a))
   
   [n2w_SUC]  Theorem
      
      |- !n. n2w (SUC n) = n2w n + 1w
   
   [n2w_itself_def]  Theorem
      
      |- n2w_itself (n,(:'a)) = n2w n
   
   [n2w_itself_ind]  Theorem
      
      |- !P. (!n. P (n,(:'a))) ==> !v v1. P (v,v1)
   
   [n2w_mod]  Theorem
      
      |- !n. n2w (n MOD dimword (:'a)) = n2w n
   
   [n2w_w2n]  Theorem
      
      |- !w. n2w (w2n w) = w
   
   [ranged_word_nchotomy]  Theorem
      
      |- !w. ?n. (w = n2w n) /\ n < dimword (:'a)
   
   [s2w_w2s]  Theorem
      
      |- !c2n n2c b w.
           1 < b /\ (!x. x < b ==> (c2n (n2c x) = x)) ==>
           (s2w b c2n (w2s b n2c w) = w)
   
   [sw2sw]  Theorem
      
      |- !w i.
           i < dimindex (:'b) ==>
           (sw2sw w ' i <=>
            if i < dimindex (:'a) \/ dimindex (:'b) < dimindex (:'a) then
              w ' i
            else
              word_msb w)
   
   [sw2sw_0]  Theorem
      
      |- sw2sw 0w = 0w
   
   [sw2sw_id]  Theorem
      
      |- !w. sw2sw w = w
   
   [sw2sw_sw2sw]  Theorem
      
      |- !w.
           sw2sw (sw2sw w) =
           if
             dimindex (:'b) < dimindex (:'a) /\
             dimindex (:'b) < dimindex (:'c)
           then
             sw2sw (w2w w)
           else
             sw2sw w
   
   [sw2sw_w2w]  Theorem
      
      |- !w.
           sw2sw w =
           (if word_msb w then -1w << dimindex (:'a) else 0w) !! w2w w
   
   [sw2sw_word_T]  Theorem
      
      |- sw2sw (-1w) = -1w
   
   [w2l_l2w]  Theorem
      
      |- !b l. w2l b (l2w b l) = n2l b (l2n b l MOD dimword (:'a))
   
   [w2n_11]  Theorem
      
      |- !v w. (w2n v = w2n w) <=> (v = w)
   
   [w2n_eq_0]  Theorem
      
      |- (w2n w = 0) <=> (w = 0w)
   
   [w2n_lsr]  Theorem
      
      |- !w m. w2n (w >>> m) = w2n w DIV 2 ** m
   
   [w2n_lt]  Theorem
      
      |- !w. w2n w < dimword (:'a)
   
   [w2n_n2w]  Theorem
      
      |- !n. w2n (n2w n) = n MOD dimword (:'a)
   
   [w2n_w2w]  Theorem
      
      |- !w.
           w2n (w2w w) =
           if dimindex (:'a) <= dimindex (:'b) then
             w2n w
           else
             w2n ((dimindex (:'b) - 1 -- 0) w)
   
   [w2s_s2w]  Theorem
      
      |- !b s.
           w2s b n2c (s2w b c2n s) =
           n2s b n2c (s2n b c2n s MOD dimword (:'a))
   
   [w2w]  Theorem
      
      |- !w i.
           i < dimindex (:'b) ==>
           (w2w w ' i <=> i < dimindex (:'a) /\ w ' i)
   
   [w2w_0]  Theorem
      
      |- w2w 0w = 0w
   
   [w2w_LSL]  Theorem
      
      |- !w n.
           w2w (w << n) =
           if n < dimindex (:'a) then
             w2w ((dimindex (:'a) - 1 - n -- 0) w) << n
           else
             0w
   
   [w2w_id]  Theorem
      
      |- !w. w2w w = w
   
   [w2w_n2w]  Theorem
      
      |- !n.
           w2w (n2w n) =
           if dimindex (:'b) <= dimindex (:'a) then
             n2w n
           else
             n2w (BITS (dimindex (:'a) - 1) 0 n)
   
   [w2w_w2w]  Theorem
      
      |- !w. w2w (w2w w) = w2w ((dimindex (:'b) - 1 -- 0) w)
   
   [word_0]  Theorem
      
      |- !i. i < dimindex (:'a) ==> ~0w ' i
   
   [word_0_n2w]  Theorem
      
      |- w2n 0w = 0
   
   [word_1_n2w]  Theorem
      
      |- w2n 1w = 1
   
   [word_1comp_n2w]  Theorem
      
      |- !n. ~n2w n = n2w (dimword (:'a) - 1 - n MOD dimword (:'a))
   
   [word_2comp_n2w]  Theorem
      
      |- !n. -n2w n = n2w (dimword (:'a) - n MOD dimword (:'a))
   
   [word_H]  Theorem
      
      |- !n.
           n < dimindex (:'a) ==> (INT_MAXw ' n <=> n < dimindex (:'a) - 1)
   
   [word_L]  Theorem
      
      |- !n.
           n < dimindex (:'a) ==>
           (INT_MINw ' n <=> (n = dimindex (:'a) - 1))
   
   [word_L2]  Theorem
      
      |- INT_MINw2 = if 1 < dimindex (:'a) then 0w else INT_MINw
   
   [word_L2_MULT]  Theorem
      
      |- (INT_MINw2 * INT_MINw2 = INT_MINw2) /\
         (INT_MINw * INT_MINw2 = INT_MINw2) /\
         (!n. n2w n * INT_MINw2 = if EVEN n then 0w else INT_MINw2) /\
         !n. -n2w n * INT_MINw2 = if EVEN n then 0w else INT_MINw2
   
   [word_L_MULT]  Theorem
      
      |- !n. n2w n * INT_MINw = if EVEN n then 0w else INT_MINw
   
   [word_L_MULT_NEG]  Theorem
      
      |- !n. -n2w n * INT_MINw = if EVEN n then 0w else INT_MINw
   
   [word_T]  Theorem
      
      |- !i. i < dimindex (:'a) ==> UINT_MAXw ' i
   
   [word_T_not_zero]  Theorem
      
      |- -1w <> 0w
   
   [word_add_n2w]  Theorem
      
      |- !m n. n2w m + n2w n = n2w (m + n)
   
   [word_and_n2w]  Theorem
      
      |- !n m. n2w n && n2w m = n2w (BITWISE (dimindex (:'a)) $/\ n m)
   
   [word_asr]  Theorem
      
      |- !w n.
           w >> n =
           if word_msb w then
             (dimindex (:'a) - 1 <> dimindex (:'a) - n) UINT_MAXw !!
             w >>> n
           else
             w >>> n
   
   [word_asr_n2w]  Theorem
      
      |- !n w.
           w >> n =
           if word_msb w then
             n2w
               (dimword (:'a) -
                2 ** (dimindex (:'a) - MIN n (dimindex (:'a)))) !! w >>> n
           else
             w >>> n
   
   [word_bin_list]  Theorem
      
      |- word_from_bin_list o word_to_bin_list = I
   
   [word_bin_string]  Theorem
      
      |- word_from_bin_string o word_to_bin_string = I
   
   [word_bit]  Theorem
      
      |- !w b. b < dimindex (:'a) ==> (w ' b <=> word_bit b w)
   
   [word_bit_0]  Theorem
      
      |- ~word_bit h 0w
   
   [word_bit_0_word_T]  Theorem
      
      |- word_bit 0 (-1w)
   
   [word_bit_n2w]  Theorem
      
      |- !b n. word_bit b (n2w n) <=> b <= dimindex (:'a) - 1 /\ BIT b n
   
   [word_bits_n2w]  Theorem
      
      |- !h l n.
           (h -- l) (n2w n) = n2w (BITS (MIN h (dimindex (:'a) - 1)) l n)
   
   [word_bits_w2w]  Theorem
      
      |- !w. (h -- l) (w2w w) = w2w ((MIN h (dimindex (:'b) - 1) -- l) w)
   
   [word_concat_0]  Theorem
      
      |- 0w @@ 0w = 0w
   
   [word_concat_word_T]  Theorem
      
      |- -1w @@ -1w = w2w (-1w)
   
   [word_dec_list]  Theorem
      
      |- word_from_dec_list o word_to_dec_list = I
   
   [word_dec_string]  Theorem
      
      |- word_from_dec_string o word_to_dec_string = I
   
   [word_div_1]  Theorem
      
      |- v // 1w = v
   
   [word_eq_n2w]  Theorem
      
      |- (!m n. (n2w m = n2w n) <=> MOD_2EXP_EQ (dimindex (:'a)) m n) /\
         (!n. (n2w n = -1w) <=> MOD_2EXP_MAX (dimindex (:'a)) n) /\
         !n. (-1w = n2w n) <=> MOD_2EXP_MAX (dimindex (:'a)) n
   
   [word_extract_n2w]  Theorem
      
      |- (h >< l) (n2w n) =
         if dimindex (:'b) <= dimindex (:'a) then
           n2w (BITS (MIN h (dimindex (:'a) - 1)) l n)
         else
           n2w
             (BITS
                (MIN (MIN h (dimindex (:'a) - 1)) (dimindex (:'a) - 1 + l))
                l n)
   
   [word_extract_w2w]  Theorem
      
      |- !w.
           dimindex (:'a) <= dimindex (:'b) ==>
           ((h >< l) (w2w w) = (h >< l) w)
   
   [word_ge_n2w]  Theorem
      
      |- !a b.
           n2w a >= n2w b <=>
           (let sa = BIT (dimindex (:'a) - 1) a and
                sb = BIT (dimindex (:'a) - 1) b
            in
              (sa <=> sb) /\ a MOD dimword (:'a) >= b MOD dimword (:'a) \/
              ~sa /\ sb)
   
   [word_gt_n2w]  Theorem
      
      |- !a b.
           n2w a > n2w b <=>
           (let sa = BIT (dimindex (:'a) - 1) a and
                sb = BIT (dimindex (:'a) - 1) b
            in
              (sa <=> sb) /\ a MOD dimword (:'a) > b MOD dimword (:'a) \/
              ~sa /\ sb)
   
   [word_hex_list]  Theorem
      
      |- word_from_hex_list o word_to_hex_list = I
   
   [word_hex_string]  Theorem
      
      |- word_from_hex_string o word_to_hex_string = I
   
   [word_hi_n2w]  Theorem
      
      |- !a b. n2w a >+ n2w b <=> a MOD dimword (:'a) > b MOD dimword (:'a)
   
   [word_hs_n2w]  Theorem
      
      |- !a b.
           n2w a >=+ n2w b <=> a MOD dimword (:'a) >= b MOD dimword (:'a)
   
   [word_index_n2w]  Theorem
      
      |- !n.
           n2w n ' i <=> if i < dimindex (:'a) then BIT i n else n2w n ' i
   
   [word_join_0]  Theorem
      
      |- !a. word_join 0w a = w2w a
   
   [word_join_word_T]  Theorem
      
      |- word_join (-1w) (-1w) = -1w
   
   [word_le_n2w]  Theorem
      
      |- !a b.
           n2w a <= n2w b <=>
           (let sa = BIT (dimindex (:'a) - 1) a and
                sb = BIT (dimindex (:'a) - 1) b
            in
              (sa <=> sb) /\ a MOD dimword (:'a) <= b MOD dimword (:'a) \/
              sa /\ ~sb)
   
   [word_lo_n2w]  Theorem
      
      |- !a b. n2w a <+ n2w b <=> a MOD dimword (:'a) < b MOD dimword (:'a)
   
   [word_log2_1]  Theorem
      
      |- word_log2 1w = 0w
   
   [word_log2_n2w]  Theorem
      
      |- !n. word_log2 (n2w n) = n2w (LOG2 (n MOD dimword (:'a)))
   
   [word_ls_n2w]  Theorem
      
      |- !a b.
           n2w a <=+ n2w b <=> a MOD dimword (:'a) <= b MOD dimword (:'a)
   
   [word_lsb]  Theorem
      
      |- word_lsb = word_bit 0
   
   [word_lsb_n2w]  Theorem
      
      |- !n. word_lsb (n2w n) <=> ODD n
   
   [word_lsb_word_T]  Theorem
      
      |- word_lsb (-1w)
   
   [word_lsl_n2w]  Theorem
      
      |- !n m.
           n2w m << n =
           if dimindex (:'a) - 1 < n then 0w else n2w (m * 2 ** n)
   
   [word_lsr_n2w]  Theorem
      
      |- !w n. w >>> n = (dimindex (:'a) - 1 -- n) w
   
   [word_lt_n2w]  Theorem
      
      |- !a b.
           n2w a < n2w b <=>
           (let sa = BIT (dimindex (:'a) - 1) a and
                sb = BIT (dimindex (:'a) - 1) b
            in
              (sa <=> sb) /\ a MOD dimword (:'a) < b MOD dimword (:'a) \/
              sa /\ ~sb)
   
   [word_modify_n2w]  Theorem
      
      |- !f n.
           word_modify f (n2w n) = n2w (BIT_MODIFY (dimindex (:'a)) f n)
   
   [word_msb]  Theorem
      
      |- word_msb = word_bit (dimindex (:'a) - 1)
   
   [word_msb_n2w]  Theorem
      
      |- !n. word_msb (n2w n) <=> BIT (dimindex (:'a) - 1) n
   
   [word_msb_n2w_numeric]  Theorem
      
      |- word_msb (n2w n) <=> INT_MIN (:'a) <= n MOD dimword (:'a)
   
   [word_msb_word_T]  Theorem
      
      |- word_msb (-1w)
   
   [word_mul_n2w]  Theorem
      
      |- !m n. n2w m * n2w n = n2w (m * n)
   
   [word_nchotomy]  Theorem
      
      |- !w. ?n. w = n2w n
   
   [word_oct_list]  Theorem
      
      |- word_from_oct_list o word_to_oct_list = I
   
   [word_oct_string]  Theorem
      
      |- word_from_oct_string o word_to_oct_string = I
   
   [word_or_n2w]  Theorem
      
      |- !n m. n2w n !! n2w m = n2w (BITWISE (dimindex (:'a)) $\/ n m)
   
   [word_reverse_0]  Theorem
      
      |- word_reverse 0w = 0w
   
   [word_reverse_n2w]  Theorem
      
      |- !n. word_reverse (n2w n) = n2w (BIT_REVERSE (dimindex (:'a)) n)
   
   [word_reverse_word_T]  Theorem
      
      |- word_reverse (-1w) = -1w
   
   [word_ror]  Theorem
      
      |- !w n.
           w #>> n =
           (let x = n MOD dimindex (:'a) in
              (dimindex (:'a) - 1 -- x) w !!
              (x - 1 -- 0) w << (dimindex (:'a) - x))
   
   [word_ror_n2w]  Theorem
      
      |- !n a.
           n2w a #>> n =
           (let x = n MOD dimindex (:'a) in
              n2w
                (BITS (dimindex (:'a) - 1) x a +
                 BITS (x - 1) 0 a * 2 ** (dimindex (:'a) - x)))
   
   [word_rrx_0]  Theorem
      
      |- (word_rrx (F,0w) = (F,0w)) /\ (word_rrx (T,0w) = (F,INT_MINw))
   
   [word_rrx_n2w]  Theorem
      
      |- !c a.
           word_rrx (c,n2w a) =
           (ODD a,
            n2w
              (BITS (dimindex (:'a) - 1) 1 a +
               SBIT c (dimindex (:'a) - 1)))
   
   [word_rrx_word_T]  Theorem
      
      |- (word_rrx (F,-1w) = (T,INT_MAXw)) /\ (word_rrx (T,-1w) = (T,-1w))
   
   [word_signed_bits_n2w]  Theorem
      
      |- !h l n.
           (h --- l) (n2w n) =
           n2w
             (SIGN_EXTEND (MIN (SUC h) (dimindex (:'a)) - l)
                (dimindex (:'a)) (BITS (MIN h (dimindex (:'a) - 1)) l n))
   
   [word_slice_n2w]  Theorem
      
      |- !h l n.
           (h <> l) (n2w n) = n2w (SLICE (MIN h (dimindex (:'a) - 1)) l n)
   
   [word_sub_w2n]  Theorem
      
      |- !x y. y <=+ x ==> (w2n (x - y) = w2n x - w2n y)
   
   [word_xor_n2w]  Theorem
      
      |- !n m.
           n2w n ?? n2w m =
           n2w (BITWISE (dimindex (:'a)) (\x y. x <=/=> y) n m)
   
   
*)
end
