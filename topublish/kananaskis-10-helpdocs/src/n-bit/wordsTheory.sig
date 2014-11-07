signature wordsTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BIT_SET_curried_def : thm
    val BIT_SET_tupled_primitive_def : thm
    val INT_MAX_def : thm
    val INT_MIN_def : thm
    val UINT_MAX_def : thm
    val add_with_carry_def : thm
    val bit_count_def : thm
    val bit_count_upto_def : thm
    val bit_field_insert_def : thm
    val concat_word_list_def : thm
    val dimword_def : thm
    val l2w_def : thm
    val n2w_def : thm
    val n2w_itself_primitive_def : thm
    val nzcv_def : thm
    val reduce_and_def : thm
    val reduce_nand_def : thm
    val reduce_nor_def : thm
    val reduce_or_def : thm
    val reduce_xnor_def : thm
    val reduce_xor_def : thm
    val s2w_def : thm
    val saturate_add_def : thm
    val saturate_mul_def : thm
    val saturate_n2w_def : thm
    val saturate_sub_def : thm
    val saturate_w2w_def : thm
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
    val word_abs_def : thm
    val word_add_def : thm
    val word_and_def : thm
    val word_asr_bv_def : thm
    val word_asr_def : thm
    val word_bit_def : thm
    val word_bits_def : thm
    val word_compare_def : thm
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
    val word_lsl_bv_def : thm
    val word_lsl_def : thm
    val word_lsr_bv_def : thm
    val word_lsr_def : thm
    val word_lt_def : thm
    val word_max_def : thm
    val word_min_def : thm
    val word_mod_def : thm
    val word_modify_def : thm
    val word_msb_def : thm
    val word_mul_def : thm
    val word_nand_def : thm
    val word_nor_def : thm
    val word_or_def : thm
    val word_reduce_def : thm
    val word_replicate_def : thm
    val word_reverse_def : thm
    val word_rol_bv_def : thm
    val word_rol_def : thm
    val word_ror_bv_def : thm
    val word_ror_def : thm
    val word_rrx_def : thm
    val word_sdiv_def : thm
    val word_sign_extend_def : thm
    val word_signed_bits_def : thm
    val word_slice_def : thm
    val word_smax_def : thm
    val word_smin_def : thm
    val word_smod_def : thm
    val word_srem_def : thm
    val word_sub_def : thm
    val word_to_bin_list_def : thm
    val word_to_bin_string_def : thm
    val word_to_dec_list_def : thm
    val word_to_dec_string_def : thm
    val word_to_hex_list_def : thm
    val word_to_hex_string_def : thm
    val word_to_oct_list_def : thm
    val word_to_oct_string_def : thm
    val word_xnor_def : thm
    val word_xor_def : thm

  (*  Theorems  *)
    val ADD_WITH_CARRY_SUB : thm
    val ASR_ADD : thm
    val ASR_LIMIT : thm
    val ASR_UINT_MAX : thm
    val BITS_ZEROL_DIMINDEX : thm
    val BIT_SET : thm
    val BIT_SET_def : thm
    val BIT_SET_ind : thm
    val BIT_UPDATE : thm
    val BOUND_ORDER : thm
    val CONCAT_EXTRACT : thm
    val DIMINDEX_GT_0 : thm
    val EXISTS_HB : thm
    val EXTEND_EXTRACT : thm
    val EXTRACT_ALL_BITS : thm
    val EXTRACT_CONCAT : thm
    val EXTRACT_JOIN : thm
    val EXTRACT_JOIN_ADD : thm
    val EXTRACT_JOIN_ADD_LSL : thm
    val EXTRACT_JOIN_LSL : thm
    val FCP_T_F : thm
    val FST_ADD_WITH_CARRY : thm
    val INT_MAX_LT_DIMWORD : thm
    val INT_MIN_1 : thm
    val INT_MIN_10 : thm
    val INT_MIN_11 : thm
    val INT_MIN_12 : thm
    val INT_MIN_128 : thm
    val INT_MIN_16 : thm
    val INT_MIN_2 : thm
    val INT_MIN_20 : thm
    val INT_MIN_24 : thm
    val INT_MIN_28 : thm
    val INT_MIN_3 : thm
    val INT_MIN_30 : thm
    val INT_MIN_32 : thm
    val INT_MIN_4 : thm
    val INT_MIN_48 : thm
    val INT_MIN_5 : thm
    val INT_MIN_6 : thm
    val INT_MIN_64 : thm
    val INT_MIN_7 : thm
    val INT_MIN_8 : thm
    val INT_MIN_9 : thm
    val INT_MIN_96 : thm
    val INT_MIN_LT_DIMWORD : thm
    val INT_MIN_SUM : thm
    val LEAST_BIT_LT : thm
    val LOG2_w2n : thm
    val LOG2_w2n_lt : thm
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
    val NOT_0w : thm
    val NOT_FINITE_IMP_dimword_2 : thm
    val NOT_INT_MIN_ZERO : thm
    val NOT_UINTMAXw : thm
    val NUMERAL_LESS_THM : thm
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
    val SHIFT_1_SUB_1 : thm
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
    val WORD_ADD_XOR : thm
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
    val WORD_DIV_LSR : thm
    val WORD_EQ : thm
    val WORD_EQ_ADD_LCANCEL : thm
    val WORD_EQ_ADD_RCANCEL : thm
    val WORD_EQ_NEG : thm
    val WORD_EQ_SUB_LADD : thm
    val WORD_EQ_SUB_RADD : thm
    val WORD_EQ_SUB_ZERO : thm
    val WORD_EXTRACT_BITS_COMP : thm
    val WORD_EXTRACT_COMP_THM : thm
    val WORD_EXTRACT_ID : thm
    val WORD_EXTRACT_LSL : thm
    val WORD_EXTRACT_LSL2 : thm
    val WORD_EXTRACT_LT : thm
    val WORD_EXTRACT_MIN_HIGH : thm
    val WORD_EXTRACT_OVER_ADD : thm
    val WORD_EXTRACT_OVER_ADD2 : thm
    val WORD_EXTRACT_OVER_BITWISE : thm
    val WORD_EXTRACT_OVER_MUL : thm
    val WORD_EXTRACT_OVER_MUL2 : thm
    val WORD_EXTRACT_ZERO : thm
    val WORD_EXTRACT_ZERO2 : thm
    val WORD_EXTRACT_ZERO3 : thm
    val WORD_FINITE : thm
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
    val WORD_MODIFY_BIT : thm
    val WORD_MOD_1 : thm
    val WORD_MOD_POW2 : thm
    val WORD_MSB_1COMP : thm
    val WORD_MSB_INT_MIN_LS : thm
    val WORD_MULT_ASSOC : thm
    val WORD_MULT_CLAUSES : thm
    val WORD_MULT_COMM : thm
    val WORD_MULT_SUC : thm
    val WORD_MUL_LSL : thm
    val WORD_NAND_NOT_AND : thm
    val WORD_NEG : thm
    val WORD_NEG_0 : thm
    val WORD_NEG_1 : thm
    val WORD_NEG_1_T : thm
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
    val WORD_NOR_NOT_OR : thm
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
    val WORD_SET_INDUCT : thm
    val WORD_SLICE_BITS_THM : thm
    val WORD_SLICE_COMP_THM : thm
    val WORD_SLICE_OVER_BITWISE : thm
    val WORD_SLICE_THM : thm
    val WORD_SLICE_ZERO : thm
    val WORD_SLICE_ZERO2 : thm
    val WORD_SUB : thm
    val WORD_SUB_ADD : thm
    val WORD_SUB_ADD2 : thm
    val WORD_SUB_INTRO : thm
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
    val WORD_SUM_ZERO : thm
    val WORD_XNOR_NOT_XOR : thm
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
    val ZERO_LE_INT_MAX : thm
    val ZERO_LO_INT_MIN : thm
    val ZERO_LT_INT_MAX : thm
    val ZERO_LT_INT_MIN : thm
    val ZERO_LT_UINT_MAX : thm
    val ZERO_LT_dimword : thm
    val ZERO_SHIFT : thm
    val bit_count_is_zero : thm
    val bit_count_upto_0 : thm
    val bit_count_upto_SUC : thm
    val bit_count_upto_is_zero : thm
    val bit_field_insert : thm
    val dimindex_1 : thm
    val dimindex_10 : thm
    val dimindex_11 : thm
    val dimindex_12 : thm
    val dimindex_128 : thm
    val dimindex_16 : thm
    val dimindex_1_cases : thm
    val dimindex_2 : thm
    val dimindex_20 : thm
    val dimindex_24 : thm
    val dimindex_28 : thm
    val dimindex_3 : thm
    val dimindex_30 : thm
    val dimindex_32 : thm
    val dimindex_4 : thm
    val dimindex_48 : thm
    val dimindex_5 : thm
    val dimindex_6 : thm
    val dimindex_64 : thm
    val dimindex_7 : thm
    val dimindex_8 : thm
    val dimindex_9 : thm
    val dimindex_96 : thm
    val dimindex_dimword_iso : thm
    val dimindex_dimword_le_iso : thm
    val dimindex_dimword_lt_iso : thm
    val dimindex_int_max_iso : thm
    val dimindex_int_max_le_iso : thm
    val dimindex_int_max_lt_iso : thm
    val dimindex_int_min_iso : thm
    val dimindex_int_min_le_iso : thm
    val dimindex_int_min_lt_iso : thm
    val dimindex_lt_dimword : thm
    val dimindex_uint_max_iso : thm
    val dimindex_uint_max_le_iso : thm
    val dimindex_uint_max_lt_iso : thm
    val dimword_1 : thm
    val dimword_10 : thm
    val dimword_11 : thm
    val dimword_12 : thm
    val dimword_128 : thm
    val dimword_16 : thm
    val dimword_2 : thm
    val dimword_20 : thm
    val dimword_24 : thm
    val dimword_28 : thm
    val dimword_3 : thm
    val dimword_30 : thm
    val dimword_32 : thm
    val dimword_4 : thm
    val dimword_48 : thm
    val dimword_5 : thm
    val dimword_6 : thm
    val dimword_64 : thm
    val dimword_7 : thm
    val dimword_8 : thm
    val dimword_9 : thm
    val dimword_96 : thm
    val dimword_IS_TWICE_INT_MIN : thm
    val dimword_sub_int_min : thm
    val fcp_n2w : thm
    val finite_1 : thm
    val finite_10 : thm
    val finite_11 : thm
    val finite_12 : thm
    val finite_128 : thm
    val finite_16 : thm
    val finite_2 : thm
    val finite_20 : thm
    val finite_24 : thm
    val finite_28 : thm
    val finite_3 : thm
    val finite_30 : thm
    val finite_32 : thm
    val finite_4 : thm
    val finite_48 : thm
    val finite_5 : thm
    val finite_6 : thm
    val finite_64 : thm
    val finite_7 : thm
    val finite_8 : thm
    val finite_9 : thm
    val finite_96 : thm
    val foldl_reduce_and : thm
    val foldl_reduce_nand : thm
    val foldl_reduce_nor : thm
    val foldl_reduce_or : thm
    val foldl_reduce_xnor : thm
    val foldl_reduce_xor : thm
    val l2w_w2l : thm
    val lsr_1_word_T : thm
    val mod_dimindex : thm
    val n2w_11 : thm
    val n2w_BITS : thm
    val n2w_DIV : thm
    val n2w_SUC : thm
    val n2w_dimword : thm
    val n2w_itself_def : thm
    val n2w_itself_ind : thm
    val n2w_mod : thm
    val n2w_sub : thm
    val n2w_sub_eq_0 : thm
    val n2w_w2n : thm
    val ranged_word_nchotomy : thm
    val reduce_and : thm
    val reduce_or : thm
    val s2w_w2s : thm
    val saturate_add : thm
    val saturate_mul : thm
    val saturate_sub : thm
    val saturate_w2w : thm
    val saturate_w2w_n2w : thm
    val sw2sw : thm
    val sw2sw_0 : thm
    val sw2sw_id : thm
    val sw2sw_sw2sw : thm
    val sw2sw_w2w : thm
    val sw2sw_w2w_add : thm
    val sw2sw_word_T : thm
    val w2l_l2w : thm
    val w2n_11 : thm
    val w2n_11_lift : thm
    val w2n_add : thm
    val w2n_eq_0 : thm
    val w2n_lsr : thm
    val w2n_lt : thm
    val w2n_minus1 : thm
    val w2n_n2w : thm
    val w2n_w2w : thm
    val w2n_w2w_le : thm
    val w2s_s2w : thm
    val w2w : thm
    val w2w_0 : thm
    val w2w_LSL : thm
    val w2w_eq_n2w : thm
    val w2w_id : thm
    val w2w_lt : thm
    val w2w_n2w : thm
    val w2w_w2w : thm
    val word_0 : thm
    val word_0_n2w : thm
    val word_1_n2w : thm
    val word_1comp_n2w : thm
    val word_2comp_dimindex_1 : thm
    val word_2comp_n2w : thm
    val word_H : thm
    val word_L : thm
    val word_L2 : thm
    val word_L2_MULT : thm
    val word_L_MULT : thm
    val word_L_MULT_NEG : thm
    val word_T : thm
    val word_T_not_zero : thm
    val word_abs : thm
    val word_abs_diff : thm
    val word_abs_neg : thm
    val word_abs_word_abs : thm
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
    val word_concat_0_0 : thm
    val word_concat_0_eq : thm
    val word_concat_word_T : thm
    val word_dec_list : thm
    val word_dec_string : thm
    val word_div_1 : thm
    val word_eq_0 : thm
    val word_eq_n2w : thm
    val word_extract_eq_n2w : thm
    val word_extract_mask : thm
    val word_extract_n2w : thm
    val word_extract_w2w : thm
    val word_ge_n2w : thm
    val word_gt_n2w : thm
    val word_hex_list : thm
    val word_hex_string : thm
    val word_hi_n2w : thm
    val word_hs_n2w : thm
    val word_index : thm
    val word_index_n2w : thm
    val word_join_0 : thm
    val word_join_index : thm
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
    val word_msb_neg : thm
    val word_msb_word_T : thm
    val word_mul_n2w : thm
    val word_nand_n2w : thm
    val word_nchotomy : thm
    val word_nor_n2w : thm
    val word_oct_list : thm
    val word_oct_string : thm
    val word_or_n2w : thm
    val word_reduce_n2w : thm
    val word_replicate_concat_word_list : thm
    val word_reverse_0 : thm
    val word_reverse_n2w : thm
    val word_reverse_thm : thm
    val word_reverse_word_T : thm
    val word_ror : thm
    val word_ror_n2w : thm
    val word_rrx_0 : thm
    val word_rrx_n2w : thm
    val word_rrx_word_T : thm
    val word_shift_bv : thm
    val word_sign_extend_bits : thm
    val word_signed_bits_n2w : thm
    val word_slice_n2w : thm
    val word_sub_w2n : thm
    val word_xnor_n2w : thm
    val word_xor_n2w : thm

  val words_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ASCIInumbers] Parent theory of "words"

   [fcp] Parent theory of "words"

   [numeral_bit] Parent theory of "words"

   [sum_num] Parent theory of "words"

   [BIT_SET_curried_def]  Definition

      |- ∀x x1. BIT_SET x x1 = BIT_SET_tupled (x,x1)

   [BIT_SET_tupled_primitive_def]  Definition

      |- BIT_SET_tupled =
         WFREC
           (@R.
              WF R ∧ (∀i n. n ≠ 0 ∧ ODD n ⇒ R (SUC i,n DIV 2) (i,n)) ∧
              ∀i n. n ≠ 0 ∧ ¬ODD n ⇒ R (SUC i,n DIV 2) (i,n))
           (λBIT_SET_tupled a.
              case a of
                (i,n) =>
                  I
                    (if n = 0 then ∅
                     else if ODD n then
                       i INSERT BIT_SET_tupled (SUC i,n DIV 2)
                     else BIT_SET_tupled (SUC i,n DIV 2)))

   [INT_MAX_def]  Definition

      |- INT_MAX (:α) = INT_MIN (:α) − 1

   [INT_MIN_def]  Definition

      |- INT_MIN (:α) = 2 ** (dimindex (:α) − 1)

   [UINT_MAX_def]  Definition

      |- UINT_MAX (:α) = dimword (:α) − 1

   [add_with_carry_def]  Definition

      |- ∀x y carry_in.
           add_with_carry (x,y,carry_in) =
           (let unsigned_sum = w2n x + w2n y + if carry_in then 1 else 0 in
            let result = n2w unsigned_sum in
            let carry_out = w2n result ≠ unsigned_sum and
                overflow =
                  (word_msb x ⇔ word_msb y) ∧
                  (word_msb x ⇎ word_msb result)
            in
              (result,carry_out,overflow))

   [bit_count_def]  Definition

      |- ∀w. bit_count w = bit_count_upto (dimindex (:α)) w

   [bit_count_upto_def]  Definition

      |- ∀n w. bit_count_upto n w = SUM n (λi. if w ' i then 1 else 0)

   [bit_field_insert_def]  Definition

      |- ∀h l a.
           bit_field_insert h l a =
           word_modify (λi. COND (l ≤ i ∧ i ≤ h) (a ' (i − l)))

   [concat_word_list_def]  Definition

      |- (concat_word_list [] = 0w) ∧
         ∀h t.
           concat_word_list (h::t) =
           w2w h ‖ concat_word_list t ≪ dimindex (:α)

   [dimword_def]  Definition

      |- dimword (:α) = 2 ** dimindex (:α)

   [l2w_def]  Definition

      |- ∀b l. l2w b l = n2w (l2n b l)

   [n2w_def]  Definition

      |- ∀n. n2w n = FCP i. BIT i n

   [n2w_itself_primitive_def]  Definition

      |- n2w_itself =
         WFREC (@R. WF R) (λn2w_itself a. case a of (n,v1) => I (n2w n))

   [nzcv_def]  Definition

      |- ∀a b.
           nzcv a b =
           (let q = w2n a + w2n (-b) in
            let r = n2w q
            in
              (word_msb r,r = 0w,BIT (dimindex (:α)) q ∨ (b = 0w),
               (word_msb a ⇎ word_msb b) ∧ (word_msb r ⇎ word_msb a)))

   [reduce_and_def]  Definition

      |- reduce_and = word_reduce $/\

   [reduce_nand_def]  Definition

      |- reduce_nand = word_reduce (λa b. ¬(a ∧ b))

   [reduce_nor_def]  Definition

      |- reduce_nor = word_reduce (λa b. ¬(a ∨ b))

   [reduce_or_def]  Definition

      |- reduce_or = word_reduce $\/

   [reduce_xnor_def]  Definition

      |- reduce_xnor = word_reduce $<=>

   [reduce_xor_def]  Definition

      |- reduce_xor = word_reduce (λx y. x ⇎ y)

   [s2w_def]  Definition

      |- ∀b f s. s2w b f s = n2w (s2n b f s)

   [saturate_add_def]  Definition

      |- ∀a b. saturate_add a b = saturate_n2w (w2n a + w2n b)

   [saturate_mul_def]  Definition

      |- ∀a b. saturate_mul a b = saturate_n2w (w2n a * w2n b)

   [saturate_n2w_def]  Definition

      |- ∀n. saturate_n2w n = if dimword (:α) ≤ n then UINT_MAXw else n2w n

   [saturate_sub_def]  Definition

      |- ∀a b. saturate_sub a b = n2w (w2n a − w2n b)

   [saturate_w2w_def]  Definition

      |- ∀w. saturate_w2w w = saturate_n2w (w2n w)

   [sw2sw_def]  Definition

      |- ∀w.
           sw2sw w =
           n2w (SIGN_EXTEND (dimindex (:α)) (dimindex (:β)) (w2n w))

   [w2l_def]  Definition

      |- ∀b w. w2l b w = n2l b (w2n w)

   [w2n_def]  Definition

      |- ∀w. w2n w = SUM (dimindex (:α)) (λi. SBIT (w ' i) i)

   [w2s_def]  Definition

      |- ∀b f w. w2s b f w = n2s b f (w2n w)

   [w2w_def]  Definition

      |- ∀w. w2w w = n2w (w2n w)

   [word_1comp_def]  Definition

      |- ∀w. ¬w = FCP i. ¬w ' i

   [word_2comp_def]  Definition

      |- ∀w. -w = n2w (dimword (:α) − w2n w)

   [word_H_def]  Definition

      |- INT_MAXw = n2w (INT_MAX (:α))

   [word_L2_def]  Definition

      |- INT_MINw2 = INT_MINw * INT_MINw

   [word_L_def]  Definition

      |- INT_MINw = n2w (INT_MIN (:α))

   [word_T_def]  Definition

      |- UINT_MAXw = n2w (UINT_MAX (:α))

   [word_abs_def]  Definition

      |- ∀w. word_abs w = if w < 0w then -w else w

   [word_add_def]  Definition

      |- ∀v w. v + w = n2w (w2n v + w2n w)

   [word_and_def]  Definition

      |- ∀v w. v && w = FCP i. v ' i ∧ w ' i

   [word_asr_bv_def]  Definition

      |- ∀w n. w >>~ n = w ≫ w2n n

   [word_asr_def]  Definition

      |- ∀w n.
           w ≫ n =
           FCP i. if dimindex (:α) ≤ i + n then word_msb w else w ' (i + n)

   [word_bit_def]  Definition

      |- ∀b w. word_bit b w ⇔ b ≤ dimindex (:α) − 1 ∧ w ' b

   [word_bits_def]  Definition

      |- ∀h l.
           h -- l =
           (λw. FCP i. i + l ≤ MIN h (dimindex (:α) − 1) ∧ w ' (i + l))

   [word_compare_def]  Definition

      |- ∀a b. word_compare a b = if a = b then 1w else 0w

   [word_concat_def]  Definition

      |- ∀v w. v @@ w = w2w (word_join v w)

   [word_div_def]  Definition

      |- ∀v w. v // w = n2w (w2n v DIV w2n w)

   [word_extract_def]  Definition

      |- ∀h l. h >< l = w2w o (h -- l)

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

      |- ∀a b. a ≥ b ⇔ (let (n,z,c,v) = nzcv a b in n ⇔ v)

   [word_gt_def]  Definition

      |- ∀a b. a > b ⇔ (let (n,z,c,v) = nzcv a b in ¬z ∧ (n ⇔ v))

   [word_hi_def]  Definition

      |- ∀a b. a >₊ b ⇔ (let (n,z,c,v) = nzcv a b in c ∧ ¬z)

   [word_hs_def]  Definition

      |- ∀a b. a ≥₊ b ⇔ (let (n,z,c,v) = nzcv a b in c)

   [word_join_def]  Definition

      |- ∀v w.
           word_join v w =
           (let cv = w2w v and cw = w2w w in cv ≪ dimindex (:β) ‖ cw)

   [word_le_def]  Definition

      |- ∀a b. a ≤ b ⇔ (let (n,z,c,v) = nzcv a b in z ∨ (n ⇎ v))

   [word_len_def]  Definition

      |- ∀w. word_len w = dimindex (:α)

   [word_lo_def]  Definition

      |- ∀a b. a <₊ b ⇔ (let (n,z,c,v) = nzcv a b in ¬c)

   [word_log2_def]  Definition

      |- ∀w. word_log2 w = n2w (LOG2 (w2n w))

   [word_ls_def]  Definition

      |- ∀a b. a ≤₊ b ⇔ (let (n,z,c,v) = nzcv a b in ¬c ∨ z)

   [word_lsb_def]  Definition

      |- ∀w. word_lsb w ⇔ w ' 0

   [word_lsl_bv_def]  Definition

      |- ∀w n. w <<~ n = w ≪ w2n n

   [word_lsl_def]  Definition

      |- ∀w n. w ≪ n = FCP i. i < dimindex (:α) ∧ n ≤ i ∧ w ' (i − n)

   [word_lsr_bv_def]  Definition

      |- ∀w n. w >>>~ n = w ⋙ w2n n

   [word_lsr_def]  Definition

      |- ∀w n. w ⋙ n = FCP i. i + n < dimindex (:α) ∧ w ' (i + n)

   [word_lt_def]  Definition

      |- ∀a b. a < b ⇔ (let (n,z,c,v) = nzcv a b in n ⇎ v)

   [word_max_def]  Definition

      |- ∀a b. word_max a b = if a <₊ b then b else a

   [word_min_def]  Definition

      |- ∀a b. word_min a b = if a <₊ b then a else b

   [word_mod_def]  Definition

      |- ∀v w. word_mod v w = n2w (w2n v MOD w2n w)

   [word_modify_def]  Definition

      |- ∀f w. word_modify f w = FCP i. f i (w ' i)

   [word_msb_def]  Definition

      |- ∀w. word_msb w ⇔ w ' (dimindex (:α) − 1)

   [word_mul_def]  Definition

      |- ∀v w. v * w = n2w (w2n v * w2n w)

   [word_nand_def]  Definition

      |- ∀v w. v ~&& w = FCP i. ¬(v ' i ∧ w ' i)

   [word_nor_def]  Definition

      |- ∀v w. v ~|| w = FCP i. ¬(v ' i ∨ w ' i)

   [word_or_def]  Definition

      |- ∀v w. v ‖ w = FCP i. v ' i ∨ w ' i

   [word_reduce_def]  Definition

      |- ∀f w.
           word_reduce f w =
           $FCP
             (K
                (let l =
                       GENLIST (λi. w ' (dimindex (:α) − 1 − i))
                         (dimindex (:α))
                 in
                   FOLDL f (HD l) (TL l)))

   [word_replicate_def]  Definition

      |- ∀n w.
           word_replicate n w =
           FCP i. i < n * dimindex (:α) ∧ w ' (i MOD dimindex (:α))

   [word_reverse_def]  Definition

      |- ∀w. word_reverse w = FCP i. w ' (dimindex (:α) − 1 − i)

   [word_rol_bv_def]  Definition

      |- ∀w n. w #<<~ n = w ⇆ w2n n

   [word_rol_def]  Definition

      |- ∀w n. w ⇆ n = w ⇄ (dimindex (:α) − n MOD dimindex (:α))

   [word_ror_bv_def]  Definition

      |- ∀w n. w #>>~ n = w ⇄ w2n n

   [word_ror_def]  Definition

      |- ∀w n. w ⇄ n = FCP i. w ' ((i + n) MOD dimindex (:α))

   [word_rrx_def]  Definition

      |- ∀c w.
           word_rrx (c,w) =
           (word_lsb w,
            FCP i. if i = dimindex (:α) − 1 then c else (w ⋙ 1) ' i)

   [word_sdiv_def]  Definition

      |- ∀a b.
           a / b =
           if word_msb a then if word_msb b then -a // -b else -(-a // b)
           else if word_msb b then -(a // -b)
           else a // b

   [word_sign_extend_def]  Definition

      |- ∀n w.
           word_sign_extend n w =
           n2w (SIGN_EXTEND n (dimindex (:α)) (w2n w))

   [word_signed_bits_def]  Definition

      |- ∀h l.
           h --- l =
           (λw.
              FCP i.
                l ≤ MIN h (dimindex (:α) − 1) ∧
                w ' (MIN (i + l) (MIN h (dimindex (:α) − 1))))

   [word_slice_def]  Definition

      |- ∀h l.
           h '' l =
           (λw. FCP i. l ≤ i ∧ i ≤ MIN h (dimindex (:α) − 1) ∧ w ' i)

   [word_smax_def]  Definition

      |- ∀a b. word_smax a b = if a < b then b else a

   [word_smin_def]  Definition

      |- ∀a b. word_smin a b = if a < b then a else b

   [word_smod_def]  Definition

      |- ∀s t.
           word_smod s t =
           (let abs_s = if word_msb s then -s else s and
                abs_t = if word_msb t then -t else t
            in
            let u = word_mod abs_s abs_t
            in
              if u = 0w then u
              else if word_msb s then if word_msb t then -u else -u + t
              else if word_msb t then u + t
              else u)

   [word_srem_def]  Definition

      |- ∀a b.
           word_srem a b =
           if word_msb a then
             if word_msb b then -word_mod (-a) (-b) else -word_mod (-a) b
           else if word_msb b then word_mod a (-b)
           else word_mod a b

   [word_sub_def]  Definition

      |- ∀v w. v − w = v + -w

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

   [word_xnor_def]  Definition

      |- ∀v w. v ~?? w = FCP i. v ' i ⇔ w ' i

   [word_xor_def]  Definition

      |- ∀v w. v ⊕ w = FCP i. v ' i ⇎ w ' i

   [ADD_WITH_CARRY_SUB]  Theorem

      |- ∀x y.
           add_with_carry (x,¬y,T) =
           (x − y,y ≤₊ x,
            (word_msb x ⇎ word_msb y) ∧ (word_msb (x − y) ⇎ word_msb x))

   [ASR_ADD]  Theorem

      |- ∀w m n. w ≫ m ≫ n = w ≫ (m + n)

   [ASR_LIMIT]  Theorem

      |- ∀w n.
           dimindex (:α) ≤ n ⇒
           (w ≫ n = if word_msb w then UINT_MAXw else 0w)

   [ASR_UINT_MAX]  Theorem

      |- ∀n. UINT_MAXw ≫ n = UINT_MAXw

   [BITS_ZEROL_DIMINDEX]  Theorem

      |- ∀n. n < dimword (:α) ⇒ (BITS (dimindex (:α) − 1) 0 n = n)

   [BIT_SET]  Theorem

      |- ∀i n. BIT i n ⇔ i ∈ BIT_SET 0 n

   [BIT_SET_def]  Theorem

      |- ∀n i.
           BIT_SET i n =
           if n = 0 then ∅
           else if ODD n then i INSERT BIT_SET (SUC i) (n DIV 2)
           else BIT_SET (SUC i) (n DIV 2)

   [BIT_SET_ind]  Theorem

      |- ∀P.
           (∀i n.
              (n ≠ 0 ∧ ODD n ⇒ P (SUC i) (n DIV 2)) ∧
              (n ≠ 0 ∧ ¬ODD n ⇒ P (SUC i) (n DIV 2)) ⇒
              P i n) ⇒
           ∀v v1. P v v1

   [BIT_UPDATE]  Theorem

      |- ∀n x. n :+ x = word_modify (λi b. if i = n then x else b)

   [BOUND_ORDER]  Theorem

      |- INT_MAX (:α) < INT_MIN (:α) ∧ INT_MIN (:α) ≤ UINT_MAX (:α) ∧
         UINT_MAX (:α) < dimword (:α)

   [CONCAT_EXTRACT]  Theorem

      |- ∀h m l w.
           (h − m = dimindex (:β)) ∧ (m + 1 − l = dimindex (:γ)) ∧
           (h + 1 − l = dimindex (:δ)) ∧ dimindex (:β + γ) ≠ 1 ⇒
           ((h >< m + 1) w @@ (m >< l) w = (h >< l) w)

   [DIMINDEX_GT_0]  Theorem

      |- 0 < dimindex (:α)

   [EXISTS_HB]  Theorem

      |- ∃m. dimindex (:α) = SUC m

   [EXTEND_EXTRACT]  Theorem

      |- ∀h l w.
           (dimindex (:γ) = h + 1 − l) ⇒ ((h >< l) w = w2w ((h >< l) w))

   [EXTRACT_ALL_BITS]  Theorem

      |- ∀h w. dimindex (:α) − 1 ≤ h ⇒ ((h >< 0) w = w2w w)

   [EXTRACT_CONCAT]  Theorem

      |- ∀v w.
           FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) ∧
           dimindex (:α) + dimindex (:β) ≤ dimindex (:γ) ⇒
           ((dimindex (:β) − 1 >< 0) (v @@ w) = w) ∧
           ((dimindex (:α) + dimindex (:β) − 1 >< dimindex (:β)) (v @@ w) =
            v)

   [EXTRACT_JOIN]  Theorem

      |- ∀h m m' l s w.
           l ≤ m ∧ m' ≤ h ∧ (m' = m + 1) ∧ (s = m' − l) ⇒
           ((h >< m') w ≪ s ‖ (m >< l) w =
            (MIN h (MIN (dimindex (:β) + l − 1) (dimindex (:α) − 1)) >< l)
              w)

   [EXTRACT_JOIN_ADD]  Theorem

      |- ∀h m m' l s w.
           l ≤ m ∧ m' ≤ h ∧ (m' = m + 1) ∧ (s = m' − l) ⇒
           ((h >< m') w ≪ s + (m >< l) w =
            (MIN h (MIN (dimindex (:β) + l − 1) (dimindex (:α) − 1)) >< l)
              w)

   [EXTRACT_JOIN_ADD_LSL]  Theorem

      |- ∀h m m' l s n w.
           l ≤ m ∧ m' ≤ h ∧ (m' = m + 1) ∧ (s = m' − l + n) ⇒
           ((h >< m') w ≪ s + (m >< l) w ≪ n =
            (MIN h (MIN (dimindex (:β) + l − 1) (dimindex (:α) − 1)) >< l)
              w ≪ n)

   [EXTRACT_JOIN_LSL]  Theorem

      |- ∀h m m' l s n w.
           l ≤ m ∧ m' ≤ h ∧ (m' = m + 1) ∧ (s = m' − l + n) ⇒
           ((h >< m') w ≪ s ‖ (m >< l) w ≪ n =
            (MIN h (MIN (dimindex (:β) + l − 1) (dimindex (:α) − 1)) >< l)
              w ≪ n)

   [FCP_T_F]  Theorem

      |- ($FCP (K T) = UINT_MAXw) ∧ ($FCP (K F) = 0w)

   [FST_ADD_WITH_CARRY]  Theorem

      |- ((∀a b. FST (add_with_carry (a,b,F)) = a + b) ∧
          (∀a b. FST (add_with_carry (a,¬b,T)) = a − b) ∧
          ∀a b. FST (add_with_carry (¬a,b,T)) = b − a) ∧
         (∀n a. FST (add_with_carry (a,n2w n,T)) = a − ¬n2w n) ∧
         ∀n b. FST (add_with_carry (n2w n,b,T)) = b − ¬n2w n

   [INT_MAX_LT_DIMWORD]  Theorem

      |- INT_MAX (:α) < dimword (:α)

   [INT_MIN_1]  Theorem

      |- INT_MIN (:unit) = 1

   [INT_MIN_10]  Theorem

      |- INT_MIN (:10) = 512

   [INT_MIN_11]  Theorem

      |- INT_MIN (:11) = 1024

   [INT_MIN_12]  Theorem

      |- INT_MIN (:12) = 2048

   [INT_MIN_128]  Theorem

      |- INT_MIN (:128) = 170141183460469231731687303715884105728

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

   [INT_MIN_48]  Theorem

      |- INT_MIN (:48) = 140737488355328

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

   [INT_MIN_9]  Theorem

      |- INT_MIN (:9) = 256

   [INT_MIN_96]  Theorem

      |- INT_MIN (:96) = 39614081257132168796771975168

   [INT_MIN_LT_DIMWORD]  Theorem

      |- INT_MIN (:α) < dimword (:α)

   [INT_MIN_SUM]  Theorem

      |- INT_MIN (:α + β) =
         if FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) then dimword (:α) * INT_MIN (:β)
         else INT_MIN (:α + β)

   [LEAST_BIT_LT]  Theorem

      |- ∀w. w ≠ 0w ⇒ (LEAST i. w ' i) < dimindex (:α)

   [LOG2_w2n]  Theorem

      |- ∀w.
           w ≠ 0w ⇒
           (LOG2 (w2n w) =
            dimindex (:α) − 1 − LEAST i. w ' (dimindex (:α) − 1 − i))

   [LOG2_w2n_lt]  Theorem

      |- ∀w. w ≠ 0w ⇒ LOG2 (w2n w) < dimindex (:α)

   [LSL_ADD]  Theorem

      |- ∀w m n. w ≪ m ≪ n = w ≪ (m + n)

   [LSL_BITWISE]  Theorem

      |- (∀n v w. w ≪ n && v ≪ n = (w && v) ≪ n) ∧
         (∀n v w. w ≪ n ‖ v ≪ n = (w ‖ v) ≪ n) ∧
         ∀n v w. w ≪ n ⊕ v ≪ n = (w ⊕ v) ≪ n

   [LSL_LIMIT]  Theorem

      |- ∀w n. dimindex (:α) ≤ n ⇒ (w ≪ n = 0w)

   [LSL_ONE]  Theorem

      |- ∀w. w ≪ 1 = w + w

   [LSL_UINT_MAX]  Theorem

      |- ∀n. UINT_MAXw ≪ n = n2w (dimword (:α) − 2 ** n)

   [LSR_ADD]  Theorem

      |- ∀w m n. w ⋙ m ⋙ n = w ⋙ (m + n)

   [LSR_BITWISE]  Theorem

      |- (∀n v w. w ⋙ n && v ⋙ n = (w && v) ⋙ n) ∧
         (∀n v w. w ⋙ n ‖ v ⋙ n = (w ‖ v) ⋙ n) ∧
         ∀n v w. w ⋙ n ⊕ v ⋙ n = (w ⊕ v) ⋙ n

   [LSR_LESS]  Theorem

      |- ∀m y. y ≠ 0w ∧ 0 < m ⇒ w2n (y ⋙ m) < w2n y

   [LSR_LIMIT]  Theorem

      |- ∀w n. dimindex (:α) ≤ n ⇒ (w ⋙ n = 0w)

   [MOD_2EXP_DIMINDEX]  Theorem

      |- ∀n. n MOD dimword (:α) = MOD_2EXP (dimindex (:α)) n

   [MOD_COMPLEMENT]  Theorem

      |- ∀n q a.
           0 < n ∧ 0 < q ∧ a < q * n ⇒
           ((q * n − a) MOD n = (n − a MOD n) MOD n)

   [MOD_DIMINDEX]  Theorem

      |- ∀n. n MOD dimword (:α) = BITS (dimindex (:α) − 1) 0 n

   [NOT_0w]  Theorem

      |- ∀w. w ≠ 0w ⇒ ∃i. i < dimindex (:α) ∧ w ' i

   [NOT_FINITE_IMP_dimword_2]  Theorem

      |- INFINITE 𝕌(:α) ⇒ (dimword (:α) = 2)

   [NOT_INT_MIN_ZERO]  Theorem

      |- INT_MINw ≠ 0w

   [NOT_UINTMAXw]  Theorem

      |- ∀w. w ≠ UINT_MAXw ⇒ ∃i. i < dimindex (:α) ∧ ¬w ' i

   [NUMERAL_LESS_THM]  Theorem

      |- (∀m n.
            m < NUMERAL (BIT1 n) ⇔
            (m = NUMERAL (BIT1 n) − 1) ∨ m < NUMERAL (BIT1 n) − 1) ∧
         ∀m n.
           m < NUMERAL (BIT2 n) ⇔
           (m = NUMERAL (BIT1 n)) ∨ m < NUMERAL (BIT1 n)

   [ONE_LT_dimword]  Theorem

      |- 1 < dimword (:α)

   [ROL_ADD]  Theorem

      |- ∀w m n. w ⇆ m ⇆ n = w ⇆ (m + n)

   [ROL_BITWISE]  Theorem

      |- (∀n v w. w ⇆ n && v ⇆ n = (w && v) ⇆ n) ∧
         (∀n v w. w ⇆ n ‖ v ⇆ n = (w ‖ v) ⇆ n) ∧
         ∀n v w. w ⇆ n ⊕ v ⇆ n = (w ⊕ v) ⇆ n

   [ROL_MOD]  Theorem

      |- ∀w n. w ⇆ (n MOD dimindex (:α)) = w ⇆ n

   [ROR_ADD]  Theorem

      |- ∀w m n. w ⇄ m ⇄ n = w ⇄ (m + n)

   [ROR_BITWISE]  Theorem

      |- (∀n v w. w ⇄ n && v ⇄ n = (w && v) ⇄ n) ∧
         (∀n v w. w ⇄ n ‖ v ⇄ n = (w ‖ v) ⇄ n) ∧
         ∀n v w. w ⇄ n ⊕ v ⇄ n = (w ⊕ v) ⇄ n

   [ROR_CYCLE]  Theorem

      |- ∀w n. w ⇄ (n * dimindex (:α)) = w

   [ROR_MOD]  Theorem

      |- ∀w n. w ⇄ (n MOD dimindex (:α)) = w ⇄ n

   [ROR_ROL]  Theorem

      |- ∀w n. (w ⇄ n ⇆ n = w) ∧ (w ⇆ n ⇄ n = w)

   [ROR_UINT_MAX]  Theorem

      |- ∀n. UINT_MAXw ⇄ n = UINT_MAXw

   [SHIFT_1_SUB_1]  Theorem

      |- ∀i n. i < dimindex (:α) ⇒ ((1w ≪ n − 1w) ' i ⇔ i < n)

   [SHIFT_ZERO]  Theorem

      |- (∀a. a ≪ 0 = a) ∧ (∀a. a ≫ 0 = a) ∧ (∀a. a ⋙ 0 = a) ∧
         (∀a. a ⇆ 0 = a) ∧ ∀a. a ⇄ 0 = a

   [SUC_WORD_PRED]  Theorem

      |- ∀x. x ≠ 0w ⇒ (SUC (w2n (x − 1w)) = w2n x)

   [TWO_COMP_NEG]  Theorem

      |- ∀a.
           word_msb a ⇒
           if (dimindex (:α) − 1 = 0) ∨ (a = INT_MINw) then word_msb (-a)
           else ¬word_msb (-a)

   [TWO_COMP_POS]  Theorem

      |- ∀a. ¬word_msb a ⇒ (a = 0w) ∨ word_msb (-a)

   [TWO_COMP_POS_NEG]  Theorem

      |- ∀a.
           ¬((dimindex (:α) − 1 = 0) ∨ (a = 0w) ∨ (a = INT_MINw)) ⇒
           (¬word_msb a ⇔ word_msb (-a))

   [WORD_0_LS]  Theorem

      |- ∀w. 0w ≤₊ w

   [WORD_0_POS]  Theorem

      |- ¬word_msb 0w

   [WORD_2COMP_LSL]  Theorem

      |- ∀n a. -a ≪ n = -(a ≪ n)

   [WORD_ADD_0]  Theorem

      |- (∀w. w + 0w = w) ∧ ∀w. 0w + w = w

   [WORD_ADD_ASSOC]  Theorem

      |- ∀v w x. v + (w + x) = v + w + x

   [WORD_ADD_BIT]  Theorem

      |- ∀n a b.
           n < dimindex (:α) ⇒
           ((a + b) ' n ⇔
            if n = 0 then a ' 0 ⇎ b ' 0
            else if ((n − 1 -- 0) a + (n − 1 -- 0) b) ' n then
              a ' n ⇔ b ' n
            else a ' n ⇎ b ' n)

   [WORD_ADD_BIT0]  Theorem

      |- ∀a b. (a + b) ' 0 ⇔ (a ' 0 ⇎ b ' 0)

   [WORD_ADD_COMM]  Theorem

      |- ∀v w. v + w = w + v

   [WORD_ADD_EQ_SUB]  Theorem

      |- ∀v w x. (v + w = x) ⇔ (v = x − w)

   [WORD_ADD_INV_0_EQ]  Theorem

      |- ∀v w. (v + w = v) ⇔ (w = 0w)

   [WORD_ADD_LEFT_LO]  Theorem

      |- ∀b c a.
           a + b <₊ c ⇔
           if b ≤₊ c then
             (let x = n2w (w2n c − w2n b) in a <₊ x ∨ b ≠ 0w ∧ -c + x ≤₊ a)
           else -b ≤₊ a ∧ a <₊ -b + c

   [WORD_ADD_LEFT_LO2]  Theorem

      |- ∀c a. c + a <₊ a ⇔ a ≠ 0w ∧ (c ≠ 0w ∧ -c <₊ a ∨ (a = -c))

   [WORD_ADD_LEFT_LS]  Theorem

      |- ∀b c a.
           a + b ≤₊ c ⇔
           if b ≤₊ c then
             (let x = n2w (w2n c − w2n b) in a ≤₊ x ∨ b ≠ 0w ∧ -c + x ≤₊ a)
           else -b ≤₊ a ∧ a ≤₊ -b + c

   [WORD_ADD_LEFT_LS2]  Theorem

      |- ∀c a. c + a ≤₊ a ⇔ (c = 0w) ∨ a ≠ 0w ∧ (-c <₊ a ∨ (a = -c))

   [WORD_ADD_LID_UNIQ]  Theorem

      |- ∀v w. (v + w = w) ⇔ (v = 0w)

   [WORD_ADD_LINV]  Theorem

      |- ∀w. -w + w = 0w

   [WORD_ADD_LSL]  Theorem

      |- ∀n a b. (a + b) ≪ n = a ≪ n + b ≪ n

   [WORD_ADD_OR]  Theorem

      |- ∀a b. (a && b = 0w) ⇒ (a + b = a ‖ b)

   [WORD_ADD_RID_UNIQ]  Theorem

      |- ∀v w. (v + w = v) ⇔ (w = 0w)

   [WORD_ADD_RIGHT_LO]  Theorem

      |- ∀c a b.
           a <₊ b + c ⇔
           if c ≤₊ a then
             (let x = n2w (w2n a − w2n c)
              in
                x <₊ b ∧ ((c = 0w) ∨ b <₊ -a + x))
           else b <₊ -c ∨ -c + a <₊ b

   [WORD_ADD_RIGHT_LO2]  Theorem

      |- ∀c a. a <₊ c + a ⇔ c ≠ 0w ∧ ((a = 0w) ∨ a <₊ -c)

   [WORD_ADD_RIGHT_LS]  Theorem

      |- ∀c a b.
           a ≤₊ b + c ⇔
           if c ≤₊ a then
             (let x = n2w (w2n a − w2n c)
              in
                x ≤₊ b ∧ ((c = 0w) ∨ b <₊ -a + x))
           else b <₊ -c ∨ -c + a ≤₊ b

   [WORD_ADD_RIGHT_LS2]  Theorem

      |- ∀c a. a ≤₊ c + a ⇔ (a = 0w) ∨ (c = 0w) ∨ a <₊ -c

   [WORD_ADD_RINV]  Theorem

      |- ∀w. w + -w = 0w

   [WORD_ADD_SUB]  Theorem

      |- ∀v w. v + w − w = v

   [WORD_ADD_SUB2]  Theorem

      |- ∀v w. w + v − w = v

   [WORD_ADD_SUB3]  Theorem

      |- ∀v x. v − (v + x) = -x

   [WORD_ADD_SUB_ASSOC]  Theorem

      |- ∀v w x. v + w − x = v + (w − x)

   [WORD_ADD_SUB_SYM]  Theorem

      |- ∀v w x. v + w − x = v − x + w

   [WORD_ADD_XOR]  Theorem

      |- ∀a b. (a && b = 0w) ⇒ (a + b = a ⊕ b)

   [WORD_ALL_BITS]  Theorem

      |- ∀w h. dimindex (:α) − 1 ≤ h ⇒ ((h -- 0) w = w)

   [WORD_AND_ABSORD]  Theorem

      |- ∀a b. a ‖ a && b = a

   [WORD_AND_ASSOC]  Theorem

      |- ∀a b c. (a && b) && c = a && b && c

   [WORD_AND_CLAUSES]  Theorem

      |- ∀a.
           (UINT_MAXw && a = a) ∧ (a && UINT_MAXw = a) ∧ (0w && a = 0w) ∧
           (a && 0w = 0w) ∧ (a && a = a)

   [WORD_AND_COMM]  Theorem

      |- ∀a b. a && b = b && a

   [WORD_AND_COMP]  Theorem

      |- ∀a. a && ¬a = 0w

   [WORD_AND_EXP_SUB1]  Theorem

      |- ∀m n. n2w n && n2w (2 ** m − 1) = n2w (n MOD 2 ** m)

   [WORD_AND_IDEM]  Theorem

      |- ∀a. a && a = a

   [WORD_BITS_COMP_THM]  Theorem

      |- ∀h1 l1 h2 l2 w.
           (h2 -- l2) ((h1 -- l1) w) = (MIN h1 (h2 + l1) -- l2 + l1) w

   [WORD_BITS_EXTRACT]  Theorem

      |- ∀h l w. (h -- l) w = (h >< l) w

   [WORD_BITS_LSL]  Theorem

      |- ∀h l n w.
           h < dimindex (:α) ⇒
           ((h -- l) (w ≪ n) =
            if n ≤ h then (h − n -- l − n) w ≪ (n − l) else 0w)

   [WORD_BITS_LSR]  Theorem

      |- ∀h l w n. (h -- l) w ⋙ n = (h -- l + n) w

   [WORD_BITS_LT]  Theorem

      |- ∀h l w. w2n ((h -- l) w) < 2 ** (SUC h − l)

   [WORD_BITS_MIN_HIGH]  Theorem

      |- ∀w h l.
           dimindex (:α) − 1 < h ⇒
           ((h -- l) w = (dimindex (:α) − 1 -- l) w)

   [WORD_BITS_OVER_BITWISE]  Theorem

      |- (∀h l v w. (h -- l) v && (h -- l) w = (h -- l) (v && w)) ∧
         (∀h l v w. (h -- l) v ‖ (h -- l) w = (h -- l) (v ‖ w)) ∧
         ∀h l v w. (h -- l) v ⊕ (h -- l) w = (h -- l) (v ⊕ w)

   [WORD_BITS_SLICE_THM]  Theorem

      |- ∀h l w. (h -- l) ((h '' l) w) = (h -- l) w

   [WORD_BITS_ZERO]  Theorem

      |- ∀h l w. h < l ⇒ ((h -- l) w = 0w)

   [WORD_BITS_ZERO2]  Theorem

      |- ∀h l. (h -- l) 0w = 0w

   [WORD_BITS_ZERO3]  Theorem

      |- ∀h l w. dimindex (:α) ≤ l ⇒ ((h -- l) w = 0w)

   [WORD_BIT_BITS]  Theorem

      |- ∀b w. word_bit b w ⇔ ((b -- b) w = 1w)

   [WORD_DE_MORGAN_THM]  Theorem

      |- ∀a b. (¬(a && b) = ¬a ‖ ¬b) ∧ (¬(a ‖ b) = ¬a && ¬b)

   [WORD_DIVISION]  Theorem

      |- ∀w.
           w ≠ 0w ⇒ ∀v. (v = v // w * w + word_mod v w) ∧ word_mod v w <₊ w

   [WORD_DIV_LSR]  Theorem

      |- ∀m n. n < dimindex (:α) ⇒ (m ⋙ n = m // n2w (2 ** n))

   [WORD_EQ]  Theorem

      |- ∀v w.
           (∀x. x < dimindex (:α) ⇒ (word_bit x v ⇔ word_bit x w)) ⇔
           (v = w)

   [WORD_EQ_ADD_LCANCEL]  Theorem

      |- ∀v w x. (v + w = v + x) ⇔ (w = x)

   [WORD_EQ_ADD_RCANCEL]  Theorem

      |- ∀v w x. (v + w = x + w) ⇔ (v = x)

   [WORD_EQ_NEG]  Theorem

      |- ∀v w. (-v = -w) ⇔ (v = w)

   [WORD_EQ_SUB_LADD]  Theorem

      |- ∀v w x. (v = w − x) ⇔ (v + x = w)

   [WORD_EQ_SUB_RADD]  Theorem

      |- ∀v w x. (v − w = x) ⇔ (v = x + w)

   [WORD_EQ_SUB_ZERO]  Theorem

      |- ∀w v. (v − w = 0w) ⇔ (v = w)

   [WORD_EXTRACT_BITS_COMP]  Theorem

      |- ∀n l k j h. (j >< k) ((h -- l) n) = (MIN h (j + l) >< k + l) n

   [WORD_EXTRACT_COMP_THM]  Theorem

      |- ∀w h l m n.
           (h >< l) ((m >< n) w) =
           (MIN m
              (MIN (h + n)
                 (MIN (dimindex (:γ) − 1) (dimindex (:β) + n − 1))) ><
            l + n) w

   [WORD_EXTRACT_ID]  Theorem

      |- ∀w h. w2n w < 2 ** SUC h ⇒ ((h >< 0) w = w)

   [WORD_EXTRACT_LSL]  Theorem

      |- ∀h l n w.
           h < dimindex (:α) ⇒
           ((h >< l) (w ≪ n) =
            if n ≤ h then (h − n >< l − n) w ≪ (n − l) else 0w)

   [WORD_EXTRACT_LSL2]  Theorem

      |- ∀h l n w.
           dimindex (:β) + l ≤ h + n ⇒
           ((h >< l) w ≪ n = (dimindex (:β) + l − (n + 1) >< l) w ≪ n)

   [WORD_EXTRACT_LT]  Theorem

      |- ∀h l w. w2n ((h >< l) w) < 2 ** (SUC h − l)

   [WORD_EXTRACT_MIN_HIGH]  Theorem

      |- (∀h l w.
            dimindex (:α) ≤ dimindex (:β) + l ∧ dimindex (:α) ≤ h ⇒
            ((h >< l) w = (dimindex (:α) − 1 >< l) w)) ∧
         ∀h l w.
           dimindex (:β) + l < dimindex (:α) ∧ dimindex (:β) + l ≤ h ⇒
           ((h >< l) w = (dimindex (:β) + l − 1 >< l) w)

   [WORD_EXTRACT_OVER_ADD]  Theorem

      |- ∀a b h.
           dimindex (:β) − 1 ≤ h ∧ dimindex (:β) ≤ dimindex (:α) ⇒
           ((h >< 0) (a + b) = (h >< 0) a + (h >< 0) b)

   [WORD_EXTRACT_OVER_ADD2]  Theorem

      |- ∀a b h.
           h < dimindex (:α) ⇒
           ((h >< 0) ((h >< 0) a + (h >< 0) b) = (h >< 0) (a + b))

   [WORD_EXTRACT_OVER_BITWISE]  Theorem

      |- (∀h l v w. (h >< l) v && (h >< l) w = (h >< l) (v && w)) ∧
         (∀h l v w. (h >< l) v ‖ (h >< l) w = (h >< l) (v ‖ w)) ∧
         ∀h l v w. (h >< l) v ⊕ (h >< l) w = (h >< l) (v ⊕ w)

   [WORD_EXTRACT_OVER_MUL]  Theorem

      |- ∀a b h.
           dimindex (:β) − 1 ≤ h ∧ dimindex (:β) ≤ dimindex (:α) ⇒
           ((h >< 0) (a * b) = (h >< 0) a * (h >< 0) b)

   [WORD_EXTRACT_OVER_MUL2]  Theorem

      |- ∀a b h.
           h < dimindex (:α) ⇒
           ((h >< 0) ((h >< 0) a * (h >< 0) b) = (h >< 0) (a * b))

   [WORD_EXTRACT_ZERO]  Theorem

      |- ∀h l w. h < l ⇒ ((h >< l) w = 0w)

   [WORD_EXTRACT_ZERO2]  Theorem

      |- ∀h l. (h >< l) 0w = 0w

   [WORD_EXTRACT_ZERO3]  Theorem

      |- ∀h l w. dimindex (:α) ≤ l ⇒ ((h >< l) w = 0w)

   [WORD_FINITE]  Theorem

      |- ∀s. FINITE s

   [WORD_GE]  Theorem

      |- ∀a b.
           a ≥ b ⇔
           (word_msb b ⇔ word_msb a) ∧ w2n a ≥ w2n b ∨
           word_msb b ∧ ¬word_msb a

   [WORD_GREATER]  Theorem

      |- ∀a b. a > b ⇔ b < a

   [WORD_GREATER_EQ]  Theorem

      |- ∀a b. a ≥ b ⇔ b ≤ a

   [WORD_GREATER_OR_EQ]  Theorem

      |- ∀a b. a ≥ b ⇔ a > b ∨ (a = b)

   [WORD_GT]  Theorem

      |- ∀a b.
           a > b ⇔
           (word_msb b ⇔ word_msb a) ∧ w2n a > w2n b ∨
           word_msb b ∧ ¬word_msb a

   [WORD_HI]  Theorem

      |- ∀a b. a >₊ b ⇔ w2n a > w2n b

   [WORD_HIGHER]  Theorem

      |- ∀a b. a >₊ b ⇔ b <₊ a

   [WORD_HIGHER_EQ]  Theorem

      |- ∀a b. a ≥₊ b ⇔ b ≤₊ a

   [WORD_HIGHER_OR_EQ]  Theorem

      |- ∀a b. a ≥₊ b ⇔ a >₊ b ∨ (a = b)

   [WORD_HS]  Theorem

      |- ∀a b. a ≥₊ b ⇔ w2n a ≥ w2n b

   [WORD_H_POS]  Theorem

      |- ¬word_msb INT_MAXw

   [WORD_H_WORD_L]  Theorem

      |- INT_MAXw = INT_MINw − 1w

   [WORD_INDUCT]  Theorem

      |- ∀P.
           P 0w ∧
           (∀n. SUC n < dimword (:α) ⇒ P (n2w n) ⇒ P (n2w (SUC n))) ⇒
           ∀x. P x

   [WORD_LCANCEL_SUB]  Theorem

      |- ∀v w x. (v − w = x − w) ⇔ (v = x)

   [WORD_LE]  Theorem

      |- ∀a b.
           a ≤ b ⇔
           (word_msb a ⇔ word_msb b) ∧ w2n a ≤ w2n b ∨
           word_msb a ∧ ¬word_msb b

   [WORD_LEFT_ADD_DISTRIB]  Theorem

      |- ∀v w x. v * (w + x) = v * w + v * x

   [WORD_LEFT_AND_OVER_OR]  Theorem

      |- ∀a b c. a && (b ‖ c) = a && b ‖ a && c

   [WORD_LEFT_AND_OVER_XOR]  Theorem

      |- ∀a b c. a && (b ⊕ c) = a && b ⊕ a && c

   [WORD_LEFT_OR_OVER_AND]  Theorem

      |- ∀a b c. a ‖ b && c = (a ‖ b) && (a ‖ c)

   [WORD_LEFT_SUB_DISTRIB]  Theorem

      |- ∀v w x. v * (w − x) = v * w − v * x

   [WORD_LESS_0_word_T]  Theorem

      |- ¬(0w < -1w) ∧ ¬(0w ≤ -1w) ∧ -1w < 0w ∧ -1w ≤ 0w

   [WORD_LESS_ANTISYM]  Theorem

      |- ∀a b. ¬(a < b ∧ b < a)

   [WORD_LESS_CASES]  Theorem

      |- ∀a b. a < b ∨ b ≤ a

   [WORD_LESS_CASES_IMP]  Theorem

      |- ∀a b. ¬(a < b) ∧ a ≠ b ⇒ b < a

   [WORD_LESS_EQUAL_ANTISYM]  Theorem

      |- ∀a b. a ≤ b ∧ b ≤ a ⇒ (a = b)

   [WORD_LESS_EQ_ANTISYM]  Theorem

      |- ∀a b. ¬(a < b ∧ b ≤ a)

   [WORD_LESS_EQ_CASES]  Theorem

      |- ∀a b. a ≤ b ∨ b ≤ a

   [WORD_LESS_EQ_H]  Theorem

      |- ∀a. a ≤ INT_MAXw

   [WORD_LESS_EQ_LESS_TRANS]  Theorem

      |- ∀a b c. a ≤ b ∧ b < c ⇒ a < c

   [WORD_LESS_EQ_REFL]  Theorem

      |- ∀a. a ≤ a

   [WORD_LESS_EQ_TRANS]  Theorem

      |- ∀a b c. a ≤ b ∧ b ≤ c ⇒ a ≤ c

   [WORD_LESS_IMP_LESS_OR_EQ]  Theorem

      |- ∀a b. a < b ⇒ a ≤ b

   [WORD_LESS_LESS_CASES]  Theorem

      |- ∀a b. (a = b) ∨ a < b ∨ b < a

   [WORD_LESS_LESS_EQ_TRANS]  Theorem

      |- ∀a b c. a < b ∧ b ≤ c ⇒ a < c

   [WORD_LESS_NEG_LEFT]  Theorem

      |- ∀a b. -a <₊ b ⇔ b ≠ 0w ∧ ((a = 0w) ∨ -b <₊ a)

   [WORD_LESS_NEG_RIGHT]  Theorem

      |- ∀a b. a <₊ -b ⇔ b ≠ 0w ∧ ((a = 0w) ∨ b <₊ -a)

   [WORD_LESS_NOT_EQ]  Theorem

      |- ∀a b. a < b ⇒ a ≠ b

   [WORD_LESS_OR_EQ]  Theorem

      |- ∀a b. a ≤ b ⇔ a < b ∨ (a = b)

   [WORD_LESS_REFL]  Theorem

      |- ∀a. ¬(a < a)

   [WORD_LESS_TRANS]  Theorem

      |- ∀a b c. a < b ∧ b < c ⇒ a < c

   [WORD_LE_EQ_LS]  Theorem

      |- ∀x y. 0w ≤ x ∧ 0w ≤ y ⇒ (x ≤ y ⇔ x ≤₊ y)

   [WORD_LE_LS]  Theorem

      |- ∀a b.
           a ≤ b ⇔
           INT_MINw ≤₊ a ∧ (b <₊ INT_MINw ∨ a ≤₊ b) ∨
           a <₊ INT_MINw ∧ b <₊ INT_MINw ∧ a ≤₊ b

   [WORD_LITERAL_ADD]  Theorem

      |- (∀m n. -n2w m + -n2w n = -n2w (m + n)) ∧
         ∀m n. n2w m + -n2w n = if n ≤ m then n2w (m − n) else -n2w (n − m)

   [WORD_LITERAL_AND]  Theorem

      |- (∀n m.
            n2w n && n2w m =
            n2w (BITWISE (SUC (MIN (LOG2 n) (LOG2 m))) $/\ n m)) ∧
         (∀n m.
            n2w n && ¬n2w m =
            n2w (BITWISE (SUC (LOG2 n)) (λa b. a ∧ ¬b) n m)) ∧
         (∀n m.
            ¬n2w m && n2w n =
            n2w (BITWISE (SUC (LOG2 n)) (λa b. a ∧ ¬b) n m)) ∧
         ∀n m.
           ¬n2w n && ¬n2w m =
           ¬n2w (BITWISE (SUC (MAX (LOG2 n) (LOG2 m))) $\/ n m)

   [WORD_LITERAL_MULT]  Theorem

      |- (∀m n. n2w m * -n2w n = -n2w (m * n)) ∧
         ∀m n. -n2w m * -n2w n = n2w (m * n)

   [WORD_LITERAL_OR]  Theorem

      |- (∀n m.
            n2w n ‖ n2w m =
            n2w (BITWISE (SUC (MAX (LOG2 n) (LOG2 m))) $\/ n m)) ∧
         (∀n m.
            n2w n ‖ ¬n2w m =
            ¬n2w (BITWISE (SUC (LOG2 m)) (λa b. a ∧ ¬b) m n)) ∧
         (∀n m.
            ¬n2w m ‖ n2w n =
            ¬n2w (BITWISE (SUC (LOG2 m)) (λa b. a ∧ ¬b) m n)) ∧
         ∀n m.
           ¬n2w n ‖ ¬n2w m =
           ¬n2w (BITWISE (SUC (MIN (LOG2 n) (LOG2 m))) $/\ n m)

   [WORD_LITERAL_XOR]  Theorem

      |- ∀n m.
           n2w n ⊕ n2w m =
           n2w (BITWISE (SUC (MAX (LOG2 n) (LOG2 m))) (λx y. x ⇎ y) n m)

   [WORD_LO]  Theorem

      |- ∀a b. a <₊ b ⇔ w2n a < w2n b

   [WORD_LOWER_ANTISYM]  Theorem

      |- ∀a b. ¬(a <₊ b ∧ b <₊ a)

   [WORD_LOWER_CASES]  Theorem

      |- ∀a b. a <₊ b ∨ b ≤₊ a

   [WORD_LOWER_CASES_IMP]  Theorem

      |- ∀a b. ¬(a <₊ b) ∧ a ≠ b ⇒ b <₊ a

   [WORD_LOWER_EQUAL_ANTISYM]  Theorem

      |- ∀a b. a ≤₊ b ∧ b ≤₊ a ⇒ (a = b)

   [WORD_LOWER_EQ_ANTISYM]  Theorem

      |- ∀a b. ¬(a <₊ b ∧ b ≤₊ a)

   [WORD_LOWER_EQ_CASES]  Theorem

      |- ∀a b. a ≤₊ b ∨ b ≤₊ a

   [WORD_LOWER_EQ_LOWER_TRANS]  Theorem

      |- ∀a b c. a ≤₊ b ∧ b <₊ c ⇒ a <₊ c

   [WORD_LOWER_EQ_REFL]  Theorem

      |- ∀a. a ≤₊ a

   [WORD_LOWER_EQ_TRANS]  Theorem

      |- ∀a b c. a ≤₊ b ∧ b ≤₊ c ⇒ a ≤₊ c

   [WORD_LOWER_IMP_LOWER_OR_EQ]  Theorem

      |- ∀a b. a <₊ b ⇒ a ≤₊ b

   [WORD_LOWER_LOWER_CASES]  Theorem

      |- ∀a b. (a = b) ∨ a <₊ b ∨ b <₊ a

   [WORD_LOWER_LOWER_EQ_TRANS]  Theorem

      |- ∀a b c. a <₊ b ∧ b ≤₊ c ⇒ a <₊ c

   [WORD_LOWER_NOT_EQ]  Theorem

      |- ∀a b. a <₊ b ⇒ a ≠ b

   [WORD_LOWER_OR_EQ]  Theorem

      |- ∀a b. a ≤₊ b ⇔ a <₊ b ∨ (a = b)

   [WORD_LOWER_REFL]  Theorem

      |- ∀a. ¬(a <₊ a)

   [WORD_LOWER_TRANS]  Theorem

      |- ∀a b c. a <₊ b ∧ b <₊ c ⇒ a <₊ c

   [WORD_LO_word_0]  Theorem

      |- (∀n. 0w <₊ n ⇔ n ≠ 0w) ∧ ∀n. ¬(n <₊ 0w)

   [WORD_LO_word_T]  Theorem

      |- (∀n. ¬(-1w <₊ n)) ∧ ∀n. n <₊ -1w ⇔ n ≠ -1w

   [WORD_LS]  Theorem

      |- ∀a b. a ≤₊ b ⇔ w2n a ≤ w2n b

   [WORD_LS_T]  Theorem

      |- ∀w. w ≤₊ UINT_MAXw

   [WORD_LS_word_0]  Theorem

      |- ∀n. n ≤₊ 0w ⇔ (n = 0w)

   [WORD_LS_word_T]  Theorem

      |- (∀n. -1w ≤₊ n ⇔ (n = -1w)) ∧ ∀n. n ≤₊ -1w

   [WORD_LT]  Theorem

      |- ∀a b.
           a < b ⇔
           (word_msb a ⇔ word_msb b) ∧ w2n a < w2n b ∨
           word_msb a ∧ ¬word_msb b

   [WORD_LT_EQ_LO]  Theorem

      |- ∀x y. 0w ≤ x ∧ 0w ≤ y ⇒ (x < y ⇔ x <₊ y)

   [WORD_LT_LO]  Theorem

      |- ∀a b.
           a < b ⇔
           INT_MINw ≤₊ a ∧ (b <₊ INT_MINw ∨ a <₊ b) ∨
           a <₊ INT_MINw ∧ b <₊ INT_MINw ∧ a <₊ b

   [WORD_LT_SUB_UPPER]  Theorem

      |- ∀x y. 0w < y ∧ y < x ⇒ x − y < x

   [WORD_L_LESS_EQ]  Theorem

      |- ∀a. INT_MINw ≤ a

   [WORD_L_LESS_H]  Theorem

      |- INT_MINw < INT_MAXw

   [WORD_L_NEG]  Theorem

      |- word_msb INT_MINw

   [WORD_L_PLUS_H]  Theorem

      |- INT_MINw + INT_MAXw = UINT_MAXw

   [WORD_MODIFY_BIT]  Theorem

      |- ∀f w i. i < dimindex (:α) ⇒ (word_modify f w ' i ⇔ f i (w ' i))

   [WORD_MOD_1]  Theorem

      |- ∀m. word_mod m 1w = 0w

   [WORD_MOD_POW2]  Theorem

      |- ∀m v.
           v < dimindex (:α) − 1 ⇒
           (word_mod m (n2w (2 ** SUC v)) = (v -- 0) m)

   [WORD_MSB_1COMP]  Theorem

      |- ∀w. word_msb (¬w) ⇔ ¬word_msb w

   [WORD_MSB_INT_MIN_LS]  Theorem

      |- ∀a. word_msb a ⇔ INT_MINw ≤₊ a

   [WORD_MULT_ASSOC]  Theorem

      |- ∀v w x. v * (w * x) = v * w * x

   [WORD_MULT_CLAUSES]  Theorem

      |- ∀v w.
           (0w * v = 0w) ∧ (v * 0w = 0w) ∧ (1w * v = v) ∧ (v * 1w = v) ∧
           ((v + 1w) * w = v * w + w) ∧ (v * (w + 1w) = v + v * w)

   [WORD_MULT_COMM]  Theorem

      |- ∀v w. v * w = w * v

   [WORD_MULT_SUC]  Theorem

      |- ∀v n. v * n2w (n + 1) = v * n2w n + v

   [WORD_MUL_LSL]  Theorem

      |- ∀a n. a ≪ n = n2w (2 ** n) * a

   [WORD_NAND_NOT_AND]  Theorem

      |- ∀a b. a ~&& b = ¬(a && b)

   [WORD_NEG]  Theorem

      |- ∀w. -w = ¬w + 1w

   [WORD_NEG_0]  Theorem

      |- -0w = 0w

   [WORD_NEG_1]  Theorem

      |- -1w = UINT_MAXw

   [WORD_NEG_1_T]  Theorem

      |- ∀i. i < dimindex (:α) ⇒ (-1w) ' i

   [WORD_NEG_ADD]  Theorem

      |- ∀v w. -(v + w) = -v + -w

   [WORD_NEG_EQ]  Theorem

      |- ∀w v. (-v = w) ⇔ (v = -w)

   [WORD_NEG_EQ_0]  Theorem

      |- (-v = 0w) ⇔ (v = 0w)

   [WORD_NEG_L]  Theorem

      |- -INT_MINw = INT_MINw

   [WORD_NEG_LMUL]  Theorem

      |- ∀v w. -(v * w) = -v * w

   [WORD_NEG_MUL]  Theorem

      |- ∀w. -w = -1w * w

   [WORD_NEG_NEG]  Theorem

      |- ∀w. - -w = w

   [WORD_NEG_RMUL]  Theorem

      |- ∀v w. -(v * w) = v * -w

   [WORD_NEG_SUB]  Theorem

      |- ∀w v. -(v − w) = w − v

   [WORD_NEG_T]  Theorem

      |- -UINT_MAXw = 1w

   [WORD_NOR_NOT_OR]  Theorem

      |- ∀a b. a ~|| b = ¬(a ‖ b)

   [WORD_NOT]  Theorem

      |- ∀w. ¬w = -w − 1w

   [WORD_NOT_0]  Theorem

      |- ¬0w = UINT_MAXw

   [WORD_NOT_GREATER]  Theorem

      |- ∀a b. ¬(a > b) ⇔ a ≤ b

   [WORD_NOT_HIGHER]  Theorem

      |- ∀a b. ¬(a >₊ b) ⇔ a ≤₊ b

   [WORD_NOT_LESS]  Theorem

      |- ∀a b. ¬(a < b) ⇔ b ≤ a

   [WORD_NOT_LESS_EQ]  Theorem

      |- ∀a b. (a = b) ⇒ ¬(a < b)

   [WORD_NOT_LESS_EQUAL]  Theorem

      |- ∀a b. ¬(a ≤ b) ⇔ b < a

   [WORD_NOT_LOWER]  Theorem

      |- ∀a b. ¬(a <₊ b) ⇔ b ≤₊ a

   [WORD_NOT_LOWER_EQ]  Theorem

      |- ∀a b. (a = b) ⇒ ¬(a <₊ b)

   [WORD_NOT_LOWER_EQUAL]  Theorem

      |- ∀a b. ¬(a ≤₊ b) ⇔ b <₊ a

   [WORD_NOT_NOT]  Theorem

      |- ∀a. ¬ ¬a = a

   [WORD_NOT_T]  Theorem

      |- ¬UINT_MAXw = 0w

   [WORD_NOT_XOR]  Theorem

      |- ∀a b.
           (¬a ⊕ ¬b = a ⊕ b) ∧ (a ⊕ ¬b = ¬(a ⊕ b)) ∧ (¬a ⊕ b = ¬(a ⊕ b))

   [WORD_OR_ABSORB]  Theorem

      |- ∀a b. a && (a ‖ b) = a

   [WORD_OR_ASSOC]  Theorem

      |- ∀a b c. (a ‖ b) ‖ c = a ‖ b ‖ c

   [WORD_OR_CLAUSES]  Theorem

      |- ∀a.
           (UINT_MAXw ‖ a = UINT_MAXw) ∧ (a ‖ UINT_MAXw = UINT_MAXw) ∧
           (0w ‖ a = a) ∧ (a ‖ 0w = a) ∧ (a ‖ a = a)

   [WORD_OR_COMM]  Theorem

      |- ∀a b. a ‖ b = b ‖ a

   [WORD_OR_COMP]  Theorem

      |- ∀a. a ‖ ¬a = UINT_MAXw

   [WORD_OR_IDEM]  Theorem

      |- ∀a. a ‖ a = a

   [WORD_PRED_THM]  Theorem

      |- ∀m. m ≠ 0w ⇒ w2n (m − 1w) < w2n m

   [WORD_RCANCEL_SUB]  Theorem

      |- ∀v w x. (v − w = v − x) ⇔ (w = x)

   [WORD_RIGHT_ADD_DISTRIB]  Theorem

      |- ∀v w x. (v + w) * x = v * x + w * x

   [WORD_RIGHT_AND_OVER_OR]  Theorem

      |- ∀a b c. (a ‖ b) && c = a && c ‖ b && c

   [WORD_RIGHT_AND_OVER_XOR]  Theorem

      |- ∀a b c. (a ⊕ b) && c = a && c ⊕ b && c

   [WORD_RIGHT_OR_OVER_AND]  Theorem

      |- ∀a b c. a && b ‖ c = (a ‖ c) && (b ‖ c)

   [WORD_RIGHT_SUB_DISTRIB]  Theorem

      |- ∀v w x. (w − x) * v = w * v − x * v

   [WORD_SET_INDUCT]  Theorem

      |- ∀P. P ∅ ∧ (∀s. P s ⇒ ∀e. e ∉ s ⇒ P (e INSERT s)) ⇒ ∀s. P s

   [WORD_SLICE_BITS_THM]  Theorem

      |- ∀h w. (h '' 0) w = (h -- 0) w

   [WORD_SLICE_COMP_THM]  Theorem

      |- ∀h m' m l w.
           l ≤ m ∧ (m' = m + 1) ∧ m < h ⇒
           ((h '' m') w ‖ (m '' l) w = (h '' l) w)

   [WORD_SLICE_OVER_BITWISE]  Theorem

      |- (∀h l v w. (h '' l) v && (h '' l) w = (h '' l) (v && w)) ∧
         (∀h l v w. (h '' l) v ‖ (h '' l) w = (h '' l) (v ‖ w)) ∧
         ∀h l v w. (h '' l) v ⊕ (h '' l) w = (h '' l) (v ⊕ w)

   [WORD_SLICE_THM]  Theorem

      |- ∀h l w. (h '' l) w = (h -- l) w ≪ l

   [WORD_SLICE_ZERO]  Theorem

      |- ∀h l w. h < l ⇒ ((h '' l) w = 0w)

   [WORD_SLICE_ZERO2]  Theorem

      |- ∀l h. (h '' l) 0w = 0w

   [WORD_SUB]  Theorem

      |- ∀v w. -w + v = v − w

   [WORD_SUB_ADD]  Theorem

      |- ∀v w. v − w + w = v

   [WORD_SUB_ADD2]  Theorem

      |- ∀v w. v + (w − v) = w

   [WORD_SUB_INTRO]  Theorem

      |- (∀x y. -y + x = x − y) ∧ (∀x y. x + -y = x − y) ∧
         (∀x y z. -x * y + z = z − x * y) ∧
         (∀x y z. z + -x * y = z − x * y) ∧ (∀x. -1w * x = -x) ∧
         (∀x y z. z − -x * y = z + x * y) ∧
         ∀x y z. -x * y − z = -(x * y + z)

   [WORD_SUB_LE]  Theorem

      |- ∀x y. 0w ≤ y ∧ y ≤ x ⇒ 0w ≤ x − y ∧ x − y ≤ x

   [WORD_SUB_LNEG]  Theorem

      |- ∀v w. -v − w = -(v + w)

   [WORD_SUB_LT]  Theorem

      |- ∀x y. 0w < y ∧ y < x ⇒ 0w < x − y ∧ x − y < x

   [WORD_SUB_LZERO]  Theorem

      |- ∀w. 0w − w = -w

   [WORD_SUB_NEG]  Theorem

      |- ∀v w. -v − -w = w − v

   [WORD_SUB_PLUS]  Theorem

      |- ∀v w x. v − (w + x) = v − w − x

   [WORD_SUB_REFL]  Theorem

      |- ∀w. w − w = 0w

   [WORD_SUB_RNEG]  Theorem

      |- ∀v w. v − -w = v + w

   [WORD_SUB_RZERO]  Theorem

      |- ∀w. w − 0w = w

   [WORD_SUB_SUB]  Theorem

      |- ∀v w x. v − (w − x) = v + x − w

   [WORD_SUB_SUB2]  Theorem

      |- ∀v w. v − (v − w) = w

   [WORD_SUB_SUB3]  Theorem

      |- ∀w v. v − w − v = -w

   [WORD_SUB_TRIANGLE]  Theorem

      |- ∀v w x. v − w + (w − x) = v − x

   [WORD_SUM_ZERO]  Theorem

      |- ∀a b. (a + b = 0w) ⇔ (a = -b)

   [WORD_XNOR_NOT_XOR]  Theorem

      |- ∀a b. a ~?? b = ¬(a ⊕ b)

   [WORD_XOR]  Theorem

      |- ∀a b. a ⊕ b = a && ¬b ‖ b && ¬a

   [WORD_XOR_ASSOC]  Theorem

      |- ∀a b c. (a ⊕ b) ⊕ c = a ⊕ b ⊕ c

   [WORD_XOR_CLAUSES]  Theorem

      |- ∀a.
           (UINT_MAXw ⊕ a = ¬a) ∧ (a ⊕ UINT_MAXw = ¬a) ∧ (0w ⊕ a = a) ∧
           (a ⊕ 0w = a) ∧ (a ⊕ a = 0w)

   [WORD_XOR_COMM]  Theorem

      |- ∀a b. a ⊕ b = b ⊕ a

   [WORD_XOR_COMP]  Theorem

      |- ∀a. a ⊕ ¬a = UINT_MAXw

   [WORD_ZERO_LE]  Theorem

      |- ∀w. 0w ≤ w ⇔ w2n w < INT_MIN (:α)

   [WORD_w2w_EXTRACT]  Theorem

      |- ∀w. w2w w = (dimindex (:α) − 1 >< 0) w

   [WORD_w2w_OVER_ADD]  Theorem

      |- ∀a b. w2w (a + b) = (dimindex (:α) − 1 -- 0) (w2w a + w2w b)

   [WORD_w2w_OVER_BITWISE]  Theorem

      |- (∀v w. w2w v && w2w w = w2w (v && w)) ∧
         (∀v w. w2w v ‖ w2w w = w2w (v ‖ w)) ∧
         ∀v w. w2w v ⊕ w2w w = w2w (v ⊕ w)

   [WORD_w2w_OVER_MUL]  Theorem

      |- ∀a b. w2w (a * b) = (dimindex (:α) − 1 -- 0) (w2w a * w2w b)

   [ZERO_LE_INT_MAX]  Theorem

      |- 0 ≤ INT_MAX (:α)

   [ZERO_LO_INT_MIN]  Theorem

      |- 0w <₊ INT_MINw

   [ZERO_LT_INT_MAX]  Theorem

      |- 1 < dimindex (:α) ⇒ 0 < INT_MAX (:α)

   [ZERO_LT_INT_MIN]  Theorem

      |- 0 < INT_MIN (:α)

   [ZERO_LT_UINT_MAX]  Theorem

      |- 0 < UINT_MAX (:α)

   [ZERO_LT_dimword]  Theorem

      |- 0 < dimword (:α)

   [ZERO_SHIFT]  Theorem

      |- (∀n. 0w ≪ n = 0w) ∧ (∀n. 0w ≫ n = 0w) ∧ (∀n. 0w ⋙ n = 0w) ∧
         (∀n. 0w ⇆ n = 0w) ∧ ∀n. 0w ⇄ n = 0w

   [bit_count_is_zero]  Theorem

      |- ∀w. (bit_count w = 0) ⇔ (w = 0w)

   [bit_count_upto_0]  Theorem

      |- ∀w. bit_count_upto 0 w = 0

   [bit_count_upto_SUC]  Theorem

      |- ∀w n.
           bit_count_upto (SUC n) w =
           (if w ' n then 1 else 0) + bit_count_upto n w

   [bit_count_upto_is_zero]  Theorem

      |- ∀n w. (bit_count_upto n w = 0) ⇔ ∀i. i < n ⇒ ¬w ' i

   [bit_field_insert]  Theorem

      |- ∀h l a b.
           h < l + dimindex (:α) ⇒
           (bit_field_insert h l a b =
            (let mask = (h '' l) (-1w) in w2w a ≪ l && mask ‖ b && ¬mask))

   [dimindex_1]  Theorem

      |- dimindex (:unit) = 1

   [dimindex_10]  Theorem

      |- dimindex (:10) = 10

   [dimindex_11]  Theorem

      |- dimindex (:11) = 11

   [dimindex_12]  Theorem

      |- dimindex (:12) = 12

   [dimindex_128]  Theorem

      |- dimindex (:128) = 128

   [dimindex_16]  Theorem

      |- dimindex (:16) = 16

   [dimindex_1_cases]  Theorem

      |- ∀a. (dimindex (:α) = 1) ⇒ (a = 0w) ∨ (a = 1w)

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

   [dimindex_48]  Theorem

      |- dimindex (:48) = 48

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

   [dimindex_9]  Theorem

      |- dimindex (:9) = 9

   [dimindex_96]  Theorem

      |- dimindex (:96) = 96

   [dimindex_dimword_iso]  Theorem

      |- (dimindex (:α) = dimindex (:β)) ⇔ (dimword (:α) = dimword (:β))

   [dimindex_dimword_le_iso]  Theorem

      |- dimindex (:α) ≤ dimindex (:β) ⇔ dimword (:α) ≤ dimword (:β)

   [dimindex_dimword_lt_iso]  Theorem

      |- dimindex (:α) < dimindex (:β) ⇔ dimword (:α) < dimword (:β)

   [dimindex_int_max_iso]  Theorem

      |- (dimindex (:α) = dimindex (:β)) ⇔ (INT_MAX (:α) = INT_MAX (:β))

   [dimindex_int_max_le_iso]  Theorem

      |- dimindex (:α) ≤ dimindex (:β) ⇔ INT_MAX (:α) ≤ INT_MAX (:β)

   [dimindex_int_max_lt_iso]  Theorem

      |- dimindex (:α) < dimindex (:β) ⇔ INT_MAX (:α) < INT_MAX (:β)

   [dimindex_int_min_iso]  Theorem

      |- (dimindex (:α) = dimindex (:β)) ⇔ (INT_MIN (:α) = INT_MIN (:β))

   [dimindex_int_min_le_iso]  Theorem

      |- dimindex (:α) ≤ dimindex (:β) ⇔ INT_MIN (:α) ≤ INT_MIN (:β)

   [dimindex_int_min_lt_iso]  Theorem

      |- dimindex (:α) < dimindex (:β) ⇔ INT_MIN (:α) < INT_MIN (:β)

   [dimindex_lt_dimword]  Theorem

      |- dimindex (:α) < dimword (:α)

   [dimindex_uint_max_iso]  Theorem

      |- (dimindex (:α) = dimindex (:β)) ⇔ (UINT_MAX (:α) = UINT_MAX (:β))

   [dimindex_uint_max_le_iso]  Theorem

      |- dimindex (:α) ≤ dimindex (:β) ⇔ UINT_MAX (:α) ≤ UINT_MAX (:β)

   [dimindex_uint_max_lt_iso]  Theorem

      |- dimindex (:α) < dimindex (:β) ⇔ UINT_MAX (:α) < UINT_MAX (:β)

   [dimword_1]  Theorem

      |- dimword (:unit) = 2

   [dimword_10]  Theorem

      |- dimword (:10) = 1024

   [dimword_11]  Theorem

      |- dimword (:11) = 2048

   [dimword_12]  Theorem

      |- dimword (:12) = 4096

   [dimword_128]  Theorem

      |- dimword (:128) = 340282366920938463463374607431768211456

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

   [dimword_48]  Theorem

      |- dimword (:48) = 281474976710656

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

   [dimword_9]  Theorem

      |- dimword (:9) = 512

   [dimword_96]  Theorem

      |- dimword (:96) = 79228162514264337593543950336

   [dimword_IS_TWICE_INT_MIN]  Theorem

      |- dimword (:α) = 2 * INT_MIN (:α)

   [dimword_sub_int_min]  Theorem

      |- dimword (:α) − INT_MIN (:α) = INT_MIN (:α)

   [fcp_n2w]  Theorem

      |- ∀f. $FCP f = word_modify (λi b. f i) 0w

   [finite_1]  Theorem

      |- FINITE 𝕌(:unit)

   [finite_10]  Theorem

      |- FINITE 𝕌(:10)

   [finite_11]  Theorem

      |- FINITE 𝕌(:11)

   [finite_12]  Theorem

      |- FINITE 𝕌(:12)

   [finite_128]  Theorem

      |- FINITE 𝕌(:128)

   [finite_16]  Theorem

      |- FINITE 𝕌(:16)

   [finite_2]  Theorem

      |- FINITE 𝕌(:2)

   [finite_20]  Theorem

      |- FINITE 𝕌(:20)

   [finite_24]  Theorem

      |- FINITE 𝕌(:24)

   [finite_28]  Theorem

      |- FINITE 𝕌(:28)

   [finite_3]  Theorem

      |- FINITE 𝕌(:3)

   [finite_30]  Theorem

      |- FINITE 𝕌(:30)

   [finite_32]  Theorem

      |- FINITE 𝕌(:32)

   [finite_4]  Theorem

      |- FINITE 𝕌(:4)

   [finite_48]  Theorem

      |- FINITE 𝕌(:48)

   [finite_5]  Theorem

      |- FINITE 𝕌(:5)

   [finite_6]  Theorem

      |- FINITE 𝕌(:6)

   [finite_64]  Theorem

      |- FINITE 𝕌(:64)

   [finite_7]  Theorem

      |- FINITE 𝕌(:7)

   [finite_8]  Theorem

      |- FINITE 𝕌(:8)

   [finite_9]  Theorem

      |- FINITE 𝕌(:9)

   [finite_96]  Theorem

      |- FINITE 𝕌(:96)

   [foldl_reduce_and]  Theorem

      |- ∀w.
           reduce_and w =
           (let l =
                  GENLIST
                    (λi. (let n = dimindex (:α) − 1 − i in (n >< n) w))
                    (dimindex (:α))
            in
              FOLDL $&& (HD l) (TL l))

   [foldl_reduce_nand]  Theorem

      |- ∀w.
           reduce_nand w =
           (let l =
                  GENLIST
                    (λi. (let n = dimindex (:α) − 1 − i in (n >< n) w))
                    (dimindex (:α))
            in
              FOLDL $~&& (HD l) (TL l))

   [foldl_reduce_nor]  Theorem

      |- ∀w.
           reduce_nor w =
           (let l =
                  GENLIST
                    (λi. (let n = dimindex (:α) − 1 − i in (n >< n) w))
                    (dimindex (:α))
            in
              FOLDL $~|| (HD l) (TL l))

   [foldl_reduce_or]  Theorem

      |- ∀w.
           reduce_or w =
           (let l =
                  GENLIST
                    (λi. (let n = dimindex (:α) − 1 − i in (n >< n) w))
                    (dimindex (:α))
            in
              FOLDL $|| (HD l) (TL l))

   [foldl_reduce_xnor]  Theorem

      |- ∀w.
           reduce_xnor w =
           (let l =
                  GENLIST
                    (λi. (let n = dimindex (:α) − 1 − i in (n >< n) w))
                    (dimindex (:α))
            in
              FOLDL $~?? (HD l) (TL l))

   [foldl_reduce_xor]  Theorem

      |- ∀w.
           reduce_xor w =
           (let l =
                  GENLIST
                    (λi. (let n = dimindex (:α) − 1 − i in (n >< n) w))
                    (dimindex (:α))
            in
              FOLDL $?? (HD l) (TL l))

   [l2w_w2l]  Theorem

      |- ∀b w. 1 < b ⇒ (l2w b (w2l b w) = w)

   [lsr_1_word_T]  Theorem

      |- -1w ⋙ 1 = INT_MAXw

   [mod_dimindex]  Theorem

      |- ∀n. n MOD dimindex (:α) < dimword (:α)

   [n2w_11]  Theorem

      |- ∀m n. (n2w m = n2w n) ⇔ (m MOD dimword (:α) = n MOD dimword (:α))

   [n2w_BITS]  Theorem

      |- ∀h l n. h < dimindex (:α) ⇒ (n2w (BITS h l n) = (h -- l) (n2w n))

   [n2w_DIV]  Theorem

      |- ∀a n. a < dimword (:α) ⇒ (n2w (a DIV 2 ** n) = n2w a ⋙ n)

   [n2w_SUC]  Theorem

      |- ∀n. n2w (SUC n) = n2w n + 1w

   [n2w_dimword]  Theorem

      |- n2w (dimword (:α)) = 0w

   [n2w_itself_def]  Theorem

      |- n2w_itself (n,(:α)) = n2w n

   [n2w_itself_ind]  Theorem

      |- ∀P. (∀n. P (n,(:α))) ⇒ ∀v v1. P (v,v1)

   [n2w_mod]  Theorem

      |- ∀n. n2w (n MOD dimword (:α)) = n2w n

   [n2w_sub]  Theorem

      |- ∀a b. b ≤ a ⇒ (n2w (a − b) = n2w a − n2w b)

   [n2w_sub_eq_0]  Theorem

      |- ∀a b. a ≤ b ⇒ (n2w (a − b) = 0w)

   [n2w_w2n]  Theorem

      |- ∀w. n2w (w2n w) = w

   [ranged_word_nchotomy]  Theorem

      |- ∀w. ∃n. (w = n2w n) ∧ n < dimword (:α)

   [reduce_and]  Theorem

      |- ∀w. reduce_and w = if w = UINT_MAXw then 1w else 0w

   [reduce_or]  Theorem

      |- ∀w. reduce_or w = if w = 0w then 0w else 1w

   [s2w_w2s]  Theorem

      |- ∀c2n n2c b w.
           1 < b ∧ (∀x. x < b ⇒ (c2n (n2c x) = x)) ⇒
           (s2w b c2n (w2s b n2c w) = w)

   [saturate_add]  Theorem

      |- ∀a b.
           saturate_add a b =
           if UINT_MAXw − a ≤₊ b then UINT_MAXw else a + b

   [saturate_mul]  Theorem

      |- ∀a b.
           saturate_mul a b =
           if FINITE 𝕌(:α) ∧ w2w UINT_MAXw ≤₊ w2w a * w2w b then UINT_MAXw
           else a * b

   [saturate_sub]  Theorem

      |- ∀a b. saturate_sub a b = if a ≤₊ b then 0w else a − b

   [saturate_w2w]  Theorem

      |- ∀w.
           saturate_w2w w =
           if dimindex (:β) ≤ dimindex (:α) ∧ w2w UINT_MAXw ≤₊ w then
             UINT_MAXw
           else w2w w

   [saturate_w2w_n2w]  Theorem

      |- ∀n.
           saturate_w2w (n2w n) =
           (let m = n MOD dimword (:α)
            in
              if dimindex (:β) ≤ dimindex (:α) ∧ dimword (:β) ≤ m then
                UINT_MAXw
              else n2w m)

   [sw2sw]  Theorem

      |- ∀w i.
           i < dimindex (:β) ⇒
           (sw2sw w ' i ⇔
            if i < dimindex (:α) ∨ dimindex (:β) < dimindex (:α) then w ' i
            else word_msb w)

   [sw2sw_0]  Theorem

      |- sw2sw 0w = 0w

   [sw2sw_id]  Theorem

      |- ∀w. sw2sw w = w

   [sw2sw_sw2sw]  Theorem

      |- ∀w.
           sw2sw (sw2sw w) =
           if
             dimindex (:β) < dimindex (:α) ∧ dimindex (:β) < dimindex (:γ)
           then
             sw2sw (w2w w)
           else sw2sw w

   [sw2sw_w2w]  Theorem

      |- ∀w.
           sw2sw w =
           (if word_msb w then -1w ≪ dimindex (:α) else 0w) ‖ w2w w

   [sw2sw_w2w_add]  Theorem

      |- ∀w.
           sw2sw w =
           (if word_msb w then -1w ≪ dimindex (:α) else 0w) + w2w w

   [sw2sw_word_T]  Theorem

      |- sw2sw (-1w) = -1w

   [w2l_l2w]  Theorem

      |- ∀b l. w2l b (l2w b l) = n2l b (l2n b l MOD dimword (:α))

   [w2n_11]  Theorem

      |- ∀v w. (w2n v = w2n w) ⇔ (v = w)

   [w2n_11_lift]  Theorem

      |- ∀a b.
           dimindex (:α) ≤ dimindex (:γ) ∧ dimindex (:β) ≤ dimindex (:γ) ⇒
           ((w2n a = w2n b) ⇔ (w2w a = w2w b))

   [w2n_add]  Theorem

      |- ∀a b. ¬word_msb a ∧ ¬word_msb b ⇒ (w2n (a + b) = w2n a + w2n b)

   [w2n_eq_0]  Theorem

      |- ∀w. (w2n w = 0) ⇔ (w = 0w)

   [w2n_lsr]  Theorem

      |- ∀w m. w2n (w ⋙ m) = w2n w DIV 2 ** m

   [w2n_lt]  Theorem

      |- ∀w. w2n w < dimword (:α)

   [w2n_minus1]  Theorem

      |- w2n (-1w) = dimword (:α) − 1

   [w2n_n2w]  Theorem

      |- ∀n. w2n (n2w n) = n MOD dimword (:α)

   [w2n_w2w]  Theorem

      |- ∀w.
           w2n (w2w w) =
           if dimindex (:α) ≤ dimindex (:β) then w2n w
           else w2n ((dimindex (:β) − 1 -- 0) w)

   [w2n_w2w_le]  Theorem

      |- ∀w. w2n (w2w w) ≤ w2n w

   [w2s_s2w]  Theorem

      |- ∀b c2n n2c s.
           w2s b n2c (s2w b c2n s) =
           n2s b n2c (s2n b c2n s MOD dimword (:α))

   [w2w]  Theorem

      |- ∀w i. i < dimindex (:β) ⇒ (w2w w ' i ⇔ i < dimindex (:α) ∧ w ' i)

   [w2w_0]  Theorem

      |- w2w 0w = 0w

   [w2w_LSL]  Theorem

      |- ∀w n.
           w2w (w ≪ n) =
           if n < dimindex (:α) then
             w2w ((dimindex (:α) − 1 − n -- 0) w) ≪ n
           else 0w

   [w2w_eq_n2w]  Theorem

      |- ∀x y.
           dimindex (:α) ≤ dimindex (:β) ∧ y < dimword (:α) ⇒
           ((w2w x = n2w y) ⇔ (x = n2w y))

   [w2w_id]  Theorem

      |- ∀w. w2w w = w

   [w2w_lt]  Theorem

      |- ∀w. w2n (w2w w) < dimword (:α)

   [w2w_n2w]  Theorem

      |- ∀n.
           w2w (n2w n) =
           if dimindex (:β) ≤ dimindex (:α) then n2w n
           else n2w (BITS (dimindex (:α) − 1) 0 n)

   [w2w_w2w]  Theorem

      |- ∀w. w2w (w2w w) = w2w ((dimindex (:β) − 1 -- 0) w)

   [word_0]  Theorem

      |- ∀i. i < dimindex (:α) ⇒ ¬0w ' i

   [word_0_n2w]  Theorem

      |- w2n 0w = 0

   [word_1_n2w]  Theorem

      |- w2n 1w = 1

   [word_1comp_n2w]  Theorem

      |- ∀n. ¬n2w n = n2w (dimword (:α) − 1 − n MOD dimword (:α))

   [word_2comp_dimindex_1]  Theorem

      |- ∀w. (dimindex (:α) = 1) ⇒ (-w = w)

   [word_2comp_n2w]  Theorem

      |- ∀n. -n2w n = n2w (dimword (:α) − n MOD dimword (:α))

   [word_H]  Theorem

      |- ∀n. n < dimindex (:α) ⇒ (INT_MAXw ' n ⇔ n < dimindex (:α) − 1)

   [word_L]  Theorem

      |- ∀n. n < dimindex (:α) ⇒ (INT_MINw ' n ⇔ (n = dimindex (:α) − 1))

   [word_L2]  Theorem

      |- INT_MINw2 = if 1 < dimindex (:α) then 0w else INT_MINw

   [word_L2_MULT]  Theorem

      |- (INT_MINw2 * INT_MINw2 = INT_MINw2) ∧
         (INT_MINw * INT_MINw2 = INT_MINw2) ∧
         (∀n. n2w n * INT_MINw2 = if EVEN n then 0w else INT_MINw2) ∧
         ∀n. -n2w n * INT_MINw2 = if EVEN n then 0w else INT_MINw2

   [word_L_MULT]  Theorem

      |- ∀n. n2w n * INT_MINw = if EVEN n then 0w else INT_MINw

   [word_L_MULT_NEG]  Theorem

      |- ∀n. -n2w n * INT_MINw = if EVEN n then 0w else INT_MINw

   [word_T]  Theorem

      |- ∀i. i < dimindex (:α) ⇒ UINT_MAXw ' i

   [word_T_not_zero]  Theorem

      |- -1w ≠ 0w

   [word_abs]  Theorem

      |- ∀w.
           word_abs w = FCP i. ¬word_msb w ∧ w ' i ∨ word_msb w ∧ (-w) ' i

   [word_abs_diff]  Theorem

      |- ∀a b. word_abs (a − b) = word_abs (b − a)

   [word_abs_neg]  Theorem

      |- ∀w. word_abs (-w) = word_abs w

   [word_abs_word_abs]  Theorem

      |- ∀w. word_abs (word_abs w) = word_abs w

   [word_add_n2w]  Theorem

      |- ∀m n. n2w m + n2w n = n2w (m + n)

   [word_and_n2w]  Theorem

      |- ∀n m. n2w n && n2w m = n2w (BITWISE (dimindex (:α)) $/\ n m)

   [word_asr]  Theorem

      |- ∀w n.
           w ≫ n =
           if word_msb w then
             (dimindex (:α) − 1 '' dimindex (:α) − n) UINT_MAXw ‖ w ⋙ n
           else w ⋙ n

   [word_asr_n2w]  Theorem

      |- ∀n w.
           w ≫ n =
           if word_msb w then
             n2w
               (dimword (:α) −
                2 ** (dimindex (:α) − MIN n (dimindex (:α)))) ‖ w ⋙ n
           else w ⋙ n

   [word_bin_list]  Theorem

      |- word_from_bin_list o word_to_bin_list = I

   [word_bin_string]  Theorem

      |- word_from_bin_string o word_to_bin_string = I

   [word_bit]  Theorem

      |- ∀w b. b < dimindex (:α) ⇒ (w ' b ⇔ word_bit b w)

   [word_bit_0]  Theorem

      |- ∀h. ¬word_bit h 0w

   [word_bit_0_word_T]  Theorem

      |- word_bit 0 (-1w)

   [word_bit_n2w]  Theorem

      |- ∀b n. word_bit b (n2w n) ⇔ b ≤ dimindex (:α) − 1 ∧ BIT b n

   [word_bits_n2w]  Theorem

      |- ∀h l n.
           (h -- l) (n2w n) = n2w (BITS (MIN h (dimindex (:α) − 1)) l n)

   [word_bits_w2w]  Theorem

      |- ∀w h l.
           (h -- l) (w2w w) = w2w ((MIN h (dimindex (:β) − 1) -- l) w)

   [word_concat_0]  Theorem

      |- ∀x. FINITE 𝕌(:α) ∧ x < dimword (:β) ⇒ (0w @@ n2w x = n2w x)

   [word_concat_0_0]  Theorem

      |- 0w @@ 0w = 0w

   [word_concat_0_eq]  Theorem

      |- ∀x y.
           FINITE 𝕌(:α) ∧ dimindex (:β) ≤ dimindex (:γ) ∧
           y < dimword (:β) ⇒
           ((0w @@ x = n2w y) ⇔ (x = n2w y))

   [word_concat_word_T]  Theorem

      |- -1w @@ -1w = w2w (-1w)

   [word_dec_list]  Theorem

      |- word_from_dec_list o word_to_dec_list = I

   [word_dec_string]  Theorem

      |- word_from_dec_string o word_to_dec_string = I

   [word_div_1]  Theorem

      |- ∀v. v // 1w = v

   [word_eq_0]  Theorem

      |- ∀w. (w = 0w) ⇔ ∀i. i < dimindex (:α) ⇒ ¬w ' i

   [word_eq_n2w]  Theorem

      |- (∀m n. (n2w m = n2w n) ⇔ MOD_2EXP_EQ (dimindex (:α)) m n) ∧
         (∀n. (n2w n = -1w) ⇔ MOD_2EXP_MAX (dimindex (:α)) n) ∧
         ∀n. (-1w = n2w n) ⇔ MOD_2EXP_MAX (dimindex (:α)) n

   [word_extract_eq_n2w]  Theorem

      |- ∀x h y.
           dimindex (:α) ≤ dimindex (:β) ∧ dimindex (:α) − 1 ≤ h ∧
           y < dimword (:α) ⇒
           (((h >< 0) x = n2w y) ⇔ (x = n2w y))

   [word_extract_mask]  Theorem

      |- ∀h l a.
           (h >< l) a = if l ≤ h then a ⋙ l && 2w ≪ (h − l) − 1w else 0w

   [word_extract_n2w]  Theorem

      |- (h >< l) (n2w n) =
         if dimindex (:β) ≤ dimindex (:α) then
           n2w (BITS (MIN h (dimindex (:α) − 1)) l n)
         else
           n2w
             (BITS
                (MIN (MIN h (dimindex (:α) − 1)) (dimindex (:α) − 1 + l)) l
                n)

   [word_extract_w2w]  Theorem

      |- ∀w h l.
           dimindex (:α) ≤ dimindex (:β) ⇒ ((h >< l) (w2w w) = (h >< l) w)

   [word_ge_n2w]  Theorem

      |- ∀a b.
           n2w a ≥ n2w b ⇔
           (let sa = BIT (dimindex (:α) − 1) a and
                sb = BIT (dimindex (:α) − 1) b
            in
              (sa ⇔ sb) ∧ a MOD dimword (:α) ≥ b MOD dimword (:α) ∨
              ¬sa ∧ sb)

   [word_gt_n2w]  Theorem

      |- ∀a b.
           n2w a > n2w b ⇔
           (let sa = BIT (dimindex (:α) − 1) a and
                sb = BIT (dimindex (:α) − 1) b
            in
              (sa ⇔ sb) ∧ a MOD dimword (:α) > b MOD dimword (:α) ∨
              ¬sa ∧ sb)

   [word_hex_list]  Theorem

      |- word_from_hex_list o word_to_hex_list = I

   [word_hex_string]  Theorem

      |- word_from_hex_string o word_to_hex_string = I

   [word_hi_n2w]  Theorem

      |- ∀a b. n2w a >₊ n2w b ⇔ a MOD dimword (:α) > b MOD dimword (:α)

   [word_hs_n2w]  Theorem

      |- ∀a b. n2w a ≥₊ n2w b ⇔ a MOD dimword (:α) ≥ b MOD dimword (:α)

   [word_index]  Theorem

      |- ∀n i. i < dimindex (:α) ⇒ (n2w n ' i ⇔ BIT i n)

   [word_index_n2w]  Theorem

      |- ∀n i.
           n2w n ' i ⇔
           if i < dimindex (:α) then BIT i n
           else FAIL $' index too large (n2w n) i

   [word_join_0]  Theorem

      |- ∀a. word_join 0w a = w2w a

   [word_join_index]  Theorem

      |- ∀i a b.
           FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) ∧ i < dimindex (:α + β) ⇒
           (word_join a b ' i ⇔
            if i < dimindex (:β) then b ' i else a ' (i − dimindex (:β)))

   [word_join_word_T]  Theorem

      |- word_join (-1w) (-1w) = -1w

   [word_le_n2w]  Theorem

      |- ∀a b.
           n2w a ≤ n2w b ⇔
           (let sa = BIT (dimindex (:α) − 1) a and
                sb = BIT (dimindex (:α) − 1) b
            in
              (sa ⇔ sb) ∧ a MOD dimword (:α) ≤ b MOD dimword (:α) ∨
              sa ∧ ¬sb)

   [word_lo_n2w]  Theorem

      |- ∀a b. n2w a <₊ n2w b ⇔ a MOD dimword (:α) < b MOD dimword (:α)

   [word_log2_1]  Theorem

      |- word_log2 1w = 0w

   [word_log2_n2w]  Theorem

      |- ∀n. word_log2 (n2w n) = n2w (LOG2 (n MOD dimword (:α)))

   [word_ls_n2w]  Theorem

      |- ∀a b. n2w a ≤₊ n2w b ⇔ a MOD dimword (:α) ≤ b MOD dimword (:α)

   [word_lsb]  Theorem

      |- word_lsb = word_bit 0

   [word_lsb_n2w]  Theorem

      |- ∀n. word_lsb (n2w n) ⇔ ODD n

   [word_lsb_word_T]  Theorem

      |- word_lsb (-1w)

   [word_lsl_n2w]  Theorem

      |- ∀n m.
           n2w m ≪ n =
           if dimindex (:α) − 1 < n then 0w else n2w (m * 2 ** n)

   [word_lsr_n2w]  Theorem

      |- ∀w n. w ⋙ n = (dimindex (:α) − 1 -- n) w

   [word_lt_n2w]  Theorem

      |- ∀a b.
           n2w a < n2w b ⇔
           (let sa = BIT (dimindex (:α) − 1) a and
                sb = BIT (dimindex (:α) − 1) b
            in
              (sa ⇔ sb) ∧ a MOD dimword (:α) < b MOD dimword (:α) ∨
              sa ∧ ¬sb)

   [word_modify_n2w]  Theorem

      |- ∀f n. word_modify f (n2w n) = n2w (BIT_MODIFY (dimindex (:α)) f n)

   [word_msb]  Theorem

      |- word_msb = word_bit (dimindex (:α) − 1)

   [word_msb_n2w]  Theorem

      |- ∀n. word_msb (n2w n) ⇔ BIT (dimindex (:α) − 1) n

   [word_msb_n2w_numeric]  Theorem

      |- word_msb (n2w n) ⇔ INT_MIN (:α) ≤ n MOD dimword (:α)

   [word_msb_neg]  Theorem

      |- ∀w. word_msb w ⇔ w < 0w

   [word_msb_word_T]  Theorem

      |- word_msb (-1w)

   [word_mul_n2w]  Theorem

      |- ∀m n. n2w m * n2w n = n2w (m * n)

   [word_nand_n2w]  Theorem

      |- ∀n m.
           n2w n ~&& n2w m =
           n2w (BITWISE (dimindex (:α)) (λx y. ¬(x ∧ y)) n m)

   [word_nchotomy]  Theorem

      |- ∀w. ∃n. w = n2w n

   [word_nor_n2w]  Theorem

      |- ∀n m.
           n2w n ~|| n2w m =
           n2w (BITWISE (dimindex (:α)) (λx y. ¬(x ∨ y)) n m)

   [word_oct_list]  Theorem

      |- word_from_oct_list o word_to_oct_list = I

   [word_oct_string]  Theorem

      |- word_from_oct_string o word_to_oct_string = I

   [word_or_n2w]  Theorem

      |- ∀n m. n2w n ‖ n2w m = n2w (BITWISE (dimindex (:α)) $\/ n m)

   [word_reduce_n2w]  Theorem

      |- ∀n f.
           word_reduce f (n2w n) =
           $FCP
             (K
                (let l = BOOLIFY (dimindex (:α)) n []
                 in
                   FOLDL f (HD l) (TL l)))

   [word_replicate_concat_word_list]  Theorem

      |- ∀n w. word_replicate n w = concat_word_list (GENLIST (K w) n)

   [word_reverse_0]  Theorem

      |- word_reverse 0w = 0w

   [word_reverse_n2w]  Theorem

      |- ∀n. word_reverse (n2w n) = n2w (BIT_REVERSE (dimindex (:α)) n)

   [word_reverse_thm]  Theorem

      |- ∀w v n.
           (word_reverse (word_reverse w) = w) ∧
           (word_reverse (w ≪ n) = word_reverse w ⋙ n) ∧
           (word_reverse (w ⋙ n) = word_reverse w ≪ n) ∧
           (word_reverse (w ‖ v) = word_reverse w ‖ word_reverse v) ∧
           (word_reverse (w && v) = word_reverse w && word_reverse v) ∧
           (word_reverse (w ⊕ v) = word_reverse w ⊕ word_reverse v) ∧
           (word_reverse (¬w) = ¬word_reverse w) ∧ (word_reverse 0w = 0w) ∧
           (word_reverse (-1w) = -1w) ∧
           ((word_reverse w = 0w) ⇔ (w = 0w)) ∧
           ((word_reverse w = -1w) ⇔ (w = -1w))

   [word_reverse_word_T]  Theorem

      |- word_reverse (-1w) = -1w

   [word_ror]  Theorem

      |- ∀w n.
           w ⇄ n =
           (let x = n MOD dimindex (:α)
            in
              (dimindex (:α) − 1 -- x) w ‖
              (x − 1 -- 0) w ≪ (dimindex (:α) − x))

   [word_ror_n2w]  Theorem

      |- ∀n a.
           n2w a ⇄ n =
           (let x = n MOD dimindex (:α)
            in
              n2w
                (BITS (dimindex (:α) − 1) x a +
                 BITS (x − 1) 0 a * 2 ** (dimindex (:α) − x)))

   [word_rrx_0]  Theorem

      |- (word_rrx (F,0w) = (F,0w)) ∧ (word_rrx (T,0w) = (F,INT_MINw))

   [word_rrx_n2w]  Theorem

      |- ∀c a.
           word_rrx (c,n2w a) =
           (ODD a,
            n2w
              (BITS (dimindex (:α) − 1) 1 a + SBIT c (dimindex (:α) − 1)))

   [word_rrx_word_T]  Theorem

      |- (word_rrx (F,-1w) = (T,INT_MAXw)) ∧ (word_rrx (T,-1w) = (T,-1w))

   [word_shift_bv]  Theorem

      |- (∀w n. n < dimword (:α) ⇒ (w ≪ n = w <<~ n2w n)) ∧
         (∀w n. n < dimword (:α) ⇒ (w ≫ n = w >>~ n2w n)) ∧
         (∀w n. n < dimword (:α) ⇒ (w ⋙ n = w >>>~ n2w n)) ∧
         (∀w n. w ⇄ n = w #>>~ n2w (n MOD dimindex (:α))) ∧
         ∀w n. w ⇆ n = w #<<~ n2w (n MOD dimindex (:α))

   [word_sign_extend_bits]  Theorem

      |- ∀h l w.
           (h --- l) w =
           word_sign_extend (MIN (SUC h) (dimindex (:α)) − l) ((h -- l) w)

   [word_signed_bits_n2w]  Theorem

      |- ∀h l n.
           (h --- l) (n2w n) =
           n2w
             (SIGN_EXTEND (MIN (SUC h) (dimindex (:α)) − l) (dimindex (:α))
                (BITS (MIN h (dimindex (:α) − 1)) l n))

   [word_slice_n2w]  Theorem

      |- ∀h l n.
           (h '' l) (n2w n) = n2w (SLICE (MIN h (dimindex (:α) − 1)) l n)

   [word_sub_w2n]  Theorem

      |- ∀x y. y ≤₊ x ⇒ (w2n (x − y) = w2n x − w2n y)

   [word_xnor_n2w]  Theorem

      |- ∀n m. n2w n ~?? n2w m = n2w (BITWISE (dimindex (:α)) $<=> n m)

   [word_xor_n2w]  Theorem

      |- ∀n m.
           n2w n ⊕ n2w m = n2w (BITWISE (dimindex (:α)) (λx y. x ⇎ y) n m)


*)
end
