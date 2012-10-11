signature complexTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val IM : thm
    val RE : thm
    val arg : thm
    val complex_add : thm
    val complex_div : thm
    val complex_exp : thm
    val complex_inv : thm
    val complex_mul : thm
    val complex_neg : thm
    val complex_of_num : thm
    val complex_of_real : thm
    val complex_pow_def : thm
    val complex_scalar_lmul : thm
    val complex_scalar_rmul : thm
    val complex_sub : thm
    val conj : thm
    val i : thm
    val modu : thm

  (*  Theorems  *)
    val ARG_COS : thm
    val ARG_SIN : thm
    val COMPLEX : thm
    val COMPLEX_0 : thm
    val COMPLEX_0_THM : thm
    val COMPLEX_1 : thm
    val COMPLEX_10 : thm
    val COMPLEX_ADD2_SUB2 : thm
    val COMPLEX_ADD_ASSOC : thm
    val COMPLEX_ADD_COMM : thm
    val COMPLEX_ADD_LDISTRIB : thm
    val COMPLEX_ADD_LID : thm
    val COMPLEX_ADD_LID_UNIQ : thm
    val COMPLEX_ADD_LINV : thm
    val COMPLEX_ADD_RAT : thm
    val COMPLEX_ADD_RDISTRIB : thm
    val COMPLEX_ADD_RID : thm
    val COMPLEX_ADD_RID_UNIQ : thm
    val COMPLEX_ADD_RINV : thm
    val COMPLEX_ADD_RSCALAR_RMUL : thm
    val COMPLEX_ADD_SCALAR_LMUL : thm
    val COMPLEX_ADD_SUB : thm
    val COMPLEX_ADD_SUB2 : thm
    val COMPLEX_DIFFSQ : thm
    val COMPLEX_DIV1 : thm
    val COMPLEX_DIV_ADD : thm
    val COMPLEX_DIV_ARG : thm
    val COMPLEX_DIV_DENOM_CANCEL : thm
    val COMPLEX_DIV_INNER_CANCEL : thm
    val COMPLEX_DIV_LMUL_CANCEL : thm
    val COMPLEX_DIV_LZERO : thm
    val COMPLEX_DIV_MUL2 : thm
    val COMPLEX_DIV_OUTER_CANCEL : thm
    val COMPLEX_DIV_REFL : thm
    val COMPLEX_DIV_RMUL_CANCEL : thm
    val COMPLEX_DIV_SUB : thm
    val COMPLEX_DOUBLE : thm
    val COMPLEX_ENTIRE : thm
    val COMPLEX_EQ_LADD : thm
    val COMPLEX_EQ_LDIV_EQ : thm
    val COMPLEX_EQ_LMUL : thm
    val COMPLEX_EQ_LMUL2 : thm
    val COMPLEX_EQ_LMUL_IMP : thm
    val COMPLEX_EQ_NEG : thm
    val COMPLEX_EQ_RADD : thm
    val COMPLEX_EQ_RDIV_EQ : thm
    val COMPLEX_EQ_RMUL_IMP : thm
    val COMPLEX_EQ_SCALAR_LMUL : thm
    val COMPLEX_EQ_SUB_LADD : thm
    val COMPLEX_EQ_SUB_RADD : thm
    val COMPLEX_EXP_0 : thm
    val COMPLEX_EXP_ADD : thm
    val COMPLEX_EXP_ADD_MUL : thm
    val COMPLEX_EXP_N : thm
    val COMPLEX_EXP_N2 : thm
    val COMPLEX_EXP_NEG : thm
    val COMPLEX_EXP_NEG_MUL : thm
    val COMPLEX_EXP_NEG_MUL2 : thm
    val COMPLEX_EXP_NZ : thm
    val COMPLEX_EXP_SUB : thm
    val COMPLEX_INV1 : thm
    val COMPLEX_INVINV : thm
    val COMPLEX_INV_0 : thm
    val COMPLEX_INV_1OVER : thm
    val COMPLEX_INV_ARG : thm
    val COMPLEX_INV_EQ_0 : thm
    val COMPLEX_INV_INJ : thm
    val COMPLEX_INV_INV : thm
    val COMPLEX_INV_MUL : thm
    val COMPLEX_INV_NEG : thm
    val COMPLEX_INV_NZ : thm
    val COMPLEX_INV_SCALAR_LMUL : thm
    val COMPLEX_LEMMA1 : thm
    val COMPLEX_LEMMA2 : thm
    val COMPLEX_LINV_UNIQ : thm
    val COMPLEX_LMUL_SCALAR_LMUL : thm
    val COMPLEX_LNEG_UNIQ : thm
    val COMPLEX_MODU_ARG_EQ : thm
    val COMPLEX_MUL_ARG : thm
    val COMPLEX_MUL_ASSOC : thm
    val COMPLEX_MUL_COMM : thm
    val COMPLEX_MUL_LCONJ1 : thm
    val COMPLEX_MUL_LID : thm
    val COMPLEX_MUL_LINV : thm
    val COMPLEX_MUL_LNEG : thm
    val COMPLEX_MUL_LZERO : thm
    val COMPLEX_MUL_RCONJ : thm
    val COMPLEX_MUL_RCONJ1 : thm
    val COMPLEX_MUL_RID : thm
    val COMPLEX_MUL_RINV : thm
    val COMPLEX_MUL_RNEG : thm
    val COMPLEX_MUL_RZERO : thm
    val COMPLEX_MUL_SCALAR_LMUL2 : thm
    val COMPLEX_NEGNEG : thm
    val COMPLEX_NEG_0 : thm
    val COMPLEX_NEG_ADD : thm
    val COMPLEX_NEG_DIV2 : thm
    val COMPLEX_NEG_INV : thm
    val COMPLEX_NEG_LDIV : thm
    val COMPLEX_NEG_LMUL : thm
    val COMPLEX_NEG_MUL2 : thm
    val COMPLEX_NEG_Q : thm
    val COMPLEX_NEG_RDIV : thm
    val COMPLEX_NEG_RMUL : thm
    val COMPLEX_NEG_SCALAR_LMUL : thm
    val COMPLEX_NEG_SCALAR_RMUL : thm
    val COMPLEX_NEG_SUB : thm
    val COMPLEX_OF_NUM_ADD : thm
    val COMPLEX_OF_NUM_EQ : thm
    val COMPLEX_OF_NUM_MUL : thm
    val COMPLEX_OF_REAL_ADD : thm
    val COMPLEX_OF_REAL_DIV : thm
    val COMPLEX_OF_REAL_EQ : thm
    val COMPLEX_OF_REAL_INV : thm
    val COMPLEX_OF_REAL_MUL : thm
    val COMPLEX_OF_REAL_NEG : thm
    val COMPLEX_OF_REAL_SUB : thm
    val COMPLEX_POWINV : thm
    val COMPLEX_POW_0 : thm
    val COMPLEX_POW_1 : thm
    val COMPLEX_POW_2 : thm
    val COMPLEX_POW_ADD : thm
    val COMPLEX_POW_DIV : thm
    val COMPLEX_POW_INV : thm
    val COMPLEX_POW_L : thm
    val COMPLEX_POW_MUL : thm
    val COMPLEX_POW_NZ : thm
    val COMPLEX_POW_ONE : thm
    val COMPLEX_POW_POW : thm
    val COMPLEX_POW_ZERO : thm
    val COMPLEX_POW_ZERO_EQ : thm
    val COMPLEX_RE_IM_EQ : thm
    val COMPLEX_RINV_UNIQ : thm
    val COMPLEX_RMUL_SCALAR_LMUL : thm
    val COMPLEX_RNEG_UNIQ : thm
    val COMPLEX_RSCALAR_RMUL_SUB : thm
    val COMPLEX_SCALAR_LMUL : thm
    val COMPLEX_SCALAR_LMUL_ADD : thm
    val COMPLEX_SCALAR_LMUL_DIV2 : thm
    val COMPLEX_SCALAR_LMUL_ENTIRE : thm
    val COMPLEX_SCALAR_LMUL_EQ : thm
    val COMPLEX_SCALAR_LMUL_EQ1 : thm
    val COMPLEX_SCALAR_LMUL_NEG : thm
    val COMPLEX_SCALAR_LMUL_NEG1 : thm
    val COMPLEX_SCALAR_LMUL_ONE : thm
    val COMPLEX_SCALAR_LMUL_SUB : thm
    val COMPLEX_SCALAR_LMUL_ZERO : thm
    val COMPLEX_SCALAR_MUL_COMM : thm
    val COMPLEX_SCALAR_RMUL : thm
    val COMPLEX_SCALAR_RMUL_ADD : thm
    val COMPLEX_SCALAR_RMUL_NEG : thm
    val COMPLEX_SCALAR_RMUL_NEG1 : thm
    val COMPLEX_SCALAR_RMUL_ONE : thm
    val COMPLEX_SCALAR_RMUL_ZERO : thm
    val COMPLEX_SUB_0 : thm
    val COMPLEX_SUB_ADD : thm
    val COMPLEX_SUB_ADD2 : thm
    val COMPLEX_SUB_G : thm
    val COMPLEX_SUB_INV2 : thm
    val COMPLEX_SUB_LZERO : thm
    val COMPLEX_SUB_NEG2 : thm
    val COMPLEX_SUB_RAT : thm
    val COMPLEX_SUB_REFL : thm
    val COMPLEX_SUB_RNEG : thm
    val COMPLEX_SUB_RZERO : thm
    val COMPLEX_SUB_SCALAR_LMUL : thm
    val COMPLEX_SUB_SCALAR_RMUL : thm
    val COMPLEX_SUB_SUB : thm
    val COMPLEX_SUB_SUB2 : thm
    val COMPLEX_SUB_TRIANGLE : thm
    val COMPLEX_TRIANGLE : thm
    val COMPLEX_ZERO_SCALAR_LMUL : thm
    val COMPLEX_ZERO_SCALAR_RMUL : thm
    val CONJ_ADD : thm
    val CONJ_CONJ : thm
    val CONJ_DIV : thm
    val CONJ_EQ : thm
    val CONJ_EQ2 : thm
    val CONJ_INV : thm
    val CONJ_MUL : thm
    val CONJ_NEG : thm
    val CONJ_NUM_REFL : thm
    val CONJ_REAL_REFL : thm
    val CONJ_SCALAR_LMUL : thm
    val CONJ_SUB : thm
    val CONJ_ZERO : thm
    val DE_MOIVRE_LEMMA : thm
    val DE_MOIVRE_THM : thm
    val EULER_FORMULE : thm
    val EXP_IMAGINARY : thm
    val IM_COMPLEX_OF_REAL : thm
    val IM_DIV_MODU_ASN_BOUNDS : thm
    val IM_DIV_MODU_ASN_SIN : thm
    val IM_DIV_MODU_BOUNDS : thm
    val IM_MODU_ARG : thm
    val MODU_0 : thm
    val MODU_1 : thm
    val MODU_CASES : thm
    val MODU_COMPLEX_INV : thm
    val MODU_COMPLEX_POW : thm
    val MODU_CONJ : thm
    val MODU_DIV : thm
    val MODU_MUL : thm
    val MODU_NEG : thm
    val MODU_NUM : thm
    val MODU_NZ : thm
    val MODU_POS : thm
    val MODU_POW2 : thm
    val MODU_REAL : thm
    val MODU_SCALAR_LMUL : thm
    val MODU_SUB : thm
    val MODU_UNIT : thm
    val MODU_ZERO : thm
    val RE_COMPLEX_OF_REAL : thm
    val RE_DIV_MODU_ACS_BOUNDS : thm
    val RE_DIV_MODU_ACS_COS : thm
    val RE_DIV_MODU_BOUNDS : thm
    val RE_IM_LE_MODU : thm
    val RE_MODU_ARG : thm
    val complex_pow_def_compute : thm

  val complex_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [poly] Parent theory of "complex"

   [transc] Parent theory of "complex"

   [IM]  Definition

      |- ∀z. IM z = SND z

   [RE]  Definition

      |- ∀z. RE z = FST z

   [arg]  Definition

      |- ∀z.
           arg z =
           if 0 ≤ IM z then
             acs (RE z / modu z)
           else
             -acs (RE z / modu z) + 2 * pi

   [complex_add]  Definition

      |- ∀z w. z + w = (RE z + RE w,IM z + IM w)

   [complex_div]  Definition

      |- ∀z w. z / w = z * inv w

   [complex_exp]  Definition

      |- ∀z. exp z = exp (RE z) * (cos (IM z),sin (IM z))

   [complex_inv]  Definition

      |- ∀z.
           inv z =
           (RE z / (RE z pow 2 + IM z pow 2),
            -IM z / (RE z pow 2 + IM z pow 2))

   [complex_mul]  Definition

      |- ∀z w.
           z * w = (RE z * RE w − IM z * IM w,RE z * IM w + IM z * RE w)

   [complex_neg]  Definition

      |- ∀z. -z = (-RE z,-IM z)

   [complex_of_num]  Definition

      |- ∀n. &n = complex_of_real (&n)

   [complex_of_real]  Definition

      |- ∀x. complex_of_real x = (x,0)

   [complex_pow_def]  Definition

      |- (∀z. z pow 0 = 1) ∧ ∀z n. z pow SUC n = z * z pow n

   [complex_scalar_lmul]  Definition

      |- ∀k z. k * z = (k * RE z,k * IM z)

   [complex_scalar_rmul]  Definition

      |- ∀z k. z * k = (RE z * k,IM z * k)

   [complex_sub]  Definition

      |- ∀z w. z − w = z + -w

   [conj]  Definition

      |- ∀z. conj z = (RE z,-IM z)

   [i]  Definition

      |- i = (0,1)

   [modu]  Definition

      |- ∀z. modu z = sqrt (RE z pow 2 + IM z pow 2)

   [ARG_COS]  Theorem

      |- ∀z. z ≠ 0 ⇒ (cos (arg z) = RE z / modu z)

   [ARG_SIN]  Theorem

      |- ∀z. z ≠ 0 ⇒ (sin (arg z) = IM z / modu z)

   [COMPLEX]  Theorem

      |- ∀z. (RE z,IM z) = z

   [COMPLEX_0]  Theorem

      |- 0 = complex_of_real 0

   [COMPLEX_0_THM]  Theorem

      |- ∀z. (z = 0) ⇔ (RE z pow 2 + IM z pow 2 = 0)

   [COMPLEX_1]  Theorem

      |- 1 = complex_of_real 1

   [COMPLEX_10]  Theorem

      |- 1 ≠ 0

   [COMPLEX_ADD2_SUB2]  Theorem

      |- ∀z w u v. z + w − (u + v) = z − u + (w − v)

   [COMPLEX_ADD_ASSOC]  Theorem

      |- ∀z w v. z + (w + v) = z + w + v

   [COMPLEX_ADD_COMM]  Theorem

      |- ∀z w. z + w = w + z

   [COMPLEX_ADD_LDISTRIB]  Theorem

      |- ∀z w v. z * (w − v) = z * w − z * v

   [COMPLEX_ADD_LID]  Theorem

      |- ∀z. 0 + z = z

   [COMPLEX_ADD_LID_UNIQ]  Theorem

      |- ∀z w. (z + w = w) ⇔ (z = 0)

   [COMPLEX_ADD_LINV]  Theorem

      |- ∀z. -z + z = 0

   [COMPLEX_ADD_RAT]  Theorem

      |- ∀z w u v.
           w ≠ 0 ∧ v ≠ 0 ⇒ (z / w + u / v = (z * v + w * u) / (w * v))

   [COMPLEX_ADD_RDISTRIB]  Theorem

      |- ∀z w v. (z − w) * v = z * v − w * v

   [COMPLEX_ADD_RID]  Theorem

      |- ∀z. z + 0 = z

   [COMPLEX_ADD_RID_UNIQ]  Theorem

      |- ∀z w. (z + w = z) ⇔ (w = 0)

   [COMPLEX_ADD_RINV]  Theorem

      |- ∀z. z + -z = 0

   [COMPLEX_ADD_RSCALAR_RMUL]  Theorem

      |- ∀k z w. (z + w) * k = z * k + w * k

   [COMPLEX_ADD_SCALAR_LMUL]  Theorem

      |- ∀k z w. k * (z + w) = k * z + k * w

   [COMPLEX_ADD_SUB]  Theorem

      |- ∀z w. z + w − z = w

   [COMPLEX_ADD_SUB2]  Theorem

      |- ∀z w. z − (z + w) = -w

   [COMPLEX_DIFFSQ]  Theorem

      |- ∀z w. (z + w) * (z − w) = z * z − w * w

   [COMPLEX_DIV1]  Theorem

      |- ∀z. z / 1 = z

   [COMPLEX_DIV_ADD]  Theorem

      |- ∀z w v. z / v + w / v = (z + w) / v

   [COMPLEX_DIV_ARG]  Theorem

      |- ∀x y. (cos x,sin x) / (cos y,sin y) = (cos (x − y),sin (x − y))

   [COMPLEX_DIV_DENOM_CANCEL]  Theorem

      |- ∀z w v. z ≠ 0 ⇒ (w / z / (v / z) = w / v)

   [COMPLEX_DIV_INNER_CANCEL]  Theorem

      |- ∀z w v. z ≠ 0 ⇒ (w / z * (z / v) = w / v)

   [COMPLEX_DIV_LMUL_CANCEL]  Theorem

      |- ∀v z w. v ≠ 0 ⇒ (v * z / (v * w) = z / w)

   [COMPLEX_DIV_LZERO]  Theorem

      |- ∀z. 0 / z = 0

   [COMPLEX_DIV_MUL2]  Theorem

      |- ∀z w. z ≠ 0 ∧ w ≠ 0 ⇒ ∀v. v / w = z * v / (z * w)

   [COMPLEX_DIV_OUTER_CANCEL]  Theorem

      |- ∀z w v. z ≠ 0 ⇒ (z / w * (v / z) = v / w)

   [COMPLEX_DIV_REFL]  Theorem

      |- ∀z. z ≠ 0 ⇒ (z / z = 1)

   [COMPLEX_DIV_RMUL_CANCEL]  Theorem

      |- ∀v z w. v ≠ 0 ⇒ (z * v / (w * v) = z / w)

   [COMPLEX_DIV_SUB]  Theorem

      |- ∀z w v. z / v − w / v = (z − w) / v

   [COMPLEX_DOUBLE]  Theorem

      |- ∀z. z + z = 2 * z

   [COMPLEX_ENTIRE]  Theorem

      |- ∀z w. (z * w = 0) ⇔ (z = 0) ∨ (w = 0)

   [COMPLEX_EQ_LADD]  Theorem

      |- ∀z w v. (z + w = z + v) ⇔ (w = v)

   [COMPLEX_EQ_LDIV_EQ]  Theorem

      |- ∀z w v. v ≠ 0 ⇒ ((z / v = w) ⇔ (z = w * v))

   [COMPLEX_EQ_LMUL]  Theorem

      |- ∀z w v. (z * v = w * v) ⇔ (v = 0) ∨ (z = w)

   [COMPLEX_EQ_LMUL2]  Theorem

      |- ∀z w v. z ≠ 0 ⇒ ((w = v) ⇔ (z * w = z * v))

   [COMPLEX_EQ_LMUL_IMP]  Theorem

      |- ∀z w v. z ≠ 0 ∧ (z * w = z * v) ⇒ (w = v)

   [COMPLEX_EQ_NEG]  Theorem

      |- ∀z w. (-z = -w) ⇔ (z = w)

   [COMPLEX_EQ_RADD]  Theorem

      |- ∀z w v. (z + v = w + v) ⇔ (z = w)

   [COMPLEX_EQ_RDIV_EQ]  Theorem

      |- ∀z w v. v ≠ 0 ⇒ ((z = w / v) ⇔ (z * v = w))

   [COMPLEX_EQ_RMUL_IMP]  Theorem

      |- ∀z w v. z ≠ 0 ∧ (w * z = v * z) ⇒ (w = v)

   [COMPLEX_EQ_SCALAR_LMUL]  Theorem

      |- ∀k z w. (k * z = k * w) ⇔ (k = 0) ∨ (z = w)

   [COMPLEX_EQ_SUB_LADD]  Theorem

      |- ∀z w v. (z = w − v) ⇔ (z + v = w)

   [COMPLEX_EQ_SUB_RADD]  Theorem

      |- ∀z w v. (z − w = v) ⇔ (z = v + w)

   [COMPLEX_EXP_0]  Theorem

      |- exp 0 = 1

   [COMPLEX_EXP_ADD]  Theorem

      |- ∀z w. exp (z + w) = exp z * exp w

   [COMPLEX_EXP_ADD_MUL]  Theorem

      |- ∀z w. exp (z + w) * exp (-z) = exp w

   [COMPLEX_EXP_N]  Theorem

      |- ∀z n. exp (&n * z) = exp z pow n

   [COMPLEX_EXP_N2]  Theorem

      |- ∀z n. exp (&n * z) = exp z pow n

   [COMPLEX_EXP_NEG]  Theorem

      |- ∀z. exp (-z) = inv (exp z)

   [COMPLEX_EXP_NEG_MUL]  Theorem

      |- ∀z. exp z * exp (-z) = 1

   [COMPLEX_EXP_NEG_MUL2]  Theorem

      |- ∀z. exp (-z) * exp z = 1

   [COMPLEX_EXP_NZ]  Theorem

      |- ∀z. exp z ≠ 0

   [COMPLEX_EXP_SUB]  Theorem

      |- ∀z w. exp (z − w) = exp z / exp w

   [COMPLEX_INV1]  Theorem

      |- inv 1 = 1

   [COMPLEX_INVINV]  Theorem

      |- ∀z. z ≠ 0 ⇒ (inv (inv z) = z)

   [COMPLEX_INV_0]  Theorem

      |- inv 0 = 0

   [COMPLEX_INV_1OVER]  Theorem

      |- ∀z. inv z = 1 / z

   [COMPLEX_INV_ARG]  Theorem

      |- ∀x. inv (cos x,sin x) = (cos (-x),sin (-x))

   [COMPLEX_INV_EQ_0]  Theorem

      |- ∀z. (inv z = 0) ⇔ (z = 0)

   [COMPLEX_INV_INJ]  Theorem

      |- ∀z w. (inv z = inv w) ⇔ (z = w)

   [COMPLEX_INV_INV]  Theorem

      |- ∀z. inv (inv z) = z

   [COMPLEX_INV_MUL]  Theorem

      |- ∀z w. z ≠ 0 ∧ w ≠ 0 ⇒ (inv (z * w) = inv z * inv w)

   [COMPLEX_INV_NEG]  Theorem

      |- ∀z. inv (-z) = -inv z

   [COMPLEX_INV_NZ]  Theorem

      |- ∀z. z ≠ 0 ⇒ inv z ≠ 0

   [COMPLEX_INV_SCALAR_LMUL]  Theorem

      |- ∀k z. k ≠ 0 ∧ z ≠ 0 ⇒ (inv (k * z) = inv k * inv z)

   [COMPLEX_LEMMA1]  Theorem

      |- ∀a b c d.
           (a * c − b * d) pow 2 + (a * d + b * c) pow 2 =
           (a pow 2 + b pow 2) * (c pow 2 + d pow 2)

   [COMPLEX_LEMMA2]  Theorem

      |- ∀x y. abs x ≤ sqrt (x pow 2 + y pow 2)

   [COMPLEX_LINV_UNIQ]  Theorem

      |- ∀z w. (z * w = 1) ⇒ (z = inv w)

   [COMPLEX_LMUL_SCALAR_LMUL]  Theorem

      |- ∀k z w. k * z * w = k * (z * w)

   [COMPLEX_LNEG_UNIQ]  Theorem

      |- ∀z w. (z + w = 0) ⇔ (z = -w)

   [COMPLEX_MODU_ARG_EQ]  Theorem

      |- ∀z w. (z = w) ⇔ (modu z = modu w) ∧ (arg z = arg w)

   [COMPLEX_MUL_ARG]  Theorem

      |- ∀x y. (cos x,sin x) * (cos y,sin y) = (cos (x + y),sin (x + y))

   [COMPLEX_MUL_ASSOC]  Theorem

      |- ∀z w v. z * (w * v) = z * w * v

   [COMPLEX_MUL_COMM]  Theorem

      |- ∀z w. z * w = w * z

   [COMPLEX_MUL_LCONJ1]  Theorem

      |- ∀z. conj z * z = complex_of_real (modu z pow 2)

   [COMPLEX_MUL_LID]  Theorem

      |- ∀z. 1 * z = z

   [COMPLEX_MUL_LINV]  Theorem

      |- ∀z. z ≠ 0 ⇒ (inv z * z = 1)

   [COMPLEX_MUL_LNEG]  Theorem

      |- ∀z w. -z * w = -(z * w)

   [COMPLEX_MUL_LZERO]  Theorem

      |- ∀z. 0 * z = 0

   [COMPLEX_MUL_RCONJ]  Theorem

      |- ∀z. conj z * z = complex_of_real (RE z pow 2 + IM z pow 2)

   [COMPLEX_MUL_RCONJ1]  Theorem

      |- ∀z. z * conj z = complex_of_real (modu z pow 2)

   [COMPLEX_MUL_RID]  Theorem

      |- ∀z. z * 1 = z

   [COMPLEX_MUL_RINV]  Theorem

      |- ∀z. z ≠ 0 ⇒ (z * inv z = 1)

   [COMPLEX_MUL_RNEG]  Theorem

      |- ∀z w. z * -w = -(z * w)

   [COMPLEX_MUL_RZERO]  Theorem

      |- ∀z. z * 0 = 0

   [COMPLEX_MUL_SCALAR_LMUL2]  Theorem

      |- ∀k l z w. k * z * (l * w) = k * l * (z * w)

   [COMPLEX_NEGNEG]  Theorem

      |- ∀z. --z = z

   [COMPLEX_NEG_0]  Theorem

      |- ∀z. (-z = 0) ⇔ (z = 0)

   [COMPLEX_NEG_ADD]  Theorem

      |- ∀z w. -(z + w) = -z + -w

   [COMPLEX_NEG_DIV2]  Theorem

      |- ∀z w. -z / -w = z / w

   [COMPLEX_NEG_INV]  Theorem

      |- ∀z. z ≠ 0 ⇒ (inv (-z) = -inv z)

   [COMPLEX_NEG_LDIV]  Theorem

      |- ∀z w. -(z / w) = -z / w

   [COMPLEX_NEG_LMUL]  Theorem

      |- ∀z w. -(z * w) = -z * w

   [COMPLEX_NEG_MUL2]  Theorem

      |- ∀z w. -z * -w = z * w

   [COMPLEX_NEG_Q]  Theorem

      |- ∀z w. (-z = w) ⇔ (z = -w)

   [COMPLEX_NEG_RDIV]  Theorem

      |- ∀z w. -(z / w) = z / -w

   [COMPLEX_NEG_RMUL]  Theorem

      |- ∀z w. -(z * w) = z * -w

   [COMPLEX_NEG_SCALAR_LMUL]  Theorem

      |- ∀k z. k * -z = -k * z

   [COMPLEX_NEG_SCALAR_RMUL]  Theorem

      |- ∀k z. -z * k = z * -k

   [COMPLEX_NEG_SUB]  Theorem

      |- ∀z w. -(z − w) = w − z

   [COMPLEX_OF_NUM_ADD]  Theorem

      |- ∀m n. &m + &n = &(m + n)

   [COMPLEX_OF_NUM_EQ]  Theorem

      |- ∀m n. (&m = &n) ⇔ (m = n)

   [COMPLEX_OF_NUM_MUL]  Theorem

      |- ∀m n. &m * &n = &(m * n)

   [COMPLEX_OF_REAL_ADD]  Theorem

      |- ∀x y.
           complex_of_real x + complex_of_real y = complex_of_real (x + y)

   [COMPLEX_OF_REAL_DIV]  Theorem

      |- ∀x y.
           complex_of_real x / complex_of_real y = complex_of_real (x / y)

   [COMPLEX_OF_REAL_EQ]  Theorem

      |- ∀x y. (complex_of_real x = complex_of_real y) ⇔ (x = y)

   [COMPLEX_OF_REAL_INV]  Theorem

      |- ∀x. inv (complex_of_real x) = complex_of_real (inv x)

   [COMPLEX_OF_REAL_MUL]  Theorem

      |- ∀x y.
           complex_of_real x * complex_of_real y = complex_of_real (x * y)

   [COMPLEX_OF_REAL_NEG]  Theorem

      |- ∀x. -complex_of_real x = complex_of_real (-x)

   [COMPLEX_OF_REAL_SUB]  Theorem

      |- ∀x y.
           complex_of_real x − complex_of_real y = complex_of_real (x − y)

   [COMPLEX_POWINV]  Theorem

      |- ∀z. z ≠ 0 ⇒ ∀n. inv (z pow n) = inv z pow n

   [COMPLEX_POW_0]  Theorem

      |- ∀n. 0 pow SUC n = 0

   [COMPLEX_POW_1]  Theorem

      |- ∀z. z pow 1 = z

   [COMPLEX_POW_2]  Theorem

      |- ∀z. z pow 2 = z * z

   [COMPLEX_POW_ADD]  Theorem

      |- ∀z m n. z pow (m + n) = z pow m * z pow n

   [COMPLEX_POW_DIV]  Theorem

      |- ∀z w n. (z / w) pow n = z pow n / w pow n

   [COMPLEX_POW_INV]  Theorem

      |- ∀z n. inv z pow n = inv (z pow n)

   [COMPLEX_POW_L]  Theorem

      |- ∀n k z. (k * z) pow n = k pow n * z pow n

   [COMPLEX_POW_MUL]  Theorem

      |- ∀n z w. (z * w) pow n = z pow n * w pow n

   [COMPLEX_POW_NZ]  Theorem

      |- ∀z n. z ≠ 0 ⇒ z pow n ≠ 0

   [COMPLEX_POW_ONE]  Theorem

      |- ∀n. 1 pow n = 1

   [COMPLEX_POW_POW]  Theorem

      |- ∀z m n. (z pow m) pow n = z pow (m * n)

   [COMPLEX_POW_ZERO]  Theorem

      |- ∀n z. (z pow n = 0) ⇒ (z = 0)

   [COMPLEX_POW_ZERO_EQ]  Theorem

      |- ∀n z. (z pow SUC n = 0) ⇔ (z = 0)

   [COMPLEX_RE_IM_EQ]  Theorem

      |- ∀z w. (z = w) ⇔ (RE z = RE w) ∧ (IM z = IM w)

   [COMPLEX_RINV_UNIQ]  Theorem

      |- ∀z w. (z * w = 1) ⇒ (w = inv z)

   [COMPLEX_RMUL_SCALAR_LMUL]  Theorem

      |- ∀k z w. z * (k * w) = k * (z * w)

   [COMPLEX_RNEG_UNIQ]  Theorem

      |- ∀z w. (z + w = 0) ⇔ (w = -z)

   [COMPLEX_RSCALAR_RMUL_SUB]  Theorem

      |- ∀k l z. z * (k − l) = z * k − z * l

   [COMPLEX_SCALAR_LMUL]  Theorem

      |- ∀k l z. k * (l * z) = k * l * z

   [COMPLEX_SCALAR_LMUL_ADD]  Theorem

      |- ∀k l z. (k + l) * z = k * z + l * z

   [COMPLEX_SCALAR_LMUL_DIV2]  Theorem

      |- ∀k l z w. l ≠ 0 ∧ w ≠ 0 ⇒ (k * z / (l * w) = k / l * (z / w))

   [COMPLEX_SCALAR_LMUL_ENTIRE]  Theorem

      |- ∀k z. (k * z = 0) ⇔ (k = 0) ∨ (z = 0)

   [COMPLEX_SCALAR_LMUL_EQ]  Theorem

      |- ∀k l z. (k * z = l * z) ⇔ (k = l) ∨ (z = 0)

   [COMPLEX_SCALAR_LMUL_EQ1]  Theorem

      |- ∀k z. (k * z = z) ⇔ (k = 1) ∨ (z = 0)

   [COMPLEX_SCALAR_LMUL_NEG]  Theorem

      |- ∀k z. -(k * z) = -k * z

   [COMPLEX_SCALAR_LMUL_NEG1]  Theorem

      |- ∀z. -1 * z = -z

   [COMPLEX_SCALAR_LMUL_ONE]  Theorem

      |- ∀z. 1 * z = z

   [COMPLEX_SCALAR_LMUL_SUB]  Theorem

      |- ∀k l z. (k − l) * z = k * z − l * z

   [COMPLEX_SCALAR_LMUL_ZERO]  Theorem

      |- ∀z. 0 * z = 0

   [COMPLEX_SCALAR_MUL_COMM]  Theorem

      |- ∀k z. k * z = z * k

   [COMPLEX_SCALAR_RMUL]  Theorem

      |- ∀k l z. z * k * l = z * (k * l)

   [COMPLEX_SCALAR_RMUL_ADD]  Theorem

      |- ∀k l z. z * (k + l) = z * k + z * l

   [COMPLEX_SCALAR_RMUL_NEG]  Theorem

      |- ∀k z. -(z * k) = z * -k

   [COMPLEX_SCALAR_RMUL_NEG1]  Theorem

      |- ∀z. z * -1 = -z

   [COMPLEX_SCALAR_RMUL_ONE]  Theorem

      |- ∀z. z * 1 = z

   [COMPLEX_SCALAR_RMUL_ZERO]  Theorem

      |- ∀z. z * 0 = 0

   [COMPLEX_SUB_0]  Theorem

      |- ∀z w. (z − w = 0) ⇔ (z = w)

   [COMPLEX_SUB_ADD]  Theorem

      |- ∀z w. z − w + w = z

   [COMPLEX_SUB_ADD2]  Theorem

      |- ∀z w. w + (z − w) = z

   [COMPLEX_SUB_G]  Theorem

      |- ∀z w. -z − w = -(z + w)

   [COMPLEX_SUB_INV2]  Theorem

      |- ∀z w. z ≠ 0 ∧ w ≠ 0 ⇒ (inv z − inv w = (w − z) / (z * w))

   [COMPLEX_SUB_LZERO]  Theorem

      |- ∀z. 0 − z = -z

   [COMPLEX_SUB_NEG2]  Theorem

      |- ∀z w. -z − -w = w − z

   [COMPLEX_SUB_RAT]  Theorem

      |- ∀z w u v.
           w ≠ 0 ∧ v ≠ 0 ⇒ (z / w − u / v = (z * v − w * u) / (w * v))

   [COMPLEX_SUB_REFL]  Theorem

      |- ∀z. z − z = 0

   [COMPLEX_SUB_RNEG]  Theorem

      |- ∀z w. z − -w = z + w

   [COMPLEX_SUB_RZERO]  Theorem

      |- ∀z. z − 0 = z

   [COMPLEX_SUB_SCALAR_LMUL]  Theorem

      |- ∀k z w. k * (z − w) = k * z − k * w

   [COMPLEX_SUB_SCALAR_RMUL]  Theorem

      |- ∀k z w. (z − w) * k = z * k − w * k

   [COMPLEX_SUB_SUB]  Theorem

      |- ∀z w. z − w − z = -w

   [COMPLEX_SUB_SUB2]  Theorem

      |- ∀z w. z − (z − w) = w

   [COMPLEX_SUB_TRIANGLE]  Theorem

      |- ∀z w v. z − w + (w − v) = z − v

   [COMPLEX_TRIANGLE]  Theorem

      |- ∀z. modu z * (cos (arg z),sin (arg z)) = z

   [COMPLEX_ZERO_SCALAR_LMUL]  Theorem

      |- ∀k. k * 0 = 0

   [COMPLEX_ZERO_SCALAR_RMUL]  Theorem

      |- ∀k. 0 * k = 0

   [CONJ_ADD]  Theorem

      |- ∀z w. conj (z + w) = conj z + conj w

   [CONJ_CONJ]  Theorem

      |- ∀z. conj (conj z) = z

   [CONJ_DIV]  Theorem

      |- ∀z w. conj (z / w) = conj z / conj w

   [CONJ_EQ]  Theorem

      |- ∀z w. (conj z = w) ⇔ (z = conj w)

   [CONJ_EQ2]  Theorem

      |- ∀z w. (conj z = conj w) ⇔ (z = w)

   [CONJ_INV]  Theorem

      |- ∀z. conj (inv z) = inv (conj z)

   [CONJ_MUL]  Theorem

      |- ∀z w. conj (z * w) = conj z * conj w

   [CONJ_NEG]  Theorem

      |- ∀z. conj (-z) = -conj z

   [CONJ_NUM_REFL]  Theorem

      |- ∀n. conj (&n) = &n

   [CONJ_REAL_REFL]  Theorem

      |- ∀x. conj (complex_of_real x) = complex_of_real x

   [CONJ_SCALAR_LMUL]  Theorem

      |- ∀k z. conj (k * z) = k * conj z

   [CONJ_SUB]  Theorem

      |- ∀z w. conj (z − w) = conj z − conj w

   [CONJ_ZERO]  Theorem

      |- conj 0 = 0

   [DE_MOIVRE_LEMMA]  Theorem

      |- ∀x n. (cos x,sin x) pow n = (cos (&n * x),sin (&n * x))

   [DE_MOIVRE_THM]  Theorem

      |- ∀z n.
           (modu z * (cos (arg z),sin (arg z))) pow n =
           modu z pow n * (cos (&n * arg z),sin (&n * arg z))

   [EULER_FORMULE]  Theorem

      |- ∀z. modu z * exp (i * arg z) = z

   [EXP_IMAGINARY]  Theorem

      |- ∀x. exp (i * x) = (cos x,sin x)

   [IM_COMPLEX_OF_REAL]  Theorem

      |- ∀x. IM (complex_of_real x) = 0

   [IM_DIV_MODU_ASN_BOUNDS]  Theorem

      |- ∀z.
           z ≠ 0 ⇒
           -(pi / 2) ≤ asn (IM z / modu z) ∧ asn (IM z / modu z) ≤ pi / 2

   [IM_DIV_MODU_ASN_SIN]  Theorem

      |- ∀z. z ≠ 0 ⇒ (sin (asn (IM z / modu z)) = IM z / modu z)

   [IM_DIV_MODU_BOUNDS]  Theorem

      |- ∀z. z ≠ 0 ⇒ -1 ≤ IM z / modu z ∧ IM z / modu z ≤ 1

   [IM_MODU_ARG]  Theorem

      |- ∀z. IM z = modu z * sin (arg z)

   [MODU_0]  Theorem

      |- modu 0 = 0

   [MODU_1]  Theorem

      |- modu 1 = 1

   [MODU_CASES]  Theorem

      |- ∀z. (z = 0) ∨ 0 < modu z

   [MODU_COMPLEX_INV]  Theorem

      |- ∀z. z ≠ 0 ⇒ (modu (inv z) = inv (modu z))

   [MODU_COMPLEX_POW]  Theorem

      |- ∀z n. modu (z pow n) = modu z pow n

   [MODU_CONJ]  Theorem

      |- ∀z. modu (conj z) = modu z

   [MODU_DIV]  Theorem

      |- ∀z w. w ≠ 0 ⇒ (modu (z / w) = modu z / modu w)

   [MODU_MUL]  Theorem

      |- ∀z w. modu (z * w) = modu z * modu w

   [MODU_NEG]  Theorem

      |- ∀z. modu (-z) = modu z

   [MODU_NUM]  Theorem

      |- ∀n. modu (&n) = &n

   [MODU_NZ]  Theorem

      |- ∀z. z ≠ 0 ⇔ 0 < modu z

   [MODU_POS]  Theorem

      |- ∀z. 0 ≤ modu z

   [MODU_POW2]  Theorem

      |- ∀z. modu z pow 2 = RE z pow 2 + IM z pow 2

   [MODU_REAL]  Theorem

      |- ∀x. modu (complex_of_real x) = abs x

   [MODU_SCALAR_LMUL]  Theorem

      |- ∀k z. modu (k * z) = abs k * modu z

   [MODU_SUB]  Theorem

      |- ∀z w. modu (z − w) = modu (w − z)

   [MODU_UNIT]  Theorem

      |- ∀x y. modu (cos x,sin x) = 1

   [MODU_ZERO]  Theorem

      |- ∀z. (z = 0) ⇔ (modu z = 0)

   [RE_COMPLEX_OF_REAL]  Theorem

      |- ∀x. RE (complex_of_real x) = x

   [RE_DIV_MODU_ACS_BOUNDS]  Theorem

      |- ∀z. z ≠ 0 ⇒ 0 ≤ acs (RE z / modu z) ∧ acs (RE z / modu z) ≤ pi

   [RE_DIV_MODU_ACS_COS]  Theorem

      |- ∀z. z ≠ 0 ⇒ (cos (acs (RE z / modu z)) = RE z / modu z)

   [RE_DIV_MODU_BOUNDS]  Theorem

      |- ∀z. z ≠ 0 ⇒ -1 ≤ RE z / modu z ∧ RE z / modu z ≤ 1

   [RE_IM_LE_MODU]  Theorem

      |- ∀z. abs (RE z) ≤ modu z ∧ abs (IM z) ≤ modu z

   [RE_MODU_ARG]  Theorem

      |- ∀z. RE z = modu z * cos (arg z)

   [complex_pow_def_compute]  Theorem

      |- (∀z. z pow 0 = 1) ∧
         (∀z n.
            z pow NUMERAL (BIT1 n) = z * z pow (NUMERAL (BIT1 n) − 1)) ∧
         ∀z n. z pow NUMERAL (BIT2 n) = z * z pow NUMERAL (BIT1 n)


*)
end
