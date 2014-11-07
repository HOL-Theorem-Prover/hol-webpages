signature hrealTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val cut_of_hrat : thm
    val hrat_lt : thm
    val hreal_1 : thm
    val hreal_TY_DEF : thm
    val hreal_add : thm
    val hreal_inv : thm
    val hreal_lt : thm
    val hreal_mul : thm
    val hreal_sub : thm
    val hreal_sup : thm
    val hreal_tybij : thm
    val isacut : thm

  (*  Theorems  *)
    val CUT_BOUNDED : thm
    val CUT_DOWN : thm
    val CUT_ISACUT : thm
    val CUT_NEARTOP_ADD : thm
    val CUT_NEARTOP_MUL : thm
    val CUT_NONEMPTY : thm
    val CUT_STRADDLE : thm
    val CUT_UBOUND : thm
    val CUT_UP : thm
    val EQUAL_CUTS : thm
    val HRAT_DOWN : thm
    val HRAT_DOWN2 : thm
    val HRAT_EQ_LADD : thm
    val HRAT_EQ_LMUL : thm
    val HRAT_GT_L1 : thm
    val HRAT_GT_LMUL1 : thm
    val HRAT_INV_MUL : thm
    val HRAT_LT_ADD2 : thm
    val HRAT_LT_ADDL : thm
    val HRAT_LT_ADDR : thm
    val HRAT_LT_ANTISYM : thm
    val HRAT_LT_GT : thm
    val HRAT_LT_L1 : thm
    val HRAT_LT_LADD : thm
    val HRAT_LT_LMUL : thm
    val HRAT_LT_LMUL1 : thm
    val HRAT_LT_MUL2 : thm
    val HRAT_LT_NE : thm
    val HRAT_LT_R1 : thm
    val HRAT_LT_RADD : thm
    val HRAT_LT_REFL : thm
    val HRAT_LT_RMUL : thm
    val HRAT_LT_RMUL1 : thm
    val HRAT_LT_TOTAL : thm
    val HRAT_LT_TRANS : thm
    val HRAT_MEAN : thm
    val HRAT_MUL_RID : thm
    val HRAT_MUL_RINV : thm
    val HRAT_RDISTRIB : thm
    val HRAT_UP : thm
    val HREAL_ADD_ASSOC : thm
    val HREAL_ADD_ISACUT : thm
    val HREAL_ADD_SYM : thm
    val HREAL_ADD_TOTAL : thm
    val HREAL_INV_ISACUT : thm
    val HREAL_LDISTRIB : thm
    val HREAL_LT : thm
    val HREAL_LT_LEMMA : thm
    val HREAL_LT_TOTAL : thm
    val HREAL_MUL_ASSOC : thm
    val HREAL_MUL_ISACUT : thm
    val HREAL_MUL_LID : thm
    val HREAL_MUL_LINV : thm
    val HREAL_MUL_SYM : thm
    val HREAL_NOZERO : thm
    val HREAL_SUB_ADD : thm
    val HREAL_SUB_ISACUT : thm
    val HREAL_SUP : thm
    val HREAL_SUP_ISACUT : thm
    val ISACUT_HRAT : thm

  val hreal_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [hrat] Parent theory of "hreal"

   [cut_of_hrat]  Definition

      |- ∀x. cut_of_hrat x = (λy. y hrat_lt x)

   [hrat_lt]  Definition

      |- ∀x y. x hrat_lt y ⇔ ∃d. y = x hrat_add d

   [hreal_1]  Definition

      |- hreal_1 = hreal (cut_of_hrat hrat_1)

   [hreal_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION isacut rep

   [hreal_add]  Definition

      |- ∀X Y.
           X hreal_add Y =
           hreal (λw. ∃x y. (w = x hrat_add y) ∧ cut X x ∧ cut Y y)

   [hreal_inv]  Definition

      |- ∀X.
           hreal_inv X =
           hreal
             (λw.
                ∃d.
                  d hrat_lt hrat_1 ∧ ∀x. cut X x ⇒ w hrat_mul x hrat_lt d)

   [hreal_lt]  Definition

      |- ∀X Y. X hreal_lt Y ⇔ X ≠ Y ∧ ∀x. cut X x ⇒ cut Y x

   [hreal_mul]  Definition

      |- ∀X Y.
           X hreal_mul Y =
           hreal (λw. ∃x y. (w = x hrat_mul y) ∧ cut X x ∧ cut Y y)

   [hreal_sub]  Definition

      |- ∀Y X.
           Y hreal_sub X = hreal (λw. ∃x. ¬cut X x ∧ cut Y (x hrat_add w))

   [hreal_sup]  Definition

      |- ∀P. hreal_sup P = hreal (λw. ∃X. P X ∧ cut X w)

   [hreal_tybij]  Definition

      |- (∀a. hreal (cut a) = a) ∧ ∀r. isacut r ⇔ (cut (hreal r) = r)

   [isacut]  Definition

      |- ∀C.
           isacut C ⇔
           (∃x. C x) ∧ (∃x. ¬C x) ∧ (∀x y. C x ∧ y hrat_lt x ⇒ C y) ∧
           ∀x. C x ⇒ ∃y. C y ∧ x hrat_lt y

   [CUT_BOUNDED]  Theorem

      |- ∀X. ∃x. ¬cut X x

   [CUT_DOWN]  Theorem

      |- ∀X x y. cut X x ∧ y hrat_lt x ⇒ cut X y

   [CUT_ISACUT]  Theorem

      |- ∀X. isacut (cut X)

   [CUT_NEARTOP_ADD]  Theorem

      |- ∀X e. ∃x. cut X x ∧ ¬cut X (x hrat_add e)

   [CUT_NEARTOP_MUL]  Theorem

      |- ∀X u. hrat_1 hrat_lt u ⇒ ∃x. cut X x ∧ ¬cut X (u hrat_mul x)

   [CUT_NONEMPTY]  Theorem

      |- ∀X. ∃x. cut X x

   [CUT_STRADDLE]  Theorem

      |- ∀X x y. cut X x ∧ ¬cut X y ⇒ x hrat_lt y

   [CUT_UBOUND]  Theorem

      |- ∀X x y. ¬cut X x ∧ x hrat_lt y ⇒ ¬cut X y

   [CUT_UP]  Theorem

      |- ∀X x. cut X x ⇒ ∃y. cut X y ∧ x hrat_lt y

   [EQUAL_CUTS]  Theorem

      |- ∀X Y. (cut X = cut Y) ⇒ (X = Y)

   [HRAT_DOWN]  Theorem

      |- ∀x. ∃y. y hrat_lt x

   [HRAT_DOWN2]  Theorem

      |- ∀x y. ∃z. z hrat_lt x ∧ z hrat_lt y

   [HRAT_EQ_LADD]  Theorem

      |- ∀x y z. (x hrat_add y = x hrat_add z) ⇔ (y = z)

   [HRAT_EQ_LMUL]  Theorem

      |- ∀x y z. (x hrat_mul y = x hrat_mul z) ⇔ (y = z)

   [HRAT_GT_L1]  Theorem

      |- ∀x y. hrat_1 hrat_lt hrat_inv x hrat_mul y ⇔ x hrat_lt y

   [HRAT_GT_LMUL1]  Theorem

      |- ∀x y. y hrat_lt x hrat_mul y ⇔ hrat_1 hrat_lt x

   [HRAT_INV_MUL]  Theorem

      |- ∀x y. hrat_inv (x hrat_mul y) = hrat_inv x hrat_mul hrat_inv y

   [HRAT_LT_ADD2]  Theorem

      |- ∀u v x y.
           u hrat_lt x ∧ v hrat_lt y ⇒ u hrat_add v hrat_lt x hrat_add y

   [HRAT_LT_ADDL]  Theorem

      |- ∀x y. x hrat_lt x hrat_add y

   [HRAT_LT_ADDR]  Theorem

      |- ∀x y. y hrat_lt x hrat_add y

   [HRAT_LT_ANTISYM]  Theorem

      |- ∀x y. ¬(x hrat_lt y ∧ y hrat_lt x)

   [HRAT_LT_GT]  Theorem

      |- ∀x y. x hrat_lt y ⇒ ¬(y hrat_lt x)

   [HRAT_LT_L1]  Theorem

      |- ∀x y. hrat_inv x hrat_mul y hrat_lt hrat_1 ⇔ y hrat_lt x

   [HRAT_LT_LADD]  Theorem

      |- ∀x y z. z hrat_add x hrat_lt z hrat_add y ⇔ x hrat_lt y

   [HRAT_LT_LMUL]  Theorem

      |- ∀x y z. z hrat_mul x hrat_lt z hrat_mul y ⇔ x hrat_lt y

   [HRAT_LT_LMUL1]  Theorem

      |- ∀x y. x hrat_mul y hrat_lt y ⇔ x hrat_lt hrat_1

   [HRAT_LT_MUL2]  Theorem

      |- ∀u v x y.
           u hrat_lt x ∧ v hrat_lt y ⇒ u hrat_mul v hrat_lt x hrat_mul y

   [HRAT_LT_NE]  Theorem

      |- ∀x y. x hrat_lt y ⇒ x ≠ y

   [HRAT_LT_R1]  Theorem

      |- ∀x y. x hrat_mul hrat_inv y hrat_lt hrat_1 ⇔ x hrat_lt y

   [HRAT_LT_RADD]  Theorem

      |- ∀x y z. x hrat_add z hrat_lt y hrat_add z ⇔ x hrat_lt y

   [HRAT_LT_REFL]  Theorem

      |- ∀x. ¬(x hrat_lt x)

   [HRAT_LT_RMUL]  Theorem

      |- ∀x y z. x hrat_mul z hrat_lt y hrat_mul z ⇔ x hrat_lt y

   [HRAT_LT_RMUL1]  Theorem

      |- ∀x y. x hrat_mul y hrat_lt x ⇔ y hrat_lt hrat_1

   [HRAT_LT_TOTAL]  Theorem

      |- ∀x y. (x = y) ∨ x hrat_lt y ∨ y hrat_lt x

   [HRAT_LT_TRANS]  Theorem

      |- ∀x y z. x hrat_lt y ∧ y hrat_lt z ⇒ x hrat_lt z

   [HRAT_MEAN]  Theorem

      |- ∀x y. x hrat_lt y ⇒ ∃z. x hrat_lt z ∧ z hrat_lt y

   [HRAT_MUL_RID]  Theorem

      |- ∀x. x hrat_mul hrat_1 = x

   [HRAT_MUL_RINV]  Theorem

      |- ∀x. x hrat_mul hrat_inv x = hrat_1

   [HRAT_RDISTRIB]  Theorem

      |- ∀x y z.
           (x hrat_add y) hrat_mul z = x hrat_mul z hrat_add y hrat_mul z

   [HRAT_UP]  Theorem

      |- ∀x. ∃y. x hrat_lt y

   [HREAL_ADD_ASSOC]  Theorem

      |- ∀X Y Z. X hreal_add (Y hreal_add Z) = X hreal_add Y hreal_add Z

   [HREAL_ADD_ISACUT]  Theorem

      |- ∀X Y. isacut (λw. ∃x y. (w = x hrat_add y) ∧ cut X x ∧ cut Y y)

   [HREAL_ADD_SYM]  Theorem

      |- ∀X Y. X hreal_add Y = Y hreal_add X

   [HREAL_ADD_TOTAL]  Theorem

      |- ∀X Y. (X = Y) ∨ (∃D. Y = X hreal_add D) ∨ ∃D. X = Y hreal_add D

   [HREAL_INV_ISACUT]  Theorem

      |- ∀X.
           isacut
             (λw.
                ∃d.
                  d hrat_lt hrat_1 ∧ ∀x. cut X x ⇒ w hrat_mul x hrat_lt d)

   [HREAL_LDISTRIB]  Theorem

      |- ∀X Y Z.
           X hreal_mul (Y hreal_add Z) =
           X hreal_mul Y hreal_add X hreal_mul Z

   [HREAL_LT]  Theorem

      |- ∀X Y. X hreal_lt Y ⇔ ∃D. Y = X hreal_add D

   [HREAL_LT_LEMMA]  Theorem

      |- ∀X Y. X hreal_lt Y ⇒ ∃x. ¬cut X x ∧ cut Y x

   [HREAL_LT_TOTAL]  Theorem

      |- ∀X Y. (X = Y) ∨ X hreal_lt Y ∨ Y hreal_lt X

   [HREAL_MUL_ASSOC]  Theorem

      |- ∀X Y Z. X hreal_mul (Y hreal_mul Z) = X hreal_mul Y hreal_mul Z

   [HREAL_MUL_ISACUT]  Theorem

      |- ∀X Y. isacut (λw. ∃x y. (w = x hrat_mul y) ∧ cut X x ∧ cut Y y)

   [HREAL_MUL_LID]  Theorem

      |- ∀X. hreal_1 hreal_mul X = X

   [HREAL_MUL_LINV]  Theorem

      |- ∀X. hreal_inv X hreal_mul X = hreal_1

   [HREAL_MUL_SYM]  Theorem

      |- ∀X Y. X hreal_mul Y = Y hreal_mul X

   [HREAL_NOZERO]  Theorem

      |- ∀X Y. X hreal_add Y ≠ X

   [HREAL_SUB_ADD]  Theorem

      |- ∀X Y. X hreal_lt Y ⇒ (Y hreal_sub X hreal_add X = Y)

   [HREAL_SUB_ISACUT]  Theorem

      |- ∀X Y.
           X hreal_lt Y ⇒ isacut (λw. ∃x. ¬cut X x ∧ cut Y (x hrat_add w))

   [HREAL_SUP]  Theorem

      |- ∀P.
           (∃X. P X) ∧ (∃Y. ∀X. P X ⇒ X hreal_lt Y) ⇒
           ∀Y. (∃X. P X ∧ Y hreal_lt X) ⇔ Y hreal_lt hreal_sup P

   [HREAL_SUP_ISACUT]  Theorem

      |- ∀P.
           (∃X. P X) ∧ (∃Y. ∀X. P X ⇒ X hreal_lt Y) ⇒
           isacut (λw. ∃X. P X ∧ cut X w)

   [ISACUT_HRAT]  Theorem

      |- ∀h. isacut (cut_of_hrat h)


*)
end
