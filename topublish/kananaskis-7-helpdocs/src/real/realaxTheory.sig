signature realaxTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val hreal_of_real : thm
    val hreal_of_treal : thm
    val real_0 : thm
    val real_1 : thm
    val real_ABS_def : thm
    val real_REP_def : thm
    val real_TY_DEF : thm
    val real_add : thm
    val real_bijections : thm
    val real_inv : thm
    val real_lt : thm
    val real_mul : thm
    val real_neg : thm
    val real_of_hreal : thm
    val treal_0 : thm
    val treal_1 : thm
    val treal_add : thm
    val treal_eq : thm
    val treal_inv : thm
    val treal_lt : thm
    val treal_mul : thm
    val treal_neg : thm
    val treal_of_hreal : thm
  
  (*  Theorems  *)
    val HREAL_EQ_ADDL : thm
    val HREAL_EQ_ADDR : thm
    val HREAL_EQ_LADD : thm
    val HREAL_LT_ADD2 : thm
    val HREAL_LT_ADDL : thm
    val HREAL_LT_ADDR : thm
    val HREAL_LT_GT : thm
    val HREAL_LT_LADD : thm
    val HREAL_LT_NE : thm
    val HREAL_LT_REFL : thm
    val HREAL_RDISTRIB : thm
    val REAL_10 : thm
    val REAL_ADD_ASSOC : thm
    val REAL_ADD_LID : thm
    val REAL_ADD_LINV : thm
    val REAL_ADD_SYM : thm
    val REAL_INV_0 : thm
    val REAL_ISO_EQ : thm
    val REAL_LDISTRIB : thm
    val REAL_LT_IADD : thm
    val REAL_LT_MUL : thm
    val REAL_LT_REFL : thm
    val REAL_LT_TOTAL : thm
    val REAL_LT_TRANS : thm
    val REAL_MUL_ASSOC : thm
    val REAL_MUL_LID : thm
    val REAL_MUL_LINV : thm
    val REAL_MUL_SYM : thm
    val REAL_POS : thm
    val REAL_SUP_ALLPOS : thm
    val SUP_ALLPOS_LEMMA1 : thm
    val SUP_ALLPOS_LEMMA2 : thm
    val SUP_ALLPOS_LEMMA3 : thm
    val SUP_ALLPOS_LEMMA4 : thm
    val TREAL_10 : thm
    val TREAL_ADD_ASSOC : thm
    val TREAL_ADD_LID : thm
    val TREAL_ADD_LINV : thm
    val TREAL_ADD_SYM : thm
    val TREAL_ADD_WELLDEF : thm
    val TREAL_ADD_WELLDEFR : thm
    val TREAL_BIJ : thm
    val TREAL_BIJ_WELLDEF : thm
    val TREAL_EQ_AP : thm
    val TREAL_EQ_EQUIV : thm
    val TREAL_EQ_REFL : thm
    val TREAL_EQ_SYM : thm
    val TREAL_EQ_TRANS : thm
    val TREAL_INV_0 : thm
    val TREAL_INV_WELLDEF : thm
    val TREAL_ISO : thm
    val TREAL_LDISTRIB : thm
    val TREAL_LT_ADD : thm
    val TREAL_LT_MUL : thm
    val TREAL_LT_REFL : thm
    val TREAL_LT_TOTAL : thm
    val TREAL_LT_TRANS : thm
    val TREAL_LT_WELLDEF : thm
    val TREAL_LT_WELLDEFL : thm
    val TREAL_LT_WELLDEFR : thm
    val TREAL_MUL_ASSOC : thm
    val TREAL_MUL_LID : thm
    val TREAL_MUL_LINV : thm
    val TREAL_MUL_SYM : thm
    val TREAL_MUL_WELLDEF : thm
    val TREAL_MUL_WELLDEFR : thm
    val TREAL_NEG_WELLDEF : thm
    val real_ABS_REP_CLASS : thm
    val real_QUOTIENT : thm
  
  val realax_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [hreal] Parent theory of "realax"
   
   [hreal_of_real]  Definition
      
      |- ∀T1. hreal_of_real T1 = hreal_of_treal (real_REP T1)
   
   [hreal_of_treal]  Definition
      
      |- ∀x y. hreal_of_treal (x,y) = @d. x = y hreal_add d
   
   [real_0]  Definition
      
      |- real_0 = real_ABS treal_0
   
   [real_1]  Definition
      
      |- real_1 = real_ABS treal_1
   
   [real_ABS_def]  Definition
      
      |- ∀r. real_ABS r = real_ABS_CLASS ($treal_eq r)
   
   [real_REP_def]  Definition
      
      |- ∀a. real_REP a = $@ (real_REP_CLASS a)
   
   [real_TY_DEF]  Definition
      
      |- ∃rep.
           TYPE_DEFINITION (λc. ∃r. r treal_eq r ∧ (c = $treal_eq r)) rep
   
   [real_add]  Definition
      
      |- ∀T1 T2. T1 + T2 = real_ABS (real_REP T1 treal_add real_REP T2)
   
   [real_bijections]  Definition
      
      |- (∀a. real_ABS_CLASS (real_REP_CLASS a) = a) ∧
         ∀r.
           (λc. ∃r. r treal_eq r ∧ (c = $treal_eq r)) r ⇔
           (real_REP_CLASS (real_ABS_CLASS r) = r)
   
   [real_inv]  Definition
      
      |- ∀T1. inv T1 = real_ABS (treal_inv (real_REP T1))
   
   [real_lt]  Definition
      
      |- ∀T1 T2. T1 < T2 ⇔ real_REP T1 treal_lt real_REP T2
   
   [real_mul]  Definition
      
      |- ∀T1 T2. T1 * T2 = real_ABS (real_REP T1 treal_mul real_REP T2)
   
   [real_neg]  Definition
      
      |- ∀T1. -T1 = real_ABS (treal_neg (real_REP T1))
   
   [real_of_hreal]  Definition
      
      |- ∀T1. real_of_hreal T1 = real_ABS (treal_of_hreal T1)
   
   [treal_0]  Definition
      
      |- treal_0 = (hreal_1,hreal_1)
   
   [treal_1]  Definition
      
      |- treal_1 = (hreal_1 hreal_add hreal_1,hreal_1)
   
   [treal_add]  Definition
      
      |- ∀x1 y1 x2 y2.
           (x1,y1) treal_add (x2,y2) = (x1 hreal_add x2,y1 hreal_add y2)
   
   [treal_eq]  Definition
      
      |- ∀x1 y1 x2 y2.
           (x1,y1) treal_eq (x2,y2) ⇔ (x1 hreal_add y2 = x2 hreal_add y1)
   
   [treal_inv]  Definition
      
      |- ∀x y.
           treal_inv (x,y) =
           if x = y then
             treal_0
           else if y hreal_lt x then
             (hreal_inv (x hreal_sub y) hreal_add hreal_1,hreal_1)
           else
             (hreal_1,hreal_inv (y hreal_sub x) hreal_add hreal_1)
   
   [treal_lt]  Definition
      
      |- ∀x1 y1 x2 y2.
           (x1,y1) treal_lt (x2,y2) ⇔
           x1 hreal_add y2 hreal_lt x2 hreal_add y1
   
   [treal_mul]  Definition
      
      |- ∀x1 y1 x2 y2.
           (x1,y1) treal_mul (x2,y2) =
           (x1 hreal_mul x2 hreal_add y1 hreal_mul y2,
            x1 hreal_mul y2 hreal_add y1 hreal_mul x2)
   
   [treal_neg]  Definition
      
      |- ∀x y. treal_neg (x,y) = (y,x)
   
   [treal_of_hreal]  Definition
      
      |- ∀x. treal_of_hreal x = (x hreal_add hreal_1,hreal_1)
   
   [HREAL_EQ_ADDL]  Theorem
      
      |- ∀x y. x ≠ x hreal_add y
   
   [HREAL_EQ_ADDR]  Theorem
      
      |- ∀x y. x hreal_add y ≠ x
   
   [HREAL_EQ_LADD]  Theorem
      
      |- ∀x y z. (x hreal_add y = x hreal_add z) ⇔ (y = z)
   
   [HREAL_LT_ADD2]  Theorem
      
      |- ∀x1 x2 y1 y2.
           x1 hreal_lt y1 ∧ x2 hreal_lt y2 ⇒
           x1 hreal_add x2 hreal_lt y1 hreal_add y2
   
   [HREAL_LT_ADDL]  Theorem
      
      |- ∀x y. x hreal_lt x hreal_add y
   
   [HREAL_LT_ADDR]  Theorem
      
      |- ∀x y. ¬(x hreal_add y hreal_lt x)
   
   [HREAL_LT_GT]  Theorem
      
      |- ∀x y. x hreal_lt y ⇒ ¬(y hreal_lt x)
   
   [HREAL_LT_LADD]  Theorem
      
      |- ∀x y z. x hreal_add y hreal_lt x hreal_add z ⇔ y hreal_lt z
   
   [HREAL_LT_NE]  Theorem
      
      |- ∀x y. x hreal_lt y ⇒ x ≠ y
   
   [HREAL_LT_REFL]  Theorem
      
      |- ∀x. ¬(x hreal_lt x)
   
   [HREAL_RDISTRIB]  Theorem
      
      |- ∀x y z.
           (x hreal_add y) hreal_mul z =
           x hreal_mul z hreal_add y hreal_mul z
   
   [REAL_10]  Theorem
      
      |- real_1 ≠ real_0
   
   [REAL_ADD_ASSOC]  Theorem
      
      |- ∀x y z. x + (y + z) = x + y + z
   
   [REAL_ADD_LID]  Theorem
      
      |- ∀x. real_0 + x = x
   
   [REAL_ADD_LINV]  Theorem
      
      |- ∀x. -x + x = real_0
   
   [REAL_ADD_SYM]  Theorem
      
      |- ∀x y. x + y = y + x
   
   [REAL_INV_0]  Theorem
      
      |- inv real_0 = real_0
   
   [REAL_ISO_EQ]  Theorem
      
      |- ∀h i. h hreal_lt i ⇔ real_of_hreal h < real_of_hreal i
   
   [REAL_LDISTRIB]  Theorem
      
      |- ∀x y z. x * (y + z) = x * y + x * z
   
   [REAL_LT_IADD]  Theorem
      
      |- ∀x y z. y < z ⇒ x + y < x + z
   
   [REAL_LT_MUL]  Theorem
      
      |- ∀x y. real_0 < x ∧ real_0 < y ⇒ real_0 < x * y
   
   [REAL_LT_REFL]  Theorem
      
      |- ∀x. ¬(x < x)
   
   [REAL_LT_TOTAL]  Theorem
      
      |- ∀x y. (x = y) ∨ x < y ∨ y < x
   
   [REAL_LT_TRANS]  Theorem
      
      |- ∀x y z. x < y ∧ y < z ⇒ x < z
   
   [REAL_MUL_ASSOC]  Theorem
      
      |- ∀x y z. x * (y * z) = x * y * z
   
   [REAL_MUL_LID]  Theorem
      
      |- ∀x. real_1 * x = x
   
   [REAL_MUL_LINV]  Theorem
      
      |- ∀x. x ≠ real_0 ⇒ (inv x * x = real_1)
   
   [REAL_MUL_SYM]  Theorem
      
      |- ∀x y. x * y = y * x
   
   [REAL_POS]  Theorem
      
      |- ∀X. real_0 < real_of_hreal X
   
   [REAL_SUP_ALLPOS]  Theorem
      
      |- ∀P.
           (∀x. P x ⇒ real_0 < x) ∧ (∃x. P x) ∧ (∃z. ∀x. P x ⇒ x < z) ⇒
           ∃s. ∀y. (∃x. P x ∧ y < x) ⇔ y < s
   
   [SUP_ALLPOS_LEMMA1]  Theorem
      
      |- ∀P y.
           (∀x. P x ⇒ real_0 < x) ⇒
           ((∃x. P x ∧ y < x) ⇔
            ∃X. P (real_of_hreal X) ∧ y < real_of_hreal X)
   
   [SUP_ALLPOS_LEMMA2]  Theorem
      
      |- ∀P X. P (real_of_hreal X) ⇔ (λh. P (real_of_hreal h)) X
   
   [SUP_ALLPOS_LEMMA3]  Theorem
      
      |- ∀P.
           (∀x. P x ⇒ real_0 < x) ∧ (∃x. P x) ∧ (∃z. ∀x. P x ⇒ x < z) ⇒
           (∃X. (λh. P (real_of_hreal h)) X) ∧
           ∃Y. ∀X. (λh. P (real_of_hreal h)) X ⇒ X hreal_lt Y
   
   [SUP_ALLPOS_LEMMA4]  Theorem
      
      |- ∀y. ¬(real_0 < y) ⇒ ∀x. y < real_of_hreal x
   
   [TREAL_10]  Theorem
      
      |- ¬(treal_1 treal_eq treal_0)
   
   [TREAL_ADD_ASSOC]  Theorem
      
      |- ∀x y z. x treal_add (y treal_add z) = x treal_add y treal_add z
   
   [TREAL_ADD_LID]  Theorem
      
      |- ∀x. treal_0 treal_add x treal_eq x
   
   [TREAL_ADD_LINV]  Theorem
      
      |- ∀x. treal_neg x treal_add x treal_eq treal_0
   
   [TREAL_ADD_SYM]  Theorem
      
      |- ∀x y. x treal_add y = y treal_add x
   
   [TREAL_ADD_WELLDEF]  Theorem
      
      |- ∀x1 x2 y1 y2.
           x1 treal_eq x2 ∧ y1 treal_eq y2 ⇒
           x1 treal_add y1 treal_eq x2 treal_add y2
   
   [TREAL_ADD_WELLDEFR]  Theorem
      
      |- ∀x1 x2 y. x1 treal_eq x2 ⇒ x1 treal_add y treal_eq x2 treal_add y
   
   [TREAL_BIJ]  Theorem
      
      |- (∀h. hreal_of_treal (treal_of_hreal h) = h) ∧
         ∀r.
           treal_0 treal_lt r ⇔
           treal_of_hreal (hreal_of_treal r) treal_eq r
   
   [TREAL_BIJ_WELLDEF]  Theorem
      
      |- ∀h i. h treal_eq i ⇒ (hreal_of_treal h = hreal_of_treal i)
   
   [TREAL_EQ_AP]  Theorem
      
      |- ∀p q. (p = q) ⇒ p treal_eq q
   
   [TREAL_EQ_EQUIV]  Theorem
      
      |- ∀p q. p treal_eq q ⇔ ($treal_eq p = $treal_eq q)
   
   [TREAL_EQ_REFL]  Theorem
      
      |- ∀x. x treal_eq x
   
   [TREAL_EQ_SYM]  Theorem
      
      |- ∀x y. x treal_eq y ⇔ y treal_eq x
   
   [TREAL_EQ_TRANS]  Theorem
      
      |- ∀x y z. x treal_eq y ∧ y treal_eq z ⇒ x treal_eq z
   
   [TREAL_INV_0]  Theorem
      
      |- treal_inv treal_0 treal_eq treal_0
   
   [TREAL_INV_WELLDEF]  Theorem
      
      |- ∀x1 x2. x1 treal_eq x2 ⇒ treal_inv x1 treal_eq treal_inv x2
   
   [TREAL_ISO]  Theorem
      
      |- ∀h i. h hreal_lt i ⇒ treal_of_hreal h treal_lt treal_of_hreal i
   
   [TREAL_LDISTRIB]  Theorem
      
      |- ∀x y z.
           x treal_mul (y treal_add z) =
           x treal_mul y treal_add x treal_mul z
   
   [TREAL_LT_ADD]  Theorem
      
      |- ∀x y z. y treal_lt z ⇒ x treal_add y treal_lt x treal_add z
   
   [TREAL_LT_MUL]  Theorem
      
      |- ∀x y.
           treal_0 treal_lt x ∧ treal_0 treal_lt y ⇒
           treal_0 treal_lt x treal_mul y
   
   [TREAL_LT_REFL]  Theorem
      
      |- ∀x. ¬(x treal_lt x)
   
   [TREAL_LT_TOTAL]  Theorem
      
      |- ∀x y. x treal_eq y ∨ x treal_lt y ∨ y treal_lt x
   
   [TREAL_LT_TRANS]  Theorem
      
      |- ∀x y z. x treal_lt y ∧ y treal_lt z ⇒ x treal_lt z
   
   [TREAL_LT_WELLDEF]  Theorem
      
      |- ∀x1 x2 y1 y2.
           x1 treal_eq x2 ∧ y1 treal_eq y2 ⇒
           (x1 treal_lt y1 ⇔ x2 treal_lt y2)
   
   [TREAL_LT_WELLDEFL]  Theorem
      
      |- ∀x y1 y2. y1 treal_eq y2 ⇒ (x treal_lt y1 ⇔ x treal_lt y2)
   
   [TREAL_LT_WELLDEFR]  Theorem
      
      |- ∀x1 x2 y. x1 treal_eq x2 ⇒ (x1 treal_lt y ⇔ x2 treal_lt y)
   
   [TREAL_MUL_ASSOC]  Theorem
      
      |- ∀x y z. x treal_mul (y treal_mul z) = x treal_mul y treal_mul z
   
   [TREAL_MUL_LID]  Theorem
      
      |- ∀x. treal_1 treal_mul x treal_eq x
   
   [TREAL_MUL_LINV]  Theorem
      
      |- ∀x.
           ¬(x treal_eq treal_0) ⇒ treal_inv x treal_mul x treal_eq treal_1
   
   [TREAL_MUL_SYM]  Theorem
      
      |- ∀x y. x treal_mul y = y treal_mul x
   
   [TREAL_MUL_WELLDEF]  Theorem
      
      |- ∀x1 x2 y1 y2.
           x1 treal_eq x2 ∧ y1 treal_eq y2 ⇒
           x1 treal_mul y1 treal_eq x2 treal_mul y2
   
   [TREAL_MUL_WELLDEFR]  Theorem
      
      |- ∀x1 x2 y. x1 treal_eq x2 ⇒ x1 treal_mul y treal_eq x2 treal_mul y
   
   [TREAL_NEG_WELLDEF]  Theorem
      
      |- ∀x1 x2. x1 treal_eq x2 ⇒ treal_neg x1 treal_eq treal_neg x2
   
   [real_ABS_REP_CLASS]  Theorem
      
      |- (∀a. real_ABS_CLASS (real_REP_CLASS a) = a) ∧
         ∀c.
           (∃r. r treal_eq r ∧ (c = $treal_eq r)) ⇔
           (real_REP_CLASS (real_ABS_CLASS c) = c)
   
   [real_QUOTIENT]  Theorem
      
      |- QUOTIENT $treal_eq real_ABS real_REP
   
   
*)
end
