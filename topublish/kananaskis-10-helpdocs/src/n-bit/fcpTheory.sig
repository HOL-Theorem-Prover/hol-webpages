signature fcpTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val FCP : thm
    val FCP_CONCAT_def : thm
    val FCP_CONS_def : thm
    val FCP_EVERY_def : thm
    val FCP_EXISTS_def : thm
    val FCP_FOLD_def : thm
    val FCP_HD_def : thm
    val FCP_MAP_def : thm
    val FCP_TL_def : thm
    val FCP_UPDATE_def : thm
    val FCP_ZIP_def : thm
    val HAS_SIZE_def : thm
    val L2V_def : thm
    val V2L_def : thm
    val bit0_TY_DEF : thm
    val bit0_case_def : thm
    val bit0_size_def : thm
    val bit1_TY_DEF : thm
    val bit1_case_def : thm
    val bit1_size_def : thm
    val cart_TY_DEF : thm
    val cart_tybij : thm
    val dimindex_def : thm
    val fcp_case_def : thm
    val fcp_index : thm
    val finite_image_TY_DEF : thm
    val finite_image_tybij : thm
    val finite_index_def : thm

  (*  Theorems  *)
    val APPLY_FCP_UPDATE_ID : thm
    val CART_EQ : thm
    val DIMINDEX_GE_1 : thm
    val EL_V2L : thm
    val FCP_APPLY_UPDATE_THM : thm
    val FCP_BETA : thm
    val FCP_CONS : thm
    val FCP_ETA : thm
    val FCP_EVERY : thm
    val FCP_EXISTS : thm
    val FCP_HD : thm
    val FCP_MAP : thm
    val FCP_TL : thm
    val FCP_UNIQUE : thm
    val FCP_UPDATE_COMMUTES : thm
    val FCP_UPDATE_EQ : thm
    val FCP_UPDATE_IMP_ID : thm
    val LENGTH_V2L : thm
    val NOT_FINITE_IMP_dimindex_1 : thm
    val NULL_V2L : thm
    val READ_L2V : thm
    val READ_TL : thm
    val V2L_L2V : thm
    val bit0_11 : thm
    val bit0_Axiom : thm
    val bit0_case_cong : thm
    val bit0_distinct : thm
    val bit0_induction : thm
    val bit0_nchotomy : thm
    val bit1_11 : thm
    val bit1_Axiom : thm
    val bit1_case_cong : thm
    val bit1_distinct : thm
    val bit1_induction : thm
    val bit1_nchotomy : thm
    val card_dimindex : thm
    val datatype_bit0 : thm
    val datatype_bit1 : thm
    val fcp_Axiom : thm
    val fcp_ind : thm
    val fcp_subst_comp : thm
    val finite_bit0 : thm
    val finite_bit1 : thm
    val finite_one : thm
    val finite_sum : thm
    val index_bit0 : thm
    val index_bit1 : thm
    val index_comp : thm
    val index_one : thm
    val index_sum : thm

  val fcp_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "fcp"

   [FCP]  Definition

      |- $FCP = (λg. @f. ∀i. i < dimindex (:β) ⇒ (f ' i = g i))

   [FCP_CONCAT_def]  Definition

      |- ∀a b.
           FCP_CONCAT a b =
           FCP i.
             if i < dimindex (:γ) then b ' i else a ' (i − dimindex (:γ))

   [FCP_CONS_def]  Definition

      |- ∀h v. FCP_CONS h v = (0 :+ h) (FCP i. v ' (PRE i))

   [FCP_EVERY_def]  Definition

      |- ∀P v. FCP_EVERY P v ⇔ ∀i. dimindex (:α) ≤ i ∨ P (v ' i)

   [FCP_EXISTS_def]  Definition

      |- ∀P v. FCP_EXISTS P v ⇔ ∃i. i < dimindex (:α) ∧ P (v ' i)

   [FCP_FOLD_def]  Definition

      |- ∀f i v. FCP_FOLD f i v = FOLDL f i (V2L v)

   [FCP_HD_def]  Definition

      |- ∀v. FCP_HD v = v ' 0

   [FCP_MAP_def]  Definition

      |- ∀f v. FCP_MAP f v = FCP i. f (v ' i)

   [FCP_TL_def]  Definition

      |- ∀v. FCP_TL v = FCP i. v ' (SUC i)

   [FCP_UPDATE_def]  Definition

      |- ∀a b. a :+ b = (λm. FCP c. if a = c then b else m ' c)

   [FCP_ZIP_def]  Definition

      |- ∀a b. FCP_ZIP a b = FCP i. (a ' i,b ' i)

   [HAS_SIZE_def]  Definition

      |- ∀s n. s HAS_SIZE n ⇔ FINITE s ∧ (CARD s = n)

   [L2V_def]  Definition

      |- ∀L. L2V L = FCP i. EL i L

   [V2L_def]  Definition

      |- ∀v. V2L v = GENLIST ($' v) (dimindex (:β))

   [bit0_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'bit0' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) a (λn. ind_type$BOTTOM))
                          a) ⇒
                     'bit0' a0) ⇒
                  'bit0' a0) rep

   [bit0_case_def]  Definition

      |- (∀a f f1. bit0_CASE (BIT0A a) f f1 = f a) ∧
         ∀a f f1. bit0_CASE (BIT0B a) f f1 = f1 a

   [bit0_size_def]  Definition

      |- (∀f a. bit0_size f (BIT0A a) = 1 + f a) ∧
         ∀f a. bit0_size f (BIT0B a) = 1 + f a

   [bit1_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'bit1' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) a (λn. ind_type$BOTTOM))
                          a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC (SUC 0)) ARB
                        (λn. ind_type$BOTTOM)) ⇒
                     'bit1' a0) ⇒
                  'bit1' a0) rep

   [bit1_case_def]  Definition

      |- (∀a f f1 v. bit1_CASE (BIT1A a) f f1 v = f a) ∧
         (∀a f f1 v. bit1_CASE (BIT1B a) f f1 v = f1 a) ∧
         ∀f f1 v. bit1_CASE BIT1C f f1 v = v

   [bit1_size_def]  Definition

      |- (∀f a. bit1_size f (BIT1A a) = 1 + f a) ∧
         (∀f a. bit1_size f (BIT1B a) = 1 + f a) ∧
         ∀f. bit1_size f BIT1C = 0

   [cart_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λf. T) rep

   [cart_tybij]  Definition

      |- (∀a. mk_cart (dest_cart a) = a) ∧
         ∀r. (λf. T) r ⇔ (dest_cart (mk_cart r) = r)

   [dimindex_def]  Definition

      |- dimindex (:α) = if FINITE 𝕌(:α) then CARD 𝕌(:α) else 1

   [fcp_case_def]  Definition

      |- ∀h f. fcp_CASE (mk_cart h) f = f h

   [fcp_index]  Definition

      |- ∀x i. x ' i = dest_cart x (finite_index i)

   [finite_image_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λx. (x = ARB) ∨ FINITE 𝕌(:α)) rep

   [finite_image_tybij]  Definition

      |- (∀a. mk_finite_image (dest_finite_image a) = a) ∧
         ∀r.
           (λx. (x = ARB) ∨ FINITE 𝕌(:α)) r ⇔
           (dest_finite_image (mk_finite_image r) = r)

   [finite_index_def]  Definition

      |- finite_index = @f. ∀x. ∃!n. n < dimindex (:α) ∧ (f n = x)

   [APPLY_FCP_UPDATE_ID]  Theorem

      |- ∀m a. (a :+ m ' a) m = m

   [CART_EQ]  Theorem

      |- ∀x y. (x = y) ⇔ ∀i. i < dimindex (:β) ⇒ (x ' i = y ' i)

   [DIMINDEX_GE_1]  Theorem

      |- 1 ≤ dimindex (:α)

   [EL_V2L]  Theorem

      |- ∀i v. i < dimindex (:β) ⇒ (EL i (V2L v) = v ' i)

   [FCP_APPLY_UPDATE_THM]  Theorem

      |- ∀m a w b.
           (a :+ w) m ' b =
           if b < dimindex (:β) then if a = b then w else m ' b
           else FAIL $' index out of range ((a :+ w) m) b

   [FCP_BETA]  Theorem

      |- ∀i. i < dimindex (:β) ⇒ ($FCP g ' i = g i)

   [FCP_CONS]  Theorem

      |- ∀a v. FCP_CONS a v = L2V (a::V2L v)

   [FCP_ETA]  Theorem

      |- ∀g. (FCP i. g ' i) = g

   [FCP_EVERY]  Theorem

      |- ∀P v. FCP_EVERY P v ⇔ EVERY P (V2L v)

   [FCP_EXISTS]  Theorem

      |- ∀P v. FCP_EXISTS P v ⇔ EXISTS P (V2L v)

   [FCP_HD]  Theorem

      |- ∀v. FCP_HD v = HD (V2L v)

   [FCP_MAP]  Theorem

      |- ∀f v. FCP_MAP f v = L2V (MAP f (V2L v))

   [FCP_TL]  Theorem

      |- ∀v.
           1 < dimindex (:β) ∧ (dimindex (:γ) = dimindex (:β) − 1) ⇒
           (FCP_TL v = L2V (TL (V2L v)))

   [FCP_UNIQUE]  Theorem

      |- ∀f g. (∀i. i < dimindex (:β) ⇒ (f ' i = g i)) ⇔ ($FCP g = f)

   [FCP_UPDATE_COMMUTES]  Theorem

      |- ∀m a b c d.
           a ≠ b ⇒ ((a :+ c) ((b :+ d) m) = (b :+ d) ((a :+ c) m))

   [FCP_UPDATE_EQ]  Theorem

      |- ∀m a b c. (a :+ c) ((a :+ b) m) = (a :+ c) m

   [FCP_UPDATE_IMP_ID]  Theorem

      |- ∀m a v. (m ' a = v) ⇒ ((a :+ v) m = m)

   [LENGTH_V2L]  Theorem

      |- ∀v. LENGTH (V2L v) = dimindex (:β)

   [NOT_FINITE_IMP_dimindex_1]  Theorem

      |- INFINITE 𝕌(:α) ⇒ (dimindex (:α) = 1)

   [NULL_V2L]  Theorem

      |- ∀v. ¬NULL (V2L v)

   [READ_L2V]  Theorem

      |- ∀i a. i < dimindex (:β) ⇒ (L2V a ' i = EL i a)

   [READ_TL]  Theorem

      |- ∀i a. i < dimindex (:β) ⇒ (FCP_TL a ' i = a ' (SUC i))

   [V2L_L2V]  Theorem

      |- ∀x. (dimindex (:β) = LENGTH x) ⇒ (V2L (L2V x) = x)

   [bit0_11]  Theorem

      |- (∀a a'. (BIT0A a = BIT0A a') ⇔ (a = a')) ∧
         ∀a a'. (BIT0B a = BIT0B a') ⇔ (a = a')

   [bit0_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (BIT0A a) = f0 a) ∧ ∀a. fn (BIT0B a) = f1 a

   [bit0_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = BIT0A a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = BIT0B a) ⇒ (f1 a = f1' a)) ⇒
           (bit0_CASE M f f1 = bit0_CASE M' f' f1')

   [bit0_distinct]  Theorem

      |- ∀a' a. BIT0A a ≠ BIT0B a'

   [bit0_induction]  Theorem

      |- ∀P. (∀a. P (BIT0A a)) ∧ (∀a. P (BIT0B a)) ⇒ ∀b. P b

   [bit0_nchotomy]  Theorem

      |- ∀bb. (∃a. bb = BIT0A a) ∨ ∃a. bb = BIT0B a

   [bit1_11]  Theorem

      |- (∀a a'. (BIT1A a = BIT1A a') ⇔ (a = a')) ∧
         ∀a a'. (BIT1B a = BIT1B a') ⇔ (a = a')

   [bit1_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (∀a. fn (BIT1A a) = f0 a) ∧ (∀a. fn (BIT1B a) = f1 a) ∧
             (fn BIT1C = f2)

   [bit1_case_cong]  Theorem

      |- ∀M M' f f1 v.
           (M = M') ∧ (∀a. (M' = BIT1A a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = BIT1B a) ⇒ (f1 a = f1' a)) ∧
           ((M' = BIT1C) ⇒ (v = v')) ⇒
           (bit1_CASE M f f1 v = bit1_CASE M' f' f1' v')

   [bit1_distinct]  Theorem

      |- (∀a' a. BIT1A a ≠ BIT1B a') ∧ (∀a. BIT1A a ≠ BIT1C) ∧
         ∀a. BIT1B a ≠ BIT1C

   [bit1_induction]  Theorem

      |- ∀P. (∀a. P (BIT1A a)) ∧ (∀a. P (BIT1B a)) ∧ P BIT1C ⇒ ∀b. P b

   [bit1_nchotomy]  Theorem

      |- ∀bb. (∃a. bb = BIT1A a) ∨ (∃a. bb = BIT1B a) ∨ (bb = BIT1C)

   [card_dimindex]  Theorem

      |- FINITE 𝕌(:α) ⇒ (CARD 𝕌(:α) = dimindex (:α))

   [datatype_bit0]  Theorem

      |- DATATYPE (bit0 BIT0A BIT0B)

   [datatype_bit1]  Theorem

      |- DATATYPE (bit1 BIT1A BIT1B BIT1C)

   [fcp_Axiom]  Theorem

      |- ∀f. ∃g. ∀h. g (mk_cart h) = f h

   [fcp_ind]  Theorem

      |- ∀P. (∀f. P (mk_cart f)) ⇒ ∀a. P a

   [fcp_subst_comp]  Theorem

      |- ∀a b f. (x :+ y) ($FCP f) = FCP c. if x = c then y else f c

   [finite_bit0]  Theorem

      |- FINITE 𝕌(:α bit0) ⇔ FINITE 𝕌(:α)

   [finite_bit1]  Theorem

      |- FINITE 𝕌(:α bit1) ⇔ FINITE 𝕌(:α)

   [finite_one]  Theorem

      |- FINITE 𝕌(:unit)

   [finite_sum]  Theorem

      |- FINITE 𝕌(:α + β) ⇔ FINITE 𝕌(:α) ∧ FINITE 𝕌(:β)

   [index_bit0]  Theorem

      |- dimindex (:α bit0) = if FINITE 𝕌(:α) then 2 * dimindex (:α) else 1

   [index_bit1]  Theorem

      |- dimindex (:α bit1) =
         if FINITE 𝕌(:α) then 2 * dimindex (:α) + 1 else 1

   [index_comp]  Theorem

      |- ∀f n.
           $FCP f ' n =
           if n < dimindex (:β) then f n
           else FAIL $' FCP out of bounds ($FCP f) n

   [index_one]  Theorem

      |- dimindex (:unit) = 1

   [index_sum]  Theorem

      |- dimindex (:α + β) =
         if FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) then dimindex (:α) + dimindex (:β)
         else 1


*)
end
