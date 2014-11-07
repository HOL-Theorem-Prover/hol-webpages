signature integer_wordTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val INT_MAX_def : thm
    val INT_MIN_def : thm
    val UINT_MAX_def : thm
    val fromString_primitive_def : thm
    val i2w_def : thm
    val saturate_i2sw_def : thm
    val saturate_i2w_def : thm
    val saturate_sw2sw_def : thm
    val saturate_sw2w_def : thm
    val saturate_w2sw_def : thm
    val signed_saturate_add_def : thm
    val signed_saturate_sub_def : thm
    val toString_def : thm
    val w2i_def : thm

  (*  Theorems  *)
    val INT_BOUND_ORDER : thm
    val INT_MAX : thm
    val INT_MAX_MONOTONIC : thm
    val INT_MIN : thm
    val INT_MIN_MONOTONIC : thm
    val INT_ZERO_LE_INT_MAX : thm
    val INT_ZERO_LT_INT_MAX : thm
    val INT_ZERO_LT_INT_MIN : thm
    val INT_ZERO_LT_UINT_MAX : thm
    val MULT_MINUS_ONE : thm
    val ONE_LE_TWOEXP : thm
    val UINT_MAX : thm
    val WORD_GEi : thm
    val WORD_GTi : thm
    val WORD_LEi : thm
    val WORD_LTi : thm
    val different_sign_then_no_overflow : thm
    val fromString_def : thm
    val fromString_ind : thm
    val i2w_0 : thm
    val i2w_DIV : thm
    val i2w_INT_MAX : thm
    val i2w_INT_MIN : thm
    val i2w_UINT_MAX : thm
    val i2w_minus_1 : thm
    val i2w_w2i : thm
    val int_word_nchotomy : thm
    val overflow : thm
    val ranged_int_word_nchotomy : thm
    val saturate_i2sw : thm
    val saturate_i2sw_0 : thm
    val saturate_i2w_0 : thm
    val saturate_sw2sw : thm
    val saturate_sw2w : thm
    val saturate_w2sw : thm
    val signed_saturate_add : thm
    val signed_saturate_sub : thm
    val sw2sw_i2w : thm
    val w2i_1 : thm
    val w2i_11 : thm
    val w2i_11_lift : thm
    val w2i_INT_MAXw : thm
    val w2i_INT_MINw : thm
    val w2i_UINT_MAXw : thm
    val w2i_ge : thm
    val w2i_i2w : thm
    val w2i_i2w_id : thm
    val w2i_i2w_neg : thm
    val w2i_i2w_pos : thm
    val w2i_le : thm
    val w2i_lt_0 : thm
    val w2i_minus_1 : thm
    val w2i_n2w_mod : thm
    val w2i_n2w_neg : thm
    val w2i_n2w_pos : thm
    val w2i_neg : thm
    val w2i_sw2sw_bounds : thm
    val w2i_w2n_pos : thm
    val w2w_i2w : thm
    val word_0_w2i : thm
    val word_abs_i2w : thm
    val word_abs_w2i : thm
    val word_add_i2w : thm
    val word_add_i2w_w2n : thm
    val word_i2w_add : thm
    val word_i2w_mul : thm
    val word_msb_i2w : thm
    val word_mul_i2w : thm
    val word_mul_i2w_w2n : thm
    val word_sub_i2w : thm
    val word_sub_i2w_w2n : thm

  val integer_word_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "integer_word"

   [int_arith] Parent theory of "integer_word"

   [words] Parent theory of "integer_word"

   [INT_MAX_def]  Definition

      |- INT_MAX (:α) = &INT_MIN (:α) − 1

   [INT_MIN_def]  Definition

      |- INT_MIN (:α) = -INT_MAX (:α) − 1

   [UINT_MAX_def]  Definition

      |- UINT_MAX (:α) = &dimword (:α) − 1

   [fromString_primitive_def]  Definition

      |- fromString =
         WFREC (@R. WF R)
           (λfromString a.
              case a of
                "" => I (&toNum "")
              | STRING #"~" t => I (-&toNum t)
              | STRING #"-" t => I (-&toNum t)
              | STRING v4 t => I (&toNum (STRING v4 t)))

   [i2w_def]  Definition

      |- ∀i. i2w i = if i < 0 then -n2w (Num (-i)) else n2w (Num i)

   [saturate_i2sw_def]  Definition

      |- ∀i.
           saturate_i2sw i =
           if INT_MAX (:α) ≤ i then INT_MAXw
           else if i ≤ INT_MIN (:α) then INT_MINw
           else i2w i

   [saturate_i2w_def]  Definition

      |- ∀i.
           saturate_i2w i =
           if UINT_MAX (:α) ≤ i then UINT_MAXw
           else if i < 0 then 0w
           else n2w (Num i)

   [saturate_sw2sw_def]  Definition

      |- ∀w. saturate_sw2sw w = saturate_i2sw (w2i w)

   [saturate_sw2w_def]  Definition

      |- ∀w. saturate_sw2w w = saturate_i2w (w2i w)

   [saturate_w2sw_def]  Definition

      |- ∀w. saturate_w2sw w = saturate_i2sw (&w2n w)

   [signed_saturate_add_def]  Definition

      |- ∀a b. signed_saturate_add a b = saturate_i2sw (w2i a + w2i b)

   [signed_saturate_sub_def]  Definition

      |- ∀a b. signed_saturate_sub a b = saturate_i2sw (w2i a − w2i b)

   [toString_def]  Definition

      |- ∀i.
           toString i =
           if i < 0 then STRCAT "~" (toString (Num (-i)))
           else toString (Num i)

   [w2i_def]  Definition

      |- ∀w. w2i w = if word_msb w then -&w2n (-w) else &w2n w

   [INT_BOUND_ORDER]  Theorem

      |- INT_MIN (:α) < INT_MAX (:α) ∧ INT_MAX (:α) < UINT_MAX (:α) ∧
         UINT_MAX (:α) < &dimword (:α)

   [INT_MAX]  Theorem

      |- INT_MAX (:α) = &INT_MAX (:α)

   [INT_MAX_MONOTONIC]  Theorem

      |- dimindex (:α) ≤ dimindex (:β) ⇒ INT_MAX (:α) ≤ INT_MAX (:β)

   [INT_MIN]  Theorem

      |- INT_MIN (:α) = -&INT_MIN (:α)

   [INT_MIN_MONOTONIC]  Theorem

      |- dimindex (:α) ≤ dimindex (:β) ⇒ INT_MIN (:β) ≤ INT_MIN (:α)

   [INT_ZERO_LE_INT_MAX]  Theorem

      |- 0 ≤ INT_MAX (:α)

   [INT_ZERO_LT_INT_MAX]  Theorem

      |- 1 < dimindex (:α) ⇒ 0 < INT_MAX (:α)

   [INT_ZERO_LT_INT_MIN]  Theorem

      |- INT_MIN (:α) < 0

   [INT_ZERO_LT_UINT_MAX]  Theorem

      |- 0 < UINT_MAX (:α)

   [MULT_MINUS_ONE]  Theorem

      |- ∀i. -1w * i2w i = i2w (-i)

   [ONE_LE_TWOEXP]  Theorem

      |- ∀n. 1 ≤ 2 ** n

   [UINT_MAX]  Theorem

      |- UINT_MAX (:α) = &UINT_MAX (:α)

   [WORD_GEi]  Theorem

      |- ∀a b. a ≥ b ⇔ w2i a ≥ w2i b

   [WORD_GTi]  Theorem

      |- ∀a b. a > b ⇔ w2i a > w2i b

   [WORD_LEi]  Theorem

      |- ∀a b. a ≤ b ⇔ w2i a ≤ w2i b

   [WORD_LTi]  Theorem

      |- ∀a b. a < b ⇔ w2i a < w2i b

   [different_sign_then_no_overflow]  Theorem

      |- ∀x y. (word_msb x ⇎ word_msb y) ⇒ (w2i (x + y) = w2i x + w2i y)

   [fromString_def]  Theorem

      |- (fromString (STRING #"~" t) = -&toNum t) ∧
         (fromString (STRING #"-" t) = -&toNum t) ∧
         (fromString "" = &toNum "") ∧
         (fromString (STRING v4 v1) =
          if v4 = #"~" then -&toNum v1
          else if v4 = #"-" then -&toNum v1
          else &toNum (STRING v4 v1))

   [fromString_ind]  Theorem

      |- ∀P.
           (∀t. P (STRING #"~" t)) ∧ (∀t. P (STRING #"-" t)) ∧ P "" ∧
           (∀v4 v1. P (STRING v4 v1)) ⇒
           ∀v. P v

   [i2w_0]  Theorem

      |- i2w 0 = 0w

   [i2w_DIV]  Theorem

      |- ∀n i.
           n < dimindex (:α) ∧ INT_MIN (:α) ≤ i ∧ i ≤ INT_MAX (:α) ⇒
           (i2w (i / 2 ** n) = i2w i ≫ n)

   [i2w_INT_MAX]  Theorem

      |- i2w (INT_MAX (:α)) = INT_MAXw

   [i2w_INT_MIN]  Theorem

      |- i2w (INT_MIN (:α)) = INT_MINw

   [i2w_UINT_MAX]  Theorem

      |- i2w (UINT_MAX (:α)) = UINT_MAXw

   [i2w_minus_1]  Theorem

      |- i2w (-1) = -1w

   [i2w_w2i]  Theorem

      |- ∀w. i2w (w2i w) = w

   [int_word_nchotomy]  Theorem

      |- ∀w. ∃i. w = i2w i

   [overflow]  Theorem

      |- ∀x y.
           w2i (x + y) ≠ w2i x + w2i y ⇔
           (word_msb x ⇔ word_msb y) ∧ (word_msb x ⇎ word_msb (x + y))

   [ranged_int_word_nchotomy]  Theorem

      |- ∀w. ∃i. (w = i2w i) ∧ INT_MIN (:α) ≤ i ∧ i ≤ INT_MAX (:α)

   [saturate_i2sw]  Theorem

      |- ∀i. saturate_i2w i = if i < 0 then 0w else saturate_n2w (Num i)

   [saturate_i2sw_0]  Theorem

      |- saturate_i2sw 0 = 0w

   [saturate_i2w_0]  Theorem

      |- saturate_i2w 0 = 0w

   [saturate_sw2sw]  Theorem

      |- ∀w.
           saturate_sw2sw w =
           if dimindex (:α) ≤ dimindex (:β) then sw2sw w
           else if sw2sw INT_MAXw ≤ w then INT_MAXw
           else if w ≤ sw2sw INT_MINw then INT_MINw
           else w2w w

   [saturate_sw2w]  Theorem

      |- ∀w. saturate_sw2w w = if w < 0w then 0w else saturate_w2w w

   [saturate_w2sw]  Theorem

      |- ∀w.
           saturate_w2sw w =
           if dimindex (:β) ≤ dimindex (:α) ∧ w2w INT_MAXw ≤₊ w then
             INT_MAXw
           else w2w w

   [signed_saturate_add]  Theorem

      |- ∀a b.
           signed_saturate_add a b =
           (let sum = a + b and msba = word_msb a
            in
              if (msba ⇔ word_msb b) ∧ (msba ⇎ word_msb sum) then
                if msba then INT_MINw else INT_MAXw
              else sum)

   [signed_saturate_sub]  Theorem

      |- ∀a b.
           signed_saturate_sub a b =
           if b = INT_MINw then if 0w ≤ a then INT_MAXw else a + INT_MINw
           else if dimindex (:α) = 1 then a && ¬b
           else signed_saturate_add a (-b)

   [sw2sw_i2w]  Theorem

      |- ∀j.
           INT_MIN (:β) ≤ j ∧ j ≤ INT_MAX (:β) ∧
           dimindex (:β) ≤ dimindex (:α) ⇒
           (sw2sw (i2w j) = i2w j)

   [w2i_1]  Theorem

      |- w2i 1w = if dimindex (:α) = 1 then -1 else 1

   [w2i_11]  Theorem

      |- ∀v w. (w2i v = w2i w) ⇔ (v = w)

   [w2i_11_lift]  Theorem

      |- ∀a b.
           dimindex (:α) ≤ dimindex (:γ) ∧ dimindex (:β) ≤ dimindex (:γ) ⇒
           ((w2i a = w2i b) ⇔ (sw2sw a = sw2sw b))

   [w2i_INT_MAXw]  Theorem

      |- w2i INT_MAXw = INT_MAX (:α)

   [w2i_INT_MINw]  Theorem

      |- w2i INT_MINw = INT_MIN (:α)

   [w2i_UINT_MAXw]  Theorem

      |- w2i UINT_MAXw = -1

   [w2i_ge]  Theorem

      |- ∀w. INT_MIN (:α) ≤ w2i w

   [w2i_i2w]  Theorem

      |- ∀i. INT_MIN (:α) ≤ i ∧ i ≤ INT_MAX (:α) ⇒ (w2i (i2w i) = i)

   [w2i_i2w_id]  Theorem

      |- ∀i.
           INT_MIN (:α) ≤ i ∧ i ≤ INT_MAX (:α) ∧
           dimindex (:β) ≤ dimindex (:α) ⇒
           ((i = w2i (i2w i)) ⇔ (i2w i = sw2sw (i2w i)))

   [w2i_i2w_neg]  Theorem

      |- ∀n. n ≤ INT_MIN (:α) ⇒ (w2i (i2w (-&n)) = -&n)

   [w2i_i2w_pos]  Theorem

      |- ∀n. n ≤ INT_MAX (:α) ⇒ (w2i (i2w (&n)) = &n)

   [w2i_le]  Theorem

      |- ∀w. w2i w ≤ INT_MAX (:α)

   [w2i_lt_0]  Theorem

      |- ∀w. w2i w < 0 ⇔ w < 0w

   [w2i_minus_1]  Theorem

      |- w2i (-1w) = -1

   [w2i_n2w_mod]  Theorem

      |- ∀n m.
           n < dimword (:α) ∧ m ≤ dimindex (:α) ⇒
           (Num (w2i (n2w n) % 2 ** m) = n MOD 2 ** m)

   [w2i_n2w_neg]  Theorem

      |- ∀n.
           INT_MIN (:α) ≤ n ∧ n < dimword (:α) ⇒
           (w2i (n2w n) = -&(dimword (:α) − n))

   [w2i_n2w_pos]  Theorem

      |- ∀n. n < INT_MIN (:α) ⇒ (w2i (n2w n) = &n)

   [w2i_neg]  Theorem

      |- ∀w. 1 < dimindex (:α) ∧ w ≠ INT_MINw ⇒ (w2i (-w) = -w2i w)

   [w2i_sw2sw_bounds]  Theorem

      |- ∀w. INT_MIN (:α) ≤ w2i (sw2sw w) ∧ w2i (sw2sw w) ≤ INT_MAX (:α)

   [w2i_w2n_pos]  Theorem

      |- ∀w n. ¬word_msb w ∧ w2i w < &n ⇒ w2n w < n

   [w2w_i2w]  Theorem

      |- ∀i. dimindex (:α) ≤ dimindex (:β) ⇒ (w2w (i2w i) = i2w i)

   [word_0_w2i]  Theorem

      |- w2i 0w = 0

   [word_abs_i2w]  Theorem

      |- ∀i.
           INT_MIN (:α) ≤ i ∧ i ≤ INT_MAX (:α) ⇒
           (word_abs (i2w i) = n2w (Num (ABS i)))

   [word_abs_w2i]  Theorem

      |- ∀w. word_abs w = n2w (Num (ABS (w2i w)))

   [word_add_i2w]  Theorem

      |- ∀a b. i2w (w2i a + w2i b) = a + b

   [word_add_i2w_w2n]  Theorem

      |- ∀a b. i2w (&w2n a + &w2n b) = a + b

   [word_i2w_add]  Theorem

      |- ∀a b. i2w a + i2w b = i2w (a + b)

   [word_i2w_mul]  Theorem

      |- ∀a b. i2w a * i2w b = i2w (a * b)

   [word_msb_i2w]  Theorem

      |- ∀i. word_msb (i2w i) ⇔ &INT_MIN (:α) ≤ i % &dimword (:α)

   [word_mul_i2w]  Theorem

      |- ∀a b. i2w (w2i a * w2i b) = a * b

   [word_mul_i2w_w2n]  Theorem

      |- ∀a b. i2w (&w2n a * &w2n b) = a * b

   [word_sub_i2w]  Theorem

      |- ∀a b. i2w (w2i a − w2i b) = a − b

   [word_sub_i2w_w2n]  Theorem

      |- ∀a b. i2w (&w2n a − &w2n b) = a − b


*)
end
