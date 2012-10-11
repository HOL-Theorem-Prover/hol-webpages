signature combinTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val APP_DEF : thm
    val C_DEF : thm
    val FAIL_DEF : thm
    val I_DEF : thm
    val K_DEF : thm
    val S_DEF : thm
    val UPDATE_def : thm
    val W_DEF : thm
    val o_DEF : thm

  (*  Theorems  *)
    val APPLY_UPDATE_ID : thm
    val APPLY_UPDATE_THM : thm
    val C_ABS_L : thm
    val C_THM : thm
    val FAIL_THM : thm
    val GEN_LET_RAND : thm
    val GEN_LET_RATOR : thm
    val GEN_literal_case_RAND : thm
    val GEN_literal_case_RATOR : thm
    val I_THM : thm
    val I_o_ID : thm
    val K_THM : thm
    val K_o_THM : thm
    val LET_FORALL_ELIM : thm
    val SAME_KEY_UPDATE_DIFFER : thm
    val S_ABS_L : thm
    val S_ABS_R : thm
    val S_THM : thm
    val UPD11_SAME_BASE : thm
    val UPD11_SAME_KEY_AND_BASE : thm
    val UPDATE_APPLY_ID : thm
    val UPDATE_APPLY_IMP_ID : thm
    val UPDATE_COMMUTES : thm
    val UPDATE_EQ : thm
    val UPD_SAME_KEY_UNWIND : thm
    val W_THM : thm
    val literal_case_FORALL_ELIM : thm
    val o_ABS_L : thm
    val o_ABS_R : thm
    val o_ASSOC : thm
    val o_THM : thm

  val combin_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [marker] Parent theory of "combin"

   [APP_DEF]  Definition

      |- ∀x f. x :> f = f x

   [C_DEF]  Definition

      |- C = (λf x y. f y x)

   [FAIL_DEF]  Definition

      |- FAIL = (λx y. x)

   [I_DEF]  Definition

      |- I = S K K

   [K_DEF]  Definition

      |- K = (λx y. x)

   [S_DEF]  Definition

      |- S = (λf g x. f x (g x))

   [UPDATE_def]  Definition

      |- ∀a b. a =+ b = (λf c. if a = c then b else f c)

   [W_DEF]  Definition

      |- W = (λf x. f x x)

   [o_DEF]  Definition

      |- ∀f g. f o g = (λx. f (g x))

   [APPLY_UPDATE_ID]  Theorem

      |- ∀f a. (a =+ f a) f = f

   [APPLY_UPDATE_THM]  Theorem

      |- ∀f a b c. (a =+ b) f c = if a = c then b else f c

   [C_ABS_L]  Theorem

      |- C (λx. f x) y = (λx. f x y)

   [C_THM]  Theorem

      |- ∀f x y. C f x y = f y x

   [FAIL_THM]  Theorem

      |- FAIL x y = x

   [GEN_LET_RAND]  Theorem

      |- P (LET f v) = LET (P o f) v

   [GEN_LET_RATOR]  Theorem

      |- LET f v x = LET (C f x) v

   [GEN_literal_case_RAND]  Theorem

      |- P (literal_case f v) = literal_case (P o f) v

   [GEN_literal_case_RATOR]  Theorem

      |- literal_case f v x = literal_case (C f x) v

   [I_THM]  Theorem

      |- ∀x. I x = x

   [I_o_ID]  Theorem

      |- ∀f. (I o f = f) ∧ (f o I = f)

   [K_THM]  Theorem

      |- ∀x y. K x y = x

   [K_o_THM]  Theorem

      |- (∀f v. K v o f = K v) ∧ ∀f v. f o K v = K (f v)

   [LET_FORALL_ELIM]  Theorem

      |- LET f v ⇔ $! (S ($==> o Abbrev o C $= v) f)

   [SAME_KEY_UPDATE_DIFFER]  Theorem

      |- ∀f1 f2 a b c. b ≠ c ⇒ (a =+ b) f ≠ (a =+ c) f

   [S_ABS_L]  Theorem

      |- S (λx. f x) g = (λx. f x (g x))

   [S_ABS_R]  Theorem

      |- S f (λx. g x) = (λx. f x (g x))

   [S_THM]  Theorem

      |- ∀f g x. S f g x = f x (g x)

   [UPD11_SAME_BASE]  Theorem

      |- ∀f a b c d.
           ((a =+ c) f = (b =+ d) f) ⇔
           (a = b) ∧ (c = d) ∨ a ≠ b ∧ ((a =+ c) f = f) ∧ ((b =+ d) f = f)

   [UPD11_SAME_KEY_AND_BASE]  Theorem

      |- ∀f a b c. ((a =+ b) f = (a =+ c) f) ⇔ (b = c)

   [UPDATE_APPLY_ID]  Theorem

      |- ∀f a b. (f a = b) ⇔ ((a =+ b) f = f)

   [UPDATE_APPLY_IMP_ID]  Theorem

      |- ∀f b a. (f a = b) ⇒ ((a =+ b) f = f)

   [UPDATE_COMMUTES]  Theorem

      |- ∀f a b c d.
           a ≠ b ⇒ ((a =+ c) ((b =+ d) f) = (b =+ d) ((a =+ c) f))

   [UPDATE_EQ]  Theorem

      |- ∀f a b c. (a =+ c) ((a =+ b) f) = (a =+ c) f

   [UPD_SAME_KEY_UNWIND]  Theorem

      |- ∀f1 f2 a b c.
           ((a =+ b) f1 = (a =+ c) f2) ⇒
           (b = c) ∧ ∀v. (a =+ v) f1 = (a =+ v) f2

   [W_THM]  Theorem

      |- ∀f x. W f x = f x x

   [literal_case_FORALL_ELIM]  Theorem

      |- literal_case f v ⇔ $! (S ($==> o Abbrev o C $= v) f)

   [o_ABS_L]  Theorem

      |- (λx. f x) o g = (λx. f (g x))

   [o_ABS_R]  Theorem

      |- f o (λx. g x) = (λx. f (g x))

   [o_ASSOC]  Theorem

      |- ∀f g h. f o g o h = (f o g) o h

   [o_THM]  Theorem

      |- ∀f g x. (f o g) x = f (g x)


*)
end
