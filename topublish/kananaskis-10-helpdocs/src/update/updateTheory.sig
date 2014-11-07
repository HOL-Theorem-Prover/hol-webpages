signature updateTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val FIND_def : thm
    val LIST_UPDATE_def : thm
    val OVERRIDE_primitive_def : thm

  (*  Theorems  *)
    val APPLY_UPDATE_ID : thm
    val APPLY_UPDATE_THM : thm
    val LIST_UPDATE_ALL_DISTINCT : thm
    val LIST_UPDATE_LOOKUP : thm
    val LIST_UPDATE_OVERRIDE : thm
    val LIST_UPDATE_SORT_OVERRIDE : thm
    val LIST_UPDATE_THMS : thm
    val OVERRIDE_def : thm
    val OVERRIDE_ind : thm
    val SAME_KEY_UPDATE_DIFFER : thm
    val UPDATE_APPLY_ID : thm
    val UPDATE_APPLY_IMP_ID : thm
    val UPDATE_COMMUTES : thm
    val UPDATE_EQ : thm
    val UPDATE_def : thm

  val update_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [sorting] Parent theory of "update"

   [FIND_def]  Definition

      |- (∀P. FIND P [] = NONE) ∧
         ∀P h t. FIND P (h::t) = if P h then SOME h else FIND P t

   [LIST_UPDATE_def]  Definition

      |- (LIST_UPDATE [] = I) ∧
         ∀h t. LIST_UPDATE (h::t) = (FST h =+ SND h) o LIST_UPDATE t

   [OVERRIDE_primitive_def]  Definition

      |- OVERRIDE =
         WFREC (@R. WF R ∧ ∀t x. R (FILTER (λy. FST x ≠ FST y) t) (x::t))
           (λOVERRIDE a.
              case a of
                [] => I []
              | x::t => I (x::OVERRIDE (FILTER (λy. FST x ≠ FST y) t)))

   [APPLY_UPDATE_ID]  Theorem

      |- ∀f a. (a =+ f a) f = f

   [APPLY_UPDATE_THM]  Theorem

      |- ∀f a b c. (a =+ b) f c = if a = c then b else f c

   [LIST_UPDATE_ALL_DISTINCT]  Theorem

      |- ∀l1 l2.
           ALL_DISTINCT (MAP FST l2) ∧ PERM l1 l2 ⇒
           (LIST_UPDATE l1 = LIST_UPDATE l2)

   [LIST_UPDATE_LOOKUP]  Theorem

      |- ∀l f i.
           LIST_UPDATE l f i =
           case FIND (λx. FST x = i) l of NONE => f i | SOME (v1,e) => e

   [LIST_UPDATE_OVERRIDE]  Theorem

      |- ∀l. LIST_UPDATE l = LIST_UPDATE (OVERRIDE l)

   [LIST_UPDATE_SORT_OVERRIDE]  Theorem

      |- ∀R l. LIST_UPDATE l = LIST_UPDATE (QSORT R (OVERRIDE l))

   [LIST_UPDATE_THMS]  Theorem

      |- ((∀l1 l2 r1 r2.
             (l1 =+ r1) o (l2 =+ r2) = LIST_UPDATE [(l1,r1); (l2,r2)]) ∧
          (∀l r t. (l =+ r) o LIST_UPDATE t = LIST_UPDATE ((l,r)::t)) ∧
          (∀l1 l2 r1 r2 f.
             (l1 =+ r1) ((l2 =+ r2) f) =
             LIST_UPDATE [(l1,r1); (l2,r2)] f) ∧
          ∀l r t f.
            (l =+ r) (LIST_UPDATE t f) = LIST_UPDATE ((l,r)::t) f) ∧
         (∀l1 l2.
            LIST_UPDATE l1 o LIST_UPDATE l2 = LIST_UPDATE (l1 ++ l2)) ∧
         (∀l1 l2 r.
            LIST_UPDATE l1 o (l2 =+ r) = LIST_UPDATE (SNOC (l2,r) l1)) ∧
         (∀l1 l2 f.
            LIST_UPDATE l1 (LIST_UPDATE l2 f) = LIST_UPDATE (l1 ++ l2) f) ∧
         ∀l1 l2 r f.
           LIST_UPDATE l1 ((l2 =+ r) f) = LIST_UPDATE (SNOC (l2,r) l1) f

   [OVERRIDE_def]  Theorem

      |- (OVERRIDE [] = []) ∧
         ∀x t. OVERRIDE (x::t) = x::OVERRIDE (FILTER (λy. FST x ≠ FST y) t)

   [OVERRIDE_ind]  Theorem

      |- ∀P.
           P [] ∧ (∀x t. P (FILTER (λy. FST x ≠ FST y) t) ⇒ P (x::t)) ⇒
           ∀v. P v

   [SAME_KEY_UPDATE_DIFFER]  Theorem

      |- ∀f1 f2 a b c. b ≠ c ⇒ (a =+ b) f ≠ (a =+ c) f

   [UPDATE_APPLY_ID]  Theorem

      |- ∀f a b. (f a = b) ⇔ ((a =+ b) f = f)

   [UPDATE_APPLY_IMP_ID]  Theorem

      |- ∀f b a. (f a = b) ⇒ ((a =+ b) f = f)

   [UPDATE_COMMUTES]  Theorem

      |- ∀f a b c d.
           a ≠ b ⇒ ((a =+ c) ((b =+ d) f) = (b =+ d) ((a =+ c) f))

   [UPDATE_EQ]  Theorem

      |- ∀f a b c. (a =+ c) ((a =+ b) f) = (a =+ c) f

   [UPDATE_def]  Theorem

      |- ∀a b. a =+ b = (λf c. if a = c then b else f c)


*)
end
