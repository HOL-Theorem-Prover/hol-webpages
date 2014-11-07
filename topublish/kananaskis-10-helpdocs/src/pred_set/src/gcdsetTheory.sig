signature gcdsetTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val gcdset_def : thm

  (*  Theorems  *)
    val gcdset_EMPTY : thm
    val gcdset_INSERT : thm
    val gcdset_divides : thm
    val gcdset_greatest : thm

  val gcdset_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [gcd] Parent theory of "gcdset"

   [pred_set] Parent theory of "gcdset"

   [gcdset_def]  Definition

      |- ∀s.
           gcdset s =
           if (s = ∅) ∨ (s = {0}) then 0
           else
             MAX_SET
               ({n | n ≤ MIN_SET (s DELETE 0)} ∩
                {d | ∀e. e ∈ s ⇒ divides d e})

   [gcdset_EMPTY]  Theorem

      |- gcdset ∅ = 0

   [gcdset_INSERT]  Theorem

      |- gcdset (x INSERT s) = gcd x (gcdset s)

   [gcdset_divides]  Theorem

      |- ∀e. e ∈ s ⇒ divides (gcdset s) e

   [gcdset_greatest]  Theorem

      |- (∀e. e ∈ s ⇒ divides g e) ⇒ divides g (gcdset s)


*)
end
