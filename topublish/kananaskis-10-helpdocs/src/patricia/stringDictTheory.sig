signature stringDictTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val sdhash_def : thm

  val stringDict_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [string] Parent theory of "stringDict"

   [sdhash_def]  Definition

      |- (∀acc. sdhash acc "" = acc MOD 1009) ∧
         ∀acc c cs. sdhash acc (STRING c cs) = sdhash (acc + 3 * ORD c) cs


*)
end
