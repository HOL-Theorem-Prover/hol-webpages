signature prob_pseudoTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val pseudo_def : thm
    val pseudo_linear1_def : thm
    val pseudo_linear_hd_def : thm
    val pseudo_linear_tl_def : thm
  
  (*  Theorems  *)
    val PSEUDO_LINEAR1_EXECUTE : thm
  
  val prob_pseudo_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [boolean_sequence] Parent theory of "prob_pseudo"
   
   [pseudo_def]  Definition
      
      |- pseudo = pseudo_linear1
   
   [pseudo_linear1_def]  Definition
      
      |- (∀x. SHD (pseudo_linear1 x) ⇔ pseudo_linear_hd x) ∧
         ∀x.
           STL (pseudo_linear1 x) =
           pseudo_linear1 (pseudo_linear_tl 103 95 79 x)
   
   [pseudo_linear_hd_def]  Definition
      
      |- pseudo_linear_hd = EVEN
   
   [pseudo_linear_tl_def]  Definition
      
      |- ∀a b n x. pseudo_linear_tl a b n x = (a * x + b) MOD (2 * n + 1)
   
   [PSEUDO_LINEAR1_EXECUTE]  Theorem
      
      |- ∃g.
           (∀x. SHD (g x) ⇔ pseudo_linear_hd x) ∧
           ∀x. STL (g x) = g (pseudo_linear_tl 103 95 79 x)
   
   
*)
end
