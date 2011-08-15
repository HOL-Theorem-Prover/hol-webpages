signature sampleTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val badstring_def : thm
  
  val sample_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [string] Parent theory of "sample"
   
   [badstring_def]  Definition
      
      |- badstring = "\042)"
   
   
*)
end
