signature gcd_emitTheory =
sig
  type thm = Thm.thm
  
  val gcd_emit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [gcd] Parent theory of "gcd_emit"
   
   [num_emit] Parent theory of "gcd_emit"
   
   
*)
end
