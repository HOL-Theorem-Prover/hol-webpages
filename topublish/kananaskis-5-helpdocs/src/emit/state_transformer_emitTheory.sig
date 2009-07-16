signature state_transformer_emitTheory =
sig
  type thm = Thm.thm
  
  val state_transformer_emit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [combin_emit] Parent theory of "state_transformer_emit"
   
   [pair_emit] Parent theory of "state_transformer_emit"
   
   [state_transformer] Parent theory of "state_transformer_emit"
   
   
*)
end
