signature set_emitTheory =
sig
  type thm = Thm.thm
  
  val set_emit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [num_emit] Parent theory of "set_emit"
   
   
*)
end
