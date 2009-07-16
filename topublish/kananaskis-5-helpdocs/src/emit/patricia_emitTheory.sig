signature patricia_emitTheory =
sig
  type thm = Thm.thm
  
  val patricia_emit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [patricia_casts] Parent theory of "patricia_emit"
   
   [set_emit] Parent theory of "patricia_emit"
   
   [sorting_emit] Parent theory of "patricia_emit"
   
   [sum_emit] Parent theory of "patricia_emit"
   
   [words_emit] Parent theory of "patricia_emit"
   
   
*)
end
