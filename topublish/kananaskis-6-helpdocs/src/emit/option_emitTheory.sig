signature option_emitTheory =
sig
  type thm = Thm.thm
  
  val option_emit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "option_emit"
   
   
*)
end
