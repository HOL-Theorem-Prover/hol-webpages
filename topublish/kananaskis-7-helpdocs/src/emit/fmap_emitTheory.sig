signature fmap_emitTheory =
sig
  type thm = Thm.thm
  
  val fmap_emit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "fmap_emit"
   
   [list_emit] Parent theory of "fmap_emit"
   
   [option_emit] Parent theory of "fmap_emit"
   
   [set_emit] Parent theory of "fmap_emit"
   
   
*)
end
