signature rich_list_emitTheory =
sig
  type thm = Thm.thm
  
  val rich_list_emit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [list_emit] Parent theory of "rich_list_emit"
   
   [rich_list] Parent theory of "rich_list_emit"
   
   
*)
end
