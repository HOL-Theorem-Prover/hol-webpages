signature llist_emitTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val LLCONS_def : thm
    val llcases_def : thm
  
  val llist_emit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list_emit] Parent theory of "llist_emit"
   
   [llist] Parent theory of "llist_emit"
   
   [option_emit] Parent theory of "llist_emit"
   
   [LLCONS_def]  Definition
      
      |- ∀h t. LLCONS h t = h:::t ()
   
   [llcases_def]  Definition
      
      |- ∀n c l.
           (l = [||]) ∧ (llcases n c l = n) ∨
           ∃h t. (l = h:::t) ∧ (llcases n c l = c (h,t))
   
   
*)
end
