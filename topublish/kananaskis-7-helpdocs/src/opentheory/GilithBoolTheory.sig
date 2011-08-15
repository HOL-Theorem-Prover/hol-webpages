signature GilithBoolTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val exports : thm
  
  val GilithBool_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "GilithBool"
   
   [exports]  Theorem
      
      |- T
   
   
*)
end
