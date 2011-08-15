signature GilithUnitTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val exports : thm
  
  val GilithUnit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [GilithBool] Parent theory of "GilithUnit"
   
   [exports]  Theorem
      
      |- T
   
   
*)
end
