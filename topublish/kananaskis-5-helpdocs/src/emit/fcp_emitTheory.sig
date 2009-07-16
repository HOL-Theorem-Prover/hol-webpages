signature fcp_emitTheory =
sig
  type thm = Thm.thm
  
  (*  Axioms  *)
    val EXPi : thm
    val MULi : thm
    val SUMi : thm
    val dimindexi : thm
  
  (*  Definitions  *)
    val FCPi_primitive_def : thm
    val mk_fcp_def : thm
  
  (*  Theorems  *)
    val FCPi_def : thm
    val FCPi_ind : thm
  
  val fcp_emit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [fcp] Parent theory of "fcp_emit"
   
   [num_emit] Parent theory of "fcp_emit"
   
   [numeral_bit] Parent theory of "fcp_emit"
   
   [EXPi]  Axiom
      
      [oracles: ] [axioms: EXPi] []
      |- EXPi (ITSELF a,ITSELF b) = ITSELF (a ** b)
   
   [MULi]  Axiom
      
      [oracles: ] [axioms: MULi] []
      |- MULi (ITSELF a,ITSELF b) = ITSELF (a * b)
   
   [SUMi]  Axiom
      
      [oracles: ] [axioms: SUMi] []
      |- SUMi (ITSELF a,ITSELF b) = ITSELF (a + b)
   
   [dimindexi]  Axiom
      
      [oracles: ] [axioms: dimindexi] [] |- dimindex (ITSELF a) = a
   
   [FCPi_primitive_def]  Definition
      
      |- FCPi =
         WFREC (@R. WF R) (\FCPi a. case a of (f,(:'b)) -> I ($FCP f))
   
   [mk_fcp_def]  Definition
      
      |- mk_fcp = FCPi
   
   [FCPi_def]  Theorem
      
      |- FCPi (f,(:'b)) = $FCP f
   
   [FCPi_ind]  Theorem
      
      |- !P. (!f. P (f,(:'b))) ==> !v v1. P (v,v1)
   
   
*)
end
