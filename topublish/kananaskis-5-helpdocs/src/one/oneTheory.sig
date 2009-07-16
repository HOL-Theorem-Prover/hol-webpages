signature oneTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val one_DEF : thm
    val one_TY_DEF : thm
    val one_case_def : thm
  
  (*  Theorems  *)
    val one : thm
    val one_Axiom : thm
    val one_axiom : thm
    val one_case_rw : thm
    val one_case_thm : thm
    val one_induction : thm
    val one_prim_rec : thm
  
  val one_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [marker] Parent theory of "one"
   
   [one_DEF]  Definition
      
      |- () = @x. T
   
   [one_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (\b. b) rep
   
   [one_case_def]  Definition
      
      |- !u x. one_case u x = if x = () then u else u
   
   [one]  Theorem
      
      |- !v. v = ()
   
   [one_Axiom]  Theorem
      
      |- !e. ?!fn. fn () = e
   
   [one_axiom]  Theorem
      
      |- !f g. f = g
   
   [one_case_rw]  Theorem
      
      |- !u x. one_case u x = u
   
   [one_case_thm]  Theorem
      
      |- !u. one_case u () = u
   
   [one_induction]  Theorem
      
      |- !P. P () ==> !x. P x
   
   [one_prim_rec]  Theorem
      
      |- !e. ?fn. fn () = e
   
   
*)
end
