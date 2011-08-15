signature state_optionTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val STATE_OPTION_BIND_def : thm
    val STATE_OPTION_FAIL_def : thm
    val STATE_OPTION_IGNORE_BIND_def : thm
    val STATE_OPTION_LIFT_def : thm
    val STATE_OPTION_UNIT_def : thm
  
  val state_option_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [option] Parent theory of "state_option"
   
   [pair] Parent theory of "state_option"
   
   [STATE_OPTION_BIND_def]  Definition
      
      |- ∀m f s. STATE_OPTION_BIND m f s = OPTION_BIND (m s) (UNCURRY f)
   
   [STATE_OPTION_FAIL_def]  Definition
      
      |- ∀s. STATE_OPTION_FAIL s = NONE
   
   [STATE_OPTION_IGNORE_BIND_def]  Definition
      
      |- ∀m1 m2 s.
           STATE_OPTION_IGNORE_BIND m1 m2 s = OPTION_BIND (m1 s) (m2 o SND)
   
   [STATE_OPTION_LIFT_def]  Definition
      
      |- ∀m s. STATE_OPTION_LIFT m s = OPTION_BIND m (λa. SOME (a,s))
   
   [STATE_OPTION_UNIT_def]  Definition
      
      |- ∀a s. STATE_OPTION_UNIT a s = SOME (a,s)
   
   
*)
end
