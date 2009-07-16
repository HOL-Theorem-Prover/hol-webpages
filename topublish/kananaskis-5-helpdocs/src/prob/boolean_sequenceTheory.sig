signature boolean_sequenceTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val SCONST_def : thm
    val SCONS_def : thm
    val SDEST_def : thm
    val SDROP_def : thm
    val SHD_def : thm
    val STAKE_def : thm
    val STL_def : thm
  
  (*  Theorems  *)
    val SCONS_SURJ : thm
    val SHD_SCONS : thm
    val SHD_SCONST : thm
    val SHD_STL_ISO : thm
    val STL_SCONS : thm
    val STL_SCONST : thm
  
  val boolean_sequence_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [prob_extra] Parent theory of "boolean_sequence"
   
   [SCONST_def]  Definition
      
      |- SCONST = K
   
   [SCONS_def]  Definition
      
      |- (!h t. SCONS h t 0 <=> h) /\ !h t n. SCONS h t (SUC n) <=> t n
   
   [SDEST_def]  Definition
      
      |- SDEST = (\s. (SHD s,STL s))
   
   [SDROP_def]  Definition
      
      |- (SDROP 0 = I) /\ !n. SDROP (SUC n) = SDROP n o STL
   
   [SHD_def]  Definition
      
      |- !f. SHD f <=> f 0
   
   [STAKE_def]  Definition
      
      |- (!s. STAKE 0 s = []) /\
         !n s. STAKE (SUC n) s = SHD s::STAKE n (STL s)
   
   [STL_def]  Definition
      
      |- !f n. STL f n <=> f (SUC n)
   
   [SCONS_SURJ]  Theorem
      
      |- !x. ?h t. x = SCONS h t
   
   [SHD_SCONS]  Theorem
      
      |- !h t. SHD (SCONS h t) <=> h
   
   [SHD_SCONST]  Theorem
      
      |- !b. SHD (SCONST b) <=> b
   
   [SHD_STL_ISO]  Theorem
      
      |- !h t. ?x. (SHD x <=> h) /\ (STL x = t)
   
   [STL_SCONS]  Theorem
      
      |- !h t. STL (SCONS h t) = t
   
   [STL_SCONST]  Theorem
      
      |- !b. STL (SCONST b) = SCONST b
   
   
*)
end
