signature words_emitTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val fromNum_primitive_def : thm
    val sw2sw_itself_def : thm
    val w2w_itself_def : thm
    val word_concat_itself_def : thm
    val word_eq_def : thm
    val word_extract_itself_def : thm
    val word_index_def : thm
  
  (*  Theorems  *)
    val fromNum_def : thm
    val fromNum_ind : thm
  
  val words_emit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
  
  val WORDS_EMIT_RULE : thm -> thm
  
(*
   [bit_emit] Parent theory of "words_emit"
   
   [fcp_emit] Parent theory of "words_emit"
   
   [words] Parent theory of "words_emit"
   
   [fromNum_primitive_def]  Definition
      
      |- fromNum =
         WFREC (@R. WF R)
           (\fromNum a.
              case a of
                 (n,(:'a)) -> I (n2w_itself (n MOD dimword (:'a),(:'a))))
   
   [sw2sw_itself_def]  Definition
      
      |- !w. sw2sw_itself (:'a) w = sw2sw w
   
   [w2w_itself_def]  Definition
      
      |- !w. w2w_itself (:'a) w = w2w w
   
   [word_concat_itself_def]  Definition
      
      |- !v w. word_concat_itself (:'a) v w = v @@ w
   
   [word_eq_def]  Definition
      
      |- !v w. word_eq v w <=> (v = w)
   
   [word_extract_itself_def]  Definition
      
      |- !h l w. word_extract_itself (:'a) h l w = (h >< l) w
   
   [word_index_def]  Definition
      
      |- !w n. word_index w n <=> w ' n
   
   [fromNum_def]  Theorem
      
      |- fromNum (n,(:'a)) = n2w_itself (n MOD dimword (:'a),(:'a))
   
   [fromNum_ind]  Theorem
      
      |- !P. (!n. P (n,(:'a))) ==> !v v1. P (v,v1)
   
   
*)
end
