signature numTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val IS_NUM_REP : thm
    val SUC_DEF : thm
    val SUC_REP_DEF : thm
    val ZERO_DEF : thm
    val ZERO_REP_DEF : thm
    val num_ISO_DEF : thm
    val num_TY_DEF : thm
  
  (*  Theorems  *)
    val INDUCTION : thm
    val INV_SUC : thm
    val NOT_SUC : thm
  
  val num_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [marker] Parent theory of "num"
   
   [IS_NUM_REP]  Definition
      
      |- !m.
           IS_NUM_REP m <=>
           !P. P ZERO_REP /\ (!n. P n ==> P (SUC_REP n)) ==> P m
   
   [SUC_DEF]  Definition
      
      |- !m. SUC m = ABS_num (SUC_REP (REP_num m))
   
   [SUC_REP_DEF]  Definition
      
      |- ONE_ONE SUC_REP /\ ~ONTO SUC_REP
   
   [ZERO_DEF]  Definition
      
      |- 0 = ABS_num ZERO_REP
   
   [ZERO_REP_DEF]  Definition
      
      |- !y. ZERO_REP <> SUC_REP y
   
   [num_ISO_DEF]  Definition
      
      |- (!a. ABS_num (REP_num a) = a) /\
         !r. IS_NUM_REP r <=> (REP_num (ABS_num r) = r)
   
   [num_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION IS_NUM_REP rep
   
   [INDUCTION]  Theorem
      
      |- !P. P 0 /\ (!n. P n ==> P (SUC n)) ==> !n. P n
   
   [INV_SUC]  Theorem
      
      |- !m n. (SUC m = SUC n) ==> (m = n)
   
   [NOT_SUC]  Theorem
      
      |- !n. SUC n <> 0
   
   
*)
end
