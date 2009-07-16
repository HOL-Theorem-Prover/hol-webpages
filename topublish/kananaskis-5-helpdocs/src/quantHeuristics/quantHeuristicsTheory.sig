signature quantHeuristicsTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val CONJ_NOT_OR_THM : thm
    val EXISTS_NOT_FORALL_THM : thm
    val EXISTS_UNIQUE_INSTANTIATE_THM : thm
    val LEFT_IMP_AND_INTRO : thm
    val LEFT_IMP_OR_INTRO : thm
    val MOVE_EXISTS_IMP_THM : thm
    val RIGHT_IMP_AND_INTRO : thm
    val RIGHT_IMP_OR_INTRO : thm
    val UNWIND_EXISTS_THM : thm
  
  val quantHeuristics_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [combin] Parent theory of "quantHeuristics"
   
   [sat] Parent theory of "quantHeuristics"
   
   [CONJ_NOT_OR_THM]  Theorem
      
      |- !A B. A /\ B <=> ~(~A \/ ~B)
   
   [EXISTS_NOT_FORALL_THM]  Theorem
      
      |- !P. (?x. P x) <=> ~!x. ~P x
   
   [EXISTS_UNIQUE_INSTANTIATE_THM]  Theorem
      
      |- !P i. (!v. v <> i ==> ~P v) ==> ((?!v. P v) <=> P i)
   
   [LEFT_IMP_AND_INTRO]  Theorem
      
      |- !x t1 t2. (t1 ==> t2) ==> x /\ t1 ==> x /\ t2
   
   [LEFT_IMP_OR_INTRO]  Theorem
      
      |- !x t1 t2. (t1 ==> t2) ==> x \/ t1 ==> x \/ t2
   
   [MOVE_EXISTS_IMP_THM]  Theorem
      
      |- (?x. (!y. ~P x y ==> R y) ==> Q x) <=>
         (!y. ~(!x. P x y) ==> R y) ==> ?x. Q x
   
   [RIGHT_IMP_AND_INTRO]  Theorem
      
      |- !x t1 t2. (t1 ==> t2) ==> t1 /\ x ==> t2 /\ x
   
   [RIGHT_IMP_OR_INTRO]  Theorem
      
      |- !x t1 t2. (t1 ==> t2) ==> t1 \/ x ==> t2 \/ x
   
   [UNWIND_EXISTS_THM]  Theorem
      
      |- !a P. (?x. P x) <=> (!x. x <> a ==> ~P x) ==> P a
   
   
*)
end
