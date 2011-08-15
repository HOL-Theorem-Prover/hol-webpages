signature intrealTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val INT_CEILING_def : thm
    val INT_FLOOR_def : thm
    val is_int_def : thm
    val real_of_int : thm
  
  val intreal_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [integer] Parent theory of "intreal"
   
   [real] Parent theory of "intreal"
   
   [INT_CEILING_def]  Definition
      
      |- ∀x. clg x = LEAST_INT i. x ≤ real_of_int i
   
   [INT_FLOOR_def]  Definition
      
      |- ∀x. flr x = LEAST_INT i. real_of_int (i + 1) > x
   
   [is_int_def]  Definition
      
      |- ∀x. is_int x ⇔ (x = real_of_int (flr x))
   
   [real_of_int]  Definition
      
      |- ∀i. real_of_int i = if i < 0 then -&Num (-i) else &Num i
   
   
*)
end
