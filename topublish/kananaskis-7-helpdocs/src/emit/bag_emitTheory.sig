signature bag_emitTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val BAG_VAL_DEF : thm
  
  (*  Theorems  *)
    val BAG_DIFF_EQNS : thm
    val BAG_INTER_EQNS : thm
    val BAG_MERGE_EQNS : thm
    val SUB_BAG_EQNS : thm
  
  val bag_emit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bag] Parent theory of "bag_emit"
   
   [set_emit] Parent theory of "bag_emit"
   
   [BAG_VAL_DEF]  Definition
      
      |- ∀b x. BAG_VAL b x = b x
   
   [BAG_DIFF_EQNS]  Theorem
      
      |- (∀b. b − {||} = b) ∧ (∀b. {||} − b = {||}) ∧
         (∀x b y.
            BAG_INSERT x b − {|y|} =
            if x = y then b else BAG_INSERT x (b − {|y|})) ∧
         ∀b1 y b2. b1 − BAG_INSERT y b2 = b1 − {|y|} − b2
   
   [BAG_INTER_EQNS]  Theorem
      
      |- (∀b. BAG_INTER {||} b = {||}) ∧ (∀b. BAG_INTER b {||} = {||}) ∧
         ∀x b1 b2.
           BAG_INTER (BAG_INSERT x b1) b2 =
           if x ⋲ b2 then
             BAG_INSERT x (BAG_INTER b1 (b2 − {|x|}))
           else
             BAG_INTER b1 b2
   
   [BAG_MERGE_EQNS]  Theorem
      
      |- (∀b. BAG_MERGE {||} b = b) ∧ (∀b. BAG_MERGE b {||} = b) ∧
         ∀x b1 b2.
           BAG_MERGE (BAG_INSERT x b1) b2 =
           BAG_INSERT x (BAG_MERGE b1 (b2 − {|x|}))
   
   [SUB_BAG_EQNS]  Theorem
      
      |- (∀b. {||} ≤ b ⇔ T) ∧
         ∀x b1 b2. BAG_INSERT x b1 ≤ b2 ⇔ x ⋲ b2 ∧ b1 ≤ b2 − {|x|}
   
   
*)
end
