signature extended_emitTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BAG_VAL_DEF : thm
    val LLCONS_def : thm
    val llcases_def : thm

  (*  Theorems  *)
    val BAG_DIFF_EQNS : thm
    val BAG_INTER_EQNS : thm
    val BAG_MERGE_EQNS : thm
    val SUB_BAG_EQNS : thm

  val extended_emit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bag] Parent theory of "extended_emit"

   [basis_emit] Parent theory of "extended_emit"

   [llist] Parent theory of "extended_emit"

   [patricia_casts] Parent theory of "extended_emit"

   [state_transformer] Parent theory of "extended_emit"

   [BAG_VAL_DEF]  Definition

      |- ! (\b. ! (\x. BAG_VAL b x = b x))

   [LLCONS_def]  Definition

      |- ! (\h. ! (\t. LLCONS h t = h:::t ()))

   [llcases_def]  Definition

      |- !
           (\n.
              !
                (\c.
                   !
                     (\l.
                        (l = [||]) /\ (llcases n c l = n) \/
                        ?
                          (\h.
                             ?
                               (\t.
                                  (l = h:::t) /\
                                  (llcases n c l = c (h,t)))))))

   [BAG_DIFF_EQNS]  Theorem

      |- ! (\b. b - {||} = b) /\ ! (\b. {||} - b = {||}) /\
         !
           (\x.
              !
                (\b.
                   !
                     (\y.
                        BAG_INSERT x b - {|y|} =
                        if x = y then b else BAG_INSERT x (b - {|y|})))) /\
         ! (\b1. ! (\y. ! (\b2. b1 - BAG_INSERT y b2 = b1 - {|y|} - b2)))

   [BAG_INTER_EQNS]  Theorem

      |- ! (\b. BAG_INTER {||} b = {||}) /\
         ! (\b. BAG_INTER b {||} = {||}) /\
         !
           (\x.
              !
                (\b1.
                   !
                     (\b2.
                        BAG_INTER (BAG_INSERT x b1) b2 =
                        if x <: b2 then
                          BAG_INSERT x (BAG_INTER b1 (b2 - {|x|}))
                        else BAG_INTER b1 b2)))

   [BAG_MERGE_EQNS]  Theorem

      |- ! (\b. BAG_MERGE {||} b = b) /\ ! (\b. BAG_MERGE b {||} = b) /\
         !
           (\x.
              !
                (\b1.
                   !
                     (\b2.
                        BAG_MERGE (BAG_INSERT x b1) b2 =
                        BAG_INSERT x (BAG_MERGE b1 (b2 - {|x|})))))

   [SUB_BAG_EQNS]  Theorem

      |- ! (\b. {||} <= b <=> T) /\
         !
           (\x.
              !
                (\b1.
                   !
                     (\b2.
                        BAG_INSERT x b1 <= b2 <=>
                        x <: b2 /\ b1 <= b2 - {|x|})))


*)
end
