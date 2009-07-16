signature fixedPointTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val closed_def : thm
    val dense_def : thm
    val empty_def : thm
    val fnsum_def : thm
    val gfp_def : thm
    val lfp_def : thm
    val monotone_def : thm
  
  (*  Theorems  *)
    val empty_monotone : thm
    val fnsum_ASSOC : thm
    val fnsum_COMM : thm
    val fnsum_SUBSET : thm
    val fnsum_empty : thm
    val fnsum_monotone : thm
    val gfp_coinduction : thm
    val gfp_greatest_dense : thm
    val gfp_greatest_fixedpoint : thm
    val gfp_strong_coinduction : thm
    val lfp_empty : thm
    val lfp_fixedpoint : thm
    val lfp_fnsum : thm
    val lfp_induction : thm
    val lfp_least_closed : thm
    val lfp_rule_applied : thm
    val lfp_strong_induction : thm
  
  val fixedPoint_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [pred_set] Parent theory of "fixedPoint"
   
   [closed_def]  Definition
      
      |- !f X. closed f X <=> f X SUBSET X
   
   [dense_def]  Definition
      
      |- !f X. dense f X <=> X SUBSET f X
   
   [empty_def]  Definition
      
      |- empty = (\X. {})
   
   [fnsum_def]  Definition
      
      |- !f1 f2 X. (f1 ++ f2) X = f1 X UNION f2 X
   
   [gfp_def]  Definition
      
      |- !f. gfp f = BIGUNION {X | X SUBSET f X}
   
   [lfp_def]  Definition
      
      |- !f. lfp f = BIGINTER {X | f X SUBSET X}
   
   [monotone_def]  Definition
      
      |- !f. monotone f <=> !X Y. X SUBSET Y ==> f X SUBSET f Y
   
   [empty_monotone]  Theorem
      
      |- monotone empty
   
   [fnsum_ASSOC]  Theorem
      
      |- !f g h. f ++ (g ++ h) = f ++ g ++ h
   
   [fnsum_COMM]  Theorem
      
      |- !f g. f ++ g = g ++ f
   
   [fnsum_SUBSET]  Theorem
      
      |- !f g X. f X SUBSET (f ++ g) X /\ g X SUBSET (f ++ g) X
   
   [fnsum_empty]  Theorem
      
      |- !f. (f ++ empty = f) /\ (empty ++ f = f)
   
   [fnsum_monotone]  Theorem
      
      |- !f1 f2. monotone f1 /\ monotone f2 ==> monotone (f1 ++ f2)
   
   [gfp_coinduction]  Theorem
      
      |- !f. monotone f ==> !X. X SUBSET f X ==> X SUBSET gfp f
   
   [gfp_greatest_dense]  Theorem
      
      |- !f.
           monotone f ==>
           dense f (gfp f) /\ !X. dense f X ==> X SUBSET gfp f
   
   [gfp_greatest_fixedpoint]  Theorem
      
      |- !f.
           monotone f ==>
           (gfp f = f (gfp f)) /\ !X. (X = f X) ==> X SUBSET gfp f
   
   [gfp_strong_coinduction]  Theorem
      
      |- !f.
           monotone f ==> !X. X SUBSET f (X UNION gfp f) ==> X SUBSET gfp f
   
   [lfp_empty]  Theorem
      
      |- !f x. monotone f /\ x IN f {} ==> x IN lfp f
   
   [lfp_fixedpoint]  Theorem
      
      |- !f.
           monotone f ==>
           (lfp f = f (lfp f)) /\ !X. (X = f X) ==> lfp f SUBSET X
   
   [lfp_fnsum]  Theorem
      
      |- !f1 f2.
           monotone f1 /\ monotone f2 ==>
           lfp f1 SUBSET lfp (f1 ++ f2) /\ lfp f2 SUBSET lfp (f1 ++ f2)
   
   [lfp_induction]  Theorem
      
      |- !f. monotone f ==> !X. f X SUBSET X ==> lfp f SUBSET X
   
   [lfp_least_closed]  Theorem
      
      |- !f.
           monotone f ==>
           closed f (lfp f) /\ !X. closed f X ==> lfp f SUBSET X
   
   [lfp_rule_applied]  Theorem
      
      |- !f X y. monotone f /\ X SUBSET lfp f /\ y IN f X ==> y IN lfp f
   
   [lfp_strong_induction]  Theorem
      
      |- !f.
           monotone f ==> !X. f (X INTER lfp f) SUBSET X ==> lfp f SUBSET X
   
   
*)
end
