signature probTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val alg_measure_def : thm
    val algebra_measure_def : thm
    val prob_def : thm
  
  (*  Theorems  *)
    val ABS_PROB : thm
    val ALGEBRA_CANON_MEASURE_MAX : thm
    val ALGEBRA_MEASURE_BASIC : thm
    val ALGEBRA_MEASURE_DEF_ALT : thm
    val ALGEBRA_MEASURE_MAX : thm
    val ALGEBRA_MEASURE_MONO_EMBED : thm
    val ALGEBRA_MEASURE_POS : thm
    val ALGEBRA_MEASURE_RANGE : thm
    val ALG_CANON1_MONO : thm
    val ALG_CANON2_MONO : thm
    val ALG_CANON_FIND_MONO : thm
    val ALG_CANON_MERGE_MONO : thm
    val ALG_CANON_MONO : thm
    val ALG_CANON_PREFS_MONO : thm
    val ALG_MEASURE_ADDITIVE : thm
    val ALG_MEASURE_APPEND : thm
    val ALG_MEASURE_BASIC : thm
    val ALG_MEASURE_COMPL : thm
    val ALG_MEASURE_POS : thm
    val ALG_MEASURE_TLS : thm
    val ALG_TWINS_MEASURE : thm
    val PROB_ADDITIVE : thm
    val PROB_ALG : thm
    val PROB_ALGEBRA : thm
    val PROB_BASIC : thm
    val PROB_COMPL : thm
    val PROB_COMPL_LE1 : thm
    val PROB_INTER_HALVES : thm
    val PROB_INTER_SHD : thm
    val PROB_LE_X : thm
    val PROB_MAX : thm
    val PROB_POS : thm
    val PROB_RANGE : thm
    val PROB_SDROP : thm
    val PROB_SHD : thm
    val PROB_STL : thm
    val PROB_SUBSET_MONO : thm
    val PROB_SUP_EXISTS1 : thm
    val PROB_SUP_EXISTS2 : thm
    val X_LE_PROB : thm
  
  val prob_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [prob_algebra] Parent theory of "prob"
   
   [alg_measure_def]  Definition
      
      |- (alg_measure [] = 0) /\
         !l rest.
           alg_measure (l::rest) = (1 / 2) pow LENGTH l + alg_measure rest
   
   [algebra_measure_def]  Definition
      
      |- !b.
           algebra_measure b =
           inf
             (\r.
                ?c.
                  (algebra_embed b = algebra_embed c) /\
                  (alg_measure c = r))
   
   [prob_def]  Definition
      
      |- !s.
           prob s =
           sup
             (\r. ?b. (algebra_measure b = r) /\ algebra_embed b SUBSET s)
   
   [ABS_PROB]  Theorem
      
      |- !p. abs (prob p) = prob p
   
   [ALGEBRA_CANON_MEASURE_MAX]  Theorem
      
      |- !l. algebra_canon l ==> alg_measure l <= 1
   
   [ALGEBRA_MEASURE_BASIC]  Theorem
      
      |- (algebra_measure [] = 0) /\ (algebra_measure [[]] = 1) /\
         !b. algebra_measure [[b]] = 1 / 2
   
   [ALGEBRA_MEASURE_DEF_ALT]  Theorem
      
      |- !l. algebra_measure l = alg_measure (alg_canon l)
   
   [ALGEBRA_MEASURE_MAX]  Theorem
      
      |- !l. algebra_measure l <= 1
   
   [ALGEBRA_MEASURE_MONO_EMBED]  Theorem
      
      |- !b c.
           algebra_embed b SUBSET algebra_embed c ==>
           algebra_measure b <= algebra_measure c
   
   [ALGEBRA_MEASURE_POS]  Theorem
      
      |- !l. 0 <= algebra_measure l
   
   [ALGEBRA_MEASURE_RANGE]  Theorem
      
      |- !l. 0 <= algebra_measure l /\ algebra_measure l <= 1
   
   [ALG_CANON1_MONO]  Theorem
      
      |- !l. alg_measure (alg_canon1 l) <= alg_measure l
   
   [ALG_CANON2_MONO]  Theorem
      
      |- !l. alg_measure (alg_canon2 l) <= alg_measure l
   
   [ALG_CANON_FIND_MONO]  Theorem
      
      |- !l b. alg_measure (alg_canon_find l b) <= alg_measure (l::b)
   
   [ALG_CANON_MERGE_MONO]  Theorem
      
      |- !l b. alg_measure (alg_canon_merge l b) <= alg_measure (l::b)
   
   [ALG_CANON_MONO]  Theorem
      
      |- !l. alg_measure (alg_canon l) <= alg_measure l
   
   [ALG_CANON_PREFS_MONO]  Theorem
      
      |- !l b. alg_measure (alg_canon_prefs l b) <= alg_measure (l::b)
   
   [ALG_MEASURE_ADDITIVE]  Theorem
      
      |- !b.
           algebra_canon b ==>
           !c.
             algebra_canon c ==>
             !d.
               algebra_canon d ==>
               (algebra_embed c INTER algebra_embed d = {}) /\
               (algebra_embed b =
                algebra_embed c UNION algebra_embed d) ==>
               (alg_measure b = alg_measure c + alg_measure d)
   
   [ALG_MEASURE_APPEND]  Theorem
      
      |- !l1 l2. alg_measure (l1 ++ l2) = alg_measure l1 + alg_measure l2
   
   [ALG_MEASURE_BASIC]  Theorem
      
      |- (alg_measure [] = 0) /\ (alg_measure [[]] = 1) /\
         !b. alg_measure [[b]] = 1 / 2
   
   [ALG_MEASURE_COMPL]  Theorem
      
      |- !b.
           algebra_canon b ==>
           !c.
             algebra_canon c ==>
             (COMPL (algebra_embed b) = algebra_embed c) ==>
             (alg_measure b + alg_measure c = 1)
   
   [ALG_MEASURE_POS]  Theorem
      
      |- !l. 0 <= alg_measure l
   
   [ALG_MEASURE_TLS]  Theorem
      
      |- !l b. 2 * alg_measure (MAP (CONS b) l) = alg_measure l
   
   [ALG_TWINS_MEASURE]  Theorem
      
      |- !l.
           (1 / 2) pow LENGTH (SNOC T l) + (1 / 2) pow LENGTH (SNOC F l) =
           (1 / 2) pow LENGTH l
   
   [PROB_ADDITIVE]  Theorem
      
      |- !s t.
           measurable s /\ measurable t /\ (s INTER t = {}) ==>
           (prob (s UNION t) = prob s + prob t)
   
   [PROB_ALG]  Theorem
      
      |- !x. prob (alg_embed x) = (1 / 2) pow LENGTH x
   
   [PROB_ALGEBRA]  Theorem
      
      |- !l. prob (algebra_embed l) = algebra_measure l
   
   [PROB_BASIC]  Theorem
      
      |- (prob {} = 0) /\ (prob UNIV = 1) /\
         !b. prob (\s. SHD s <=> b) = 1 / 2
   
   [PROB_COMPL]  Theorem
      
      |- !s. measurable s ==> (prob (COMPL s) = 1 - prob s)
   
   [PROB_COMPL_LE1]  Theorem
      
      |- !p r. measurable p ==> (prob (COMPL p) <= r <=> 1 - r <= prob p)
   
   [PROB_INTER_HALVES]  Theorem
      
      |- !p.
           measurable p ==>
           (prob ((\x. SHD x <=> T) INTER p) +
            prob ((\x. SHD x <=> F) INTER p) =
            prob p)
   
   [PROB_INTER_SHD]  Theorem
      
      |- !b p.
           measurable p ==>
           (prob ((\x. SHD x <=> b) INTER p o STL) = 1 / 2 * prob p)
   
   [PROB_LE_X]  Theorem
      
      |- !s x.
           (!s'. measurable s' /\ s' SUBSET s ==> prob s' <= x) ==>
           prob s <= x
   
   [PROB_MAX]  Theorem
      
      |- !p. prob p <= 1
   
   [PROB_POS]  Theorem
      
      |- !p. 0 <= prob p
   
   [PROB_RANGE]  Theorem
      
      |- !p. 0 <= prob p /\ prob p <= 1
   
   [PROB_SDROP]  Theorem
      
      |- !n p. measurable p ==> (prob (p o SDROP n) = prob p)
   
   [PROB_SHD]  Theorem
      
      |- !b. prob (\s. SHD s <=> b) = 1 / 2
   
   [PROB_STL]  Theorem
      
      |- !p. measurable p ==> (prob (p o STL) = prob p)
   
   [PROB_SUBSET_MONO]  Theorem
      
      |- !s t. s SUBSET t ==> prob s <= prob t
   
   [PROB_SUP_EXISTS1]  Theorem
      
      |- !s. ?r b. (algebra_measure b = r) /\ algebra_embed b SUBSET s
   
   [PROB_SUP_EXISTS2]  Theorem
      
      |- !s.
           ?z.
             !r.
               (?b.
                  (algebra_measure b = r) /\ algebra_embed b SUBSET s) ==>
               r <= z
   
   [X_LE_PROB]  Theorem
      
      |- !s x.
           (?s'. measurable s' /\ s' SUBSET s /\ x <= prob s') ==>
           x <= prob s
   
   
*)
end
