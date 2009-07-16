signature quotient_pred_setTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val DELETER_def : thm
    val DISJOINTR_def : thm
    val FINITER_def : thm
    val GSPECR_def : thm
    val IMAGER_def : thm
    val INSERTR_def : thm
    val PSUBSETR_def : thm
    val SUBSETR_def : thm
  
  (*  Theorems  *)
    val ABSORPTIONR : thm
    val DELETER_RSP : thm
    val DELETE_PRS : thm
    val DIFF_PRS : thm
    val DIFF_RSP : thm
    val DISJOINTR_RSP : thm
    val DISJOINT_PRS : thm
    val EMPTY_PRS : thm
    val EMPTY_RSP : thm
    val FINITER_EMPTY : thm
    val FINITER_EQ : thm
    val FINITER_INDUCT : thm
    val FINITER_INSERTR : thm
    val FINITER_RSP : thm
    val FINITE_PRS : thm
    val GSPECR_RSP : thm
    val GSPEC_PRS : thm
    val IMAGER_RSP : thm
    val IMAGE_PRS : thm
    val INSERTR_RSP : thm
    val INSERT_PRS : thm
    val INTER_PRS : thm
    val INTER_RSP : thm
    val IN_DELETER : thm
    val IN_GSPECR : thm
    val IN_IMAGER : thm
    val IN_INSERTR : thm
    val IN_PRS : thm
    val IN_RSP : thm
    val IN_SET_MAP : thm
    val PSUBSETR_RSP : thm
    val PSUBSET_PRS : thm
    val SET_REL : thm
    val SET_REL_MP : thm
    val SUBSETR_RSP : thm
    val SUBSET_PRS : thm
    val UNION_PRS : thm
    val UNION_RSP : thm
    val UNIV_PRS : thm
    val UNIV_RSP : thm
  
  val quotient_pred_set_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [quotient_pair] Parent theory of "quotient_pred_set"
   
   [DELETER_def]  Definition
      
      |- !R s x. DELETER R s x = {y | y IN s /\ ~R x y}
   
   [DISJOINTR_def]  Definition
      
      |- !R s t. DISJOINTR R s t <=> ~?x::respects R. x IN s /\ x IN t
   
   [FINITER_def]  Definition
      
      |- !R s.
           FINITER R s <=>
           !P::respects ((R ===> $<=>) ===> $<=>).
             P {} /\
             (!s::respects (R ===> $<=>).
                P s ==> !e::respects R. P (INSERTR R e s)) ==>
             P s
   
   [GSPECR_def]  Definition
      
      |- !R1 R2 f v.
           GSPECR R1 R2 f v <=> ?x::respects R1. (R2 ### $<=>) (v,T) (f x)
   
   [IMAGER_def]  Definition
      
      |- !R1 R2 f s.
           IMAGER R1 R2 f s = {y | ?x::respects R1. R2 y (f x) /\ x IN s}
   
   [INSERTR_def]  Definition
      
      |- !R x s. INSERTR R x s = {y | R y x \/ y IN s}
   
   [PSUBSETR_def]  Definition
      
      |- !R s t. PSUBSETR R s t <=> SUBSETR R s t /\ ~(R ===> $<=>) s t
   
   [SUBSETR_def]  Definition
      
      |- !R s t. SUBSETR R s t <=> !x::respects R. x IN s ==> x IN t
   
   [ABSORPTIONR]  Theorem
      
      |- !R (x::respects R) (s::respects (R ===> $<=>)).
           x IN s <=> (R ===> $<=>) (INSERTR R x s) s
   
   [DELETER_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2 x1 x2.
             (R ===> $<=>) s1 s2 /\ R x1 x2 ==>
             (R ===> $<=>) (DELETER R s1 x1) (DELETER R s2 x2)
   
   [DELETE_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s x.
             s DELETE x = (rep --> I) (DELETER R ((abs --> I) s) (rep x))
   
   [DIFF_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s t. s DIFF t = (rep --> I) ((abs --> I) s DIFF (abs --> I) t)
   
   [DIFF_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2 t1 t2.
             (R ===> $<=>) s1 s2 /\ (R ===> $<=>) t1 t2 ==>
             (R ===> $<=>) (s1 DIFF t1) (s2 DIFF t2)
   
   [DISJOINTR_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2 t1 t2.
             (R ===> $<=>) s1 s2 /\ (R ===> $<=>) t1 t2 ==>
             (DISJOINTR R s1 t1 <=> DISJOINTR R s2 t2)
   
   [DISJOINT_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s t.
             DISJOINT s t <=> DISJOINTR R ((abs --> I) s) ((abs --> I) t)
   
   [EMPTY_PRS]  Theorem
      
      |- !R abs rep. QUOTIENT R abs rep ==> ({} = (rep --> I) {})
   
   [EMPTY_RSP]  Theorem
      
      |- !R abs rep. QUOTIENT R abs rep ==> (R ===> $<=>) {} {}
   
   [FINITER_EMPTY]  Theorem
      
      |- !R. FINITER R {}
   
   [FINITER_EQ]  Theorem
      
      |- !R s1 s2. (R ===> $<=>) s1 s2 ==> (FINITER R s1 <=> FINITER R s2)
   
   [FINITER_INDUCT]  Theorem
      
      |- !R (P::respects ((R ===> $<=>) ===> $<=>)).
           P {} /\
           (!s::respects (R ===> $<=>).
              FINITER R s /\ P s ==>
              !e::respects R. e NOTIN s ==> P (INSERTR R e s)) ==>
           !s::respects (R ===> $<=>). FINITER R s ==> P s
   
   [FINITER_INSERTR]  Theorem
      
      |- !R (s::respects (R ===> $<=>)).
           FINITER R s ==> !x::respects R. FINITER R (INSERTR R x s)
   
   [FINITER_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2. (R ===> $<=>) s1 s2 ==> (FINITER R s1 <=> FINITER R s2)
   
   [FINITE_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s. FINITE s <=> FINITER R ((abs --> I) s)
   
   [GSPECR_RSP]  Theorem
      
      |- !R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ==>
           !R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ==>
             !f1 f2.
               (R1 ===> R2 ### $<=>) f1 f2 ==>
               (R2 ===> $<=>) (GSPECR R1 R2 f1) (GSPECR R1 R2 f2)
   
   [GSPEC_PRS]  Theorem
      
      |- !R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ==>
           !R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ==>
             !f.
               GSPEC f =
               (rep2 --> I) (GSPECR R1 R2 ((abs1 --> rep2 ## I) f))
   
   [IMAGER_RSP]  Theorem
      
      |- !R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ==>
           !R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ==>
             !f1 f2 s1 s2.
               (R1 ===> R2) f1 f2 /\ (R1 ===> $<=>) s1 s2 ==>
               (R2 ===> $<=>) (IMAGER R1 R2 f1 s1) (IMAGER R1 R2 f2 s2)
   
   [IMAGE_PRS]  Theorem
      
      |- !R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ==>
           !R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ==>
             !f s.
               IMAGE f s =
               (rep2 --> I)
                 (IMAGER R1 R2 ((abs1 --> rep2) f) ((abs1 --> I) s))
   
   [INSERTR_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !x1 x2 s1 s2.
             R x1 x2 /\ (R ===> $<=>) s1 s2 ==>
             (R ===> $<=>) (INSERTR R x1 s1) (INSERTR R x2 s2)
   
   [INSERT_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s x.
             x INSERT s = (rep --> I) (INSERTR R (rep x) ((abs --> I) s))
   
   [INTER_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s t.
             s INTER t = (rep --> I) ((abs --> I) s INTER (abs --> I) t)
   
   [INTER_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2 t1 t2.
             (R ===> $<=>) s1 s2 /\ (R ===> $<=>) t1 t2 ==>
             (R ===> $<=>) (s1 INTER t1) (s2 INTER t2)
   
   [IN_DELETER]  Theorem
      
      |- !R s x y. y IN DELETER R s x <=> y IN s /\ ~R x y
   
   [IN_GSPECR]  Theorem
      
      |- !R1 R2 f v.
           v IN GSPECR R1 R2 f <=>
           ?x::respects R1. (R2 ### $<=>) (v,T) (f x)
   
   [IN_IMAGER]  Theorem
      
      |- !R1 R2 y f s.
           y IN IMAGER R1 R2 f s <=> ?x::respects R1. R2 y (f x) /\ x IN s
   
   [IN_INSERTR]  Theorem
      
      |- !R x s y. y IN INSERTR R x s <=> R y x \/ y IN s
   
   [IN_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==> !x s. x IN s <=> rep x IN (abs --> I) s
   
   [IN_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !x1 x2 s1 s2.
             R x1 x2 /\ (R ===> $<=>) s1 s2 ==> (x1 IN s1 <=> x2 IN s2)
   
   [IN_SET_MAP]  Theorem
      
      |- !f s x. x IN (f --> I) s <=> f x IN s
   
   [PSUBSETR_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2 t1 t2.
             (R ===> $<=>) s1 s2 /\ (R ===> $<=>) t1 t2 ==>
             (PSUBSETR R s1 t1 <=> PSUBSETR R s2 t2)
   
   [PSUBSET_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s t. s PSUBSET t <=> PSUBSETR R ((abs --> I) s) ((abs --> I) t)
   
   [SET_REL]  Theorem
      
      |- !R s t. (R ===> $<=>) s t <=> !x y. R x y ==> (x IN s <=> y IN t)
   
   [SET_REL_MP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s t x y. (R ===> $<=>) s t /\ R x y ==> (x IN s <=> y IN t)
   
   [SUBSETR_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2 t1 t2.
             (R ===> $<=>) s1 s2 /\ (R ===> $<=>) t1 t2 ==>
             (SUBSETR R s1 t1 <=> SUBSETR R s2 t2)
   
   [SUBSET_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s t. s SUBSET t <=> SUBSETR R ((abs --> I) s) ((abs --> I) t)
   
   [UNION_PRS]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s t.
             s UNION t = (rep --> I) ((abs --> I) s UNION (abs --> I) t)
   
   [UNION_RSP]  Theorem
      
      |- !R abs rep.
           QUOTIENT R abs rep ==>
           !s1 s2 t1 t2.
             (R ===> $<=>) s1 s2 /\ (R ===> $<=>) t1 t2 ==>
             (R ===> $<=>) (s1 UNION t1) (s2 UNION t2)
   
   [UNIV_PRS]  Theorem
      
      |- !R abs rep. QUOTIENT R abs rep ==> (UNIV = (rep --> I) UNIV)
   
   [UNIV_RSP]  Theorem
      
      |- !R abs rep. QUOTIENT R abs rep ==> (R ===> $<=>) UNIV UNIV
   
   
*)
end
