signature sum_numTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val GSUM_curried_def : thm
    val GSUM_tupled_primitive_def : thm
    val SUM_def : thm
  
  (*  Theorems  *)
    val GSUM_1 : thm
    val GSUM_ADD : thm
    val GSUM_EQUAL : thm
    val GSUM_FUN_EQUAL : thm
    val GSUM_LESS : thm
    val GSUM_MONO : thm
    val GSUM_ZERO : thm
    val GSUM_def : thm
    val GSUM_ind : thm
    val SUM : thm
    val SUM_1 : thm
    val SUM_EQUAL : thm
    val SUM_FUN_EQUAL : thm
    val SUM_LESS : thm
    val SUM_MONO : thm
    val SUM_ZERO : thm
  
  val sum_num_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [list] Parent theory of "sum_num"
   
   [GSUM_curried_def]  Definition
      
      |- !x x1. GSUM x x1 = GSUM_tupled (x,x1)
   
   [GSUM_tupled_primitive_def]  Definition
      
      |- GSUM_tupled =
         WFREC (@R. WF R /\ !f m n. R ((n,m),f) ((n,SUC m),f))
           (\GSUM_tupled a.
              case a of
                 ((n,0),f) -> I 0
              || ((n,SUC m),f) -> I (GSUM_tupled ((n,m),f) + f (n + m)))
   
   [SUM_def]  Definition
      
      |- (!f. SUM 0 f = 0) /\ !m f. SUM (SUC m) f = SUM m f + f m
   
   [GSUM_1]  Theorem
      
      |- !m f. GSUM (m,1) f = f m
   
   [GSUM_ADD]  Theorem
      
      |- !p m n f. GSUM (p,m + n) f = GSUM (p,m) f + GSUM (p + m,n) f
   
   [GSUM_EQUAL]  Theorem
      
      |- !p m n f.
           (GSUM (p,m) f = GSUM (p,n) f) <=>
           m <= n /\ (!q. p + m <= q /\ q < p + n ==> (f q = 0)) \/
           n < m /\ !q. p + n <= q /\ q < p + m ==> (f q = 0)
   
   [GSUM_FUN_EQUAL]  Theorem
      
      |- !p n f g.
           (!x. p <= x /\ x < p + n ==> (f x = g x)) ==>
           (GSUM (p,n) f = GSUM (p,n) g)
   
   [GSUM_LESS]  Theorem
      
      |- !p m n f.
           (?q. m + p <= q /\ q < n + p /\ f q <> 0) <=>
           GSUM (p,m) f < GSUM (p,n) f
   
   [GSUM_MONO]  Theorem
      
      |- !p m n f.
           m <= n /\ f (p + n) <> 0 ==> GSUM (p,m) f < GSUM (p,SUC n) f
   
   [GSUM_ZERO]  Theorem
      
      |- !p n f.
           (!m. p <= m /\ m < p + n ==> (f m = 0)) <=> (GSUM (p,n) f = 0)
   
   [GSUM_def]  Theorem
      
      |- (!n f. GSUM (n,0) f = 0) /\
         !n m f. GSUM (n,SUC m) f = GSUM (n,m) f + f (n + m)
   
   [GSUM_ind]  Theorem
      
      |- !P.
           (!n f. P (n,0) f) /\ (!n m f. P (n,m) f ==> P (n,SUC m) f) ==>
           !v v1 v2. P (v,v1) v2
   
   [SUM]  Theorem
      
      |- !m f. SUM m f = GSUM (0,m) f
   
   [SUM_1]  Theorem
      
      |- !f. SUM 1 f = f 0
   
   [SUM_EQUAL]  Theorem
      
      |- !m n f.
           (SUM m f = SUM n f) <=>
           m <= n /\ (!q. m <= q /\ q < n ==> (f q = 0)) \/
           n < m /\ !q. n <= q /\ q < m ==> (f q = 0)
   
   [SUM_FUN_EQUAL]  Theorem
      
      |- !f g. (!x. x < n ==> (f x = g x)) ==> (SUM n f = SUM n g)
   
   [SUM_LESS]  Theorem
      
      |- !m n f. (?q. m <= q /\ q < n /\ f q <> 0) <=> SUM m f < SUM n f
   
   [SUM_MONO]  Theorem
      
      |- !m n f. m <= n /\ f n <> 0 ==> SUM m f < SUM (SUC n) f
   
   [SUM_ZERO]  Theorem
      
      |- !n f. (!m. m < n ==> (f m = 0)) <=> (SUM n f = 0)
   
   
*)
end
