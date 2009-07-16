signature prob_uniformTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val unif_bound_primitive_def : thm
    val unif_curried_def : thm
    val unif_tupled_primitive_def : thm
    val uniform_curried_def : thm
    val uniform_tupled_primitive_def : thm
  
  (*  Theorems  *)
    val INDEP_UNIF : thm
    val INDEP_UNIFORM : thm
    val PROB_UNIF : thm
    val PROB_UNIFORM : thm
    val PROB_UNIFORM_LOWER_BOUND : thm
    val PROB_UNIFORM_PAIR_SUC : thm
    val PROB_UNIFORM_SUC : thm
    val PROB_UNIFORM_UPPER_BOUND : thm
    val PROB_UNIF_BOUND : thm
    val PROB_UNIF_GOOD : thm
    val PROB_UNIF_PAIR : thm
    val SUC_DIV_TWO_ZERO : thm
    val UNIFORM_DEF_MONAD : thm
    val UNIFORM_RANGE : thm
    val UNIF_BOUND_LOWER : thm
    val UNIF_BOUND_LOWER_SUC : thm
    val UNIF_BOUND_UPPER : thm
    val UNIF_BOUND_UPPER_SUC : thm
    val UNIF_DEF_MONAD : thm
    val UNIF_RANGE : thm
    val unif_bound_def : thm
    val unif_bound_ind : thm
    val unif_def : thm
    val unif_ind : thm
    val uniform_def : thm
    val uniform_ind : thm
  
  val prob_uniform_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [prob_indep] Parent theory of "prob_uniform"
   
   [unif_bound_primitive_def]  Definition
      
      |- unif_bound =
         WFREC (@R. WF R /\ !v. R (SUC v DIV 2) (SUC v))
           (\unif_bound a.
              case a of
                 0 -> I 0
              || SUC v1 -> I (SUC (unif_bound (SUC v1 DIV 2))))
   
   [unif_curried_def]  Definition
      
      |- !x x1. unif x x1 = unif_tupled (x,x1)
   
   [unif_tupled_primitive_def]  Definition
      
      |- unif_tupled =
         WFREC (@R. WF R /\ !s v2. R (SUC v2 DIV 2,s) (SUC v2,s))
           (\unif_tupled a.
              case a of
                 (0,s) -> I (0,s)
              || (SUC v3,s) ->
                   I
                     (let (m,s') = unif_tupled (SUC v3 DIV 2,s) in
                        (if SHD s' then 2 * m + 1 else 2 * m,STL s')))
   
   [uniform_curried_def]  Definition
      
      |- !x x1 x2. uniform x x1 x2 = uniform_tupled (x,x1,x2)
   
   [uniform_tupled_primitive_def]  Definition
      
      |- uniform_tupled =
         WFREC
           (@R.
              WF R /\
              !t s n res s'.
                ((res,s') = unif n s) /\ ~(res < SUC n) ==>
                R (t,SUC n,s') (SUC t,SUC n,s))
           (\uniform_tupled a.
              case a of
                 (0,0,s) -> ARB
              || (0,SUC n,s) -> I (0,s)
              || (SUC t,0,s') -> ARB
              || (SUC t,SUC n',s') ->
                   I
                     (let (res,s') = unif n' s' in
                        if res < SUC n' then
                          (res,s')
                        else
                          uniform_tupled (t,SUC n',s')))
   
   [INDEP_UNIF]  Theorem
      
      |- !n. indep (unif n)
   
   [INDEP_UNIFORM]  Theorem
      
      |- !t n. indep (uniform t (SUC n))
   
   [PROB_UNIF]  Theorem
      
      |- !n k.
           prob (\s. FST (unif n s) = k) =
           if k < 2 ** unif_bound n then (1 / 2) pow unif_bound n else 0
   
   [PROB_UNIFORM]  Theorem
      
      |- !t n k.
           k < n ==>
           abs (prob (\s. FST (uniform t n s) = k) - 1 / &n) <=
           (1 / 2) pow t
   
   [PROB_UNIFORM_LOWER_BOUND]  Theorem
      
      |- !b.
           (!k.
              k < SUC n ==>
              prob (\s. FST (uniform t (SUC n) s) = k) < b) ==>
           !m.
             m < SUC n ==>
             prob (\s. FST (uniform t (SUC n) s) < SUC m) < &SUC m * b
   
   [PROB_UNIFORM_PAIR_SUC]  Theorem
      
      |- !t n k k'.
           k < SUC n /\ k' < SUC n ==>
           abs
             (prob (\s. FST (uniform t (SUC n) s) = k) -
              prob (\s. FST (uniform t (SUC n) s) = k')) <= (1 / 2) pow t
   
   [PROB_UNIFORM_SUC]  Theorem
      
      |- !t n k.
           k < SUC n ==>
           abs (prob (\s. FST (uniform t (SUC n) s) = k) - 1 / &SUC n) <=
           (1 / 2) pow t
   
   [PROB_UNIFORM_UPPER_BOUND]  Theorem
      
      |- !b.
           (!k.
              k < SUC n ==>
              b < prob (\s. FST (uniform t (SUC n) s) = k)) ==>
           !m.
             m < SUC n ==>
             &SUC m * b < prob (\s. FST (uniform t (SUC n) s) < SUC m)
   
   [PROB_UNIF_BOUND]  Theorem
      
      |- !n k.
           k <= 2 ** unif_bound n ==>
           (prob (\s. FST (unif n s) < k) = &k * (1 / 2) pow unif_bound n)
   
   [PROB_UNIF_GOOD]  Theorem
      
      |- !n. 1 / 2 <= prob (\s. FST (unif n s) < SUC n)
   
   [PROB_UNIF_PAIR]  Theorem
      
      |- !n k k'.
           (prob (\s. FST (unif n s) = k) =
            prob (\s. FST (unif n s) = k')) <=>
           (k < 2 ** unif_bound n <=> k' < 2 ** unif_bound n)
   
   [SUC_DIV_TWO_ZERO]  Theorem
      
      |- !n. (SUC n DIV 2 = 0) <=> (n = 0)
   
   [UNIFORM_DEF_MONAD]  Theorem
      
      |- (!n. uniform 0 (SUC n) = UNIT 0) /\
         !t n.
           uniform (SUC t) (SUC n) =
           BIND (unif n)
             (\m. if m < SUC n then UNIT m else uniform t (SUC n))
   
   [UNIFORM_RANGE]  Theorem
      
      |- !t n s. FST (uniform t (SUC n) s) < SUC n
   
   [UNIF_BOUND_LOWER]  Theorem
      
      |- !n. n < 2 ** unif_bound n
   
   [UNIF_BOUND_LOWER_SUC]  Theorem
      
      |- !n. SUC n <= 2 ** unif_bound n
   
   [UNIF_BOUND_UPPER]  Theorem
      
      |- !n. n <> 0 ==> 2 ** unif_bound n <= 2 * n
   
   [UNIF_BOUND_UPPER_SUC]  Theorem
      
      |- !n. 2 ** unif_bound n <= SUC (2 * n)
   
   [UNIF_DEF_MONAD]  Theorem
      
      |- (unif 0 = UNIT 0) /\
         !n.
           unif (SUC n) =
           BIND (unif (SUC n DIV 2))
             (\m. BIND SDEST (\b. UNIT (if b then 2 * m + 1 else 2 * m)))
   
   [UNIF_RANGE]  Theorem
      
      |- !n s. FST (unif n s) < 2 ** unif_bound n
   
   [unif_bound_def]  Theorem
      
      |- (unif_bound 0 = 0) /\
         (unif_bound (SUC v) = SUC (unif_bound (SUC v DIV 2)))
   
   [unif_bound_ind]  Theorem
      
      |- !P. P 0 /\ (!v. P (SUC v DIV 2) ==> P (SUC v)) ==> !v. P v
   
   [unif_def]  Theorem
      
      |- (unif 0 s = (0,s)) /\
         (unif (SUC v2) s =
          (let (m,s') = unif (SUC v2 DIV 2) s in
             (if SHD s' then 2 * m + 1 else 2 * m,STL s')))
   
   [unif_ind]  Theorem
      
      |- !P.
           (!s. P 0 s) /\ (!v2 s. P (SUC v2 DIV 2) s ==> P (SUC v2) s) ==>
           !v v1. P v v1
   
   [uniform_def]  Theorem
      
      |- (!s n. uniform 0 (SUC n) s = (0,s)) /\
         !t s n.
           uniform (SUC t) (SUC n) s =
           (let (res,s') = unif n s in
              if res < SUC n then (res,s') else uniform t (SUC n) s')
   
   [uniform_ind]  Theorem
      
      |- !P.
           (!n s. P 0 (SUC n) s) /\
           (!t n s.
              (!res s'.
                 ((res,s') = unif n s) /\ ~(res < SUC n) ==>
                 P t (SUC n) s') ==>
              P (SUC t) (SUC n) s) /\ (!v6. P 0 0 v6) /\
           (!t v10. P (SUC t) 0 v10) ==>
           !v v1 v2. P v v1 v2
   
   
*)
end
