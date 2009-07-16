signature prob_indepTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val alg_cover_def : thm
    val alg_cover_set_def : thm
    val indep_def : thm
    val indep_set_def : thm
  
  (*  Theorems  *)
    val ALG_COVER_EXISTS_UNIQUE : thm
    val ALG_COVER_HEAD : thm
    val ALG_COVER_SET_BASIC : thm
    val ALG_COVER_SET_CASES : thm
    val ALG_COVER_SET_CASES_THM : thm
    val ALG_COVER_SET_INDUCTION : thm
    val ALG_COVER_STEP : thm
    val ALG_COVER_TAIL_MEASURABLE : thm
    val ALG_COVER_TAIL_PROB : thm
    val ALG_COVER_TAIL_STEP : thm
    val ALG_COVER_UNIQUE : thm
    val ALG_COVER_UNIV : thm
    val ALG_COVER_WELL_DEFINED : thm
    val BIND_STEP : thm
    val INDEP_BIND : thm
    val INDEP_BIND_SDEST : thm
    val INDEP_INDEP_SET : thm
    val INDEP_INDEP_SET_LEMMA : thm
    val INDEP_MEASURABLE1 : thm
    val INDEP_MEASURABLE2 : thm
    val INDEP_PROB : thm
    val INDEP_SDEST : thm
    val INDEP_SET_BASIC : thm
    val INDEP_SET_DISJOINT_DECOMP : thm
    val INDEP_SET_LIST : thm
    val INDEP_SET_SYM : thm
    val INDEP_UNIT : thm
    val MAP_CONS_TL_FILTER : thm
    val PROB_INDEP_BOUND : thm
  
  val prob_indep_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [prob] Parent theory of "prob_indep"
   
   [state_transformer] Parent theory of "prob_indep"
   
   [alg_cover_def]  Definition
      
      |- !l x. alg_cover l x = @b. MEM b l /\ alg_embed b x
   
   [alg_cover_set_def]  Definition
      
      |- !l.
           alg_cover_set l <=>
           alg_sorted l /\ alg_prefixfree l /\ (algebra_embed l = UNIV)
   
   [indep_def]  Definition
      
      |- !f.
           indep f <=>
           ?l r.
             alg_cover_set l /\
             !s. f s = (let c = alg_cover l s in (r c,SDROP (LENGTH c) s))
   
   [indep_set_def]  Definition
      
      |- !p q.
           indep_set p q <=>
           measurable p /\ measurable q /\
           (prob (p INTER q) = prob p * prob q)
   
   [ALG_COVER_EXISTS_UNIQUE]  Theorem
      
      |- !l. alg_cover_set l ==> !s. ?!x. MEM x l /\ alg_embed x s
   
   [ALG_COVER_HEAD]  Theorem
      
      |- !l.
           alg_cover_set l ==>
           !f. f o alg_cover l = algebra_embed (FILTER f l)
   
   [ALG_COVER_SET_BASIC]  Theorem
      
      |- ~alg_cover_set [] /\ alg_cover_set [[]] /\
         alg_cover_set [[T]; [F]]
   
   [ALG_COVER_SET_CASES]  Theorem
      
      |- !P.
           P [[]] /\
           (!l1 l2.
              alg_cover_set l1 /\ alg_cover_set l2 /\
              alg_cover_set (MAP (CONS T) l1 ++ MAP (CONS F) l2) ==>
              P (MAP (CONS T) l1 ++ MAP (CONS F) l2)) ==>
           !l. alg_cover_set l ==> P l
   
   [ALG_COVER_SET_CASES_THM]  Theorem
      
      |- !l.
           alg_cover_set l <=>
           (l = [[]]) \/
           ?l1 l2.
             alg_cover_set l1 /\ alg_cover_set l2 /\
             (l = MAP (CONS T) l1 ++ MAP (CONS F) l2)
   
   [ALG_COVER_SET_INDUCTION]  Theorem
      
      |- !P.
           P [[]] /\
           (!l1 l2.
              alg_cover_set l1 /\ alg_cover_set l2 /\ P l1 /\ P l2 /\
              alg_cover_set (MAP (CONS T) l1 ++ MAP (CONS F) l2) ==>
              P (MAP (CONS T) l1 ++ MAP (CONS F) l2)) ==>
           !l. alg_cover_set l ==> P l
   
   [ALG_COVER_STEP]  Theorem
      
      |- !l1 l2 h t.
           alg_cover_set l1 /\ alg_cover_set l2 ==>
           (alg_cover (MAP (CONS T) l1 ++ MAP (CONS F) l2) (SCONS h t) =
            if h then T::alg_cover l1 t else F::alg_cover l2 t)
   
   [ALG_COVER_TAIL_MEASURABLE]  Theorem
      
      |- !l.
           alg_cover_set l ==>
           !q.
             measurable (q o (\x. SDROP (LENGTH (alg_cover l x)) x)) <=>
             measurable q
   
   [ALG_COVER_TAIL_PROB]  Theorem
      
      |- !l.
           alg_cover_set l ==>
           !q.
             measurable q ==>
             (prob (q o (\x. SDROP (LENGTH (alg_cover l x)) x)) = prob q)
   
   [ALG_COVER_TAIL_STEP]  Theorem
      
      |- !l1 l2 q.
           alg_cover_set l1 /\ alg_cover_set l2 ==>
           (q o
            (\x.
               SDROP
                 (LENGTH
                    (alg_cover (MAP (CONS T) l1 ++ MAP (CONS F) l2) x))
                 x) =
            (\x. SHD x <=> T) INTER
            q o (\x. SDROP (LENGTH (alg_cover l1 x)) x) o STL UNION
            (\x. SHD x <=> F) INTER
            q o (\x. SDROP (LENGTH (alg_cover l2 x)) x) o STL)
   
   [ALG_COVER_UNIQUE]  Theorem
      
      |- !l x s.
           alg_cover_set l /\ MEM x l /\ alg_embed x s ==>
           (alg_cover l s = x)
   
   [ALG_COVER_UNIV]  Theorem
      
      |- alg_cover [[]] = K []
   
   [ALG_COVER_WELL_DEFINED]  Theorem
      
      |- !l x.
           alg_cover_set l ==>
           MEM (alg_cover l x) l /\ alg_embed (alg_cover l x) x
   
   [BIND_STEP]  Theorem
      
      |- !f. BIND SDEST (\k. f o SCONS k) = f
   
   [INDEP_BIND]  Theorem
      
      |- !f g. indep f /\ (!x. indep (g x)) ==> indep (BIND f g)
   
   [INDEP_BIND_SDEST]  Theorem
      
      |- !f. (!x. indep (f x)) ==> indep (BIND SDEST f)
   
   [INDEP_INDEP_SET]  Theorem
      
      |- !f p q.
           indep f /\ measurable q ==>
           indep_set (p o FST o f) (q o SND o f)
   
   [INDEP_INDEP_SET_LEMMA]  Theorem
      
      |- !l.
           alg_cover_set l ==>
           !q.
             measurable q ==>
             !x.
               MEM x l ==>
               (prob
                  (alg_embed x INTER
                   q o (\x. SDROP (LENGTH (alg_cover l x)) x)) =
                (1 / 2) pow LENGTH x * prob q)
   
   [INDEP_MEASURABLE1]  Theorem
      
      |- !f p. indep f ==> measurable (p o FST o f)
   
   [INDEP_MEASURABLE2]  Theorem
      
      |- !f q. indep f /\ measurable q ==> measurable (q o SND o f)
   
   [INDEP_PROB]  Theorem
      
      |- !f p q.
           indep f /\ measurable q ==>
           (prob (p o FST o f INTER q o SND o f) =
            prob (p o FST o f) * prob q)
   
   [INDEP_SDEST]  Theorem
      
      |- indep SDEST
   
   [INDEP_SET_BASIC]  Theorem
      
      |- !p. measurable p ==> indep_set {} p /\ indep_set UNIV p
   
   [INDEP_SET_DISJOINT_DECOMP]  Theorem
      
      |- !p q r.
           indep_set p r /\ indep_set q r /\ (p INTER q = {}) ==>
           indep_set (p UNION q) r
   
   [INDEP_SET_LIST]  Theorem
      
      |- !q l.
           alg_sorted l /\ alg_prefixfree l /\ measurable q /\
           (!x. MEM x l ==> indep_set (alg_embed x) q) ==>
           indep_set (algebra_embed l) q
   
   [INDEP_SET_SYM]  Theorem
      
      |- !p q. indep_set p q <=> indep_set p q
   
   [INDEP_UNIT]  Theorem
      
      |- !x. indep (UNIT x)
   
   [MAP_CONS_TL_FILTER]  Theorem
      
      |- !l b.
           ~MEM [] l ==>
           (MAP (CONS b) (MAP TL (FILTER (\x. HD x <=> b) l)) =
            FILTER (\x. HD x <=> b) l)
   
   [PROB_INDEP_BOUND]  Theorem
      
      |- !f n.
           indep f ==>
           (prob (\s. FST (f s) < SUC n) =
            prob (\s. FST (f s) < n) + prob (\s. FST (f s) = n))
   
   
*)
end
