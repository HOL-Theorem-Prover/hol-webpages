signature prob_canonTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val alg_canon1_def : thm
    val alg_canon2_def : thm
    val alg_canon_def : thm
    val alg_canon_find_def : thm
    val alg_canon_merge_def : thm
    val alg_canon_prefs_def : thm
    val alg_longest_def : thm
    val alg_order_curried_def : thm
    val alg_order_tupled_primitive_def : thm
    val alg_prefixfree_primitive_def : thm
    val alg_sorted_primitive_def : thm
    val alg_twin_def : thm
    val alg_twinfree_primitive_def : thm
    val algebra_canon_def : thm
  
  (*  Theorems  *)
    val ALGEBRA_CANON_BASIC : thm
    val ALGEBRA_CANON_CASES : thm
    val ALGEBRA_CANON_CASES_THM : thm
    val ALGEBRA_CANON_DEF_ALT : thm
    val ALGEBRA_CANON_INDUCTION : thm
    val ALGEBRA_CANON_NIL_MEM : thm
    val ALGEBRA_CANON_STEP : thm
    val ALGEBRA_CANON_STEP1 : thm
    val ALGEBRA_CANON_STEP2 : thm
    val ALGEBRA_CANON_TL : thm
    val ALGEBRA_CANON_TLS : thm
    val ALG_CANON1_CONSTANT : thm
    val ALG_CANON1_PREFIXFREE : thm
    val ALG_CANON1_SORTED : thm
    val ALG_CANON2_CONSTANT : thm
    val ALG_CANON2_PREFIXFREE_PRESERVE : thm
    val ALG_CANON2_SHORTENS : thm
    val ALG_CANON2_SORTED_PREFIXFREE_TWINFREE : thm
    val ALG_CANON_BASIC : thm
    val ALG_CANON_CONSTANT : thm
    val ALG_CANON_FIND_CONSTANT : thm
    val ALG_CANON_FIND_DELETES : thm
    val ALG_CANON_FIND_HD : thm
    val ALG_CANON_FIND_PREFIXFREE : thm
    val ALG_CANON_FIND_SORTED : thm
    val ALG_CANON_IDEMPOT : thm
    val ALG_CANON_MERGE_CONSTANT : thm
    val ALG_CANON_MERGE_PREFIXFREE_PRESERVE : thm
    val ALG_CANON_MERGE_SHORTENS : thm
    val ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE : thm
    val ALG_CANON_PREFS_CONSTANT : thm
    val ALG_CANON_PREFS_DELETES : thm
    val ALG_CANON_PREFS_HD : thm
    val ALG_CANON_PREFS_PREFIXFREE : thm
    val ALG_CANON_PREFS_SORTED : thm
    val ALG_CANON_SORTED_PREFIXFREE_TWINFREE : thm
    val ALG_LONGEST_APPEND : thm
    val ALG_LONGEST_HD : thm
    val ALG_LONGEST_TL : thm
    val ALG_LONGEST_TLS : thm
    val ALG_ORDER_ANTISYM : thm
    val ALG_ORDER_NIL : thm
    val ALG_ORDER_PREFIX : thm
    val ALG_ORDER_PREFIX_ANTI : thm
    val ALG_ORDER_PREFIX_MONO : thm
    val ALG_ORDER_PREFIX_TRANS : thm
    val ALG_ORDER_REFL : thm
    val ALG_ORDER_SNOC : thm
    val ALG_ORDER_TOTAL : thm
    val ALG_ORDER_TRANS : thm
    val ALG_PREFIXFREE_APPEND : thm
    val ALG_PREFIXFREE_ELT : thm
    val ALG_PREFIXFREE_FILTER : thm
    val ALG_PREFIXFREE_MONO : thm
    val ALG_PREFIXFREE_STEP : thm
    val ALG_PREFIXFREE_TL : thm
    val ALG_PREFIXFREE_TLS : thm
    val ALG_SORTED_APPEND : thm
    val ALG_SORTED_DEF_ALT : thm
    val ALG_SORTED_FILTER : thm
    val ALG_SORTED_MIN : thm
    val ALG_SORTED_MONO : thm
    val ALG_SORTED_PREFIXFREE_EQUALITY : thm
    val ALG_SORTED_PREFIXFREE_MEM_NIL : thm
    val ALG_SORTED_STEP : thm
    val ALG_SORTED_TL : thm
    val ALG_SORTED_TLS : thm
    val ALG_TWINFREE_STEP : thm
    val ALG_TWINFREE_STEP1 : thm
    val ALG_TWINFREE_STEP2 : thm
    val ALG_TWINFREE_TL : thm
    val ALG_TWINFREE_TLS : thm
    val ALG_TWINS_PREFIX : thm
    val ALG_TWIN_CONS : thm
    val ALG_TWIN_NIL : thm
    val ALG_TWIN_REDUCE : thm
    val ALG_TWIN_SING : thm
    val MEM_NIL_STEP : thm
    val alg_order_def : thm
    val alg_order_ind : thm
    val alg_prefixfree_def : thm
    val alg_prefixfree_ind : thm
    val alg_sorted_def : thm
    val alg_sorted_ind : thm
    val alg_twinfree_def : thm
    val alg_twinfree_ind : thm
  
  val prob_canon_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [prob_extra] Parent theory of "prob_canon"
   
   [alg_canon1_def]  Definition
      
      |- alg_canon1 = FOLDR alg_canon_find []
   
   [alg_canon2_def]  Definition
      
      |- alg_canon2 = FOLDR alg_canon_merge []
   
   [alg_canon_def]  Definition
      
      |- !l. alg_canon l = alg_canon2 (alg_canon1 l)
   
   [alg_canon_find_def]  Definition
      
      |- (!l. alg_canon_find l [] = [l]) /\
         !l h t.
           alg_canon_find l (h::t) =
           if alg_order h l then
             if h <<= l then h::t else h::alg_canon_find l t
           else
             alg_canon_prefs l (h::t)
   
   [alg_canon_merge_def]  Definition
      
      |- (!l. alg_canon_merge l [] = [l]) /\
         !l h t.
           alg_canon_merge l (h::t) =
           if alg_twin l h then alg_canon_merge (FRONT h) t else l::h::t
   
   [alg_canon_prefs_def]  Definition
      
      |- (!l. alg_canon_prefs l [] = [l]) /\
         !l h t.
           alg_canon_prefs l (h::t) =
           if l <<= h then alg_canon_prefs l t else l::h::t
   
   [alg_longest_def]  Definition
      
      |- alg_longest =
         FOLDR (\h t. if t <= LENGTH h then LENGTH h else t) 0
   
   [alg_order_curried_def]  Definition
      
      |- !x x1. alg_order x x1 <=> alg_order_tupled (x,x1)
   
   [alg_order_tupled_primitive_def]  Definition
      
      |- alg_order_tupled =
         WFREC (@R. WF R /\ !h' h t' t. R (t,t') (h::t,h'::t'))
           (\alg_order_tupled a.
              case a of
                 ([],[]) -> I T
              || ([],v9::v10) -> I T
              || (h::t,[]) -> I F
              || (h::t,h'::t') ->
                   I
                     ((h <=> T) /\ (h' <=> F) \/
                      (h <=> h') /\ alg_order_tupled (t,t')))
   
   [alg_prefixfree_primitive_def]  Definition
      
      |- alg_prefixfree =
         WFREC (@R. WF R /\ !x z y. R (y::z) (x::y::z))
           (\alg_prefixfree a.
              case a of
                 [] -> I T
              || [x] -> I T
              || x::y::z -> I (~(x <<= y) /\ alg_prefixfree (y::z)))
   
   [alg_sorted_primitive_def]  Definition
      
      |- alg_sorted =
         WFREC (@R. WF R /\ !x z y. R (y::z) (x::y::z))
           (\alg_sorted a.
              case a of
                 [] -> I T
              || [x] -> I T
              || x::y::z -> I (alg_order x y /\ alg_sorted (y::z)))
   
   [alg_twin_def]  Definition
      
      |- !x y. alg_twin x y <=> ?l. (x = SNOC T l) /\ (y = SNOC F l)
   
   [alg_twinfree_primitive_def]  Definition
      
      |- alg_twinfree =
         WFREC (@R. WF R /\ !x z y. R (y::z) (x::y::z))
           (\alg_twinfree a.
              case a of
                 [] -> I T
              || [x] -> I T
              || x::y::z -> I (~alg_twin x y /\ alg_twinfree (y::z)))
   
   [algebra_canon_def]  Definition
      
      |- !l. algebra_canon l <=> (alg_canon l = l)
   
   [ALGEBRA_CANON_BASIC]  Theorem
      
      |- algebra_canon [] /\ algebra_canon [[]] /\ !x. algebra_canon [x]
   
   [ALGEBRA_CANON_CASES]  Theorem
      
      |- !P.
           P [] /\ P [[]] /\
           (!l1 l2.
              algebra_canon l1 /\ algebra_canon l2 /\
              algebra_canon (MAP (CONS T) l1 ++ MAP (CONS F) l2) ==>
              P (MAP (CONS T) l1 ++ MAP (CONS F) l2)) ==>
           !l. algebra_canon l ==> P l
   
   [ALGEBRA_CANON_CASES_THM]  Theorem
      
      |- !l.
           algebra_canon l ==>
           (l = []) \/ (l = [[]]) \/
           ?l1 l2.
             algebra_canon l1 /\ algebra_canon l2 /\
             (l = MAP (CONS T) l1 ++ MAP (CONS F) l2)
   
   [ALGEBRA_CANON_DEF_ALT]  Theorem
      
      |- !l.
           algebra_canon l <=>
           alg_sorted l /\ alg_prefixfree l /\ alg_twinfree l
   
   [ALGEBRA_CANON_INDUCTION]  Theorem
      
      |- !P.
           P [] /\ P [[]] /\
           (!l1 l2.
              algebra_canon l1 /\ algebra_canon l2 /\ P l1 /\ P l2 /\
              algebra_canon (MAP (CONS T) l1 ++ MAP (CONS F) l2) ==>
              P (MAP (CONS T) l1 ++ MAP (CONS F) l2)) ==>
           !l. algebra_canon l ==> P l
   
   [ALGEBRA_CANON_NIL_MEM]  Theorem
      
      |- !l. algebra_canon l /\ MEM [] l <=> (l = [[]])
   
   [ALGEBRA_CANON_STEP]  Theorem
      
      |- !l1 l2.
           l1 <> [[]] \/ l2 <> [[]] ==>
           (algebra_canon (MAP (CONS T) l1 ++ MAP (CONS F) l2) <=>
            algebra_canon l1 /\ algebra_canon l2)
   
   [ALGEBRA_CANON_STEP1]  Theorem
      
      |- !l1 l2.
           algebra_canon (MAP (CONS T) l1 ++ MAP (CONS F) l2) ==>
           algebra_canon l1 /\ algebra_canon l2
   
   [ALGEBRA_CANON_STEP2]  Theorem
      
      |- !l1 l2.
           (l1 <> [[]] \/ l2 <> [[]]) /\ algebra_canon l1 /\
           algebra_canon l2 ==>
           algebra_canon (MAP (CONS T) l1 ++ MAP (CONS F) l2)
   
   [ALGEBRA_CANON_TL]  Theorem
      
      |- !h t. algebra_canon (h::t) ==> algebra_canon t
   
   [ALGEBRA_CANON_TLS]  Theorem
      
      |- !l b. algebra_canon (MAP (CONS b) l) <=> algebra_canon l
   
   [ALG_CANON1_CONSTANT]  Theorem
      
      |- !l. alg_sorted l /\ alg_prefixfree l ==> (alg_canon1 l = l)
   
   [ALG_CANON1_PREFIXFREE]  Theorem
      
      |- !l. alg_prefixfree (alg_canon1 l)
   
   [ALG_CANON1_SORTED]  Theorem
      
      |- !l. alg_sorted (alg_canon1 l)
   
   [ALG_CANON2_CONSTANT]  Theorem
      
      |- !l. alg_twinfree l ==> (alg_canon2 l = l)
   
   [ALG_CANON2_PREFIXFREE_PRESERVE]  Theorem
      
      |- !l h.
           (!x. MEM x l ==> ~(x <<= h) /\ ~(h <<= x)) ==>
           !x. MEM x (alg_canon2 l) ==> ~(x <<= h) /\ ~(h <<= x)
   
   [ALG_CANON2_SHORTENS]  Theorem
      
      |- !l x. MEM x (alg_canon2 l) ==> ?y. MEM y l /\ x <<= y
   
   [ALG_CANON2_SORTED_PREFIXFREE_TWINFREE]  Theorem
      
      |- !l.
           alg_sorted l /\ alg_prefixfree l ==>
           alg_sorted (alg_canon2 l) /\ alg_prefixfree (alg_canon2 l) /\
           alg_twinfree (alg_canon2 l)
   
   [ALG_CANON_BASIC]  Theorem
      
      |- (alg_canon [] = []) /\ (alg_canon [[]] = [[]]) /\
         !x. alg_canon [x] = [x]
   
   [ALG_CANON_CONSTANT]  Theorem
      
      |- !l.
           alg_sorted l /\ alg_prefixfree l /\ alg_twinfree l ==>
           (alg_canon l = l)
   
   [ALG_CANON_FIND_CONSTANT]  Theorem
      
      |- !l b.
           alg_sorted (l::b) /\ alg_prefixfree (l::b) ==>
           (alg_canon_find l b = l::b)
   
   [ALG_CANON_FIND_DELETES]  Theorem
      
      |- !l b x. MEM x (alg_canon_find l b) ==> MEM x (l::b)
   
   [ALG_CANON_FIND_HD]  Theorem
      
      |- !l h t.
           (HD (alg_canon_find l (h::t)) = l) \/
           (HD (alg_canon_find l (h::t)) = h)
   
   [ALG_CANON_FIND_PREFIXFREE]  Theorem
      
      |- !l b.
           alg_sorted b /\ alg_prefixfree b ==>
           alg_prefixfree (alg_canon_find l b)
   
   [ALG_CANON_FIND_SORTED]  Theorem
      
      |- !l b. alg_sorted b ==> alg_sorted (alg_canon_find l b)
   
   [ALG_CANON_IDEMPOT]  Theorem
      
      |- !l. alg_canon (alg_canon l) = alg_canon l
   
   [ALG_CANON_MERGE_CONSTANT]  Theorem
      
      |- !l b. alg_twinfree (l::b) ==> (alg_canon_merge l b = l::b)
   
   [ALG_CANON_MERGE_PREFIXFREE_PRESERVE]  Theorem
      
      |- !l b h.
           (!x. MEM x (l::b) ==> ~(x <<= h) /\ ~(h <<= x)) ==>
           !x. MEM x (alg_canon_merge l b) ==> ~(x <<= h) /\ ~(h <<= x)
   
   [ALG_CANON_MERGE_SHORTENS]  Theorem
      
      |- !l b x.
           MEM x (alg_canon_merge l b) ==> ?y. MEM y (l::b) /\ x <<= y
   
   [ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE]  Theorem
      
      |- !l b.
           alg_sorted (l::b) /\ alg_prefixfree (l::b) /\ alg_twinfree b ==>
           alg_sorted (alg_canon_merge l b) /\
           alg_prefixfree (alg_canon_merge l b) /\
           alg_twinfree (alg_canon_merge l b)
   
   [ALG_CANON_PREFS_CONSTANT]  Theorem
      
      |- !l b. alg_prefixfree (l::b) ==> (alg_canon_prefs l b = l::b)
   
   [ALG_CANON_PREFS_DELETES]  Theorem
      
      |- !l b x. MEM x (alg_canon_prefs l b) ==> MEM x (l::b)
   
   [ALG_CANON_PREFS_HD]  Theorem
      
      |- !l b. HD (alg_canon_prefs l b) = l
   
   [ALG_CANON_PREFS_PREFIXFREE]  Theorem
      
      |- !l b.
           alg_sorted b /\ alg_prefixfree b ==>
           alg_prefixfree (alg_canon_prefs l b)
   
   [ALG_CANON_PREFS_SORTED]  Theorem
      
      |- !l b. alg_sorted (l::b) ==> alg_sorted (alg_canon_prefs l b)
   
   [ALG_CANON_SORTED_PREFIXFREE_TWINFREE]  Theorem
      
      |- !l.
           alg_sorted (alg_canon l) /\ alg_prefixfree (alg_canon l) /\
           alg_twinfree (alg_canon l)
   
   [ALG_LONGEST_APPEND]  Theorem
      
      |- !l1 l2.
           alg_longest l1 <= alg_longest (l1 ++ l2) /\
           alg_longest l2 <= alg_longest (l1 ++ l2)
   
   [ALG_LONGEST_HD]  Theorem
      
      |- !h t. LENGTH h <= alg_longest (h::t)
   
   [ALG_LONGEST_TL]  Theorem
      
      |- !h t. alg_longest t <= alg_longest (h::t)
   
   [ALG_LONGEST_TLS]  Theorem
      
      |- !h t b.
           alg_longest (MAP (CONS b) (h::t)) = SUC (alg_longest (h::t))
   
   [ALG_ORDER_ANTISYM]  Theorem
      
      |- !x y. alg_order x y /\ alg_order y x ==> (x = y)
   
   [ALG_ORDER_NIL]  Theorem
      
      |- !x. alg_order [] x /\ (alg_order x [] <=> (x = []))
   
   [ALG_ORDER_PREFIX]  Theorem
      
      |- !x y. x <<= y ==> alg_order x y
   
   [ALG_ORDER_PREFIX_ANTI]  Theorem
      
      |- !x y. alg_order x y /\ y <<= x ==> (x = y)
   
   [ALG_ORDER_PREFIX_MONO]  Theorem
      
      |- !x y z. alg_order x y /\ alg_order y z /\ x <<= z ==> x <<= y
   
   [ALG_ORDER_PREFIX_TRANS]  Theorem
      
      |- !x y z. alg_order x y /\ z <<= y ==> alg_order x z \/ z <<= x
   
   [ALG_ORDER_REFL]  Theorem
      
      |- !x. alg_order x x
   
   [ALG_ORDER_SNOC]  Theorem
      
      |- !x l. ~alg_order (SNOC x l) l
   
   [ALG_ORDER_TOTAL]  Theorem
      
      |- !x y. alg_order x y \/ alg_order y x
   
   [ALG_ORDER_TRANS]  Theorem
      
      |- !x y z. alg_order x y /\ alg_order y z ==> alg_order x z
   
   [ALG_PREFIXFREE_APPEND]  Theorem
      
      |- !h h' t t'.
           alg_prefixfree (h::t ++ h'::t') <=>
           alg_prefixfree (h::t) /\ alg_prefixfree (h'::t') /\
           ~(LAST (h::t) <<= h')
   
   [ALG_PREFIXFREE_ELT]  Theorem
      
      |- !h t.
           alg_sorted (h::t) /\ alg_prefixfree (h::t) ==>
           !x. MEM x t ==> ~(h <<= x) /\ ~(x <<= h)
   
   [ALG_PREFIXFREE_FILTER]  Theorem
      
      |- !P b.
           alg_sorted b /\ alg_prefixfree b ==> alg_prefixfree (FILTER P b)
   
   [ALG_PREFIXFREE_MONO]  Theorem
      
      |- !x y z.
           alg_sorted (x::y::z) /\ alg_prefixfree (x::y::z) ==>
           alg_prefixfree (x::z)
   
   [ALG_PREFIXFREE_STEP]  Theorem
      
      |- !l1 l2.
           alg_prefixfree (MAP (CONS T) l1 ++ MAP (CONS F) l2) <=>
           alg_prefixfree l1 /\ alg_prefixfree l2
   
   [ALG_PREFIXFREE_TL]  Theorem
      
      |- !h t. alg_prefixfree (h::t) ==> alg_prefixfree t
   
   [ALG_PREFIXFREE_TLS]  Theorem
      
      |- !l b. alg_prefixfree (MAP (CONS b) l) <=> alg_prefixfree l
   
   [ALG_SORTED_APPEND]  Theorem
      
      |- !h h' t t'.
           alg_sorted (h::t ++ h'::t') <=>
           alg_sorted (h::t) /\ alg_sorted (h'::t') /\
           alg_order (LAST (h::t)) h'
   
   [ALG_SORTED_DEF_ALT]  Theorem
      
      |- !h t.
           alg_sorted (h::t) <=>
           (!x. MEM x t ==> alg_order h x) /\ alg_sorted t
   
   [ALG_SORTED_FILTER]  Theorem
      
      |- !P b. alg_sorted b ==> alg_sorted (FILTER P b)
   
   [ALG_SORTED_MIN]  Theorem
      
      |- !h t. alg_sorted (h::t) ==> !x. MEM x t ==> alg_order h x
   
   [ALG_SORTED_MONO]  Theorem
      
      |- !x y z. alg_sorted (x::y::z) ==> alg_sorted (x::z)
   
   [ALG_SORTED_PREFIXFREE_EQUALITY]  Theorem
      
      |- !l l'.
           (!x. MEM x l <=> MEM x l') /\ alg_sorted l /\ alg_sorted l' /\
           alg_prefixfree l /\ alg_prefixfree l' ==>
           (l = l')
   
   [ALG_SORTED_PREFIXFREE_MEM_NIL]  Theorem
      
      |- !l. alg_sorted l /\ alg_prefixfree l /\ MEM [] l <=> (l = [[]])
   
   [ALG_SORTED_STEP]  Theorem
      
      |- !l1 l2.
           alg_sorted (MAP (CONS T) l1 ++ MAP (CONS F) l2) <=>
           alg_sorted l1 /\ alg_sorted l2
   
   [ALG_SORTED_TL]  Theorem
      
      |- !h t. alg_sorted (h::t) ==> alg_sorted t
   
   [ALG_SORTED_TLS]  Theorem
      
      |- !l b. alg_sorted (MAP (CONS b) l) <=> alg_sorted l
   
   [ALG_TWINFREE_STEP]  Theorem
      
      |- !l1 l2.
           ~MEM [] l1 \/ ~MEM [] l2 ==>
           (alg_twinfree (MAP (CONS T) l1 ++ MAP (CONS F) l2) <=>
            alg_twinfree l1 /\ alg_twinfree l2)
   
   [ALG_TWINFREE_STEP1]  Theorem
      
      |- !l1 l2.
           alg_twinfree (MAP (CONS T) l1 ++ MAP (CONS F) l2) ==>
           alg_twinfree l1 /\ alg_twinfree l2
   
   [ALG_TWINFREE_STEP2]  Theorem
      
      |- !l1 l2.
           (~MEM [] l1 \/ ~MEM [] l2) /\ alg_twinfree l1 /\
           alg_twinfree l2 ==>
           alg_twinfree (MAP (CONS T) l1 ++ MAP (CONS F) l2)
   
   [ALG_TWINFREE_TL]  Theorem
      
      |- !h t. alg_twinfree (h::t) ==> alg_twinfree t
   
   [ALG_TWINFREE_TLS]  Theorem
      
      |- !l b. alg_twinfree (MAP (CONS b) l) <=> alg_twinfree l
   
   [ALG_TWINS_PREFIX]  Theorem
      
      |- !x l. l <<= x ==> (x = l) \/ SNOC T l <<= x \/ SNOC F l <<= x
   
   [ALG_TWIN_CONS]  Theorem
      
      |- !x y z h t.
           (alg_twin (x::y::z) (h::t) <=>
            (x <=> h) /\ alg_twin (y::z) t) /\
           (alg_twin (h::t) (x::y::z) <=> (x <=> h) /\ alg_twin t (y::z))
   
   [ALG_TWIN_NIL]  Theorem
      
      |- !l. ~alg_twin l [] /\ ~alg_twin [] l
   
   [ALG_TWIN_REDUCE]  Theorem
      
      |- !h t t'. alg_twin (h::t) (h::t') <=> alg_twin t t'
   
   [ALG_TWIN_SING]  Theorem
      
      |- !x l.
           (alg_twin [x] l <=> (x <=> T) /\ (l = [F])) /\
           (alg_twin l [x] <=> (l = [T]) /\ (x <=> F))
   
   [MEM_NIL_STEP]  Theorem
      
      |- !l1 l2. ~MEM [] (MAP (CONS T) l1 ++ MAP (CONS F) l2)
   
   [alg_order_def]  Theorem
      
      |- (alg_order [] [] <=> T) /\
         (!v8 v7. alg_order [] (v7::v8) <=> T) /\
         (!v4 v3. alg_order (v3::v4) [] <=> F) /\
         !t' t h' h.
           alg_order (h::t) (h'::t') <=>
           (h <=> T) /\ (h' <=> F) \/ (h <=> h') /\ alg_order t t'
   
   [alg_order_ind]  Theorem
      
      |- !P.
           P [] [] /\ (!v7 v8. P [] (v7::v8)) /\ (!v3 v4. P (v3::v4) []) /\
           (!h t h' t'. P t t' ==> P (h::t) (h'::t')) ==>
           !v v1. P v v1
   
   [alg_prefixfree_def]  Theorem
      
      |- (!z y x.
            alg_prefixfree (x::y::z) <=>
            ~(x <<= y) /\ alg_prefixfree (y::z)) /\
         (alg_prefixfree [] <=> T) /\ !v. alg_prefixfree [v] <=> T
   
   [alg_prefixfree_ind]  Theorem
      
      |- !P.
           (!x y z. P (y::z) ==> P (x::y::z)) /\ P [] /\ (!v. P [v]) ==>
           !v. P v
   
   [alg_sorted_def]  Theorem
      
      |- (!z y x.
            alg_sorted (x::y::z) <=> alg_order x y /\ alg_sorted (y::z)) /\
         (alg_sorted [] <=> T) /\ !v. alg_sorted [v] <=> T
   
   [alg_sorted_ind]  Theorem
      
      |- !P.
           (!x y z. P (y::z) ==> P (x::y::z)) /\ P [] /\ (!v. P [v]) ==>
           !v. P v
   
   [alg_twinfree_def]  Theorem
      
      |- (!z y x.
            alg_twinfree (x::y::z) <=>
            ~alg_twin x y /\ alg_twinfree (y::z)) /\
         (alg_twinfree [] <=> T) /\ !v. alg_twinfree [v] <=> T
   
   [alg_twinfree_ind]  Theorem
      
      |- !P.
           (!x y z. P (y::z) ==> P (x::y::z)) /\ P [] /\ (!v. P [v]) ==>
           !v. P v
   
   
*)
end
