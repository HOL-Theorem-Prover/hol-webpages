signature prob_algebraTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val alg_embed_def : thm
    val algebra_embed_def : thm
    val measurable_def : thm
  
  (*  Theorems  *)
    val ALGEBRA_CANON_EMBED_EMPTY : thm
    val ALGEBRA_CANON_EMBED_UNIV : thm
    val ALGEBRA_CANON_UNIV : thm
    val ALGEBRA_EMBED_APPEND : thm
    val ALGEBRA_EMBED_BASIC : thm
    val ALGEBRA_EMBED_COMPL : thm
    val ALGEBRA_EMBED_MEM : thm
    val ALGEBRA_EMBED_TLS : thm
    val ALG_CANON1_EMBED : thm
    val ALG_CANON2_EMBED : thm
    val ALG_CANON_EMBED : thm
    val ALG_CANON_FIND_EMBED : thm
    val ALG_CANON_MERGE_EMBED : thm
    val ALG_CANON_PREFS_EMBED : thm
    val ALG_CANON_REP : thm
    val ALG_EMBED_BASIC : thm
    val ALG_EMBED_NIL : thm
    val ALG_EMBED_POPULATED : thm
    val ALG_EMBED_PREFIX : thm
    val ALG_EMBED_PREFIX_SUBSET : thm
    val ALG_EMBED_TWINS : thm
    val COMPL_SHD : thm
    val HALVES_INTER : thm
    val INTER_STL : thm
    val MEASURABLE_ALGEBRA : thm
    val MEASURABLE_BASIC : thm
    val MEASURABLE_COMPL : thm
    val MEASURABLE_HALVES : thm
    val MEASURABLE_INTER : thm
    val MEASURABLE_INTER_HALVES : thm
    val MEASURABLE_INTER_SHD : thm
    val MEASURABLE_SDROP : thm
    val MEASURABLE_SHD : thm
    val MEASURABLE_STL : thm
    val MEASURABLE_UNION : thm
  
  val prob_algebra_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [boolean_sequence] Parent theory of "prob_algebra"
   
   [prob_canon] Parent theory of "prob_algebra"
   
   [alg_embed_def]  Definition
      
      |- (!s. alg_embed [] s <=> T) /\
         !h t s.
           alg_embed (h::t) s <=> (h <=> SHD s) /\ alg_embed t (STL s)
   
   [algebra_embed_def]  Definition
      
      |- (algebra_embed [] = {}) /\
         !h t. algebra_embed (h::t) = alg_embed h UNION algebra_embed t
   
   [measurable_def]  Definition
      
      |- !s. measurable s <=> ?b. s = algebra_embed b
   
   [ALGEBRA_CANON_EMBED_EMPTY]  Theorem
      
      |- !l. algebra_canon l ==> ((!v. ~algebra_embed l v) <=> (l = []))
   
   [ALGEBRA_CANON_EMBED_UNIV]  Theorem
      
      |- !l. algebra_canon l ==> ((!v. algebra_embed l v) <=> (l = [[]]))
   
   [ALGEBRA_CANON_UNIV]  Theorem
      
      |- !l. algebra_canon l ==> (algebra_embed l = UNIV) ==> (l = [[]])
   
   [ALGEBRA_EMBED_APPEND]  Theorem
      
      |- !l1 l2.
           algebra_embed (l1 ++ l2) =
           algebra_embed l1 UNION algebra_embed l2
   
   [ALGEBRA_EMBED_BASIC]  Theorem
      
      |- (algebra_embed [] = {}) /\ (algebra_embed [[]] = UNIV) /\
         !b. algebra_embed [[b]] = (\s. SHD s <=> b)
   
   [ALGEBRA_EMBED_COMPL]  Theorem
      
      |- !l. ?l'. COMPL (algebra_embed l) = algebra_embed l'
   
   [ALGEBRA_EMBED_MEM]  Theorem
      
      |- !b x. algebra_embed b x ==> ?l. MEM l b /\ alg_embed l x
   
   [ALGEBRA_EMBED_TLS]  Theorem
      
      |- !l b.
           algebra_embed (MAP (CONS b) l) (SCONS h t) <=>
           (h <=> b) /\ algebra_embed l t
   
   [ALG_CANON1_EMBED]  Theorem
      
      |- !l. algebra_embed (alg_canon1 l) = algebra_embed l
   
   [ALG_CANON2_EMBED]  Theorem
      
      |- !l. algebra_embed (alg_canon2 l) = algebra_embed l
   
   [ALG_CANON_EMBED]  Theorem
      
      |- !l. algebra_embed (alg_canon l) = algebra_embed l
   
   [ALG_CANON_FIND_EMBED]  Theorem
      
      |- !l b. algebra_embed (alg_canon_find l b) = algebra_embed (l::b)
   
   [ALG_CANON_MERGE_EMBED]  Theorem
      
      |- !l b. algebra_embed (alg_canon_merge l b) = algebra_embed (l::b)
   
   [ALG_CANON_PREFS_EMBED]  Theorem
      
      |- !l b. algebra_embed (alg_canon_prefs l b) = algebra_embed (l::b)
   
   [ALG_CANON_REP]  Theorem
      
      |- !b c.
           (alg_canon b = alg_canon c) <=>
           (algebra_embed b = algebra_embed c)
   
   [ALG_EMBED_BASIC]  Theorem
      
      |- (alg_embed [] = UNIV) /\
         !h t. alg_embed (h::t) = (\x. SHD x <=> h) INTER alg_embed t o STL
   
   [ALG_EMBED_NIL]  Theorem
      
      |- !c. (!x. alg_embed c x) <=> (c = [])
   
   [ALG_EMBED_POPULATED]  Theorem
      
      |- !b. ?x. alg_embed b x
   
   [ALG_EMBED_PREFIX]  Theorem
      
      |- !b c s. alg_embed b s /\ alg_embed c s ==> c <<= b \/ b <<= c
   
   [ALG_EMBED_PREFIX_SUBSET]  Theorem
      
      |- !b c. alg_embed b SUBSET alg_embed c <=> c <<= b
   
   [ALG_EMBED_TWINS]  Theorem
      
      |- !l. alg_embed (SNOC T l) UNION alg_embed (SNOC F l) = alg_embed l
   
   [COMPL_SHD]  Theorem
      
      |- !b. COMPL (\x. SHD x <=> b) = (\x. SHD x <=> ~b)
   
   [HALVES_INTER]  Theorem
      
      |- (\x. SHD x <=> T) INTER (\x. SHD x <=> F) = {}
   
   [INTER_STL]  Theorem
      
      |- !p q. (p INTER q) o STL = p o STL INTER q o STL
   
   [MEASURABLE_ALGEBRA]  Theorem
      
      |- !b. measurable (algebra_embed b)
   
   [MEASURABLE_BASIC]  Theorem
      
      |- measurable {} /\ measurable UNIV /\
         !b. measurable (\s. SHD s <=> b)
   
   [MEASURABLE_COMPL]  Theorem
      
      |- !s. measurable (COMPL s) <=> measurable s
   
   [MEASURABLE_HALVES]  Theorem
      
      |- !p q.
           measurable
             ((\x. SHD x <=> T) INTER p UNION
              (\x. SHD x <=> F) INTER q) <=>
           measurable ((\x. SHD x <=> T) INTER p) /\
           measurable ((\x. SHD x <=> F) INTER q)
   
   [MEASURABLE_INTER]  Theorem
      
      |- !s t. measurable s /\ measurable t ==> measurable (s INTER t)
   
   [MEASURABLE_INTER_HALVES]  Theorem
      
      |- !p.
           measurable ((\x. SHD x <=> T) INTER p) /\
           measurable ((\x. SHD x <=> F) INTER p) <=> measurable p
   
   [MEASURABLE_INTER_SHD]  Theorem
      
      |- !b p.
           measurable ((\x. SHD x <=> b) INTER p o STL) <=> measurable p
   
   [MEASURABLE_SDROP]  Theorem
      
      |- !n p. measurable (p o SDROP n) <=> measurable p
   
   [MEASURABLE_SHD]  Theorem
      
      |- !b. measurable (\s. SHD s <=> b)
   
   [MEASURABLE_STL]  Theorem
      
      |- !p. measurable (p o STL) <=> measurable p
   
   [MEASURABLE_UNION]  Theorem
      
      |- !s t. measurable s /\ measurable t ==> measurable (s UNION t)
   
   
*)
end
