signature pathTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val PL_def : thm
    val SN_def : thm
    val drop_def : thm
    val el_def : thm
    val every_def : thm
    val exists_def : thm
    val filter_def : thm
    val finite_def : thm
    val firstP_at_def : thm
    val first_def : thm
    val first_label_def : thm
    val is_stopped_def : thm
    val labels_def : thm
    val last_thm : thm
    val length_def : thm
    val mem_def : thm
    val nth_label_def : thm
    val okpath_def : thm
    val okpath_f_def : thm
    val path_TY_DEF : thm
    val path_absrep_bijections : thm
    val pconcat_def : thm
    val pcons_def : thm
    val pgenerate_def : thm
    val plink_def : thm
    val pmap_def : thm
    val seg_def : thm
    val stopped_at_def : thm
    val tail_def : thm
    val take_def : thm
  
  (*  Theorems  *)
    val FORALL_path : thm
    val IN_PL_drop : thm
    val PL_0 : thm
    val PL_downward_closed : thm
    val PL_drop : thm
    val PL_pcons : thm
    val PL_pmap : thm
    val PL_seg : thm
    val PL_stopped_at : thm
    val PL_take : thm
    val PL_thm : thm
    val SN_finite_paths : thm
    val SN_finite_paths_EQ : thm
    val alt_length_thm : thm
    val el_drop : thm
    val el_pgenerate : thm
    val el_pmap : thm
    val every_coinduction : thm
    val every_el : thm
    val every_thm : thm
    val exists_el : thm
    val exists_induction : thm
    val exists_thm : thm
    val filter_every : thm
    val finite_drop : thm
    val finite_length : thm
    val finite_okpath_ind : thm
    val finite_path_ind : thm
    val finite_paths_SN : thm
    val finite_pconcat : thm
    val finite_plink : thm
    val finite_pmap : thm
    val finite_seg : thm
    val finite_take : thm
    val finite_thm : thm
    val firstP_at_thm : thm
    val firstP_at_unique : thm
    val firstP_at_zero : thm
    val first_drop : thm
    val first_label_drop : thm
    val first_plink : thm
    val first_pmap : thm
    val first_seg : thm
    val first_take : thm
    val first_thm : thm
    val fromPath_11 : thm
    val fromPath_onto : thm
    val infinite_PL : thm
    val is_stopped_thm : thm
    val last_plink : thm
    val last_pmap : thm
    val last_seg : thm
    val last_take : thm
    val length_drop : thm
    val length_never_zero : thm
    val length_pmap : thm
    val length_take : thm
    val length_thm : thm
    val mem_thm : thm
    val not_every : thm
    val not_exists : thm
    val nth_label_drop : thm
    val nth_label_pgenerate : thm
    val nth_label_pmap : thm
    val nth_label_take : thm
    val numeral_drop : thm
    val okpath_cases : thm
    val okpath_co_ind : thm
    val okpath_drop : thm
    val okpath_monotone : thm
    val okpath_plink : thm
    val okpath_pmap : thm
    val okpath_seg : thm
    val okpath_take : thm
    val okpath_thm : thm
    val path_Axiom : thm
    val path_bisimulation : thm
    val path_cases : thm
    val path_rep_bijections_thm : thm
    val pconcat_eq_pcons : thm
    val pconcat_eq_stopped : thm
    val pconcat_thm : thm
    val pcons_11 : thm
    val pgenerate_11 : thm
    val pgenerate_infinite : thm
    val pgenerate_not_stopped : thm
    val pgenerate_onto : thm
    val pmap_thm : thm
    val recursive_seg : thm
    val singleton_seg : thm
    val stopped_at_11 : thm
    val stopped_at_not_pcons : thm
    val tail_drop : thm
    val toPath_11 : thm
    val toPath_onto : thm
  
  val path_grammars : type_grammar.grammar * term_grammar.grammar
  
  val path_rwts : simpLib.ssfrag
(*
   [fixedPoint] Parent theory of "path"
   
   [llist] Parent theory of "path"
   
   [PL_def]  Definition
      
      |- !p. PL p = {i | finite p ==> i < THE (length p)}
   
   [SN_def]  Definition
      
      |- !R. SN R <=> WF (\x y. ?l. R y l x)
   
   [drop_def]  Definition
      
      |- (!p. drop 0 p = p) /\ !n p. drop (SUC n) p = drop n (tail p)
   
   [el_def]  Definition
      
      |- (!p. el 0 p = first p) /\ !n p. el (SUC n) p = el n (tail p)
   
   [every_def]  Definition
      
      |- !P p. every P p <=> ~exists ($~ o P) p
   
   [exists_def]  Definition
      
      |- !P p. exists P p <=> ?i. firstP_at P p i
   
   [filter_def]  Definition
      
      |- !P.
           (!x. P x ==> (filter P (stopped_at x) = stopped_at x)) /\
           !x r p.
             filter P (pcons x r p) =
             if P x then
               if exists P p then pcons x r (filter P p) else stopped_at x
             else
               filter P p
   
   [finite_def]  Definition
      
      |- !sigma. finite sigma <=> LFINITE (SND (fromPath sigma))
   
   [firstP_at_def]  Definition
      
      |- !P p i.
           firstP_at P p i <=>
           i IN PL p /\ P (el i p) /\ !j. j < i ==> ~P (el j p)
   
   [first_def]  Definition
      
      |- !p. first p = FST (fromPath p)
   
   [first_label_def]  Definition
      
      |- !x r p. first_label (pcons x r p) = r
   
   [is_stopped_def]  Definition
      
      |- !p. is_stopped p <=> ?x. p = stopped_at x
   
   [labels_def]  Definition
      
      |- (!x. labels (stopped_at x) = [||]) /\
         !x r p. labels (pcons x r p) = r:::labels p
   
   [last_thm]  Definition
      
      |- (!x. last (stopped_at x) = x) /\
         !x r p. last (pcons x r p) = last p
   
   [length_def]  Definition
      
      |- !p.
           length p =
           if finite p then
             SOME (LENGTH (THE (toList (SND (fromPath p)))) + 1)
           else
             NONE
   
   [mem_def]  Definition
      
      |- !s p. mem s p <=> ?i. i IN PL p /\ (s = el i p)
   
   [nth_label_def]  Definition
      
      |- (!p. nth_label 0 p = first_label p) /\
         !n p. nth_label (SUC n) p = nth_label n (tail p)
   
   [okpath_def]  Definition
      
      |- !R. okpath R = gfp (okpath_f R)
   
   [okpath_f_def]  Definition
      
      |- !R X.
           okpath_f R X =
           {stopped_at x | x IN UNIV} UNION
           {pcons x r p | R x r (first p) /\ p IN X}
   
   [path_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (\x. T) rep
   
   [path_absrep_bijections]  Definition
      
      |- (!a. toPath (fromPath a) = a) /\
         !r. (\x. T) r <=> (fromPath (toPath r) = r)
   
   [pconcat_def]  Definition
      
      |- !p1 lab p2.
           pconcat p1 lab p2 =
           toPath
             (first p1,
              LAPPEND (SND (fromPath p1))
                ((lab,first p2):::SND (fromPath p2)))
   
   [pcons_def]  Definition
      
      |- !x r p. pcons x r p = toPath (x,(r,first p):::SND (fromPath p))
   
   [pgenerate_def]  Definition
      
      |- !f g.
           pgenerate f g =
           pcons (f 0) (g 0) (pgenerate (f o SUC) (g o SUC))
   
   [plink_def]  Definition
      
      |- (!x p. plink (stopped_at x) p = p) /\
         !x r p1 p2. plink (pcons x r p1) p2 = pcons x r (plink p1 p2)
   
   [pmap_def]  Definition
      
      |- !f g p. pmap f g p = toPath ((f ## LMAP (g ## f)) (fromPath p))
   
   [seg_def]  Definition
      
      |- !i j p. seg i j p = take (j - i) (drop i p)
   
   [stopped_at_def]  Definition
      
      |- !x. stopped_at x = toPath (x,[||])
   
   [tail_def]  Definition
      
      |- !x r p. tail (pcons x r p) = p
   
   [take_def]  Definition
      
      |- (!p. take 0 p = stopped_at (first p)) /\
         !n p.
           take (SUC n) p =
           pcons (first p) (first_label p) (take n (tail p))
   
   [FORALL_path]  Theorem
      
      |- !P.
           (!p. P p) <=> (!x. P (stopped_at x)) /\ !x r p. P (pcons x r p)
   
   [IN_PL_drop]  Theorem
      
      |- !i j p. i IN PL p ==> (j IN PL (drop i p) <=> i + j IN PL p)
   
   [PL_0]  Theorem
      
      |- !p. 0 IN PL p
   
   [PL_downward_closed]  Theorem
      
      |- !i p. i IN PL p ==> !j. j < i ==> j IN PL p
   
   [PL_drop]  Theorem
      
      |- !p i. i IN PL p ==> (PL (drop i p) = IMAGE (\n. n - i) (PL p))
   
   [PL_pcons]  Theorem
      
      |- !x r q. PL (pcons x r q) = 0 INSERT IMAGE SUC (PL q)
   
   [PL_pmap]  Theorem
      
      |- PL (pmap f g p) = PL p
   
   [PL_seg]  Theorem
      
      |- !i j p.
           i <= j /\ j IN PL p ==> (PL (seg i j p) = {n | n <= j - i})
   
   [PL_stopped_at]  Theorem
      
      |- !x. PL (stopped_at x) = {0}
   
   [PL_take]  Theorem
      
      |- !p i. i IN PL p ==> (PL (take i p) = {n | n <= i})
   
   [PL_thm]  Theorem
      
      |- (!x. PL (stopped_at x) = {0}) /\
         !x r q. PL (pcons x r q) = 0 INSERT IMAGE SUC (PL q)
   
   [SN_finite_paths]  Theorem
      
      |- !R p. SN R /\ okpath R p ==> finite p
   
   [SN_finite_paths_EQ]  Theorem
      
      |- !R. SN R <=> !p. okpath R p ==> finite p
   
   [alt_length_thm]  Theorem
      
      |- (!x. length (stopped_at x) = SOME 1) /\
         !x r p. length (pcons x r p) = OPTION_MAP SUC (length p)
   
   [el_drop]  Theorem
      
      |- !i j p. i + j IN PL p ==> (el i (drop j p) = el (i + j) p)
   
   [el_pgenerate]  Theorem
      
      |- !n f g. el n (pgenerate f g) = f n
   
   [el_pmap]  Theorem
      
      |- !i p. i IN PL p ==> (el i (pmap f g p) = f (el i p))
   
   [every_coinduction]  Theorem
      
      |- !P Q.
           (!x. P (stopped_at x) ==> Q x) /\
           (!x r p. P (pcons x r p) ==> Q x /\ P p) ==>
           !p. P p ==> every Q p
   
   [every_el]  Theorem
      
      |- !P p. every P p <=> !i. i IN PL p ==> P (el i p)
   
   [every_thm]  Theorem
      
      |- !P.
           (!x. every P (stopped_at x) <=> P x) /\
           !x r p. every P (pcons x r p) <=> P x /\ every P p
   
   [exists_el]  Theorem
      
      |- !P p. exists P p <=> ?i. i IN PL p /\ P (el i p)
   
   [exists_induction]  Theorem
      
      |- (!x. Q x ==> P (stopped_at x)) /\
         (!x r p. Q x ==> P (pcons x r p)) /\
         (!x r p. P p ==> P (pcons x r p)) ==>
         !p. exists Q p ==> P p
   
   [exists_thm]  Theorem
      
      |- !P.
           (!x. exists P (stopped_at x) <=> P x) /\
           !x r p. exists P (pcons x r p) <=> P x \/ exists P p
   
   [filter_every]  Theorem
      
      |- !P p. exists P p ==> every P (filter P p)
   
   [finite_drop]  Theorem
      
      |- !p n. n IN PL p ==> (finite (drop n p) <=> finite p)
   
   [finite_length]  Theorem
      
      |- !p.
           (finite p <=> ?n. length p = SOME n) /\
           (~finite p <=> (length p = NONE))
   
   [finite_okpath_ind]  Theorem
      
      |- !R.
           (!x. P (stopped_at x)) /\
           (!x r p.
              okpath R p /\ finite p /\ R x r (first p) /\ P p ==>
              P (pcons x r p)) ==>
           !sigma. okpath R sigma /\ finite sigma ==> P sigma
   
   [finite_path_ind]  Theorem
      
      |- !P.
           (!x. P (stopped_at x)) /\
           (!x r p. finite p /\ P p ==> P (pcons x r p)) ==>
           !q. finite q ==> P q
   
   [finite_paths_SN]  Theorem
      
      |- !R. (!p. okpath R p ==> finite p) ==> SN R
   
   [finite_pconcat]  Theorem
      
      |- !p1 lab p2. finite (pconcat p1 lab p2) <=> finite p1 /\ finite p2
   
   [finite_plink]  Theorem
      
      |- !p1 p2. finite (plink p1 p2) <=> finite p1 /\ finite p2
   
   [finite_pmap]  Theorem
      
      |- !f g p. finite (pmap f g p) <=> finite p
   
   [finite_seg]  Theorem
      
      |- !p i j. i <= j /\ j IN PL p ==> finite (seg i j p)
   
   [finite_take]  Theorem
      
      |- !p i. i IN PL p ==> finite (take i p)
   
   [finite_thm]  Theorem
      
      |- (!x. finite (stopped_at x) <=> T) /\
         !x r p. finite (pcons x r p) <=> finite p
   
   [firstP_at_thm]  Theorem
      
      |- (!P x n. firstP_at P (stopped_at x) n <=> (n = 0) /\ P x) /\
         !P n x r p.
           firstP_at P (pcons x r p) n <=>
           (n = 0) /\ P x \/ 0 < n /\ ~P x /\ firstP_at P p (n - 1)
   
   [firstP_at_unique]  Theorem
      
      |- !P p n. firstP_at P p n ==> !m. firstP_at P p m <=> (m = n)
   
   [firstP_at_zero]  Theorem
      
      |- !P p. firstP_at P p 0 <=> P (first p)
   
   [first_drop]  Theorem
      
      |- !i p. i IN PL p ==> (first (drop i p) = el i p)
   
   [first_label_drop]  Theorem
      
      |- !i p. i IN PL p ==> (first_label (drop i p) = nth_label i p)
   
   [first_plink]  Theorem
      
      |- !p1 p2. (last p1 = first p2) ==> (first (plink p1 p2) = first p1)
   
   [first_pmap]  Theorem
      
      |- !p. first (pmap f g p) = f (first p)
   
   [first_seg]  Theorem
      
      |- !i j p. i <= j /\ j IN PL p ==> (first (seg i j p) = el i p)
   
   [first_take]  Theorem
      
      |- !p i. first (take i p) = first p
   
   [first_thm]  Theorem
      
      |- (!x. first (stopped_at x) = x) /\ !x r p. first (pcons x r p) = x
   
   [fromPath_11]  Theorem
      
      |- !a a'. (fromPath a = fromPath a') <=> (a = a')
   
   [fromPath_onto]  Theorem
      
      |- !r. ?a. r = fromPath a
   
   [infinite_PL]  Theorem
      
      |- !p. ~finite p ==> !i. i IN PL p
   
   [is_stopped_thm]  Theorem
      
      |- (!x. is_stopped (stopped_at x) <=> T) /\
         !x r p. is_stopped (pcons x r p) <=> F
   
   [last_plink]  Theorem
      
      |- !p1 p2.
           finite p1 /\ finite p2 /\ (last p1 = first p2) ==>
           (last (plink p1 p2) = last p2)
   
   [last_pmap]  Theorem
      
      |- !p. finite p ==> (last (pmap f g p) = f (last p))
   
   [last_seg]  Theorem
      
      |- !i j p. i <= j /\ j IN PL p ==> (last (seg i j p) = el j p)
   
   [last_take]  Theorem
      
      |- !i p. i IN PL p ==> (last (take i p) = el i p)
   
   [length_drop]  Theorem
      
      |- !p n.
           n IN PL p ==>
           (length (drop n p) =
            case length p of NONE -> NONE || SOME m -> SOME (m - n))
   
   [length_never_zero]  Theorem
      
      |- !p. length p <> SOME 0
   
   [length_pmap]  Theorem
      
      |- !f g p. length (pmap f g p) = length p
   
   [length_take]  Theorem
      
      |- !p i. i IN PL p ==> (length (take i p) = SOME (i + 1))
   
   [length_thm]  Theorem
      
      |- (!x. length (stopped_at x) = SOME 1) /\
         !x r p.
           length (pcons x r p) =
           if finite p then SOME (THE (length p) + 1) else NONE
   
   [mem_thm]  Theorem
      
      |- (!x s. mem s (stopped_at x) <=> (s = x)) /\
         !x r p s. mem s (pcons x r p) <=> (s = x) \/ mem s p
   
   [not_every]  Theorem
      
      |- !P p. ~every P p <=> exists ($~ o P) p
   
   [not_exists]  Theorem
      
      |- !P p. ~exists P p <=> every ($~ o P) p
   
   [nth_label_drop]  Theorem
      
      |- !i j p.
           SUC (i + j) IN PL p ==>
           (nth_label i (drop j p) = nth_label (i + j) p)
   
   [nth_label_pgenerate]  Theorem
      
      |- !n f g. nth_label n (pgenerate f g) = g n
   
   [nth_label_pmap]  Theorem
      
      |- !i p.
           SUC i IN PL p ==> (nth_label i (pmap f g p) = g (nth_label i p))
   
   [nth_label_take]  Theorem
      
      |- !n p i.
           i < n /\ n IN PL p ==> (nth_label i (take n p) = nth_label i p)
   
   [numeral_drop]  Theorem
      
      |- (!n p.
            drop (NUMERAL (BIT1 n)) p =
            drop (NUMERAL (BIT1 n) - 1) (tail p)) /\
         !n p. drop (NUMERAL (BIT2 n)) p = drop (NUMERAL (BIT1 n)) (tail p)
   
   [okpath_cases]  Theorem
      
      |- !R x.
           okpath R x <=>
           (?x'. x = stopped_at x') \/
           ?x' r p. (x = pcons x' r p) /\ R x' r (first p) /\ okpath R p
   
   [okpath_co_ind]  Theorem
      
      |- !P.
           (!x r p. P (pcons x r p) ==> R x r (first p) /\ P p) ==>
           !p. P p ==> okpath R p
   
   [okpath_drop]  Theorem
      
      |- !R p i. i IN PL p /\ okpath R p ==> okpath R (drop i p)
   
   [okpath_monotone]  Theorem
      
      |- !R. monotone (okpath_f R)
   
   [okpath_plink]  Theorem
      
      |- !R p1 p2.
           finite p1 /\ (last p1 = first p2) ==>
           (okpath R (plink p1 p2) <=> okpath R p1 /\ okpath R p2)
   
   [okpath_pmap]  Theorem
      
      |- !R f g p.
           okpath R p /\ (!x r y. R x r y ==> R (f x) (g r) (f y)) ==>
           okpath R (pmap f g p)
   
   [okpath_seg]  Theorem
      
      |- !R p i j.
           i <= j /\ j IN PL p /\ okpath R p ==> okpath R (seg i j p)
   
   [okpath_take]  Theorem
      
      |- !R p i. i IN PL p /\ okpath R p ==> okpath R (take i p)
   
   [okpath_thm]  Theorem
      
      |- !R.
           (!x. okpath R (stopped_at x)) /\
           !x r p. okpath R (pcons x r p) <=> R x r (first p) /\ okpath R p
   
   [path_Axiom]  Theorem
      
      |- !f.
           ?g.
             !x.
               g x =
               case f x of
                  (y,NONE) -> stopped_at y
               || (y,SOME (l,v)) -> pcons y l (g v)
   
   [path_bisimulation]  Theorem
      
      |- !p1 p2.
           (p1 = p2) <=>
           ?R.
             R p1 p2 /\
             !q1 q2.
               R q1 q2 ==>
               (?x. (q1 = stopped_at x) /\ (q2 = stopped_at x)) \/
               ?x r q1' q2'.
                 (q1 = pcons x r q1') /\ (q2 = pcons x r q2') /\ R q1' q2'
   
   [path_cases]  Theorem
      
      |- !p. (?x. p = stopped_at x) \/ ?x r q. p = pcons x r q
   
   [path_rep_bijections_thm]  Theorem
      
      |- (!a. toPath (fromPath a) = a) /\ !r. fromPath (toPath r) = r
   
   [pconcat_eq_pcons]  Theorem
      
      |- !x r p p1 lab p2.
           ((pconcat p1 lab p2 = pcons x r p) <=>
            (lab = r) /\ (p1 = stopped_at x) /\ (p = p2) \/
            ?p1'. (p1 = pcons x r p1') /\ (p = pconcat p1' lab p2)) /\
           ((pcons x r p = pconcat p1 lab p2) <=>
            (lab = r) /\ (p1 = stopped_at x) /\ (p = p2) \/
            ?p1'. (p1 = pcons x r p1') /\ (p = pconcat p1' lab p2))
   
   [pconcat_eq_stopped]  Theorem
      
      |- !p1 lab p2 x.
           pconcat p1 lab p2 <> stopped_at x /\
           stopped_at x <> pconcat p1 lab p2
   
   [pconcat_thm]  Theorem
      
      |- (!x lab p2. pconcat (stopped_at x) lab p2 = pcons x lab p2) /\
         !x r p lab p2.
           pconcat (pcons x r p) lab p2 = pcons x r (pconcat p lab p2)
   
   [pcons_11]  Theorem
      
      |- !x r p y s q.
           (pcons x r p = pcons y s q) <=> (x = y) /\ (r = s) /\ (p = q)
   
   [pgenerate_11]  Theorem
      
      |- !f1 g1 f2 g2.
           (pgenerate f1 g1 = pgenerate f2 g2) <=> (f1 = f2) /\ (g1 = g2)
   
   [pgenerate_infinite]  Theorem
      
      |- !f g. ~finite (pgenerate f g)
   
   [pgenerate_not_stopped]  Theorem
      
      |- !f g x. stopped_at x <> pgenerate f g
   
   [pgenerate_onto]  Theorem
      
      |- !p. ~finite p ==> ?f g. p = pgenerate f g
   
   [pmap_thm]  Theorem
      
      |- (!x. pmap f g (stopped_at x) = stopped_at (f x)) /\
         !x r p. pmap f g (pcons x r p) = pcons (f x) (g r) (pmap f g p)
   
   [recursive_seg]  Theorem
      
      |- !i j p.
           i < j /\ j IN PL p ==>
           (seg i j p = pcons (el i p) (nth_label i p) (seg (i + 1) j p))
   
   [singleton_seg]  Theorem
      
      |- !i p. i IN PL p ==> (seg i i p = stopped_at (el i p))
   
   [stopped_at_11]  Theorem
      
      |- !x y. (stopped_at x = stopped_at y) <=> (x = y)
   
   [stopped_at_not_pcons]  Theorem
      
      |- !x y r p.
           stopped_at x <> pcons y r p /\ pcons y r p <> stopped_at x
   
   [tail_drop]  Theorem
      
      |- !i p. i + 1 IN PL p ==> (tail (drop i p) = drop (i + 1) p)
   
   [toPath_11]  Theorem
      
      |- !r r'. (toPath r = toPath r') <=> (r = r')
   
   [toPath_onto]  Theorem
      
      |- !a. ?r. a = toPath r
   
   
*)
end
