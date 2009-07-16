signature llistTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val LAPPEND : thm
    val LCONS : thm
    val LDROP : thm
    val LFILTER : thm
    val LFLATTEN : thm
    val LHD : thm
    val LLENGTH : thm
    val LMAP : thm
    val LNIL : thm
    val LNTH : thm
    val LTAKE : thm
    val LTL : thm
    val LUNFOLD : thm
    val LUNZIP_THM : thm
    val LZIP_THM : thm
    val every_def : thm
    val exists : thm
    val fromList : thm
    val llength_rel : thm
    val llist_TY_DEF : thm
    val llist_absrep : thm
    val lrep_ok_def : thm
    val toList : thm
  
  (*  Theorems  *)
    val LAPPEND_ASSOC : thm
    val LAPPEND_EQ_LNIL : thm
    val LAPPEND_NIL_2ND : thm
    val LCONS_11 : thm
    val LCONS_NOT_NIL : thm
    val LDROP1_THM : thm
    val LDROP_THM : thm
    val LFILTER_APPEND : thm
    val LFILTER_EQ_NIL : thm
    val LFILTER_NIL : thm
    val LFILTER_THM : thm
    val LFINITE : thm
    val LFINITE_APPEND : thm
    val LFINITE_DROP : thm
    val LFINITE_HAS_LENGTH : thm
    val LFINITE_INDUCTION : thm
    val LFINITE_MAP : thm
    val LFINITE_STRONG_INDUCTION : thm
    val LFINITE_TAKE : thm
    val LFINITE_THM : thm
    val LFINITE_cases : thm
    val LFINITE_fromList : thm
    val LFINITE_ind : thm
    val LFINITE_rules : thm
    val LFINITE_toList : thm
    val LFLATTEN_APPEND : thm
    val LFLATTEN_EQ_NIL : thm
    val LFLATTEN_SINGLETON : thm
    val LFLATTEN_THM : thm
    val LHDTL_CONS_THM : thm
    val LHDTL_EQ_SOME : thm
    val LHD_EQ_NONE : thm
    val LHD_LCONS : thm
    val LHD_THM : thm
    val LLENGTH_APPEND : thm
    val LLENGTH_MAP : thm
    val LLENGTH_THM : thm
    val LLENGTH_fromList : thm
    val LLIST_BISIMULATION : thm
    val LLIST_BISIMULATION0 : thm
    val LLIST_STRONG_BISIMULATION : thm
    val LL_ALL_THM : thm
    val LMAP_APPEND : thm
    val LMAP_MAP : thm
    val LNTH_EQ : thm
    val LNTH_THM : thm
    val LTAKE_CONS_EQ_NONE : thm
    val LTAKE_CONS_EQ_SOME : thm
    val LTAKE_DROP : thm
    val LTAKE_EQ : thm
    val LTAKE_EQ_SOME_CONS : thm
    val LTAKE_LNTH : thm
    val LTAKE_NIL_EQ_NONE : thm
    val LTAKE_NIL_EQ_SOME : thm
    val LTAKE_SNOC_LNTH : thm
    val LTAKE_THM : thm
    val LTAKE_fromList : thm
    val LTL_EQ_NONE : thm
    val LTL_LCONS : thm
    val LTL_THM : thm
    val LZIP_LUNZIP : thm
    val MONO_every : thm
    val MONO_exists : thm
    val NOT_LFINITE_APPEND : thm
    val NOT_LFINITE_DROP : thm
    val NOT_LFINITE_NO_LENGTH : thm
    val NOT_LFINITE_TAKE : thm
    val every_coind : thm
    val every_thm : thm
    val exists_LNTH : thm
    val exists_cases : thm
    val exists_ind : thm
    val exists_rules : thm
    val exists_thm : thm
    val from_toList : thm
    val llength_rel_cases : thm
    val llength_rel_ind : thm
    val llength_rel_rules : thm
    val llist_Axiom : thm
    val llist_Axiom_1 : thm
    val llist_Axiom_1ue : thm
    val llist_CASES : thm
    val llist_rep_LCONS : thm
    val llist_ue_Axiom : thm
    val toList_THM : thm
    val to_fromList : thm
  
  val llist_grammars : type_grammar.grammar * term_grammar.grammar
  
  val llist_rwts : simpLib.ssfrag
(*
   [list] Parent theory of "llist"
   
   [LAPPEND]  Definition
      
      |- (!x. LAPPEND [||] x = x) /\
         !h t x. LAPPEND (h:::t) x = h:::LAPPEND t x
   
   [LCONS]  Definition
      
      |- !h t.
           h:::t =
           llist_abs (\n. if n = 0 then SOME h else llist_rep t (n - 1))
   
   [LDROP]  Definition
      
      |- (!ll. LDROP 0 ll = SOME ll) /\
         !n ll.
           LDROP (SUC n) ll = OPTION_JOIN (OPTION_MAP (LDROP n) (LTL ll))
   
   [LFILTER]  Definition
      
      |- !P ll.
           LFILTER P ll =
           if ~exists P ll then
             [||]
           else
             if P (THE (LHD ll)) then
               THE (LHD ll):::LFILTER P (THE (LTL ll))
             else
               LFILTER P (THE (LTL ll))
   
   [LFLATTEN]  Definition
      
      |- !ll.
           LFLATTEN ll =
           if every ($= [||]) ll then
             [||]
           else
             if THE (LHD ll) = [||] then
               LFLATTEN (THE (LTL ll))
             else
               THE (LHD (THE (LHD ll))):::
                   LFLATTEN (THE (LTL (THE (LHD ll))):::THE (LTL ll))
   
   [LHD]  Definition
      
      |- !ll. LHD ll = llist_rep ll 0
   
   [LLENGTH]  Definition
      
      |- !ll.
           LLENGTH ll =
           if LFINITE ll then SOME (@n. llength_rel ll n) else NONE
   
   [LMAP]  Definition
      
      |- (!f. LMAP f [||] = [||]) /\
         !f h t. LMAP f (h:::t) = f h:::LMAP f t
   
   [LNIL]  Definition
      
      |- [||] = llist_abs (\n. NONE)
   
   [LNTH]  Definition
      
      |- (!ll. LNTH 0 ll = LHD ll) /\
         !n ll.
           LNTH (SUC n) ll = OPTION_JOIN (OPTION_MAP (LNTH n) (LTL ll))
   
   [LTAKE]  Definition
      
      |- (!ll. LTAKE 0 ll = SOME []) /\
         !n ll.
           LTAKE (SUC n) ll =
           case LHD ll of
              NONE -> NONE
           || SOME hd ->
                case LTAKE n (THE (LTL ll)) of
                   NONE -> NONE
                || SOME tl -> SOME (hd::tl)
   
   [LTL]  Definition
      
      |- !ll.
           LTL ll =
           case LHD ll of
              NONE -> NONE
           || SOME v -> SOME (llist_abs (\n. llist_rep ll (n + 1)))
   
   [LUNFOLD]  Definition
      
      |- !f x.
           LUNFOLD f x =
           case f x of NONE -> [||] || SOME (v1,v2) -> v2:::LUNFOLD f v1
   
   [LUNZIP_THM]  Definition
      
      |- (LUNZIP [||] = ([||],[||])) /\
         !x y t.
           LUNZIP ((x,y):::t) =
           (let (ll1,ll2) = LUNZIP t in (x:::ll1,y:::ll2))
   
   [LZIP_THM]  Definition
      
      |- (!l1. LZIP (l1,[||]) = [||]) /\ (!l2. LZIP ([||],l2) = [||]) /\
         !h1 h2 t1 t2. LZIP (h1:::t1,h2:::t2) = (h1,h2):::LZIP (t1,t2)
   
   [every_def]  Definition
      
      |- !P ll. every P ll <=> ~exists ($~ o P) ll
   
   [exists]  Definition
      
      |- exists =
         (\P a0.
            !exists'.
              (!a0.
                 (?h t. (a0 = h:::t) /\ P h) \/
                 (?h t. (a0 = h:::t) /\ exists' t) ==>
                 exists' a0) ==>
              exists' a0)
   
   [fromList]  Definition
      
      |- (fromList [] = [||]) /\ !h t. fromList (h::t) = h:::fromList t
   
   [llength_rel]  Definition
      
      |- llength_rel =
         (\a0 a1.
            !llength_rel'.
              (!a0 a1.
                 (a0 = [||]) /\ (a1 = 0) \/
                 (?h n t.
                    (a0 = h:::t) /\ (a1 = SUC n) /\ llength_rel' t n) ==>
                 llength_rel' a0 a1) ==>
              llength_rel' a0 a1)
   
   [llist_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION lrep_ok rep
   
   [llist_absrep]  Definition
      
      |- (!a. llist_abs (llist_rep a) = a) /\
         !r. lrep_ok r <=> (llist_rep (llist_abs r) = r)
   
   [lrep_ok_def]  Definition
      
      |- !f.
           lrep_ok f <=>
           ?P.
             (!g.
                P g ==>
                (g = (\n. NONE)) \/
                ?h t.
                  P t /\
                  (g = (\n. if n = 0 then SOME h else t (n - 1)))) /\ P f
   
   [toList]  Definition
      
      |- !ll.
           toList ll =
           if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE
   
   [LAPPEND_ASSOC]  Theorem
      
      |- !ll1 ll2 ll3.
           LAPPEND (LAPPEND ll1 ll2) ll3 = LAPPEND ll1 (LAPPEND ll2 ll3)
   
   [LAPPEND_EQ_LNIL]  Theorem
      
      |- (LAPPEND l1 l2 = [||]) <=> (l1 = [||]) /\ (l2 = [||])
   
   [LAPPEND_NIL_2ND]  Theorem
      
      |- !ll. LAPPEND ll [||] = ll
   
   [LCONS_11]  Theorem
      
      |- !h1 t1 h2 t2. (h1:::t1 = h2:::t2) <=> (h1 = h2) /\ (t1 = t2)
   
   [LCONS_NOT_NIL]  Theorem
      
      |- !h t. h:::t <> [||] /\ [||] <> h:::t
   
   [LDROP1_THM]  Theorem
      
      |- LDROP 1 = LTL
   
   [LDROP_THM]  Theorem
      
      |- (!ll. LDROP 0 ll = SOME ll) /\ (!n. LDROP (SUC n) [||] = NONE) /\
         !n h t. LDROP (SUC n) (h:::t) = LDROP n t
   
   [LFILTER_APPEND]  Theorem
      
      |- !P ll1 ll2.
           LFINITE ll1 ==>
           (LFILTER P (LAPPEND ll1 ll2) =
            LAPPEND (LFILTER P ll1) (LFILTER P ll2))
   
   [LFILTER_EQ_NIL]  Theorem
      
      |- !ll. (LFILTER P ll = [||]) <=> every ($~ o P) ll
   
   [LFILTER_NIL]  Theorem
      
      |- !P ll. every ($~ o P) ll ==> (LFILTER P ll = [||])
   
   [LFILTER_THM]  Theorem
      
      |- (!P. LFILTER P [||] = [||]) /\
         !P h t.
           LFILTER P (h:::t) = if P h then h:::LFILTER P t else LFILTER P t
   
   [LFINITE]  Theorem
      
      |- LFINITE ll <=> ?n. LTAKE n ll = NONE
   
   [LFINITE_APPEND]  Theorem
      
      |- !ll1 ll2. LFINITE (LAPPEND ll1 ll2) <=> LFINITE ll1 /\ LFINITE ll2
   
   [LFINITE_DROP]  Theorem
      
      |- !n ll.
           LFINITE ll /\ n <= THE (LLENGTH ll) ==> ?y. LDROP n ll = SOME y
   
   [LFINITE_HAS_LENGTH]  Theorem
      
      |- !ll. LFINITE ll ==> ?n. LLENGTH ll = SOME n
   
   [LFINITE_INDUCTION]  Theorem
      
      |- !P.
           P [||] /\ (!h t. P t ==> P (h:::t)) ==> !a0. LFINITE a0 ==> P a0
   
   [LFINITE_MAP]  Theorem
      
      |- !f ll. LFINITE (LMAP f ll) <=> LFINITE ll
   
   [LFINITE_STRONG_INDUCTION]  Theorem
      
      |- P [||] /\ (!h t. LFINITE t /\ P t ==> P (h:::t)) ==>
         !a0. LFINITE a0 ==> P a0
   
   [LFINITE_TAKE]  Theorem
      
      |- !n ll.
           LFINITE ll /\ n <= THE (LLENGTH ll) ==> ?y. LTAKE n ll = SOME y
   
   [LFINITE_THM]  Theorem
      
      |- (LFINITE [||] <=> T) /\ !h t. LFINITE (h:::t) <=> LFINITE t
   
   [LFINITE_cases]  Theorem
      
      |- !a0. LFINITE a0 <=> (a0 = [||]) \/ ?h t. (a0 = h:::t) /\ LFINITE t
   
   [LFINITE_fromList]  Theorem
      
      |- !l. LFINITE (fromList l)
   
   [LFINITE_ind]  Theorem
      
      |- !LFINITE'.
           LFINITE' [||] /\ (!h t. LFINITE' t ==> LFINITE' (h:::t)) ==>
           !a0. LFINITE a0 ==> LFINITE' a0
   
   [LFINITE_rules]  Theorem
      
      |- LFINITE [||] /\ !h t. LFINITE t ==> LFINITE (h:::t)
   
   [LFINITE_toList]  Theorem
      
      |- !ll. LFINITE ll ==> ?l. toList ll = SOME l
   
   [LFLATTEN_APPEND]  Theorem
      
      |- !h t. LFLATTEN (h:::t) = LAPPEND h (LFLATTEN t)
   
   [LFLATTEN_EQ_NIL]  Theorem
      
      |- !ll. (LFLATTEN ll = [||]) <=> every ($= [||]) ll
   
   [LFLATTEN_SINGLETON]  Theorem
      
      |- !h. LFLATTEN [|h|] = h
   
   [LFLATTEN_THM]  Theorem
      
      |- (LFLATTEN [||] = [||]) /\
         (!tl. LFLATTEN ([||]:::t) = LFLATTEN t) /\
         !h t tl. LFLATTEN ((h:::t):::tl) = h:::LFLATTEN (t:::tl)
   
   [LHDTL_CONS_THM]  Theorem
      
      |- !h t. (LHD (h:::t) = SOME h) /\ (LTL (h:::t) = SOME t)
   
   [LHDTL_EQ_SOME]  Theorem
      
      |- !h t ll. (ll = h:::t) <=> (LHD ll = SOME h) /\ (LTL ll = SOME t)
   
   [LHD_EQ_NONE]  Theorem
      
      |- !ll.
           ((LHD ll = NONE) <=> (ll = [||])) /\
           ((NONE = LHD ll) <=> (ll = [||]))
   
   [LHD_LCONS]  Theorem
      
      |- LHD (h:::t) = SOME h
   
   [LHD_THM]  Theorem
      
      |- (LHD [||] = NONE) /\ !h t. LHD (h:::t) = SOME h
   
   [LLENGTH_APPEND]  Theorem
      
      |- !ll1 ll2.
           LLENGTH (LAPPEND ll1 ll2) =
           if LFINITE ll1 /\ LFINITE ll2 then
             SOME (THE (LLENGTH ll1) + THE (LLENGTH ll2))
           else
             NONE
   
   [LLENGTH_MAP]  Theorem
      
      |- !ll f. LLENGTH (LMAP f ll) = LLENGTH ll
   
   [LLENGTH_THM]  Theorem
      
      |- (LLENGTH [||] = SOME 0) /\
         !h t. LLENGTH (h:::t) = OPTION_MAP SUC (LLENGTH t)
   
   [LLENGTH_fromList]  Theorem
      
      |- !l. LLENGTH (fromList l) = SOME (LENGTH l)
   
   [LLIST_BISIMULATION]  Theorem
      
      |- !ll1 ll2.
           (ll1 = ll2) <=>
           ?R.
             R ll1 ll2 /\
             !ll3 ll4.
               R ll3 ll4 ==>
               (ll3 = [||]) /\ (ll4 = [||]) \/
               (LHD ll3 = LHD ll4) /\ R (THE (LTL ll3)) (THE (LTL ll4))
   
   [LLIST_BISIMULATION0]  Theorem
      
      |- !ll1 ll2.
           (ll1 = ll2) <=>
           ?R.
             R ll1 ll2 /\
             !ll3 ll4.
               R ll3 ll4 ==>
               (ll3 = [||]) /\ (ll4 = [||]) \/
               ?h t1 t2. (ll3 = h:::t1) /\ (ll4 = h:::t2) /\ R t1 t2
   
   [LLIST_STRONG_BISIMULATION]  Theorem
      
      |- !ll1 ll2.
           (ll1 = ll2) <=>
           ?R.
             R ll1 ll2 /\
             !ll3 ll4.
               R ll3 ll4 ==>
               (ll3 = ll4) \/
               ?h t1 t2. (ll3 = h:::t1) /\ (ll4 = h:::t2) /\ R t1 t2
   
   [LL_ALL_THM]  Theorem
      
      |- (every P [||] <=> T) /\ (every P (h:::t) <=> P h /\ every P t)
   
   [LMAP_APPEND]  Theorem
      
      |- !f ll1 ll2.
           LMAP f (LAPPEND ll1 ll2) = LAPPEND (LMAP f ll1) (LMAP f ll2)
   
   [LMAP_MAP]  Theorem
      
      |- !f g ll. LMAP f (LMAP g ll) = LMAP (f o g) ll
   
   [LNTH_EQ]  Theorem
      
      |- !ll1 ll2. (ll1 = ll2) <=> !n. LNTH n ll1 = LNTH n ll2
   
   [LNTH_THM]  Theorem
      
      |- (!n. LNTH n [||] = NONE) /\ (!h t. LNTH 0 (h:::t) = SOME h) /\
         !n h t. LNTH (SUC n) (h:::t) = LNTH n t
   
   [LTAKE_CONS_EQ_NONE]  Theorem
      
      |- !m h t.
           (LTAKE m (h:::t) = NONE) <=>
           ?n. (m = SUC n) /\ (LTAKE n t = NONE)
   
   [LTAKE_CONS_EQ_SOME]  Theorem
      
      |- !m h t l.
           (LTAKE m (h:::t) = SOME l) <=>
           (m = 0) /\ (l = []) \/
           ?n l'. (m = SUC n) /\ (LTAKE n t = SOME l') /\ (l = h::l')
   
   [LTAKE_DROP]  Theorem
      
      |- (!n ll.
            ~LFINITE ll ==>
            (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) =
             ll)) /\
         !n ll.
           LFINITE ll /\ n <= THE (LLENGTH ll) ==>
           (LAPPEND (fromList (THE (LTAKE n ll))) (THE (LDROP n ll)) = ll)
   
   [LTAKE_EQ]  Theorem
      
      |- !ll1 ll2. (ll1 = ll2) <=> !n. LTAKE n ll1 = LTAKE n ll2
   
   [LTAKE_EQ_SOME_CONS]  Theorem
      
      |- !n l x. (LTAKE n l = SOME x) ==> !h. ?y. LTAKE n (h:::l) = SOME y
   
   [LTAKE_LNTH]  Theorem
      
      |- !n ll. (LTAKE n ll = NONE) ==> (LNTH n ll = NONE)
   
   [LTAKE_NIL_EQ_NONE]  Theorem
      
      |- !m. (LTAKE m [||] = NONE) <=> 0 < m
   
   [LTAKE_NIL_EQ_SOME]  Theorem
      
      |- !l m. (LTAKE m [||] = SOME l) <=> (m = 0) /\ (l = [])
   
   [LTAKE_SNOC_LNTH]  Theorem
      
      |- !n ll.
           LTAKE (SUC n) ll =
           case LTAKE n ll of
              NONE -> NONE
           || SOME l ->
                case LNTH n ll of NONE -> NONE || SOME e -> SOME (l ++ [e])
   
   [LTAKE_THM]  Theorem
      
      |- (!l. LTAKE 0 l = SOME []) /\ (!n. LTAKE (SUC n) [||] = NONE) /\
         !n h t. LTAKE (SUC n) (h:::t) = OPTION_MAP (CONS h) (LTAKE n t)
   
   [LTAKE_fromList]  Theorem
      
      |- !l. LTAKE (LENGTH l) (fromList l) = SOME l
   
   [LTL_EQ_NONE]  Theorem
      
      |- !ll.
           ((LTL ll = NONE) <=> (ll = [||])) /\
           ((NONE = LTL ll) <=> (ll = [||]))
   
   [LTL_LCONS]  Theorem
      
      |- LTL (h:::t) = SOME t
   
   [LTL_THM]  Theorem
      
      |- (LTL [||] = NONE) /\ !h t. LTL (h:::t) = SOME t
   
   [LZIP_LUNZIP]  Theorem
      
      |- !ll. LZIP (LUNZIP ll) = ll
   
   [MONO_every]  Theorem
      
      |- (!x. P x ==> Q x) ==> every P l ==> every Q l
   
   [MONO_exists]  Theorem
      
      |- (!x. P x ==> Q x) ==> exists P l ==> exists Q l
   
   [NOT_LFINITE_APPEND]  Theorem
      
      |- !ll1 ll2. ~LFINITE ll1 ==> (LAPPEND ll1 ll2 = ll1)
   
   [NOT_LFINITE_DROP]  Theorem
      
      |- !ll. ~LFINITE ll ==> !n. ?y. LDROP n ll = SOME y
   
   [NOT_LFINITE_NO_LENGTH]  Theorem
      
      |- !ll. ~LFINITE ll ==> (LLENGTH ll = NONE)
   
   [NOT_LFINITE_TAKE]  Theorem
      
      |- !ll. ~LFINITE ll ==> !n. ?y. LTAKE n ll = SOME y
   
   [every_coind]  Theorem
      
      |- !P Q.
           (!h t. Q (h:::t) ==> P h /\ Q t) ==> !ll. Q ll ==> every P ll
   
   [every_thm]  Theorem
      
      |- (every P [||] <=> T) /\ (every P (h:::t) <=> P h /\ every P t)
   
   [exists_LNTH]  Theorem
      
      |- !l. exists P l <=> ?n e. (SOME e = LNTH n l) /\ P e
   
   [exists_cases]  Theorem
      
      |- !P a0.
           exists P a0 <=>
           (?h t. (a0 = h:::t) /\ P h) \/ ?h t. (a0 = h:::t) /\ exists P t
   
   [exists_ind]  Theorem
      
      |- !P exists'.
           (!h t. P h ==> exists' (h:::t)) /\
           (!h t. exists' t ==> exists' (h:::t)) ==>
           !a0. exists P a0 ==> exists' a0
   
   [exists_rules]  Theorem
      
      |- !P.
           (!h t. P h ==> exists P (h:::t)) /\
           !h t. exists P t ==> exists P (h:::t)
   
   [exists_thm]  Theorem
      
      |- (exists P [||] <=> F) /\ (exists P (h:::t) <=> P h \/ exists P t)
   
   [from_toList]  Theorem
      
      |- !l. toList (fromList l) = SOME l
   
   [llength_rel_cases]  Theorem
      
      |- !a0 a1.
           llength_rel a0 a1 <=>
           (a0 = [||]) /\ (a1 = 0) \/
           ?h n t. (a0 = h:::t) /\ (a1 = SUC n) /\ llength_rel t n
   
   [llength_rel_ind]  Theorem
      
      |- !llength_rel'.
           llength_rel' [||] 0 /\
           (!h n t. llength_rel' t n ==> llength_rel' (h:::t) (SUC n)) ==>
           !a0 a1. llength_rel a0 a1 ==> llength_rel' a0 a1
   
   [llength_rel_rules]  Theorem
      
      |- llength_rel [||] 0 /\
         !h n t. llength_rel t n ==> llength_rel (h:::t) (SUC n)
   
   [llist_Axiom]  Theorem
      
      |- !f.
           ?g.
             (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
             !x. LTL (g x) = OPTION_MAP (g o FST) (f x)
   
   [llist_Axiom_1]  Theorem
      
      |- !f.
           ?g. !x. g x = case f x of NONE -> [||] || SOME (a,b) -> b:::g a
   
   [llist_Axiom_1ue]  Theorem
      
      |- !f.
           ?!g. !x. g x = case f x of NONE -> [||] || SOME (a,b) -> b:::g a
   
   [llist_CASES]  Theorem
      
      |- !l. (l = [||]) \/ ?h t. l = h:::t
   
   [llist_rep_LCONS]  Theorem
      
      |- llist_rep (h:::t) =
         (\n. if n = 0 then SOME h else llist_rep t (n - 1))
   
   [llist_ue_Axiom]  Theorem
      
      |- !f.
           ?!g.
             (!x. LHD (g x) = OPTION_MAP SND (f x)) /\
             !x. LTL (g x) = OPTION_MAP (g o FST) (f x)
   
   [toList_THM]  Theorem
      
      |- (toList [||] = SOME []) /\
         !h t. toList (h:::t) = OPTION_MAP (CONS h) (toList t)
   
   [to_fromList]  Theorem
      
      |- !ll. LFINITE ll ==> (fromList (THE (toList ll)) = ll)
   
   
*)
end
