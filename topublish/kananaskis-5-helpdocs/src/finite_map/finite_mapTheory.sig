signature finite_mapTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val DRESTRICT_DEF : thm
    val FAPPLY_DEF : thm
    val FCARD_DEF : thm
    val FDOM_DEF : thm
    val FEMPTY_DEF : thm
    val FEVERY_DEF : thm
    val FLOOKUP_DEF : thm
    val FMAP_MAP2_def : thm
    val FMERGE_DEF : thm
    val FRANGE_DEF : thm
    val FUNION_DEF : thm
    val FUN_FMAP_DEF : thm
    val FUPDATE_DEF : thm
    val FUPDATE_LIST : thm
    val RRESTRICT_DEF : thm
    val SUBMAP_DEF : thm
    val f_o_DEF : thm
    val f_o_f_DEF : thm
    val fmap_ISO_DEF : thm
    val fmap_TY_DEF : thm
    val fmap_domsub : thm
    val is_fmap : thm
    val o_f_DEF : thm
  
  (*  Theorems  *)
    val DOMSUB_FAPPLY : thm
    val DOMSUB_FAPPLY_NEQ : thm
    val DOMSUB_FAPPLY_THM : thm
    val DOMSUB_FEMPTY : thm
    val DOMSUB_FUNION : thm
    val DOMSUB_FUPDATE : thm
    val DOMSUB_FUPDATE_NEQ : thm
    val DOMSUB_FUPDATE_THM : thm
    val DOMSUB_IDEM : thm
    val DOMSUB_NOT_IN_DOM : thm
    val DRESTRICT_DRESTRICT : thm
    val DRESTRICT_EQ_FUNION : thm
    val DRESTRICT_FEMPTY : thm
    val DRESTRICT_FUNION : thm
    val DRESTRICT_FUNION_DRESTRICT_COMPL : thm
    val DRESTRICT_FUPDATE : thm
    val DRESTRICT_IDEMPOT : thm
    val DRESTRICT_IS_FEMPTY : thm
    val DRESTRICT_SUBMAP : thm
    val DRESTRICT_UNIV : thm
    val FAPPLY_FUPDATE : thm
    val FAPPLY_FUPDATE_THM : thm
    val FAPPLY_f_o : thm
    val FCARD_0_FEMPTY : thm
    val FCARD_FEMPTY : thm
    val FCARD_FUPDATE : thm
    val FCARD_SUC : thm
    val FDOM_DOMSUB : thm
    val FDOM_DRESTRICT : thm
    val FDOM_EQ_EMPTY : thm
    val FDOM_EQ_FDOM_FUPDATE : thm
    val FDOM_FEMPTY : thm
    val FDOM_FINITE : thm
    val FDOM_FUNION : thm
    val FDOM_FUPDATE : thm
    val FDOM_FUPDATE_LIST : thm
    val FDOM_F_FEMPTY1 : thm
    val FDOM_f_o : thm
    val FDOM_o_f : thm
    val FEMPTY_SUBMAP : thm
    val FEVERY_DRESTRICT_COMPL : thm
    val FEVERY_FEMPTY : thm
    val FEVERY_FUPDATE : thm
    val FEVERY_STRENGTHEN_THM : thm
    val FEVERY_o_f : thm
    val FINITE_FRANGE : thm
    val FINITE_PRED_11 : thm
    val FLOOKUP_EMPTY : thm
    val FLOOKUP_UPDATE : thm
    val FMAP_MAP2_FEMPTY : thm
    val FMAP_MAP2_FUPDATE : thm
    val FMAP_MAP2_THM : thm
    val FMEQ_ENUMERATE_CASES : thm
    val FMEQ_SINGLE_SIMPLE_DISJ_ELIM : thm
    val FMEQ_SINGLE_SIMPLE_ELIM : thm
    val FMERGE_ASSOC : thm
    val FMERGE_COMM : thm
    val FMERGE_DRESTRICT : thm
    val FMERGE_EQ_FEMPTY : thm
    val FMERGE_FEMPTY : thm
    val FMERGE_FUNION : thm
    val FMERGE_NO_CHANGE : thm
    val FM_PULL_APART : thm
    val FRANGE_FEMPTY : thm
    val FRANGE_FMAP : thm
    val FRANGE_FUPDATE : thm
    val FRANGE_FUPDATE_DOMSUB : thm
    val FUNION_ASSOC : thm
    val FUNION_COMM : thm
    val FUNION_EQ : thm
    val FUNION_EQ_FEMPTY : thm
    val FUNION_EQ_IMPL : thm
    val FUNION_FEMPTY_1 : thm
    val FUNION_FEMPTY_2 : thm
    val FUNION_FMERGE : thm
    val FUNION_FUPDATE_1 : thm
    val FUNION_FUPDATE_2 : thm
    val FUN_FMAP_EMPTY : thm
    val FUPD11_SAME_BASE : thm
    val FUPD11_SAME_KEY_AND_BASE : thm
    val FUPD11_SAME_NEW_KEY : thm
    val FUPD11_SAME_UPDATE : thm
    val FUPDATE_COMMUTES : thm
    val FUPDATE_DRESTRICT : thm
    val FUPDATE_ELIM : thm
    val FUPDATE_EQ : thm
    val FUPDATE_LIST_APPLY_NOT_MEM : thm
    val FUPDATE_LIST_SAME_KEYS_UNWIND : thm
    val FUPDATE_LIST_SAME_UPDATE : thm
    val FUPDATE_LIST_THM : thm
    val FUPDATE_PURGE : thm
    val FUPD_SAME_KEY_UNWIND : thm
    val IN_FDOM_FOLDR_UNION : thm
    val NOT_EQ_FAPPLY : thm
    val NOT_EQ_FEMPTY_FUPDATE : thm
    val NOT_FDOM_DRESTRICT : thm
    val NOT_FDOM_FAPPLY_FEMPTY : thm
    val RRESTRICT_FEMPTY : thm
    val RRESTRICT_FUPDATE : thm
    val SAME_KEY_UPDATES_DIFFER : thm
    val STRONG_DRESTRICT_FUPDATE : thm
    val STRONG_DRESTRICT_FUPDATE_THM : thm
    val SUBMAP_ANTISYM : thm
    val SUBMAP_FEMPTY : thm
    val SUBMAP_FRANGE : thm
    val SUBMAP_FUNION : thm
    val SUBMAP_FUNION_EQ : thm
    val SUBMAP_FUNION_ID : thm
    val SUBMAP_FUPDATE : thm
    val SUBMAP_REFL : thm
    val SUBMAP_TRANS : thm
    val f_o_f_FEMPTY_1 : thm
    val f_o_f_FEMPTY_2 : thm
    val fmap_CASES : thm
    val fmap_EQ : thm
    val fmap_EQ_THM : thm
    val fmap_EXT : thm
    val fmap_INDUCT : thm
    val fmap_SIMPLE_INDUCT : thm
    val is_fmap_cases : thm
    val is_fmap_ind : thm
    val is_fmap_rules : thm
    val o_f_DOMSUB : thm
    val o_f_FAPPLY : thm
    val o_f_FDOM : thm
    val o_f_FEMPTY : thm
    val o_f_FUPDATE : thm
    val o_f_o_f : thm
  
  val finite_map_grammars : type_grammar.grammar * term_grammar.grammar
  
  val finite_map_rwts : simpLib.ssfrag
(*
   [list] Parent theory of "finite_map"
   
   [DRESTRICT_DEF]  Definition
      
      |- !f r.
           (FDOM (DRESTRICT f r) = FDOM f INTER r) /\
           !x.
             DRESTRICT f r ' x =
             if x IN FDOM f INTER r then f ' x else FEMPTY ' x
   
   [FAPPLY_DEF]  Definition
      
      |- !f x. f ' x = OUTL (fmap_REP f x)
   
   [FCARD_DEF]  Definition
      
      |- !fm. FCARD fm = CARD (FDOM fm)
   
   [FDOM_DEF]  Definition
      
      |- !f x. FDOM f x <=> ISL (fmap_REP f x)
   
   [FEMPTY_DEF]  Definition
      
      |- FEMPTY = fmap_ABS (\a. INR ())
   
   [FEVERY_DEF]  Definition
      
      |- !P f. FEVERY P f <=> !x. x IN FDOM f ==> P (x,f ' x)
   
   [FLOOKUP_DEF]  Definition
      
      |- !f x. FLOOKUP f x = if x IN FDOM f then SOME (f ' x) else NONE
   
   [FMAP_MAP2_def]  Definition
      
      |- !f m. FMAP_MAP2 f m = FUN_FMAP (\x. f (x,m ' x)) (FDOM m)
   
   [FMERGE_DEF]  Definition
      
      |- !m f g.
           (FDOM (FMERGE m f g) = FDOM f UNION FDOM g) /\
           !x.
             FMERGE m f g ' x =
             if x NOTIN FDOM f then
               g ' x
             else
               if x NOTIN FDOM g then f ' x else m (f ' x) (g ' x)
   
   [FRANGE_DEF]  Definition
      
      |- !f. FRANGE f = {y | ?x. x IN FDOM f /\ (f ' x = y)}
   
   [FUNION_DEF]  Definition
      
      |- !f g.
           (FDOM (FUNION f g) = FDOM f UNION FDOM g) /\
           !x. FUNION f g ' x = if x IN FDOM f then f ' x else g ' x
   
   [FUN_FMAP_DEF]  Definition
      
      |- !f P.
           FINITE P ==>
           (FDOM (FUN_FMAP f P) = P) /\
           !x. x IN P ==> (FUN_FMAP f P ' x = f x)
   
   [FUPDATE_DEF]  Definition
      
      |- !f x y.
           f |+ (x,y) =
           fmap_ABS (\a. if a = x then INL y else fmap_REP f a)
   
   [FUPDATE_LIST]  Definition
      
      |- $|++ = FOLDL $|+
   
   [RRESTRICT_DEF]  Definition
      
      |- !f r.
           (FDOM (RRESTRICT f r) = {x | x IN FDOM f /\ f ' x IN r}) /\
           !x.
             RRESTRICT f r ' x =
             if x IN FDOM f /\ f ' x IN r then f ' x else FEMPTY ' x
   
   [SUBMAP_DEF]  Definition
      
      |- !f g.
           f SUBMAP g <=>
           !x. x IN FDOM f ==> x IN FDOM g /\ (f ' x = g ' x)
   
   [f_o_DEF]  Definition
      
      |- !f g. f f_o g = f f_o_f FUN_FMAP g {x | g x IN FDOM f}
   
   [f_o_f_DEF]  Definition
      
      |- !f g.
           (FDOM (f f_o_f g) = FDOM g INTER {x | g ' x IN FDOM f}) /\
           !x. x IN FDOM (f f_o_f g) ==> ((f f_o_f g) ' x = f ' (g ' x))
   
   [fmap_ISO_DEF]  Definition
      
      |- (!a. fmap_ABS (fmap_REP a) = a) /\
         !r. is_fmap r <=> (fmap_REP (fmap_ABS r) = r)
   
   [fmap_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION is_fmap rep
   
   [fmap_domsub]  Definition
      
      |- !fm k. fm \\ k = DRESTRICT fm (COMPL {k})
   
   [is_fmap]  Definition
      
      |- is_fmap =
         (\a0.
            !is_fmap'.
              (!a0.
                 (a0 = (\a. INR ())) \/
                 (?f a b.
                    (a0 = (\x. if x = a then INL b else f x)) /\
                    is_fmap' f) ==>
                 is_fmap' a0) ==>
              is_fmap' a0)
   
   [o_f_DEF]  Definition
      
      |- !f g.
           (FDOM (f o_f g) = FDOM g) /\
           !x. x IN FDOM (f o_f g) ==> ((f o_f g) ' x = f (g ' x))
   
   [DOMSUB_FAPPLY]  Theorem
      
      |- !fm k. (fm \\ k) ' k = FEMPTY ' k
   
   [DOMSUB_FAPPLY_NEQ]  Theorem
      
      |- !fm k1 k2. k1 <> k2 ==> ((fm \\ k1) ' k2 = fm ' k2)
   
   [DOMSUB_FAPPLY_THM]  Theorem
      
      |- !fm k1 k2.
           (fm \\ k1) ' k2 = if k1 = k2 then FEMPTY ' k2 else fm ' k2
   
   [DOMSUB_FEMPTY]  Theorem
      
      |- !k. FEMPTY \\ k = FEMPTY
   
   [DOMSUB_FUNION]  Theorem
      
      |- FUNION f g \\ k = FUNION (f \\ k) (g \\ k)
   
   [DOMSUB_FUPDATE]  Theorem
      
      |- !fm k v. fm |+ (k,v) \\ k = fm \\ k
   
   [DOMSUB_FUPDATE_NEQ]  Theorem
      
      |- !fm k1 k2 v.
           k1 <> k2 ==> (fm |+ (k1,v) \\ k2 = fm \\ k2 |+ (k1,v))
   
   [DOMSUB_FUPDATE_THM]  Theorem
      
      |- !fm k1 k2 v.
           fm |+ (k1,v) \\ k2 =
           if k1 = k2 then fm \\ k2 else fm \\ k2 |+ (k1,v)
   
   [DOMSUB_IDEM]  Theorem
      
      |- fm \\ k \\ k = fm \\ k
   
   [DOMSUB_NOT_IN_DOM]  Theorem
      
      |- k NOTIN FDOM fm ==> (fm \\ k = fm)
   
   [DRESTRICT_DRESTRICT]  Theorem
      
      |- !f P Q. DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (P INTER Q)
   
   [DRESTRICT_EQ_FUNION]  Theorem
      
      |- !h h1 h2.
           DISJOINT (FDOM h1) (FDOM h2) /\ (FUNION h1 h2 = h) ==>
           (h2 = DRESTRICT h (COMPL (FDOM h1)))
   
   [DRESTRICT_FEMPTY]  Theorem
      
      |- !r. DRESTRICT FEMPTY r = FEMPTY
   
   [DRESTRICT_FUNION]  Theorem
      
      |- !h s1 s2.
           FUNION (DRESTRICT h s1) (DRESTRICT h s2) =
           DRESTRICT h (s1 UNION s2)
   
   [DRESTRICT_FUNION_DRESTRICT_COMPL]  Theorem
      
      |- FUNION (DRESTRICT f s) (DRESTRICT f (COMPL s)) = f
   
   [DRESTRICT_FUPDATE]  Theorem
      
      |- !f r x y.
           DRESTRICT (f |+ (x,y)) r =
           if x IN r then DRESTRICT f r |+ (x,y) else DRESTRICT f r
   
   [DRESTRICT_IDEMPOT]  Theorem
      
      |- !s vs. DRESTRICT (DRESTRICT s vs) vs = DRESTRICT s vs
   
   [DRESTRICT_IS_FEMPTY]  Theorem
      
      |- !f. DRESTRICT f {} = FEMPTY
   
   [DRESTRICT_SUBMAP]  Theorem
      
      |- !f r. DRESTRICT f r SUBMAP f
   
   [DRESTRICT_UNIV]  Theorem
      
      |- !f. DRESTRICT f UNIV = f
   
   [FAPPLY_FUPDATE]  Theorem
      
      |- !f x y. (f |+ (x,y)) ' x = y
   
   [FAPPLY_FUPDATE_THM]  Theorem
      
      |- !f a b x. (f |+ (a,b)) ' x = if x = a then b else f ' x
   
   [FAPPLY_f_o]  Theorem
      
      |- !f g.
           FINITE {x | g x IN FDOM f} ==>
           !x. x IN FDOM (f f_o g) ==> ((f f_o g) ' x = f ' (g x))
   
   [FCARD_0_FEMPTY]  Theorem
      
      |- !f. (FCARD f = 0) <=> (f = FEMPTY)
   
   [FCARD_FEMPTY]  Theorem
      
      |- FCARD FEMPTY = 0
   
   [FCARD_FUPDATE]  Theorem
      
      |- !fm a b.
           FCARD (fm |+ (a,b)) =
           if a IN FDOM fm then FCARD fm else 1 + FCARD fm
   
   [FCARD_SUC]  Theorem
      
      |- !f n.
           (FCARD f = SUC n) <=>
           ?f' x y. x NOTIN FDOM f' /\ (FCARD f' = n) /\ (f = f' |+ (x,y))
   
   [FDOM_DOMSUB]  Theorem
      
      |- !fm k. FDOM (fm \\ k) = FDOM fm DELETE k
   
   [FDOM_DRESTRICT]  Theorem
      
      |- !f r x. FDOM (DRESTRICT f r) = FDOM f INTER r
   
   [FDOM_EQ_EMPTY]  Theorem
      
      |- !f. (FDOM f = {}) <=> (f = FEMPTY)
   
   [FDOM_EQ_FDOM_FUPDATE]  Theorem
      
      |- !f x. x IN FDOM f ==> !y. FDOM (f |+ (x,y)) = FDOM f
   
   [FDOM_FEMPTY]  Theorem
      
      |- FDOM FEMPTY = {}
   
   [FDOM_FINITE]  Theorem
      
      |- !fm. FINITE (FDOM fm)
   
   [FDOM_FUNION]  Theorem
      
      |- !f g x. FDOM (FUNION f g) = FDOM f UNION FDOM g
   
   [FDOM_FUPDATE]  Theorem
      
      |- !f a b. FDOM (f |+ (a,b)) = a INSERT FDOM f
   
   [FDOM_FUPDATE_LIST]  Theorem
      
      |- !kvl fm. FDOM (fm |++ kvl) = FDOM fm UNION LMEM (MAP FST kvl)
   
   [FDOM_F_FEMPTY1]  Theorem
      
      |- !f. (!a. a NOTIN FDOM f) <=> (f = FEMPTY)
   
   [FDOM_f_o]  Theorem
      
      |- !f g.
           FINITE {x | g x IN FDOM f} ==>
           (FDOM (f f_o g) = {x | g x IN FDOM f})
   
   [FDOM_o_f]  Theorem
      
      |- !f g. FDOM (f o_f g) = FDOM g
   
   [FEMPTY_SUBMAP]  Theorem
      
      |- !h. h SUBMAP FEMPTY <=> (h = FEMPTY)
   
   [FEVERY_DRESTRICT_COMPL]  Theorem
      
      |- FEVERY P (DRESTRICT (f |+ (k,v)) (COMPL s)) <=>
         (k NOTIN s ==> P (k,v)) /\
         FEVERY P (DRESTRICT f (COMPL (k INSERT s)))
   
   [FEVERY_FEMPTY]  Theorem
      
      |- !P. FEVERY P FEMPTY
   
   [FEVERY_FUPDATE]  Theorem
      
      |- !P f x y.
           FEVERY P (f |+ (x,y)) <=>
           P (x,y) /\ FEVERY P (DRESTRICT f (COMPL {x}))
   
   [FEVERY_STRENGTHEN_THM]  Theorem
      
      |- FEVERY P FEMPTY /\
         (FEVERY P f /\ P (x,y) ==> FEVERY P (f |+ (x,y)))
   
   [FEVERY_o_f]  Theorem
      
      |- !m P f. FEVERY P (f o_f m) <=> FEVERY (\x. P (FST x,f (SND x))) m
   
   [FINITE_FRANGE]  Theorem
      
      |- !fm. FINITE (FRANGE fm)
   
   [FINITE_PRED_11]  Theorem
      
      |- !g.
           (!x y. (g x = g y) <=> (x = y)) ==>
           !f. FINITE {x | g x IN FDOM f}
   
   [FLOOKUP_EMPTY]  Theorem
      
      |- FLOOKUP FEMPTY k = NONE
   
   [FLOOKUP_UPDATE]  Theorem
      
      |- FLOOKUP (fm |+ (k1,v)) k2 =
         if k1 = k2 then SOME v else FLOOKUP fm k2
   
   [FMAP_MAP2_FEMPTY]  Theorem
      
      |- FMAP_MAP2 f FEMPTY = FEMPTY
   
   [FMAP_MAP2_FUPDATE]  Theorem
      
      |- FMAP_MAP2 f (m |+ (x,v)) = FMAP_MAP2 f m |+ (x,f (x,v))
   
   [FMAP_MAP2_THM]  Theorem
      
      |- (FDOM (FMAP_MAP2 f m) = FDOM m) /\
         !x. x IN FDOM m ==> (FMAP_MAP2 f m ' x = f (x,m ' x))
   
   [FMEQ_ENUMERATE_CASES]  Theorem
      
      |- !f1 kvl p. (f1 |+ p = FEMPTY |++ kvl) ==> MEM p kvl
   
   [FMEQ_SINGLE_SIMPLE_DISJ_ELIM]  Theorem
      
      |- !fm k v ck cv.
           (fm |+ (k,v) = FEMPTY |+ (ck,cv)) <=>
           (k = ck) /\ (v = cv) /\
           ((fm = FEMPTY) \/ ?v'. fm = FEMPTY |+ (k,v'))
   
   [FMEQ_SINGLE_SIMPLE_ELIM]  Theorem
      
      |- !P k v ck cv nv.
           (?fm. (fm |+ (k,v) = FEMPTY |+ (ck,cv)) /\ P (fm |+ (k,nv))) <=>
           (k = ck) /\ (v = cv) /\ P (FEMPTY |+ (ck,nv))
   
   [FMERGE_ASSOC]  Theorem
      
      |- ASSOC (FMERGE m) <=> ASSOC m
   
   [FMERGE_COMM]  Theorem
      
      |- COMM (FMERGE m) <=> COMM m
   
   [FMERGE_DRESTRICT]  Theorem
      
      |- DRESTRICT (FMERGE f st1 st2) vs =
         FMERGE f (DRESTRICT st1 vs) (DRESTRICT st2 vs)
   
   [FMERGE_EQ_FEMPTY]  Theorem
      
      |- (FMERGE m f g = FEMPTY) <=> (f = FEMPTY) /\ (g = FEMPTY)
   
   [FMERGE_FEMPTY]  Theorem
      
      |- (FMERGE m f FEMPTY = f) /\ (FMERGE m FEMPTY f = f)
   
   [FMERGE_FUNION]  Theorem
      
      |- FUNION = FMERGE (\x y. x)
   
   [FMERGE_NO_CHANGE]  Theorem
      
      |- ((FMERGE m f1 f2 = f1) <=>
          !x.
            x IN FDOM f2 ==>
            x IN FDOM f1 /\ (m (f1 ' x) (f2 ' x) = f1 ' x)) /\
         ((FMERGE m f1 f2 = f2) <=>
          !x.
            x IN FDOM f1 ==>
            x IN FDOM f2 /\ (m (f1 ' x) (f2 ' x) = f2 ' x))
   
   [FM_PULL_APART]  Theorem
      
      |- !fm k.
           k IN FDOM fm ==> ?fm0 v. (fm = fm0 |+ (k,v)) /\ k NOTIN FDOM fm0
   
   [FRANGE_FEMPTY]  Theorem
      
      |- FRANGE FEMPTY = {}
   
   [FRANGE_FMAP]  Theorem
      
      |- FINITE P ==> (FRANGE (FUN_FMAP f P) = IMAGE f P)
   
   [FRANGE_FUPDATE]  Theorem
      
      |- !f x y.
           FRANGE (f |+ (x,y)) = y INSERT FRANGE (DRESTRICT f (COMPL {x}))
   
   [FRANGE_FUPDATE_DOMSUB]  Theorem
      
      |- !fm k v. FRANGE (fm |+ (k,v)) = v INSERT FRANGE (fm \\ k)
   
   [FUNION_ASSOC]  Theorem
      
      |- !f g h. FUNION f (FUNION g h) = FUNION (FUNION f g) h
   
   [FUNION_COMM]  Theorem
      
      |- !f g. DISJOINT (FDOM f) (FDOM g) ==> (FUNION f g = FUNION g f)
   
   [FUNION_EQ]  Theorem
      
      |- !f1 f2 f3.
           DISJOINT (FDOM f1) (FDOM f2) /\ DISJOINT (FDOM f1) (FDOM f3) ==>
           ((FUNION f1 f2 = FUNION f1 f3) <=> (f2 = f3))
   
   [FUNION_EQ_FEMPTY]  Theorem
      
      |- !h1 h2. (FUNION h1 h2 = FEMPTY) <=> (h1 = FEMPTY) /\ (h2 = FEMPTY)
   
   [FUNION_EQ_IMPL]  Theorem
      
      |- !f1 f2 f3.
           DISJOINT (FDOM f1) (FDOM f2) /\ DISJOINT (FDOM f1) (FDOM f3) /\
           (f2 = f3) ==>
           (FUNION f1 f2 = FUNION f1 f3)
   
   [FUNION_FEMPTY_1]  Theorem
      
      |- !g. FUNION FEMPTY g = g
   
   [FUNION_FEMPTY_2]  Theorem
      
      |- !f. FUNION f FEMPTY = f
   
   [FUNION_FMERGE]  Theorem
      
      |- !f1 f2 m.
           DISJOINT (FDOM f1) (FDOM f2) ==> (FMERGE m f1 f2 = FUNION f1 f2)
   
   [FUNION_FUPDATE_1]  Theorem
      
      |- !f g x y. FUNION (f |+ (x,y)) g = FUNION f g |+ (x,y)
   
   [FUNION_FUPDATE_2]  Theorem
      
      |- !f g x y.
           FUNION f (g |+ (x,y)) =
           if x IN FDOM f then FUNION f g else FUNION f g |+ (x,y)
   
   [FUN_FMAP_EMPTY]  Theorem
      
      |- FUN_FMAP f {} = FEMPTY
   
   [FUPD11_SAME_BASE]  Theorem
      
      |- !f k1 v1 k2 v2.
           (f |+ (k1,v1) = f |+ (k2,v2)) <=>
           (k1 = k2) /\ (v1 = v2) \/
           k1 <> k2 /\ k1 IN FDOM f /\ k2 IN FDOM f /\
           (f |+ (k1,v1) = f) /\ (f |+ (k2,v2) = f)
   
   [FUPD11_SAME_KEY_AND_BASE]  Theorem
      
      |- !f k v1 v2. (f |+ (k,v1) = f |+ (k,v2)) <=> (v1 = v2)
   
   [FUPD11_SAME_NEW_KEY]  Theorem
      
      |- !f1 f2 k v1 v2.
           k NOTIN FDOM f1 /\ k NOTIN FDOM f2 ==>
           ((f1 |+ (k,v1) = f2 |+ (k,v2)) <=> (f1 = f2) /\ (v1 = v2))
   
   [FUPD11_SAME_UPDATE]  Theorem
      
      |- !f1 f2 k v.
           (f1 |+ (k,v) = f2 |+ (k,v)) <=>
           (DRESTRICT f1 (COMPL {k}) = DRESTRICT f2 (COMPL {k}))
   
   [FUPDATE_COMMUTES]  Theorem
      
      |- !f a b c d. a <> c ==> (f |+ (a,b) |+ (c,d) = f |+ (c,d) |+ (a,b))
   
   [FUPDATE_DRESTRICT]  Theorem
      
      |- !f x y. f |+ (x,y) = DRESTRICT f (COMPL {x}) |+ (x,y)
   
   [FUPDATE_ELIM]  Theorem
      
      |- !k v f. k IN FDOM f /\ (f ' k = v) ==> (f |+ (k,v) = f)
   
   [FUPDATE_EQ]  Theorem
      
      |- !f a b c. f |+ (a,b) |+ (a,c) = f |+ (a,c)
   
   [FUPDATE_LIST_APPLY_NOT_MEM]  Theorem
      
      |- !kvl f k. ~MEM k (MAP FST kvl) ==> ((f |++ kvl) ' k = f ' k)
   
   [FUPDATE_LIST_SAME_KEYS_UNWIND]  Theorem
      
      |- !f1 f2 kvl1 kvl2.
           (f1 |++ kvl1 = f2 |++ kvl2) /\ (MAP FST kvl1 = MAP FST kvl2) /\
           ALL_DISTINCT (MAP FST kvl1) ==>
           (kvl1 = kvl2) /\
           !kvl. (MAP FST kvl = MAP FST kvl1) ==> (f1 |++ kvl = f2 |++ kvl)
   
   [FUPDATE_LIST_SAME_UPDATE]  Theorem
      
      |- !kvl f1 f2.
           (f1 |++ kvl = f2 |++ kvl) <=>
           (DRESTRICT f1 (COMPL (LMEM (MAP FST kvl))) =
            DRESTRICT f2 (COMPL (LMEM (MAP FST kvl))))
   
   [FUPDATE_LIST_THM]  Theorem
      
      |- !f. (f |++ [] = f) /\ !h t. f |++ (h::t) = f |+ h |++ t
   
   [FUPDATE_PURGE]  Theorem
      
      |- !f x y. f |+ (x,y) = f \\ x |+ (x,y)
   
   [FUPD_SAME_KEY_UNWIND]  Theorem
      
      |- !f1 f2 k v1 v2.
           (f1 |+ (k,v1) = f2 |+ (k,v2)) ==>
           (v1 = v2) /\ !v. f1 |+ (k,v) = f2 |+ (k,v)
   
   [IN_FDOM_FOLDR_UNION]  Theorem
      
      |- !x hL.
           x IN FDOM (FOLDR FUNION FEMPTY hL) <=>
           ?h. MEM h hL /\ x IN FDOM h
   
   [NOT_EQ_FAPPLY]  Theorem
      
      |- !f a x y. a <> x ==> ((f |+ (x,y)) ' a = f ' a)
   
   [NOT_EQ_FEMPTY_FUPDATE]  Theorem
      
      |- !f a b. FEMPTY <> f |+ (a,b)
   
   [NOT_FDOM_DRESTRICT]  Theorem
      
      |- !f x. x NOTIN FDOM f ==> (DRESTRICT f (COMPL {x}) = f)
   
   [NOT_FDOM_FAPPLY_FEMPTY]  Theorem
      
      |- !f x. x NOTIN FDOM f ==> (f ' x = FEMPTY ' x)
   
   [RRESTRICT_FEMPTY]  Theorem
      
      |- !r. RRESTRICT FEMPTY r = FEMPTY
   
   [RRESTRICT_FUPDATE]  Theorem
      
      |- !f r x y.
           RRESTRICT (f |+ (x,y)) r =
           if y IN r then
             RRESTRICT f r |+ (x,y)
           else
             RRESTRICT (DRESTRICT f (COMPL {x})) r
   
   [SAME_KEY_UPDATES_DIFFER]  Theorem
      
      |- !f1 f2 k v1 v2. v1 <> v2 ==> f1 |+ (k,v1) <> f2 |+ (k,v2)
   
   [STRONG_DRESTRICT_FUPDATE]  Theorem
      
      |- !f r x y.
           x IN r ==>
           (DRESTRICT (f |+ (x,y)) r = DRESTRICT f (r DELETE x) |+ (x,y))
   
   [STRONG_DRESTRICT_FUPDATE_THM]  Theorem
      
      |- !f r x y.
           DRESTRICT (f |+ (x,y)) r =
           if x IN r then
             DRESTRICT f (COMPL {x} INTER r) |+ (x,y)
           else
             DRESTRICT f (COMPL {x} INTER r)
   
   [SUBMAP_ANTISYM]  Theorem
      
      |- !f g. f SUBMAP g /\ g SUBMAP f <=> (f = g)
   
   [SUBMAP_FEMPTY]  Theorem
      
      |- !f. FEMPTY SUBMAP f
   
   [SUBMAP_FRANGE]  Theorem
      
      |- !f g. f SUBMAP g ==> FRANGE f SUBSET FRANGE g
   
   [SUBMAP_FUNION]  Theorem
      
      |- !f1 f2 f3.
           f1 SUBMAP f2 \/ DISJOINT (FDOM f1) (FDOM f2) /\ f1 SUBMAP f3 ==>
           f1 SUBMAP FUNION f2 f3
   
   [SUBMAP_FUNION_EQ]  Theorem
      
      |- (!f1 f2 f3.
            DISJOINT (FDOM f1) (FDOM f2) ==>
            (f1 SUBMAP FUNION f2 f3 <=> f1 SUBMAP f3)) /\
         !f1 f2 f3.
           DISJOINT (FDOM f1) (FDOM f3 DIFF FDOM f2) ==>
           (f1 SUBMAP FUNION f2 f3 <=> f1 SUBMAP f2)
   
   [SUBMAP_FUNION_ID]  Theorem
      
      |- (!f1 f2. f1 SUBMAP FUNION f1 f2) /\
         !f1 f2. DISJOINT (FDOM f1) (FDOM f2) ==> f2 SUBMAP FUNION f1 f2
   
   [SUBMAP_FUPDATE]  Theorem
      
      |- !f g x y.
           f |+ (x,y) SUBMAP g <=>
           x IN FDOM g /\ (g ' x = y) /\ f \\ x SUBMAP g \\ x
   
   [SUBMAP_REFL]  Theorem
      
      |- !f. f SUBMAP f
   
   [SUBMAP_TRANS]  Theorem
      
      |- !f g h. f SUBMAP g /\ g SUBMAP h ==> f SUBMAP h
   
   [f_o_f_FEMPTY_1]  Theorem
      
      |- !f. FEMPTY f_o_f f = FEMPTY
   
   [f_o_f_FEMPTY_2]  Theorem
      
      |- !f. f f_o_f FEMPTY = FEMPTY
   
   [fmap_CASES]  Theorem
      
      |- !f. (f = FEMPTY) \/ ?g x y. f = g |+ (x,y)
   
   [fmap_EQ]  Theorem
      
      |- !f g. (FDOM f = FDOM g) /\ ($' f = $' g) <=> (f = g)
   
   [fmap_EQ_THM]  Theorem
      
      |- !f g.
           (FDOM f = FDOM g) /\ (!x. x IN FDOM f ==> (f ' x = g ' x)) <=>
           (f = g)
   
   [fmap_EXT]  Theorem
      
      |- !f g.
           (f = g) <=>
           (FDOM f = FDOM g) /\ !x. x IN FDOM f ==> (f ' x = g ' x)
   
   [fmap_INDUCT]  Theorem
      
      |- !P.
           P FEMPTY /\
           (!f. P f ==> !x y. x NOTIN FDOM f ==> P (f |+ (x,y))) ==>
           !f. P f
   
   [fmap_SIMPLE_INDUCT]  Theorem
      
      |- !P. P FEMPTY /\ (!f. P f ==> !x y. P (f |+ (x,y))) ==> !f. P f
   
   [is_fmap_cases]  Theorem
      
      |- !a0.
           is_fmap a0 <=>
           (a0 = (\a. INR ())) \/
           ?f a b. (a0 = (\x. if x = a then INL b else f x)) /\ is_fmap f
   
   [is_fmap_ind]  Theorem
      
      |- !is_fmap'.
           is_fmap' (\a. INR ()) /\
           (!f a b.
              is_fmap' f ==>
              is_fmap' (\x. if x = a then INL b else f x)) ==>
           !a0. is_fmap a0 ==> is_fmap' a0
   
   [is_fmap_rules]  Theorem
      
      |- is_fmap (\a. INR ()) /\
         !f a b. is_fmap f ==> is_fmap (\x. if x = a then INL b else f x)
   
   [o_f_DOMSUB]  Theorem
      
      |- (g o_f fm) \\ k = g o_f fm \\ k
   
   [o_f_FAPPLY]  Theorem
      
      |- !f g x. x IN FDOM g ==> ((f o_f g) ' x = f (g ' x))
   
   [o_f_FDOM]  Theorem
      
      |- !f g. FDOM g = FDOM (f o_f g)
   
   [o_f_FEMPTY]  Theorem
      
      |- f o_f FEMPTY = FEMPTY
   
   [o_f_FUPDATE]  Theorem
      
      |- f o_f fm |+ (k,v) = (f o_f fm \\ k) |+ (k,f v)
   
   [o_f_o_f]  Theorem
      
      |- f o_f (g o_f h) = f o g o_f h
   
   
*)
end
