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
    val MAP_KEYS_def : thm
    val RRESTRICT_DEF : thm
    val SUBMAP_DEF : thm
    val f_o_DEF : thm
    val f_o_f_DEF : thm
    val fmap_EQ_UPTO_def : thm
    val fmap_ISO_DEF : thm
    val fmap_TY_DEF : thm
    val fmap_domsub : thm
    val fmap_rel_def : thm
    val fmap_size_def : thm
    val is_fmap_def : thm
    val o_f_DEF : thm

  (*  Theorems  *)
    val DOMSUB_COMMUTES : thm
    val DOMSUB_FAPPLY : thm
    val DOMSUB_FAPPLY_NEQ : thm
    val DOMSUB_FAPPLY_THM : thm
    val DOMSUB_FEMPTY : thm
    val DOMSUB_FLOOKUP : thm
    val DOMSUB_FLOOKUP_NEQ : thm
    val DOMSUB_FLOOKUP_THM : thm
    val DOMSUB_FUNION : thm
    val DOMSUB_FUPDATE : thm
    val DOMSUB_FUPDATE_NEQ : thm
    val DOMSUB_FUPDATE_THM : thm
    val DOMSUB_IDEM : thm
    val DOMSUB_NOT_IN_DOM : thm
    val DRESTRICT_DRESTRICT : thm
    val DRESTRICT_EQ_DRESTRICT : thm
    val DRESTRICT_EQ_FUNION : thm
    val DRESTRICT_FEMPTY : thm
    val DRESTRICT_FUNION : thm
    val DRESTRICT_FUNION_DRESTRICT_COMPL : thm
    val DRESTRICT_FUPDATE : thm
    val DRESTRICT_IDEMPOT : thm
    val DRESTRICT_IS_FEMPTY : thm
    val DRESTRICT_SUBMAP : thm
    val DRESTRICT_UNIV : thm
    val EQ_FDOM_SUBMAP : thm
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
    val FDOM_EQ_EMPTY_SYM : thm
    val FDOM_EQ_FDOM_FUPDATE : thm
    val FDOM_FEMPTY : thm
    val FDOM_FINITE : thm
    val FDOM_FMAP : thm
    val FDOM_FMERGE : thm
    val FDOM_FUNION : thm
    val FDOM_FUPDATE : thm
    val FDOM_FUPDATE_LIST : thm
    val FDOM_F_FEMPTY1 : thm
    val FDOM_f_o : thm
    val FDOM_o_f : thm
    val FEMPTY_SUBMAP : thm
    val FEVERY_DRESTRICT_COMPL : thm
    val FEVERY_FEMPTY : thm
    val FEVERY_FLOOKUP : thm
    val FEVERY_FUPDATE : thm
    val FEVERY_FUPDATE_LIST : thm
    val FEVERY_STRENGTHEN_THM : thm
    val FEVERY_o_f : thm
    val FINITE_FRANGE : thm
    val FINITE_PRED_11 : thm
    val FLOOKUP_EMPTY : thm
    val FLOOKUP_EXT : thm
    val FLOOKUP_FUNION : thm
    val FLOOKUP_FUN_FMAP : thm
    val FLOOKUP_SUBMAP : thm
    val FLOOKUP_UPDATE : thm
    val FLOOKUP_o_f : thm
    val FMAP_MAP2_FEMPTY : thm
    val FMAP_MAP2_FUPDATE : thm
    val FMAP_MAP2_THM : thm
    val FMEQ_ENUMERATE_CASES : thm
    val FMEQ_SINGLE_SIMPLE_DISJ_ELIM : thm
    val FMEQ_SINGLE_SIMPLE_ELIM : thm
    val FMERGE_ASSOC : thm
    val FMERGE_COMM : thm
    val FMERGE_DOMSUB : thm
    val FMERGE_DRESTRICT : thm
    val FMERGE_EQ_FEMPTY : thm
    val FMERGE_FEMPTY : thm
    val FMERGE_FUNION : thm
    val FMERGE_NO_CHANGE : thm
    val FM_PULL_APART : thm
    val FOLDL_FUPDATE_LIST : thm
    val FRANGE_FEMPTY : thm
    val FRANGE_FLOOKUP : thm
    val FRANGE_FMAP : thm
    val FRANGE_FUNION : thm
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
    val FUNION_IDEMPOT : thm
    val FUN_FMAP_EMPTY : thm
    val FUPD11_SAME_BASE : thm
    val FUPD11_SAME_KEY_AND_BASE : thm
    val FUPD11_SAME_NEW_KEY : thm
    val FUPD11_SAME_UPDATE : thm
    val FUPDATE_COMMUTES : thm
    val FUPDATE_DRESTRICT : thm
    val FUPDATE_ELIM : thm
    val FUPDATE_EQ : thm
    val FUPDATE_FUPDATE_LIST_COMMUTES : thm
    val FUPDATE_FUPDATE_LIST_MEM : thm
    val FUPDATE_LIST_APPEND : thm
    val FUPDATE_LIST_APPLY_MEM : thm
    val FUPDATE_LIST_APPLY_NOT_MEM : thm
    val FUPDATE_LIST_SAME_KEYS_UNWIND : thm
    val FUPDATE_LIST_SAME_UPDATE : thm
    val FUPDATE_LIST_SNOC : thm
    val FUPDATE_LIST_THM : thm
    val FUPDATE_PURGE : thm
    val FUPD_SAME_KEY_UNWIND : thm
    val IN_FDOM_FOLDR_UNION : thm
    val MAP_KEYS_FEMPTY : thm
    val MAP_KEYS_FUPDATE : thm
    val MAP_KEYS_using_LINV : thm
    val MAP_KEYS_witness : thm
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
    val SUBMAP_DOMSUB : thm
    val SUBMAP_DRESTRICT : thm
    val SUBMAP_FEMPTY : thm
    val SUBMAP_FRANGE : thm
    val SUBMAP_FUNION : thm
    val SUBMAP_FUNION_ABSORPTION : thm
    val SUBMAP_FUNION_EQ : thm
    val SUBMAP_FUNION_ID : thm
    val SUBMAP_FUPDATE : thm
    val SUBMAP_FUPDATE_EQN : thm
    val SUBMAP_FUPDATE_FLOOKUP : thm
    val SUBMAP_REFL : thm
    val SUBMAP_TRANS : thm
    val f_o_FEMPTY : thm
    val f_o_FUPDATE : thm
    val f_o_f_FEMPTY_1 : thm
    val f_o_f_FEMPTY_2 : thm
    val fmap_CASES : thm
    val fmap_EQ : thm
    val fmap_EQ_THM : thm
    val fmap_EQ_UPTO___EMPTY : thm
    val fmap_EQ_UPTO___EQ : thm
    val fmap_EQ_UPTO___FUPDATE_BOTH : thm
    val fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE : thm
    val fmap_EQ_UPTO___FUPDATE_SING : thm
    val fmap_EXT : thm
    val fmap_INDUCT : thm
    val fmap_SIMPLE_INDUCT : thm
    val fmap_rel_FEMPTY : thm
    val fmap_rel_FEMPTY2 : thm
    val fmap_rel_FUNION_rels : thm
    val fmap_rel_FUPDATE_I : thm
    val fmap_rel_FUPDATE_LIST_same : thm
    val fmap_rel_FUPDATE_same : thm
    val fmap_rel_mono : thm
    val fmap_rel_refl : thm
    val is_fmap_cases : thm
    val is_fmap_ind : thm
    val is_fmap_rules : thm
    val is_fmap_strongind : thm
    val o_f_DOMSUB : thm
    val o_f_FAPPLY : thm
    val o_f_FDOM : thm
    val o_f_FEMPTY : thm
    val o_f_FRANGE : thm
    val o_f_FUPDATE : thm
    val o_f_o_f : thm

  val finite_map_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [rich_list] Parent theory of "finite_map"

   [DRESTRICT_DEF]  Definition

      |- ∀f r.
           (FDOM (DRESTRICT f r) = FDOM f ∩ r) ∧
           ∀x.
             DRESTRICT f r ' x =
             if x ∈ FDOM f ∩ r then f ' x else FEMPTY ' x

   [FAPPLY_DEF]  Definition

      |- ∀f x. f ' x = OUTL (fmap_REP f x)

   [FCARD_DEF]  Definition

      |- ∀fm. FCARD fm = CARD (FDOM fm)

   [FDOM_DEF]  Definition

      |- ∀f x. FDOM f x ⇔ ISL (fmap_REP f x)

   [FEMPTY_DEF]  Definition

      |- FEMPTY = fmap_ABS (λa. INR ())

   [FEVERY_DEF]  Definition

      |- ∀P f. FEVERY P f ⇔ ∀x. x ∈ FDOM f ⇒ P (x,f ' x)

   [FLOOKUP_DEF]  Definition

      |- ∀f x. FLOOKUP f x = if x ∈ FDOM f then SOME (f ' x) else NONE

   [FMAP_MAP2_def]  Definition

      |- ∀f m. FMAP_MAP2 f m = FUN_FMAP (λx. f (x,m ' x)) (FDOM m)

   [FMERGE_DEF]  Definition

      |- ∀m f g.
           (FDOM (FMERGE m f g) = FDOM f ∪ FDOM g) ∧
           ∀x.
             FMERGE m f g ' x =
             if x ∉ FDOM f then g ' x
             else if x ∉ FDOM g then f ' x
             else m (f ' x) (g ' x)

   [FRANGE_DEF]  Definition

      |- ∀f. FRANGE f = {y | ∃x. x ∈ FDOM f ∧ (f ' x = y)}

   [FUNION_DEF]  Definition

      |- ∀f g.
           (FDOM (f ⊌ g) = FDOM f ∪ FDOM g) ∧
           ∀x. (f ⊌ g) ' x = if x ∈ FDOM f then f ' x else g ' x

   [FUN_FMAP_DEF]  Definition

      |- ∀f P.
           FINITE P ⇒
           (FDOM (FUN_FMAP f P) = P) ∧ ∀x. x ∈ P ⇒ (FUN_FMAP f P ' x = f x)

   [FUPDATE_DEF]  Definition

      |- ∀f x y.
           f |+ (x,y) =
           fmap_ABS (λa. if a = x then INL y else fmap_REP f a)

   [FUPDATE_LIST]  Definition

      |- $|++ = FOLDL $|+

   [MAP_KEYS_def]  Definition

      |- ∀f fm.
           (FDOM (MAP_KEYS f fm) = IMAGE f (FDOM fm)) ∧
           (INJ f (FDOM fm) 𝕌(:β) ⇒
            ∀x. x ∈ FDOM fm ⇒ (MAP_KEYS f fm ' (f x) = fm ' x))

   [RRESTRICT_DEF]  Definition

      |- ∀f r.
           (FDOM (RRESTRICT f r) = {x | x ∈ FDOM f ∧ f ' x ∈ r}) ∧
           ∀x.
             RRESTRICT f r ' x =
             if x ∈ FDOM f ∧ f ' x ∈ r then f ' x else FEMPTY ' x

   [SUBMAP_DEF]  Definition

      |- ∀f g. f ⊑ g ⇔ ∀x. x ∈ FDOM f ⇒ x ∈ FDOM g ∧ (f ' x = g ' x)

   [f_o_DEF]  Definition

      |- ∀f g. f f_o g = f f_o_f FUN_FMAP g {x | g x ∈ FDOM f}

   [f_o_f_DEF]  Definition

      |- ∀f g.
           (FDOM (f f_o_f g) = FDOM g ∩ {x | g ' x ∈ FDOM f}) ∧
           ∀x. x ∈ FDOM (f f_o_f g) ⇒ ((f f_o_f g) ' x = f ' (g ' x))

   [fmap_EQ_UPTO_def]  Definition

      |- ∀f1 f2 vs.
           fmap_EQ_UPTO f1 f2 vs ⇔
           (FDOM f1 ∩ COMPL vs = FDOM f2 ∩ COMPL vs) ∧
           ∀x. x ∈ FDOM f1 ∩ COMPL vs ⇒ (f1 ' x = f2 ' x)

   [fmap_ISO_DEF]  Definition

      |- (∀a. fmap_ABS (fmap_REP a) = a) ∧
         ∀r. is_fmap r ⇔ (fmap_REP (fmap_ABS r) = r)

   [fmap_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION is_fmap rep

   [fmap_domsub]  Definition

      |- ∀fm k. fm \\ k = DRESTRICT fm (COMPL {k})

   [fmap_rel_def]  Definition

      |- ∀R f1 f2.
           fmap_rel R f1 f2 ⇔
           (FDOM f2 = FDOM f1) ∧ ∀x. x ∈ FDOM f1 ⇒ R (f1 ' x) (f2 ' x)

   [fmap_size_def]  Definition

      |- ∀kz vz fm.
           fmap_size kz vz fm = ∑ (λk. kz k + vz (fm ' k)) (FDOM fm)

   [is_fmap_def]  Definition

      |- is_fmap =
         (λa0.
            ∀is_fmap'.
              (∀a0.
                 (a0 = (λa. INR ())) ∨
                 (∃f a b.
                    (a0 = (λx. if x = a then INL b else f x)) ∧
                    is_fmap' f) ⇒
                 is_fmap' a0) ⇒
              is_fmap' a0)

   [o_f_DEF]  Definition

      |- ∀f g.
           (FDOM (f o_f g) = FDOM g) ∧
           ∀x. x ∈ FDOM (f o_f g) ⇒ ((f o_f g) ' x = f (g ' x))

   [DOMSUB_COMMUTES]  Theorem

      |- fm \\ k1 \\ k2 = fm \\ k2 \\ k1

   [DOMSUB_FAPPLY]  Theorem

      |- ∀fm k. (fm \\ k) ' k = FEMPTY ' k

   [DOMSUB_FAPPLY_NEQ]  Theorem

      |- ∀fm k1 k2. k1 ≠ k2 ⇒ ((fm \\ k1) ' k2 = fm ' k2)

   [DOMSUB_FAPPLY_THM]  Theorem

      |- ∀fm k1 k2.
           (fm \\ k1) ' k2 = if k1 = k2 then FEMPTY ' k2 else fm ' k2

   [DOMSUB_FEMPTY]  Theorem

      |- ∀k. FEMPTY \\ k = FEMPTY

   [DOMSUB_FLOOKUP]  Theorem

      |- ∀fm k. FLOOKUP (fm \\ k) k = NONE

   [DOMSUB_FLOOKUP_NEQ]  Theorem

      |- ∀fm k1 k2. k1 ≠ k2 ⇒ (FLOOKUP (fm \\ k1) k2 = FLOOKUP fm k2)

   [DOMSUB_FLOOKUP_THM]  Theorem

      |- ∀fm k1 k2.
           FLOOKUP (fm \\ k1) k2 = if k1 = k2 then NONE else FLOOKUP fm k2

   [DOMSUB_FUNION]  Theorem

      |- (f ⊌ g) \\ k = f \\ k ⊌ g \\ k

   [DOMSUB_FUPDATE]  Theorem

      |- ∀fm k v. fm |+ (k,v) \\ k = fm \\ k

   [DOMSUB_FUPDATE_NEQ]  Theorem

      |- ∀fm k1 k2 v. k1 ≠ k2 ⇒ (fm |+ (k1,v) \\ k2 = fm \\ k2 |+ (k1,v))

   [DOMSUB_FUPDATE_THM]  Theorem

      |- ∀fm k1 k2 v.
           fm |+ (k1,v) \\ k2 =
           if k1 = k2 then fm \\ k2 else fm \\ k2 |+ (k1,v)

   [DOMSUB_IDEM]  Theorem

      |- fm \\ k \\ k = fm \\ k

   [DOMSUB_NOT_IN_DOM]  Theorem

      |- k ∉ FDOM fm ⇒ (fm \\ k = fm)

   [DRESTRICT_DRESTRICT]  Theorem

      |- ∀f P Q. DRESTRICT (DRESTRICT f P) Q = DRESTRICT f (P ∩ Q)

   [DRESTRICT_EQ_DRESTRICT]  Theorem

      |- ∀f1 f2 s1 s2.
           (DRESTRICT f1 s1 = DRESTRICT f2 s2) ⇔
           DRESTRICT f1 s1 ⊑ f2 ∧ DRESTRICT f2 s2 ⊑ f1 ∧
           (s1 ∩ FDOM f1 = s2 ∩ FDOM f2)

   [DRESTRICT_EQ_FUNION]  Theorem

      |- ∀h h1 h2.
           DISJOINT (FDOM h1) (FDOM h2) ∧ (h1 ⊌ h2 = h) ⇒
           (h2 = DRESTRICT h (COMPL (FDOM h1)))

   [DRESTRICT_FEMPTY]  Theorem

      |- ∀r. DRESTRICT FEMPTY r = FEMPTY

   [DRESTRICT_FUNION]  Theorem

      |- ∀h s1 s2. DRESTRICT h s1 ⊌ DRESTRICT h s2 = DRESTRICT h (s1 ∪ s2)

   [DRESTRICT_FUNION_DRESTRICT_COMPL]  Theorem

      |- DRESTRICT f s ⊌ DRESTRICT f (COMPL s) = f

   [DRESTRICT_FUPDATE]  Theorem

      |- ∀f r x y.
           DRESTRICT (f |+ (x,y)) r =
           if x ∈ r then DRESTRICT f r |+ (x,y) else DRESTRICT f r

   [DRESTRICT_IDEMPOT]  Theorem

      |- ∀s vs. DRESTRICT (DRESTRICT s vs) vs = DRESTRICT s vs

   [DRESTRICT_IS_FEMPTY]  Theorem

      |- ∀f. DRESTRICT f ∅ = FEMPTY

   [DRESTRICT_SUBMAP]  Theorem

      |- ∀f r. DRESTRICT f r ⊑ f

   [DRESTRICT_UNIV]  Theorem

      |- ∀f. DRESTRICT f 𝕌(:α) = f

   [EQ_FDOM_SUBMAP]  Theorem

      |- (f = g) ⇔ f ⊑ g ∧ (FDOM f = FDOM g)

   [FAPPLY_FUPDATE]  Theorem

      |- ∀f x y. (f |+ (x,y)) ' x = y

   [FAPPLY_FUPDATE_THM]  Theorem

      |- ∀f a b x. (f |+ (a,b)) ' x = if x = a then b else f ' x

   [FAPPLY_f_o]  Theorem

      |- ∀f g.
           FINITE {x | g x ∈ FDOM f} ⇒
           ∀x. x ∈ FDOM (f f_o g) ⇒ ((f f_o g) ' x = f ' (g x))

   [FCARD_0_FEMPTY]  Theorem

      |- ∀f. (FCARD f = 0) ⇔ (f = FEMPTY)

   [FCARD_FEMPTY]  Theorem

      |- FCARD FEMPTY = 0

   [FCARD_FUPDATE]  Theorem

      |- ∀fm a b.
           FCARD (fm |+ (a,b)) =
           if a ∈ FDOM fm then FCARD fm else 1 + FCARD fm

   [FCARD_SUC]  Theorem

      |- ∀f n.
           (FCARD f = SUC n) ⇔
           ∃f' x y. x ∉ FDOM f' ∧ (FCARD f' = n) ∧ (f = f' |+ (x,y))

   [FDOM_DOMSUB]  Theorem

      |- ∀fm k. FDOM (fm \\ k) = FDOM fm DELETE k

   [FDOM_DRESTRICT]  Theorem

      |- ∀f r x. FDOM (DRESTRICT f r) = FDOM f ∩ r

   [FDOM_EQ_EMPTY]  Theorem

      |- ∀f. (FDOM f = ∅) ⇔ (f = FEMPTY)

   [FDOM_EQ_EMPTY_SYM]  Theorem

      |- ∀f. (∅ = FDOM f) ⇔ (f = FEMPTY)

   [FDOM_EQ_FDOM_FUPDATE]  Theorem

      |- ∀f x. x ∈ FDOM f ⇒ ∀y. FDOM (f |+ (x,y)) = FDOM f

   [FDOM_FEMPTY]  Theorem

      |- FDOM FEMPTY = ∅

   [FDOM_FINITE]  Theorem

      |- ∀fm. FINITE (FDOM fm)

   [FDOM_FMAP]  Theorem

      |- ∀f s. FINITE s ⇒ (FDOM (FUN_FMAP f s) = s)

   [FDOM_FMERGE]  Theorem

      |- ∀m f g. FDOM (FMERGE m f g) = FDOM f ∪ FDOM g

   [FDOM_FUNION]  Theorem

      |- ∀f g x. FDOM (f ⊌ g) = FDOM f ∪ FDOM g

   [FDOM_FUPDATE]  Theorem

      |- ∀f a b. FDOM (f |+ (a,b)) = a INSERT FDOM f

   [FDOM_FUPDATE_LIST]  Theorem

      |- ∀kvl fm. FDOM (fm |++ kvl) = FDOM fm ∪ set (MAP FST kvl)

   [FDOM_F_FEMPTY1]  Theorem

      |- ∀f. (∀a. a ∉ FDOM f) ⇔ (f = FEMPTY)

   [FDOM_f_o]  Theorem

      |- ∀f g.
           FINITE {x | g x ∈ FDOM f} ⇒
           (FDOM (f f_o g) = {x | g x ∈ FDOM f})

   [FDOM_o_f]  Theorem

      |- ∀f g. FDOM (f o_f g) = FDOM g

   [FEMPTY_SUBMAP]  Theorem

      |- ∀h. h ⊑ FEMPTY ⇔ (h = FEMPTY)

   [FEVERY_DRESTRICT_COMPL]  Theorem

      |- FEVERY P (DRESTRICT (f |+ (k,v)) (COMPL s)) ⇔
         (k ∉ s ⇒ P (k,v)) ∧ FEVERY P (DRESTRICT f (COMPL (k INSERT s)))

   [FEVERY_FEMPTY]  Theorem

      |- ∀P. FEVERY P FEMPTY

   [FEVERY_FLOOKUP]  Theorem

      |- FEVERY P f ∧ (FLOOKUP f k = SOME v) ⇒ P (k,v)

   [FEVERY_FUPDATE]  Theorem

      |- ∀P f x y.
           FEVERY P (f |+ (x,y)) ⇔
           P (x,y) ∧ FEVERY P (DRESTRICT f (COMPL {x}))

   [FEVERY_FUPDATE_LIST]  Theorem

      |- ALL_DISTINCT (MAP FST kvl) ⇒
         (FEVERY P (fm |++ kvl) ⇔
          EVERY P kvl ∧
          FEVERY P (DRESTRICT fm (COMPL (set (MAP FST kvl)))))

   [FEVERY_STRENGTHEN_THM]  Theorem

      |- FEVERY P FEMPTY ∧ (FEVERY P f ∧ P (x,y) ⇒ FEVERY P (f |+ (x,y)))

   [FEVERY_o_f]  Theorem

      |- ∀m P f. FEVERY P (f o_f m) ⇔ FEVERY (λx. P (FST x,f (SND x))) m

   [FINITE_FRANGE]  Theorem

      |- ∀fm. FINITE (FRANGE fm)

   [FINITE_PRED_11]  Theorem

      |- ∀g. (∀x y. (g x = g y) ⇔ (x = y)) ⇒ ∀f. FINITE {x | g x ∈ FDOM f}

   [FLOOKUP_EMPTY]  Theorem

      |- FLOOKUP FEMPTY k = NONE

   [FLOOKUP_EXT]  Theorem

      |- (f1 = f2) ⇔ (FLOOKUP f1 = FLOOKUP f2)

   [FLOOKUP_FUNION]  Theorem

      |- FLOOKUP (f1 ⊌ f2) k =
         case FLOOKUP f1 k of NONE => FLOOKUP f2 k | SOME v => SOME v

   [FLOOKUP_FUN_FMAP]  Theorem

      |- FINITE P ⇒
         (FLOOKUP (FUN_FMAP f P) k = if k ∈ P then SOME (f k) else NONE)

   [FLOOKUP_SUBMAP]  Theorem

      |- f ⊑ g ∧ (FLOOKUP f k = SOME v) ⇒ (FLOOKUP g k = SOME v)

   [FLOOKUP_UPDATE]  Theorem

      |- FLOOKUP (fm |+ (k1,v)) k2 =
         if k1 = k2 then SOME v else FLOOKUP fm k2

   [FLOOKUP_o_f]  Theorem

      |- FLOOKUP (f o_f fm) k =
         case FLOOKUP fm k of NONE => NONE | SOME v => SOME (f v)

   [FMAP_MAP2_FEMPTY]  Theorem

      |- FMAP_MAP2 f FEMPTY = FEMPTY

   [FMAP_MAP2_FUPDATE]  Theorem

      |- FMAP_MAP2 f (m |+ (x,v)) = FMAP_MAP2 f m |+ (x,f (x,v))

   [FMAP_MAP2_THM]  Theorem

      |- (FDOM (FMAP_MAP2 f m) = FDOM m) ∧
         ∀x. x ∈ FDOM m ⇒ (FMAP_MAP2 f m ' x = f (x,m ' x))

   [FMEQ_ENUMERATE_CASES]  Theorem

      |- ∀f1 kvl p. (f1 |+ p = FEMPTY |++ kvl) ⇒ MEM p kvl

   [FMEQ_SINGLE_SIMPLE_DISJ_ELIM]  Theorem

      |- ∀fm k v ck cv.
           (fm |+ (k,v) = FEMPTY |+ (ck,cv)) ⇔
           (k = ck) ∧ (v = cv) ∧
           ((fm = FEMPTY) ∨ ∃v'. fm = FEMPTY |+ (k,v'))

   [FMEQ_SINGLE_SIMPLE_ELIM]  Theorem

      |- ∀P k v ck cv nv.
           (∃fm. (fm |+ (k,v) = FEMPTY |+ (ck,cv)) ∧ P (fm |+ (k,nv))) ⇔
           (k = ck) ∧ (v = cv) ∧ P (FEMPTY |+ (ck,nv))

   [FMERGE_ASSOC]  Theorem

      |- ASSOC (FMERGE m) ⇔ ASSOC m

   [FMERGE_COMM]  Theorem

      |- COMM (FMERGE m) ⇔ COMM m

   [FMERGE_DOMSUB]  Theorem

      |- ∀m m1 m2 k. FMERGE m m1 m2 \\ k = FMERGE m (m1 \\ k) (m2 \\ k)

   [FMERGE_DRESTRICT]  Theorem

      |- DRESTRICT (FMERGE f st1 st2) vs =
         FMERGE f (DRESTRICT st1 vs) (DRESTRICT st2 vs)

   [FMERGE_EQ_FEMPTY]  Theorem

      |- (FMERGE m f g = FEMPTY) ⇔ (f = FEMPTY) ∧ (g = FEMPTY)

   [FMERGE_FEMPTY]  Theorem

      |- (FMERGE m f FEMPTY = f) ∧ (FMERGE m FEMPTY f = f)

   [FMERGE_FUNION]  Theorem

      |- $⊌ = FMERGE (λx y. x)

   [FMERGE_NO_CHANGE]  Theorem

      |- ((FMERGE m f1 f2 = f1) ⇔
          ∀x. x ∈ FDOM f2 ⇒ x ∈ FDOM f1 ∧ (m (f1 ' x) (f2 ' x) = f1 ' x)) ∧
         ((FMERGE m f1 f2 = f2) ⇔
          ∀x. x ∈ FDOM f1 ⇒ x ∈ FDOM f2 ∧ (m (f1 ' x) (f2 ' x) = f2 ' x))

   [FM_PULL_APART]  Theorem

      |- ∀fm k. k ∈ FDOM fm ⇒ ∃fm0 v. (fm = fm0 |+ (k,v)) ∧ k ∉ FDOM fm0

   [FOLDL_FUPDATE_LIST]  Theorem

      |- ∀f1 f2 ls a.
           FOLDL (λfm k. fm |+ (f1 k,f2 k)) a ls =
           a |++ MAP (λk. (f1 k,f2 k)) ls

   [FRANGE_FEMPTY]  Theorem

      |- FRANGE FEMPTY = ∅

   [FRANGE_FLOOKUP]  Theorem

      |- v ∈ FRANGE f ⇔ ∃k. FLOOKUP f k = SOME v

   [FRANGE_FMAP]  Theorem

      |- FINITE P ⇒ (FRANGE (FUN_FMAP f P) = IMAGE f P)

   [FRANGE_FUNION]  Theorem

      |- DISJOINT (FDOM fm1) (FDOM fm2) ⇒
         (FRANGE (fm1 ⊌ fm2) = FRANGE fm1 ∪ FRANGE fm2)

   [FRANGE_FUPDATE]  Theorem

      |- ∀f x y.
           FRANGE (f |+ (x,y)) = y INSERT FRANGE (DRESTRICT f (COMPL {x}))

   [FRANGE_FUPDATE_DOMSUB]  Theorem

      |- ∀fm k v. FRANGE (fm |+ (k,v)) = v INSERT FRANGE (fm \\ k)

   [FUNION_ASSOC]  Theorem

      |- ∀f g h. f ⊌ (g ⊌ h) = f ⊌ g ⊌ h

   [FUNION_COMM]  Theorem

      |- ∀f g. DISJOINT (FDOM f) (FDOM g) ⇒ (f ⊌ g = g ⊌ f)

   [FUNION_EQ]  Theorem

      |- ∀f1 f2 f3.
           DISJOINT (FDOM f1) (FDOM f2) ∧ DISJOINT (FDOM f1) (FDOM f3) ⇒
           ((f1 ⊌ f2 = f1 ⊌ f3) ⇔ (f2 = f3))

   [FUNION_EQ_FEMPTY]  Theorem

      |- ∀h1 h2. (h1 ⊌ h2 = FEMPTY) ⇔ (h1 = FEMPTY) ∧ (h2 = FEMPTY)

   [FUNION_EQ_IMPL]  Theorem

      |- ∀f1 f2 f3.
           DISJOINT (FDOM f1) (FDOM f2) ∧ DISJOINT (FDOM f1) (FDOM f3) ∧
           (f2 = f3) ⇒
           (f1 ⊌ f2 = f1 ⊌ f3)

   [FUNION_FEMPTY_1]  Theorem

      |- ∀g. FEMPTY ⊌ g = g

   [FUNION_FEMPTY_2]  Theorem

      |- ∀f. f ⊌ FEMPTY = f

   [FUNION_FMERGE]  Theorem

      |- ∀f1 f2 m.
           DISJOINT (FDOM f1) (FDOM f2) ⇒ (FMERGE m f1 f2 = f1 ⊌ f2)

   [FUNION_FUPDATE_1]  Theorem

      |- ∀f g x y. f |+ (x,y) ⊌ g = (f ⊌ g) |+ (x,y)

   [FUNION_FUPDATE_2]  Theorem

      |- ∀f g x y.
           f ⊌ g |+ (x,y) = if x ∈ FDOM f then f ⊌ g else (f ⊌ g) |+ (x,y)

   [FUNION_IDEMPOT]  Theorem

      |- fm ⊌ fm = fm

   [FUN_FMAP_EMPTY]  Theorem

      |- FUN_FMAP f ∅ = FEMPTY

   [FUPD11_SAME_BASE]  Theorem

      |- ∀f k1 v1 k2 v2.
           (f |+ (k1,v1) = f |+ (k2,v2)) ⇔
           (k1 = k2) ∧ (v1 = v2) ∨
           k1 ≠ k2 ∧ k1 ∈ FDOM f ∧ k2 ∈ FDOM f ∧ (f |+ (k1,v1) = f) ∧
           (f |+ (k2,v2) = f)

   [FUPD11_SAME_KEY_AND_BASE]  Theorem

      |- ∀f k v1 v2. (f |+ (k,v1) = f |+ (k,v2)) ⇔ (v1 = v2)

   [FUPD11_SAME_NEW_KEY]  Theorem

      |- ∀f1 f2 k v1 v2.
           k ∉ FDOM f1 ∧ k ∉ FDOM f2 ⇒
           ((f1 |+ (k,v1) = f2 |+ (k,v2)) ⇔ (f1 = f2) ∧ (v1 = v2))

   [FUPD11_SAME_UPDATE]  Theorem

      |- ∀f1 f2 k v.
           (f1 |+ (k,v) = f2 |+ (k,v)) ⇔
           (DRESTRICT f1 (COMPL {k}) = DRESTRICT f2 (COMPL {k}))

   [FUPDATE_COMMUTES]  Theorem

      |- ∀f a b c d. a ≠ c ⇒ (f |+ (a,b) |+ (c,d) = f |+ (c,d) |+ (a,b))

   [FUPDATE_DRESTRICT]  Theorem

      |- ∀f x y. f |+ (x,y) = DRESTRICT f (COMPL {x}) |+ (x,y)

   [FUPDATE_ELIM]  Theorem

      |- ∀k v f. k ∈ FDOM f ∧ (f ' k = v) ⇒ (f |+ (k,v) = f)

   [FUPDATE_EQ]  Theorem

      |- ∀f a b c. f |+ (a,b) |+ (a,c) = f |+ (a,c)

   [FUPDATE_FUPDATE_LIST_COMMUTES]  Theorem

      |- k ∉ set (MAP FST kvl) ⇒
         (fm |+ (k,v) |++ kvl = (fm |++ kvl) |+ (k,v))

   [FUPDATE_FUPDATE_LIST_MEM]  Theorem

      |- MEM k (MAP FST kvl) ⇒ (fm |+ (k,v) |++ kvl = fm |++ kvl)

   [FUPDATE_LIST_APPEND]  Theorem

      |- fm |++ (kvl1 ++ kvl2) = fm |++ kvl1 |++ kvl2

   [FUPDATE_LIST_APPLY_MEM]  Theorem

      |- ∀kvl f k v n.
           n < LENGTH kvl ∧ (k = EL n (MAP FST kvl)) ∧
           (v = EL n (MAP SND kvl)) ∧
           (∀m. n < m ∧ m < LENGTH kvl ⇒ EL m (MAP FST kvl) ≠ k) ⇒
           ((f |++ kvl) ' k = v)

   [FUPDATE_LIST_APPLY_NOT_MEM]  Theorem

      |- ∀kvl f k. k ∉ set (MAP FST kvl) ⇒ ((f |++ kvl) ' k = f ' k)

   [FUPDATE_LIST_SAME_KEYS_UNWIND]  Theorem

      |- ∀f1 f2 kvl1 kvl2.
           (f1 |++ kvl1 = f2 |++ kvl2) ∧ (MAP FST kvl1 = MAP FST kvl2) ∧
           ALL_DISTINCT (MAP FST kvl1) ⇒
           (kvl1 = kvl2) ∧
           ∀kvl. (MAP FST kvl = MAP FST kvl1) ⇒ (f1 |++ kvl = f2 |++ kvl)

   [FUPDATE_LIST_SAME_UPDATE]  Theorem

      |- ∀kvl f1 f2.
           (f1 |++ kvl = f2 |++ kvl) ⇔
           (DRESTRICT f1 (COMPL (set (MAP FST kvl))) =
            DRESTRICT f2 (COMPL (set (MAP FST kvl))))

   [FUPDATE_LIST_SNOC]  Theorem

      |- ∀xs x fm. fm |++ SNOC x xs = (fm |++ xs) |+ x

   [FUPDATE_LIST_THM]  Theorem

      |- ∀f. (f |++ [] = f) ∧ ∀h t. f |++ (h::t) = f |+ h |++ t

   [FUPDATE_PURGE]  Theorem

      |- ∀f x y. f |+ (x,y) = f \\ x |+ (x,y)

   [FUPD_SAME_KEY_UNWIND]  Theorem

      |- ∀f1 f2 k v1 v2.
           (f1 |+ (k,v1) = f2 |+ (k,v2)) ⇒
           (v1 = v2) ∧ ∀v. f1 |+ (k,v) = f2 |+ (k,v)

   [IN_FDOM_FOLDR_UNION]  Theorem

      |- ∀x hL. x ∈ FDOM (FOLDR $⊌ FEMPTY hL) ⇔ ∃h. MEM h hL ∧ x ∈ FDOM h

   [MAP_KEYS_FEMPTY]  Theorem

      |- ∀f. MAP_KEYS f FEMPTY = FEMPTY

   [MAP_KEYS_FUPDATE]  Theorem

      |- ∀f fm k v.
           INJ f (k INSERT FDOM fm) 𝕌(:β) ⇒
           (MAP_KEYS f (fm |+ (k,v)) = MAP_KEYS f fm |+ (f k,v))

   [MAP_KEYS_using_LINV]  Theorem

      |- ∀f fm.
           INJ f (FDOM fm) 𝕌(:β) ⇒
           (MAP_KEYS f fm =
            fm f_o_f FUN_FMAP (LINV f (FDOM fm)) (IMAGE f (FDOM fm)))

   [MAP_KEYS_witness]  Theorem

      |- let m f fm =
               if INJ f (FDOM fm) 𝕌(:β) then
                 fm f_o_f FUN_FMAP (LINV f (FDOM fm)) (IMAGE f (FDOM fm))
               else FUN_FMAP ARB (IMAGE f (FDOM fm))
         in
           ∀f fm.
             (FDOM (m f fm) = IMAGE f (FDOM fm)) ∧
             (INJ f (FDOM fm) 𝕌(:β) ⇒
              ∀x. x ∈ FDOM fm ⇒ (m f fm ' (f x) = fm ' x))

   [NOT_EQ_FAPPLY]  Theorem

      |- ∀f a x y. a ≠ x ⇒ ((f |+ (x,y)) ' a = f ' a)

   [NOT_EQ_FEMPTY_FUPDATE]  Theorem

      |- ∀f a b. FEMPTY ≠ f |+ (a,b)

   [NOT_FDOM_DRESTRICT]  Theorem

      |- ∀f x. x ∉ FDOM f ⇒ (DRESTRICT f (COMPL {x}) = f)

   [NOT_FDOM_FAPPLY_FEMPTY]  Theorem

      |- ∀f x. x ∉ FDOM f ⇒ (f ' x = FEMPTY ' x)

   [RRESTRICT_FEMPTY]  Theorem

      |- ∀r. RRESTRICT FEMPTY r = FEMPTY

   [RRESTRICT_FUPDATE]  Theorem

      |- ∀f r x y.
           RRESTRICT (f |+ (x,y)) r =
           if y ∈ r then RRESTRICT f r |+ (x,y)
           else RRESTRICT (DRESTRICT f (COMPL {x})) r

   [SAME_KEY_UPDATES_DIFFER]  Theorem

      |- ∀f1 f2 k v1 v2. v1 ≠ v2 ⇒ f1 |+ (k,v1) ≠ f2 |+ (k,v2)

   [STRONG_DRESTRICT_FUPDATE]  Theorem

      |- ∀f r x y.
           x ∈ r ⇒
           (DRESTRICT (f |+ (x,y)) r = DRESTRICT f (r DELETE x) |+ (x,y))

   [STRONG_DRESTRICT_FUPDATE_THM]  Theorem

      |- ∀f r x y.
           DRESTRICT (f |+ (x,y)) r =
           if x ∈ r then DRESTRICT f (COMPL {x} ∩ r) |+ (x,y)
           else DRESTRICT f (COMPL {x} ∩ r)

   [SUBMAP_ANTISYM]  Theorem

      |- ∀f g. f ⊑ g ∧ g ⊑ f ⇔ (f = g)

   [SUBMAP_DOMSUB]  Theorem

      |- f \\ k ⊑ f

   [SUBMAP_DRESTRICT]  Theorem

      |- DRESTRICT f P ⊑ f

   [SUBMAP_FEMPTY]  Theorem

      |- ∀f. FEMPTY ⊑ f

   [SUBMAP_FRANGE]  Theorem

      |- ∀f g. f ⊑ g ⇒ FRANGE f ⊆ FRANGE g

   [SUBMAP_FUNION]  Theorem

      |- ∀f1 f2 f3.
           f1 ⊑ f2 ∨ DISJOINT (FDOM f1) (FDOM f2) ∧ f1 ⊑ f3 ⇒ f1 ⊑ f2 ⊌ f3

   [SUBMAP_FUNION_ABSORPTION]  Theorem

      |- ∀f g. f ⊑ g ⇔ (f ⊌ g = g)

   [SUBMAP_FUNION_EQ]  Theorem

      |- (∀f1 f2 f3.
            DISJOINT (FDOM f1) (FDOM f2) ⇒ (f1 ⊑ f2 ⊌ f3 ⇔ f1 ⊑ f3)) ∧
         ∀f1 f2 f3.
           DISJOINT (FDOM f1) (FDOM f3 DIFF FDOM f2) ⇒
           (f1 ⊑ f2 ⊌ f3 ⇔ f1 ⊑ f2)

   [SUBMAP_FUNION_ID]  Theorem

      |- (∀f1 f2. f1 ⊑ f1 ⊌ f2) ∧
         ∀f1 f2. DISJOINT (FDOM f1) (FDOM f2) ⇒ f2 ⊑ f1 ⊌ f2

   [SUBMAP_FUPDATE]  Theorem

      |- ∀f g x y.
           f |+ (x,y) ⊑ g ⇔ x ∈ FDOM g ∧ (g ' x = y) ∧ f \\ x ⊑ g \\ x

   [SUBMAP_FUPDATE_EQN]  Theorem

      |- f ⊑ f |+ (x,y) ⇔ x ∉ FDOM f ∨ (f ' x = y) ∧ x ∈ FDOM f

   [SUBMAP_FUPDATE_FLOOKUP]  Theorem

      |- f ⊑ f |+ (x,y) ⇔ (FLOOKUP f x = NONE) ∨ (FLOOKUP f x = SOME y)

   [SUBMAP_REFL]  Theorem

      |- ∀f. f ⊑ f

   [SUBMAP_TRANS]  Theorem

      |- ∀f g h. f ⊑ g ∧ g ⊑ h ⇒ f ⊑ h

   [f_o_FEMPTY]  Theorem

      |- ∀g. FEMPTY f_o g = FEMPTY

   [f_o_FUPDATE]  Theorem

      |- ∀fm k v g.
           FINITE {x | g x ∈ FDOM fm} ∧ FINITE {x | g x = k} ⇒
           (fm |+ (k,v) f_o g =
            FMERGE (combin$C K) (fm f_o g) (FUN_FMAP (K v) {x | g x = k}))

   [f_o_f_FEMPTY_1]  Theorem

      |- ∀f. FEMPTY f_o_f f = FEMPTY

   [f_o_f_FEMPTY_2]  Theorem

      |- ∀f. f f_o_f FEMPTY = FEMPTY

   [fmap_CASES]  Theorem

      |- ∀f. (f = FEMPTY) ∨ ∃g x y. f = g |+ (x,y)

   [fmap_EQ]  Theorem

      |- ∀f g. (FDOM f = FDOM g) ∧ ($' f = $' g) ⇔ (f = g)

   [fmap_EQ_THM]  Theorem

      |- ∀f g.
           (FDOM f = FDOM g) ∧ (∀x. x ∈ FDOM f ⇒ (f ' x = g ' x)) ⇔ (f = g)

   [fmap_EQ_UPTO___EMPTY]  Theorem

      |- ∀f1 f2. fmap_EQ_UPTO f1 f2 ∅ ⇔ (f1 = f2)

   [fmap_EQ_UPTO___EQ]  Theorem

      |- ∀vs f. fmap_EQ_UPTO f f vs

   [fmap_EQ_UPTO___FUPDATE_BOTH]  Theorem

      |- ∀f1 f2 ks k v.
           fmap_EQ_UPTO f1 f2 ks ⇒
           fmap_EQ_UPTO (f1 |+ (k,v)) (f2 |+ (k,v)) (ks DELETE k)

   [fmap_EQ_UPTO___FUPDATE_BOTH___NO_DELETE]  Theorem

      |- ∀f1 f2 ks k v.
           fmap_EQ_UPTO f1 f2 ks ⇒
           fmap_EQ_UPTO (f1 |+ (k,v)) (f2 |+ (k,v)) ks

   [fmap_EQ_UPTO___FUPDATE_SING]  Theorem

      |- ∀f1 f2 ks k v.
           fmap_EQ_UPTO f1 f2 ks ⇒
           fmap_EQ_UPTO (f1 |+ (k,v)) f2 (k INSERT ks)

   [fmap_EXT]  Theorem

      |- ∀f g.
           (f = g) ⇔ (FDOM f = FDOM g) ∧ ∀x. x ∈ FDOM f ⇒ (f ' x = g ' x)

   [fmap_INDUCT]  Theorem

      |- ∀P.
           P FEMPTY ∧ (∀f. P f ⇒ ∀x y. x ∉ FDOM f ⇒ P (f |+ (x,y))) ⇒
           ∀f. P f

   [fmap_SIMPLE_INDUCT]  Theorem

      |- ∀P. P FEMPTY ∧ (∀f. P f ⇒ ∀x y. P (f |+ (x,y))) ⇒ ∀f. P f

   [fmap_rel_FEMPTY]  Theorem

      |- fmap_rel R FEMPTY FEMPTY

   [fmap_rel_FEMPTY2]  Theorem

      |- (fmap_rel R FEMPTY f ⇔ (f = FEMPTY)) ∧
         (fmap_rel R f FEMPTY ⇔ (f = FEMPTY))

   [fmap_rel_FUNION_rels]  Theorem

      |- fmap_rel R f1 f2 ∧ fmap_rel R f3 f4 ⇒
         fmap_rel R (f1 ⊌ f3) (f2 ⊌ f4)

   [fmap_rel_FUPDATE_I]  Theorem

      |- fmap_rel R (f1 \\ k) (f2 \\ k) ∧ R v1 v2 ⇒
         fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))

   [fmap_rel_FUPDATE_LIST_same]  Theorem

      |- ∀R ls1 ls2 f1 f2.
           fmap_rel R f1 f2 ∧ (MAP FST ls1 = MAP FST ls2) ∧
           LIST_REL R (MAP SND ls1) (MAP SND ls2) ⇒
           fmap_rel R (f1 |++ ls1) (f2 |++ ls2)

   [fmap_rel_FUPDATE_same]  Theorem

      |- fmap_rel R f1 f2 ∧ R v1 v2 ⇒
         fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))

   [fmap_rel_mono]  Theorem

      |- (∀x y. R1 x y ⇒ R2 x y) ⇒ fmap_rel R1 f1 f2 ⇒ fmap_rel R2 f1 f2

   [fmap_rel_refl]  Theorem

      |- (∀x. R x x) ⇒ fmap_rel R x x

   [is_fmap_cases]  Theorem

      |- ∀a0.
           is_fmap a0 ⇔
           (a0 = (λa. INR ())) ∨
           ∃f a b. (a0 = (λx. if x = a then INL b else f x)) ∧ is_fmap f

   [is_fmap_ind]  Theorem

      |- ∀is_fmap'.
           is_fmap' (λa. INR ()) ∧
           (∀f a b.
              is_fmap' f ⇒ is_fmap' (λx. if x = a then INL b else f x)) ⇒
           ∀a0. is_fmap a0 ⇒ is_fmap' a0

   [is_fmap_rules]  Theorem

      |- is_fmap (λa. INR ()) ∧
         ∀f a b. is_fmap f ⇒ is_fmap (λx. if x = a then INL b else f x)

   [is_fmap_strongind]  Theorem

      |- ∀is_fmap'.
           is_fmap' (λa. INR ()) ∧
           (∀f a b.
              is_fmap f ∧ is_fmap' f ⇒
              is_fmap' (λx. if x = a then INL b else f x)) ⇒
           ∀a0. is_fmap a0 ⇒ is_fmap' a0

   [o_f_DOMSUB]  Theorem

      |- (g o_f fm) \\ k = g o_f fm \\ k

   [o_f_FAPPLY]  Theorem

      |- ∀f g x. x ∈ FDOM g ⇒ ((f o_f g) ' x = f (g ' x))

   [o_f_FDOM]  Theorem

      |- ∀f g. FDOM g = FDOM (f o_f g)

   [o_f_FEMPTY]  Theorem

      |- f o_f FEMPTY = FEMPTY

   [o_f_FRANGE]  Theorem

      |- x ∈ FRANGE g ⇒ f x ∈ FRANGE (f o_f g)

   [o_f_FUPDATE]  Theorem

      |- f o_f fm |+ (k,v) = (f o_f fm \\ k) |+ (k,f v)

   [o_f_o_f]  Theorem

      |- f o_f (g o_f h) = f o g o_f h


*)
end
