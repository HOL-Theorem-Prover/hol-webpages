signature fmapalTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val AP_SND : thm
    val OFU : thm
    val OPTION_FLAT_primitive : thm
    val OPTION_UPDATE : thm
    val ORL_bt_curried : thm
    val ORL_bt_lb_curried : thm
    val ORL_bt_lb_tupled_primitive : thm
    val ORL_bt_lb_ub_curried : thm
    val ORL_bt_lb_ub_tupled_primitive : thm
    val ORL_bt_tupled_primitive : thm
    val ORL_bt_ub_curried : thm
    val ORL_bt_ub_tupled_primitive : thm
    val ORL_curried : thm
    val ORL_sublists_curried : thm
    val ORL_sublists_tupled_primitive : thm
    val ORL_tupled_primitive : thm
    val ORWL : thm
    val UFO : thm
    val assocv_curried : thm
    val assocv_tupled_primitive : thm
    val bl_to_fmap_curried : thm
    val bl_to_fmap_tupled_primitive : thm
    val bt_map : thm
    val bt_rplacv_cn_curried : thm
    val bt_rplacv_cn_tupled_primitive : thm
    val bt_to_fmap_curried : thm
    val bt_to_fmap_lb : thm
    val bt_to_fmap_lb_ub : thm
    val bt_to_fmap_tupled_primitive : thm
    val bt_to_fmap_ub : thm
    val bt_to_orl_ac_curried : thm
    val bt_to_orl_ac_tupled_primitive : thm
    val bt_to_orl_curried : thm
    val bt_to_orl_lb_ac_curried : thm
    val bt_to_orl_lb_ac_tupled_primitive : thm
    val bt_to_orl_lb_curried : thm
    val bt_to_orl_lb_tupled_primitive : thm
    val bt_to_orl_lb_ub_ac_curried : thm
    val bt_to_orl_lb_ub_ac_tupled_AUX : thm
    val bt_to_orl_lb_ub_ac_tupled_primitive : thm
    val bt_to_orl_lb_ub_curried : thm
    val bt_to_orl_lb_ub_tupled_primitive : thm
    val bt_to_orl_tupled_primitive : thm
    val bt_to_orl_ub_ac_curried : thm
    val bt_to_orl_ub_ac_tupled_primitive : thm
    val bt_to_orl_ub_curried : thm
    val bt_to_orl_ub_tupled_primitive : thm
    val diff_merge_curried : thm
    val diff_merge_tupled_primitive : thm
    val fmap : thm
    val incr_build : thm
    val incr_flat : thm
    val incr_merge_curried : thm
    val incr_merge_tupled_primitive : thm
    val incr_sort : thm
    val inter_merge_curried : thm
    val inter_merge_tupled_primitive : thm
    val list_rplacv_cn_curried : thm
    val list_rplacv_cn_tupled_primitive : thm
    val merge_curried : thm
    val merge_out_curried : thm
    val merge_out_tupled_primitive : thm
    val merge_tupled_primitive : thm
    val optry : thm
    val optry_list_curried : thm
    val optry_list_tupled_primitive : thm
    val unlookup : thm
    val vcossa : thm

  (*  Theorems  *)
    val FAPPLY_fmap_CONS : thm
    val FAPPLY_fmap_NIL : thm
    val FAPPLY_node : thm
    val FAPPLY_nt : thm
    val FMAPAL_FDOM_THM : thm
    val FMAPAL_fmap : thm
    val FUN_fmap_thm : thm
    val OPTION_FLAT : thm
    val OPTION_FLAT_ind : thm
    val ORL : thm
    val ORL_DRESTRICT_COMPL_IMP : thm
    val ORL_DRESTRICT_IMP : thm
    val ORL_FMAPAL : thm
    val ORL_FUNION_IMP : thm
    val ORL_bt : thm
    val ORL_bt_ind : thm
    val ORL_bt_lb : thm
    val ORL_bt_lb_ind : thm
    val ORL_bt_lb_ub : thm
    val ORL_bt_lb_ub_ind : thm
    val ORL_bt_ub : thm
    val ORL_bt_ub_ind : thm
    val ORL_ind : thm
    val ORL_sublists : thm
    val ORL_sublists_ind : thm
    val ORWL_DRESTRICT_COMPL_THM : thm
    val ORWL_DRESTRICT_THM : thm
    val ORWL_FUNION_THM : thm
    val ORWL_bt_to_orl : thm
    val assocv : thm
    val assocv_ind : thm
    val better_bt_to_orl : thm
    val bl_to_fmap : thm
    val bl_to_fmap_ind : thm
    val bt_FST_FDOM : thm
    val bt_rplacv_cn : thm
    val bt_rplacv_cn_ind : thm
    val bt_rplacv_thm : thm
    val bt_to_fmap : thm
    val bt_to_fmap_ind : thm
    val bt_to_orl : thm
    val bt_to_orl_ID_IMP : thm
    val bt_to_orl_ac : thm
    val bt_to_orl_ac_ind : thm
    val bt_to_orl_ind : thm
    val bt_to_orl_lb : thm
    val bt_to_orl_lb_ac : thm
    val bt_to_orl_lb_ac_ind : thm
    val bt_to_orl_lb_ind : thm
    val bt_to_orl_lb_ub : thm
    val bt_to_orl_lb_ub_ac : thm
    val bt_to_orl_lb_ub_ac_ind : thm
    val bt_to_orl_lb_ub_ind : thm
    val bt_to_orl_ub : thm
    val bt_to_orl_ub_ac : thm
    val bt_to_orl_ub_ac_ind : thm
    val bt_to_orl_ub_ind : thm
    val diff_merge : thm
    val diff_merge_ind : thm
    val fmap_FDOM : thm
    val fmap_FDOM_rec : thm
    val fmap_ORWL_thm : thm
    val incr_merge : thm
    val incr_merge_ind : thm
    val inter_merge : thm
    val inter_merge_ind : thm
    val list_rplacv_cn : thm
    val list_rplacv_cn_ind : thm
    val list_rplacv_thm : thm
    val merge : thm
    val merge_ind : thm
    val merge_out : thm
    val merge_out_ind : thm
    val o_f_bt_map : thm
    val o_f_fmap : thm
    val optry_list : thm
    val optry_list_ind : thm

  val fmapal_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [enumeral] Parent theory of "fmapal"

   [finite_map] Parent theory of "fmapal"

   [AP_SND]  Definition

      |- !f a b. AP_SND f (a,b) = (a,f b)

   [OFU]  Definition

      |- !cmp f g.
           OFU cmp f g = DRESTRICT f {x | LESS_ALL cmp x (FDOM g)} FUNION g

   [OPTION_FLAT_primitive]  Definition

      |- OPTION_FLAT =
         WFREC (@R. WF R /\ (!l. R l (NONE::l)) /\ !a l. R l (SOME a::l))
           (\OPTION_FLAT a'.
              case a' of
                [] => I []
              | NONE::l => I (OPTION_FLAT l)
              | SOME a::l => I (a ++ OPTION_FLAT l))

   [OPTION_UPDATE]  Definition

      |- !f g x. OPTION_UPDATE f g x = optry (f x) (g x)

   [ORL_bt_curried]  Definition

      |- !x x1. ORL_bt x x1 <=> ORL_bt_tupled (x,x1)

   [ORL_bt_lb_curried]  Definition

      |- !x x1 x2. ORL_bt_lb x x1 x2 <=> ORL_bt_lb_tupled (x,x1,x2)

   [ORL_bt_lb_tupled_primitive]  Definition

      |- ORL_bt_lb_tupled =
         WFREC
           (@R.
              WF R /\ !y l lb r x cmp. R (cmp,x,r) (cmp,lb,node l (x,y) r))
           (\ORL_bt_lb_tupled a.
              case a of
                (cmp,lb,nt) => I T
              | (cmp,lb,node l (x,y) r) =>
                  I
                    (ORL_bt_lb_ub cmp lb l x /\
                     ORL_bt_lb_tupled (cmp,x,r)))

   [ORL_bt_lb_ub_curried]  Definition

      |- !x x1 x2 x3.
           ORL_bt_lb_ub x x1 x2 x3 <=> ORL_bt_lb_ub_tupled (x,x1,x2,x3)

   [ORL_bt_lb_ub_tupled_primitive]  Definition

      |- ORL_bt_lb_ub_tupled =
         WFREC
           (@R.
              WF R /\
              (!ub r y x l lb cmp.
                 R (cmp,lb,l,x) (cmp,lb,node l (x,y) r,ub)) /\
              !y l lb ub r x cmp.
                R (cmp,x,r,ub) (cmp,lb,node l (x,y) r,ub))
           (\ORL_bt_lb_ub_tupled a.
              case a of
                (cmp,lb,nt,ub) => I (apto cmp lb ub = LESS)
              | (cmp,lb,node l (x,y) r,ub) =>
                  I
                    (ORL_bt_lb_ub_tupled (cmp,lb,l,x) /\
                     ORL_bt_lb_ub_tupled (cmp,x,r,ub)))

   [ORL_bt_tupled_primitive]  Definition

      |- ORL_bt_tupled =
         WFREC (@R. WF R)
           (\ORL_bt_tupled a.
              case a of
                (cmp,nt) => I T
              | (cmp,node l (x,y) r) =>
                  I (ORL_bt_ub cmp l x /\ ORL_bt_lb cmp x r))

   [ORL_bt_ub_curried]  Definition

      |- !x x1 x2. ORL_bt_ub x x1 x2 <=> ORL_bt_ub_tupled (x,x1,x2)

   [ORL_bt_ub_tupled_primitive]  Definition

      |- ORL_bt_ub_tupled =
         WFREC
           (@R.
              WF R /\ !ub r y x l cmp. R (cmp,l,x) (cmp,node l (x,y) r,ub))
           (\ORL_bt_ub_tupled a.
              case a of
                (cmp,nt,ub) => I T
              | (cmp,node l (x,y) r,ub) =>
                  I
                    (ORL_bt_ub_tupled (cmp,l,x) /\
                     ORL_bt_lb_ub cmp x r ub))

   [ORL_curried]  Definition

      |- !x x1. ORL x x1 <=> ORL_tupled (x,x1)

   [ORL_sublists_curried]  Definition

      |- !x x1. ORL_sublists x x1 <=> ORL_sublists_tupled (x,x1)

   [ORL_sublists_tupled_primitive]  Definition

      |- ORL_sublists_tupled =
         WFREC
           (@R.
              WF R /\ (!lol cmp. R (cmp,lol) (cmp,NONE::lol)) /\
              !m lol cmp. R (cmp,lol) (cmp,SOME m::lol))
           (\ORL_sublists_tupled a.
              case a of
                (cmp,[]) => I T
              | (cmp,NONE::lol) => I (ORL_sublists_tupled (cmp,lol))
              | (cmp,SOME m::lol) =>
                  I (ORL cmp m /\ ORL_sublists_tupled (cmp,lol)))

   [ORL_tupled_primitive]  Definition

      |- ORL_tupled =
         WFREC (@R. WF R /\ !b a l cmp. R (cmp,l) (cmp,(a,b)::l))
           (\ORL_tupled a'.
              case a' of
                (cmp,[]) => I T
              | (cmp,(a,b)::l) =>
                  I
                    (ORL_tupled (cmp,l) /\
                     !p q. MEM (p,q) l ==> (apto cmp a p = LESS)))

   [ORWL]  Definition

      |- !cmp f l. ORWL cmp f l <=> (f = fmap l) /\ ORL cmp l

   [UFO]  Definition

      |- !cmp f g.
           UFO cmp f g =
           f FUNION
           DRESTRICT g {y | !z. z IN FDOM f ==> (apto cmp z y = LESS)}

   [assocv_curried]  Definition

      |- !x x1. assocv x x1 = assocv_tupled (x,x1)

   [assocv_tupled_primitive]  Definition

      |- assocv_tupled =
         WFREC (@R. WF R /\ !y l x a. a <> x ==> R (l,a) ((x,y)::l,a))
           (\assocv_tupled a'.
              case a' of
                ([],a) => I NONE
              | ((x,y)::l,a) =>
                  I (if a = x then SOME y else assocv_tupled (l,a)))

   [bl_to_fmap_curried]  Definition

      |- !x x1. bl_to_fmap x x1 = bl_to_fmap_tupled (x,x1)

   [bl_to_fmap_tupled_primitive]  Definition

      |- bl_to_fmap_tupled =
         WFREC
           (@R.
              WF R /\ (!b cmp. R (cmp,b) (cmp,zerbl b)) /\
              !t y x b cmp. R (cmp,b) (cmp,onebl (x,y) t b))
           (\bl_to_fmap_tupled a.
              case a of
                (cmp,nbl) => I FEMPTY
              | (cmp,zerbl b) => I (bl_to_fmap_tupled (cmp,b))
              | (cmp,onebl (x,y) t b') =>
                  I
                    (OFU cmp
                       (FEMPTY |+ (x,y) FUNION
                        DRESTRICT (FMAPAL cmp t) {z | apto cmp x z = LESS})
                       (bl_to_fmap_tupled (cmp,b'))))

   [bt_map]  Definition

      |- (!f. bt_map f nt = nt) /\
         !f l x r.
           bt_map f (node l x r) = node (bt_map f l) (f x) (bt_map f r)

   [bt_rplacv_cn_curried]  Definition

      |- !x x1 x2 x3.
           bt_rplacv_cn x x1 x2 x3 = bt_rplacv_cn_tupled (x,x1,x2,x3)

   [bt_rplacv_cn_tupled_primitive]  Definition

      |- bt_rplacv_cn_tupled =
         WFREC
           (@R.
              WF R /\
              (!z l cn r y w x cmp.
                 (apto cmp x w = GREATER) ==>
                 R (cmp,(x,y),r,(\m. cn (node l (w,z) m)))
                   (cmp,(x,y),node l (w,z) r,cn)) /\
              !r z cn l y w x cmp.
                (apto cmp x w = LESS) ==>
                R (cmp,(x,y),l,(\m. cn (node m (w,z) r)))
                  (cmp,(x,y),node l (w,z) r,cn))
           (\bt_rplacv_cn_tupled a.
              case a of
                (cmp,(x,y),nt,cn) => I nt
              | (cmp,(x,y),node l (w,z) r,cn) =>
                  I
                    (case apto cmp x w of
                       LESS =>
                         bt_rplacv_cn_tupled
                           (cmp,(x,y),l,(\m. cn (node m (w,z) r)))
                     | EQUAL => cn (node l (x,y) r)
                     | GREATER =>
                         bt_rplacv_cn_tupled
                           (cmp,(x,y),r,(\m. cn (node l (w,z) m)))))

   [bt_to_fmap_curried]  Definition

      |- !x x1. FMAPAL x x1 = bt_to_fmap_tupled (x,x1)

   [bt_to_fmap_lb]  Definition

      |- !cmp lb t.
           bt_to_fmap_lb cmp lb t =
           DRESTRICT (FMAPAL cmp t) {x | apto cmp lb x = LESS}

   [bt_to_fmap_lb_ub]  Definition

      |- !cmp lb t ub.
           bt_to_fmap_lb_ub cmp lb t ub =
           DRESTRICT (FMAPAL cmp t)
             {x | (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS)}

   [bt_to_fmap_tupled_primitive]  Definition

      |- bt_to_fmap_tupled =
         WFREC
           (@R.
              WF R /\ (!r v x l cmp. R (cmp,l) (cmp,node l (x,v) r)) /\
              !v x l r cmp. R (cmp,r) (cmp,node l (x,v) r))
           (\bt_to_fmap_tupled a.
              case a of
                (cmp,nt) => I FEMPTY
              | (cmp,node l (x,v) r) =>
                  I
                    (DRESTRICT (bt_to_fmap_tupled (cmp,l))
                       {y | apto cmp y x = LESS} FUNION
                     FEMPTY |+ (x,v) FUNION
                     DRESTRICT (bt_to_fmap_tupled (cmp,r))
                       {z | apto cmp x z = LESS}))

   [bt_to_fmap_ub]  Definition

      |- !cmp t ub.
           bt_to_fmap_ub cmp t ub =
           DRESTRICT (FMAPAL cmp t) {x | apto cmp x ub = LESS}

   [bt_to_orl_ac_curried]  Definition

      |- !x x1 x2. bt_to_orl_ac x x1 x2 = bt_to_orl_ac_tupled (x,x1,x2)

   [bt_to_orl_ac_tupled_primitive]  Definition

      |- bt_to_orl_ac_tupled =
         WFREC (@R. WF R)
           (\bt_to_orl_ac_tupled a.
              case a of
                (cmp,nt,m) => I m
              | (cmp,node l (x,y) r,m) =>
                  I
                    (bt_to_orl_ub_ac cmp l x
                       ((x,y)::bt_to_orl_lb_ac cmp x r m)))

   [bt_to_orl_curried]  Definition

      |- !x x1. bt_to_orl x x1 = bt_to_orl_tupled (x,x1)

   [bt_to_orl_lb_ac_curried]  Definition

      |- !x x1 x2 x3.
           bt_to_orl_lb_ac x x1 x2 x3 = bt_to_orl_lb_ac_tupled (x,x1,x2,x3)

   [bt_to_orl_lb_ac_tupled_primitive]  Definition

      |- bt_to_orl_lb_ac_tupled =
         WFREC
           (@R.
              WF R /\
              (!y l m r x lb cmp.
                 apto cmp lb x <> LESS ==>
                 R (cmp,lb,r,m) (cmp,lb,node l (x,y) r,m)) /\
              !y l m r x lb cmp.
                (apto cmp lb x = LESS) ==>
                R (cmp,x,r,m) (cmp,lb,node l (x,y) r,m))
           (\bt_to_orl_lb_ac_tupled a.
              case a of
                (cmp,lb,nt,m) => I m
              | (cmp,lb,node l (x,y) r,m) =>
                  I
                    (if apto cmp lb x = LESS then
                       bt_to_orl_lb_ub_ac cmp lb l x
                         ((x,y)::bt_to_orl_lb_ac_tupled (cmp,x,r,m))
                     else bt_to_orl_lb_ac_tupled (cmp,lb,r,m)))

   [bt_to_orl_lb_curried]  Definition

      |- !x x1 x2. bt_to_orl_lb x x1 x2 = bt_to_orl_lb_tupled (x,x1,x2)

   [bt_to_orl_lb_tupled_primitive]  Definition

      |- bt_to_orl_lb_tupled =
         WFREC
           (@R.
              WF R /\
              (!y l r x lb cmp.
                 apto cmp lb x <> LESS ==>
                 R (cmp,lb,r) (cmp,lb,node l (x,y) r)) /\
              !y l r x lb cmp.
                (apto cmp lb x = LESS) ==>
                R (cmp,x,r) (cmp,lb,node l (x,y) r))
           (\bt_to_orl_lb_tupled a.
              case a of
                (cmp,lb,nt) => I []
              | (cmp,lb,node l (x,y) r) =>
                  I
                    (if apto cmp lb x = LESS then
                       bt_to_orl_lb_ub cmp lb l x ++ [(x,y)] ++
                       bt_to_orl_lb_tupled (cmp,x,r)
                     else bt_to_orl_lb_tupled (cmp,lb,r)))

   [bt_to_orl_lb_ub_ac_curried]  Definition

      |- !x x1 x2 x3 x4.
           bt_to_orl_lb_ub_ac x x1 x2 x3 x4 =
           bt_to_orl_lb_ub_ac_tupled (x,x1,x2,x3,x4)

   [bt_to_orl_lb_ub_ac_tupled_AUX]  Definition

      |- !R.
           bt_to_orl_lb_ub_ac_tupled_aux R =
           WFREC R
             (\bt_to_orl_lb_ub_ac_tupled a.
                case a of
                  (cmp,lb,nt,ub,m) => I m
                | (cmp,lb,node l (x,y) r,ub,m) =>
                    I
                      (if apto cmp lb x = LESS then
                         if apto cmp x ub = LESS then
                           bt_to_orl_lb_ub_ac_tupled
                             (cmp,lb,l,x,
                              (x,y)::
                                  bt_to_orl_lb_ub_ac_tupled (cmp,x,r,ub,m))
                         else bt_to_orl_lb_ub_ac_tupled (cmp,lb,l,ub,m)
                       else bt_to_orl_lb_ub_ac_tupled (cmp,lb,r,ub,m)))

   [bt_to_orl_lb_ub_ac_tupled_primitive]  Definition

      |- bt_to_orl_lb_ub_ac_tupled =
         bt_to_orl_lb_ub_ac_tupled_aux
           (@R.
              WF R /\
              (!y l m ub r x lb cmp.
                 apto cmp lb x <> LESS ==>
                 R (cmp,lb,r,ub,m) (cmp,lb,node l (x,y) r,ub,m)) /\
              (!r y m l ub x lb cmp.
                 (apto cmp lb x = LESS) /\ apto cmp x ub <> LESS ==>
                 R (cmp,lb,l,ub,m) (cmp,lb,node l (x,y) r,ub,m)) /\
              (!m r y l ub x lb cmp.
                 (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
                 R
                   (cmp,lb,l,x,
                    (x,y)::bt_to_orl_lb_ub_ac_tupled_aux R (cmp,x,r,ub,m))
                   (cmp,lb,node l (x,y) r,ub,m)) /\
              !y l m r ub x lb cmp.
                (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
                R (cmp,x,r,ub,m) (cmp,lb,node l (x,y) r,ub,m))

   [bt_to_orl_lb_ub_curried]  Definition

      |- !x x1 x2 x3.
           bt_to_orl_lb_ub x x1 x2 x3 = bt_to_orl_lb_ub_tupled (x,x1,x2,x3)

   [bt_to_orl_lb_ub_tupled_primitive]  Definition

      |- bt_to_orl_lb_ub_tupled =
         WFREC
           (@R.
              WF R /\
              (!y l ub r x lb cmp.
                 apto cmp lb x <> LESS ==>
                 R (cmp,lb,r,ub) (cmp,lb,node l (x,y) r,ub)) /\
              (!r y l ub x lb cmp.
                 (apto cmp lb x = LESS) /\ apto cmp x ub <> LESS ==>
                 R (cmp,lb,l,ub) (cmp,lb,node l (x,y) r,ub)) /\
              (!r y l ub x lb cmp.
                 (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
                 R (cmp,lb,l,x) (cmp,lb,node l (x,y) r,ub)) /\
              !y l r ub x lb cmp.
                (apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
                R (cmp,x,r,ub) (cmp,lb,node l (x,y) r,ub))
           (\bt_to_orl_lb_ub_tupled a.
              case a of
                (cmp,lb,nt,ub) => I []
              | (cmp,lb,node l (x,y) r,ub) =>
                  I
                    (if apto cmp lb x = LESS then
                       if apto cmp x ub = LESS then
                         bt_to_orl_lb_ub_tupled (cmp,lb,l,x) ++ [(x,y)] ++
                         bt_to_orl_lb_ub_tupled (cmp,x,r,ub)
                       else bt_to_orl_lb_ub_tupled (cmp,lb,l,ub)
                     else bt_to_orl_lb_ub_tupled (cmp,lb,r,ub)))

   [bt_to_orl_tupled_primitive]  Definition

      |- bt_to_orl_tupled =
         WFREC (@R. WF R)
           (\bt_to_orl_tupled a.
              case a of
                (cmp,nt) => I []
              | (cmp,node l (x,y) r) =>
                  I
                    (bt_to_orl_ub cmp l x ++ [(x,y)] ++
                     bt_to_orl_lb cmp x r))

   [bt_to_orl_ub_ac_curried]  Definition

      |- !x x1 x2 x3.
           bt_to_orl_ub_ac x x1 x2 x3 = bt_to_orl_ub_ac_tupled (x,x1,x2,x3)

   [bt_to_orl_ub_ac_tupled_primitive]  Definition

      |- bt_to_orl_ub_ac_tupled =
         WFREC
           (@R.
              WF R /\
              (!r y m l ub x cmp.
                 apto cmp x ub <> LESS ==>
                 R (cmp,l,ub,m) (cmp,node l (x,y) r,ub,m)) /\
              !m r y l ub x cmp.
                (apto cmp x ub = LESS) ==>
                R (cmp,l,x,(x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)
                  (cmp,node l (x,y) r,ub,m))
           (\bt_to_orl_ub_ac_tupled a.
              case a of
                (cmp,nt,ub,m) => I m
              | (cmp,node l (x,y) r,ub,m) =>
                  I
                    (if apto cmp x ub = LESS then
                       bt_to_orl_ub_ac_tupled
                         (cmp,l,x,(x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)
                     else bt_to_orl_ub_ac_tupled (cmp,l,ub,m)))

   [bt_to_orl_ub_curried]  Definition

      |- !x x1 x2. bt_to_orl_ub x x1 x2 = bt_to_orl_ub_tupled (x,x1,x2)

   [bt_to_orl_ub_tupled_primitive]  Definition

      |- bt_to_orl_ub_tupled =
         WFREC
           (@R.
              WF R /\
              (!r y l ub x cmp.
                 apto cmp x ub <> LESS ==>
                 R (cmp,l,ub) (cmp,node l (x,y) r,ub)) /\
              !r y l ub x cmp.
                (apto cmp x ub = LESS) ==>
                R (cmp,l,x) (cmp,node l (x,y) r,ub))
           (\bt_to_orl_ub_tupled a.
              case a of
                (cmp,nt,ub) => I []
              | (cmp,node l (x,y) r,ub) =>
                  I
                    (if apto cmp x ub = LESS then
                       bt_to_orl_ub_tupled (cmp,l,x) ++ [(x,y)] ++
                       bt_to_orl_lb_ub cmp x r ub
                     else bt_to_orl_ub_tupled (cmp,l,ub)))

   [diff_merge_curried]  Definition

      |- !x x1 x2. diff_merge x x1 x2 = diff_merge_tupled (x,x1,x2)

   [diff_merge_tupled_primitive]  Definition

      |- diff_merge_tupled =
         WFREC
           (@R.
              WF R /\
              (!b m l y a cmp.
                 (apto cmp a y = EQUAL) ==>
                 R (cmp,l,m) (cmp,(a,b)::l,y::m)) /\
              (!m l b y a cmp.
                 (apto cmp a y = GREATER) ==>
                 R (cmp,(a,b)::l,m) (cmp,(a,b)::l,y::m)) /\
              !b m l y a cmp.
                (apto cmp a y = LESS) ==>
                R (cmp,l,y::m) (cmp,(a,b)::l,y::m))
           (\diff_merge_tupled a'.
              case a' of
                (cmp,[],v3) => I []
              | (cmp,(a,b)::l,[]) => I ((a,b)::l)
              | (cmp,(a,b)::l,y::m) =>
                  I
                    (case apto cmp a y of
                       LESS => (a,b)::diff_merge_tupled (cmp,l,y::m)
                     | EQUAL => diff_merge_tupled (cmp,l,m)
                     | GREATER => diff_merge_tupled (cmp,(a,b)::l,m)))

   [fmap]  Definition

      |- !l. fmap l = FEMPTY |++ REVERSE l

   [incr_build]  Definition

      |- (!cmp. incr_build cmp [] = []) /\
         !cmp ab l.
           incr_build cmp (ab::l) = incr_merge cmp [ab] (incr_build cmp l)

   [incr_flat]  Definition

      |- !cmp lol. incr_flat cmp lol = merge_out cmp [] lol

   [incr_merge_curried]  Definition

      |- !x x1 x2. incr_merge x x1 x2 = incr_merge_tupled (x,x1,x2)

   [incr_merge_tupled_primitive]  Definition

      |- incr_merge_tupled =
         WFREC
           (@R.
              WF R /\
              !lol m l cmp. R (cmp,merge cmp l m,lol) (cmp,l,SOME m::lol))
           (\incr_merge_tupled a.
              case a of
                (cmp,l,[]) => I [SOME l]
              | (cmp,l,NONE::lol) => I (SOME l::lol)
              | (cmp,l,SOME m::lol) =>
                  I (NONE::incr_merge_tupled (cmp,merge cmp l m,lol)))

   [incr_sort]  Definition

      |- !cmp l. incr_sort cmp l = merge_out cmp [] (incr_build cmp l)

   [inter_merge_curried]  Definition

      |- !x x1 x2. inter_merge x x1 x2 = inter_merge_tupled (x,x1,x2)

   [inter_merge_tupled_primitive]  Definition

      |- inter_merge_tupled =
         WFREC
           (@R.
              WF R /\
              (!b m l y a cmp.
                 (apto cmp a y = EQUAL) ==>
                 R (cmp,l,m) (cmp,(a,b)::l,y::m)) /\
              (!m l b y a cmp.
                 (apto cmp a y = GREATER) ==>
                 R (cmp,(a,b)::l,m) (cmp,(a,b)::l,y::m)) /\
              !b m l y a cmp.
                (apto cmp a y = LESS) ==>
                R (cmp,l,y::m) (cmp,(a,b)::l,y::m))
           (\inter_merge_tupled a'.
              case a' of
                (cmp,(a,b)::l,y::m) =>
                  I
                    (case apto cmp a y of
                       LESS => inter_merge_tupled (cmp,l,y::m)
                     | EQUAL => (a,b)::inter_merge_tupled (cmp,l,m)
                     | GREATER => inter_merge_tupled (cmp,(a,b)::l,m))
              | _ => I [])

   [list_rplacv_cn_curried]  Definition

      |- !x x1 x2. list_rplacv_cn x x1 x2 = list_rplacv_cn_tupled (x,x1,x2)

   [list_rplacv_cn_tupled_primitive]  Definition

      |- list_rplacv_cn_tupled =
         WFREC
           (@R.
              WF R /\
              !z cn l y w x.
                x <> w ==>
                R ((x,y),l,(\m. cn ((w,z)::m))) ((x,y),(w,z)::l,cn))
           (\list_rplacv_cn_tupled a.
              case a of
                ((x,y),[],cn) => I []
              | ((x,y),(w,z)::l,cn) =>
                  I
                    (if x = w then cn ((x,y)::l)
                     else
                       list_rplacv_cn_tupled
                         ((x,y),l,(\m. cn ((w,z)::m)))))

   [merge_curried]  Definition

      |- !x x1 x2. merge x x1 x2 = merge_tupled (x,x1,x2)

   [merge_out_curried]  Definition

      |- !x x1 x2. merge_out x x1 x2 = merge_out_tupled (x,x1,x2)

   [merge_out_tupled_primitive]  Definition

      |- merge_out_tupled =
         WFREC
           (@R.
              WF R /\ (!lol l cmp. R (cmp,l,lol) (cmp,l,NONE::lol)) /\
              !lol m l cmp. R (cmp,merge cmp l m,lol) (cmp,l,SOME m::lol))
           (\merge_out_tupled a.
              case a of
                (cmp,l,[]) => I l
              | (cmp,l,NONE::lol) => I (merge_out_tupled (cmp,l,lol))
              | (cmp,l,SOME m::lol) =>
                  I (merge_out_tupled (cmp,merge cmp l m,lol)))

   [merge_tupled_primitive]  Definition

      |- merge_tupled =
         WFREC
           (@R.
              WF R /\
              (!b2 b1 l2 l1 a2 a1 cmp.
                 (apto cmp a1 a2 = EQUAL) ==>
                 R (cmp,l1,l2) (cmp,(a1,b1)::l1,(a2,b2)::l2)) /\
              (!b2 l2 l1 b1 a2 a1 cmp.
                 (apto cmp a1 a2 = GREATER) ==>
                 R (cmp,(a1,b1)::l1,l2) (cmp,(a1,b1)::l1,(a2,b2)::l2)) /\
              !b1 l2 b2 l1 a2 a1 cmp.
                (apto cmp a1 a2 = LESS) ==>
                R (cmp,l1,(a2,b2)::l2) (cmp,(a1,b1)::l1,(a2,b2)::l2))
           (\merge_tupled a.
              case a of
                (cmp,[],l) => I l
              | (cmp,v6::l1,[]) => I (v6::l1)
              | (cmp,(a1,b1)::l1,(a2,b2)::l2) =>
                  I
                    (case apto cmp a1 a2 of
                       LESS => (a1,b1)::merge_tupled (cmp,l1,(a2,b2)::l2)
                     | EQUAL => (a1,b1)::merge_tupled (cmp,l1,l2)
                     | GREATER =>
                         (a2,b2)::merge_tupled (cmp,(a1,b1)::l1,l2)))

   [optry]  Definition

      |- (!p q. optry (SOME p) q = SOME p) /\ !q. optry NONE q = q

   [optry_list_curried]  Definition

      |- !x x1. optry_list x x1 = optry_list_tupled (x,x1)

   [optry_list_tupled_primitive]  Definition

      |- optry_list_tupled =
         WFREC
           (@R.
              WF R /\ (!l f. R (f,l) (f,NONE::l)) /\
              !z l f. R (f,l) (f,SOME z::l))
           (\optry_list_tupled a.
              case a of
                (f,[]) => I NONE
              | (f,NONE::l) => I (optry_list_tupled (f,l))
              | (f,SOME z::l) => I (optry (f z) (optry_list_tupled (f,l))))

   [unlookup]  Definition

      |- !f. unlookup f = FUN_FMAP (THE o f) (IS_SOME o f)

   [vcossa]  Definition

      |- !a l. vcossa a l = assocv l a

   [FAPPLY_fmap_CONS]  Theorem

      |- !x y z l. fmap ((y,z)::l) ' x = if x = y then z else fmap l ' x

   [FAPPLY_fmap_NIL]  Theorem

      |- !x. fmap [] ' x = FEMPTY ' x

   [FAPPLY_node]  Theorem

      |- !cmp x l a b r.
           FMAPAL cmp (node l (a,b) r) ' x =
           case apto cmp x a of
             LESS => FMAPAL cmp l ' x
           | EQUAL => b
           | GREATER => FMAPAL cmp r ' x

   [FAPPLY_nt]  Theorem

      |- !cmp x. FMAPAL cmp nt ' x = FEMPTY ' x

   [FMAPAL_FDOM_THM]  Theorem

      |- (!cmp x. x IN FDOM (FMAPAL cmp nt) <=> F) /\
         !cmp x a b l r.
           x IN FDOM (FMAPAL cmp (node l (a,b) r)) <=>
           case apto cmp x a of
             LESS => x IN FDOM (FMAPAL cmp l)
           | EQUAL => T
           | GREATER => x IN FDOM (FMAPAL cmp r)

   [FMAPAL_fmap]  Theorem

      |- !cmp l. fmap l = FMAPAL cmp (list_to_bt (incr_sort cmp l))

   [FUN_fmap_thm]  Theorem

      |- !f l. fmap (MAP (\x. (x,f x)) l) = FUN_FMAP f (set l)

   [OPTION_FLAT]  Theorem

      |- (OPTION_FLAT [] = []) /\
         (!l. OPTION_FLAT (NONE::l) = OPTION_FLAT l) /\
         !l a. OPTION_FLAT (SOME a::l) = a ++ OPTION_FLAT l

   [OPTION_FLAT_ind]  Theorem

      |- !P.
           P [] /\ (!l. P l ==> P (NONE::l)) /\
           (!a l. P l ==> P (SOME a::l)) ==>
           !v. P v

   [ORL]  Theorem

      |- (!cmp. ORL cmp [] <=> T) /\
         !l cmp b a.
           ORL cmp ((a,b)::l) <=>
           ORL cmp l /\ !p q. MEM (p,q) l ==> (apto cmp a p = LESS)

   [ORL_DRESTRICT_COMPL_IMP]  Theorem

      |- !cmp l.
           ORL cmp l ==>
           !m.
             OL cmp m ==>
             ORL cmp (diff_merge cmp l m) /\
             (fmap (diff_merge cmp l m) =
              DRESTRICT (fmap l) (COMPL (set m)))

   [ORL_DRESTRICT_IMP]  Theorem

      |- !cmp l.
           ORL cmp l ==>
           !m.
             OL cmp m ==>
             ORL cmp (inter_merge cmp l m) /\
             (fmap (inter_merge cmp l m) = DRESTRICT (fmap l) (set m))

   [ORL_FMAPAL]  Theorem

      |- !cmp l. ORL cmp l ==> (fmap l = FMAPAL cmp (list_to_bt l))

   [ORL_FUNION_IMP]  Theorem

      |- !cmp l.
           ORL cmp l ==>
           !m.
             ORL cmp m ==>
             ORL cmp (merge cmp l m) /\
             (fmap (merge cmp l m) = fmap l FUNION fmap m)

   [ORL_bt]  Theorem

      |- (ORL_bt cmp nt <=> T) /\
         (ORL_bt cmp (node l (x,y) r) <=>
          ORL_bt_ub cmp l x /\ ORL_bt_lb cmp x r)

   [ORL_bt_ind]  Theorem

      |- !P.
           (!cmp. P cmp nt) /\ (!cmp l x y r. P cmp (node l (x,y) r)) ==>
           !v v1. P v v1

   [ORL_bt_lb]  Theorem

      |- (!lb cmp. ORL_bt_lb cmp lb nt <=> T) /\
         !y x r lb l cmp.
           ORL_bt_lb cmp lb (node l (x,y) r) <=>
           ORL_bt_lb_ub cmp lb l x /\ ORL_bt_lb cmp x r

   [ORL_bt_lb_ind]  Theorem

      |- !P.
           (!cmp lb. P cmp lb nt) /\
           (!cmp lb l x y r. P cmp x r ==> P cmp lb (node l (x,y) r)) ==>
           !v v1 v2. P v v1 v2

   [ORL_bt_lb_ub]  Theorem

      |- (!ub lb cmp.
            ORL_bt_lb_ub cmp lb nt ub <=> (apto cmp lb ub = LESS)) /\
         !y x ub r lb l cmp.
           ORL_bt_lb_ub cmp lb (node l (x,y) r) ub <=>
           ORL_bt_lb_ub cmp lb l x /\ ORL_bt_lb_ub cmp x r ub

   [ORL_bt_lb_ub_ind]  Theorem

      |- !P.
           (!cmp lb ub. P cmp lb nt ub) /\
           (!cmp lb l x y r ub.
              P cmp lb l x /\ P cmp x r ub ==>
              P cmp lb (node l (x,y) r) ub) ==>
           !v v1 v2 v3. P v v1 v2 v3

   [ORL_bt_ub]  Theorem

      |- (!ub cmp. ORL_bt_ub cmp nt ub <=> T) /\
         !y x ub r l cmp.
           ORL_bt_ub cmp (node l (x,y) r) ub <=>
           ORL_bt_ub cmp l x /\ ORL_bt_lb_ub cmp x r ub

   [ORL_bt_ub_ind]  Theorem

      |- !P.
           (!cmp ub. P cmp nt ub) /\
           (!cmp l x y r ub. P cmp l x ==> P cmp (node l (x,y) r) ub) ==>
           !v v1 v2. P v v1 v2

   [ORL_ind]  Theorem

      |- !P.
           (!cmp. P cmp []) /\
           (!cmp a b l. P cmp l ==> P cmp ((a,b)::l)) ==>
           !v v1. P v v1

   [ORL_sublists]  Theorem

      |- (!cmp. ORL_sublists cmp [] <=> T) /\
         (!lol cmp.
            ORL_sublists cmp (NONE::lol) <=> ORL_sublists cmp lol) /\
         !m lol cmp.
           ORL_sublists cmp (SOME m::lol) <=>
           ORL cmp m /\ ORL_sublists cmp lol

   [ORL_sublists_ind]  Theorem

      |- !P.
           (!cmp. P cmp []) /\
           (!cmp lol. P cmp lol ==> P cmp (NONE::lol)) /\
           (!cmp m lol. P cmp lol ==> P cmp (SOME m::lol)) ==>
           !v v1. P v v1

   [ORWL_DRESTRICT_COMPL_THM]  Theorem

      |- !cmp s l t m.
           ORWL cmp s l /\ OWL cmp t m ==>
           ORWL cmp (DRESTRICT s (COMPL t)) (diff_merge cmp l m)

   [ORWL_DRESTRICT_THM]  Theorem

      |- !cmp s l t m.
           ORWL cmp s l /\ OWL cmp t m ==>
           ORWL cmp (DRESTRICT s t) (inter_merge cmp l m)

   [ORWL_FUNION_THM]  Theorem

      |- !cmp s l t m.
           ORWL cmp s l /\ ORWL cmp t m ==>
           ORWL cmp (s FUNION t) (merge cmp l m)

   [ORWL_bt_to_orl]  Theorem

      |- !cmp t. ORWL cmp (FMAPAL cmp t) (bt_to_orl cmp t)

   [assocv]  Theorem

      |- (!a. assocv [] a = NONE) /\
         !y x l a.
           assocv ((x,y)::l) a = if a = x then SOME y else assocv l a

   [assocv_ind]  Theorem

      |- !P.
           (!a. P [] a) /\
           (!x y l a. (a <> x ==> P l a) ==> P ((x,y)::l) a) ==>
           !v v1. P v v1

   [better_bt_to_orl]  Theorem

      |- !cmp t.
           bt_to_orl cmp t =
           if ORL_bt cmp t then bt_to_list_ac t []
           else bt_to_orl_ac cmp t []

   [bl_to_fmap]  Theorem

      |- (!cmp. bl_to_fmap cmp nbl = FEMPTY) /\
         (!cmp b. bl_to_fmap cmp (zerbl b) = bl_to_fmap cmp b) /\
         !y x t cmp b.
           bl_to_fmap cmp (onebl (x,y) t b) =
           OFU cmp
             (FEMPTY |+ (x,y) FUNION
              DRESTRICT (FMAPAL cmp t) {z | apto cmp x z = LESS})
             (bl_to_fmap cmp b)

   [bl_to_fmap_ind]  Theorem

      |- !P.
           (!cmp. P cmp nbl) /\ (!cmp b. P cmp b ==> P cmp (zerbl b)) /\
           (!cmp x y t b. P cmp b ==> P cmp (onebl (x,y) t b)) ==>
           !v v1. P v v1

   [bt_FST_FDOM]  Theorem

      |- !cmp t. FDOM (FMAPAL cmp t) = ENUMERAL cmp (bt_map FST t)

   [bt_rplacv_cn]  Theorem

      |- (!y x cn cmp. bt_rplacv_cn cmp (x,y) nt cn = nt) /\
         !z y x w r l cn cmp.
           bt_rplacv_cn cmp (x,y) (node l (w,z) r) cn =
           case apto cmp x w of
             LESS => bt_rplacv_cn cmp (x,y) l (\m. cn (node m (w,z) r))
           | EQUAL => cn (node l (x,y) r)
           | GREATER => bt_rplacv_cn cmp (x,y) r (\m. cn (node l (w,z) m))

   [bt_rplacv_cn_ind]  Theorem

      |- !P.
           (!cmp x y cn. P cmp (x,y) nt cn) /\
           (!cmp x y l w z r cn.
              ((apto cmp x w = GREATER) ==>
               P cmp (x,y) r (\m. cn (node l (w,z) m))) /\
              ((apto cmp x w = LESS) ==>
               P cmp (x,y) l (\m. cn (node m (w,z) r))) ==>
              P cmp (x,y) (node l (w,z) r) cn) ==>
           !v v1 v2 v3 v4. P v (v1,v2) v3 v4

   [bt_rplacv_thm]  Theorem

      |- !cmp x y t.
           (let ans = bt_rplacv_cn cmp (x,y) t (\m. m)
            in
              if ans = nt then x NOTIN FDOM (FMAPAL cmp t)
              else
                x IN FDOM (FMAPAL cmp t) /\
                (FMAPAL cmp t |+ (x,y) = FMAPAL cmp ans))

   [bt_to_fmap]  Theorem

      |- (!cmp. FMAPAL cmp nt = FEMPTY) /\
         !x v r l cmp.
           FMAPAL cmp (node l (x,v) r) =
           DRESTRICT (FMAPAL cmp l) {y | apto cmp y x = LESS} FUNION
           FEMPTY |+ (x,v) FUNION
           DRESTRICT (FMAPAL cmp r) {z | apto cmp x z = LESS}

   [bt_to_fmap_ind]  Theorem

      |- !P.
           (!cmp. P cmp nt) /\
           (!cmp l x v r.
              P cmp l /\ P cmp r ==> P cmp (node l (x,v) r)) ==>
           !v v1. P v v1

   [bt_to_orl]  Theorem

      |- (bt_to_orl cmp nt = []) /\
         (bt_to_orl cmp (node l (x,y) r) =
          bt_to_orl_ub cmp l x ++ [(x,y)] ++ bt_to_orl_lb cmp x r)

   [bt_to_orl_ID_IMP]  Theorem

      |- !cmp l. ORL cmp l ==> (bt_to_orl cmp (list_to_bt l) = l)

   [bt_to_orl_ac]  Theorem

      |- (bt_to_orl_ac cmp nt m = m) /\
         (bt_to_orl_ac cmp (node l (x,y) r) m =
          bt_to_orl_ub_ac cmp l x ((x,y)::bt_to_orl_lb_ac cmp x r m))

   [bt_to_orl_ac_ind]  Theorem

      |- !P.
           (!cmp m. P cmp nt m) /\
           (!cmp l x y r m. P cmp (node l (x,y) r) m) ==>
           !v v1 v2. P v v1 v2

   [bt_to_orl_ind]  Theorem

      |- !P.
           (!cmp. P cmp nt) /\ (!cmp l x y r. P cmp (node l (x,y) r)) ==>
           !v v1. P v v1

   [bt_to_orl_lb]  Theorem

      |- (!lb cmp. bt_to_orl_lb cmp lb nt = []) /\
         !y x r lb l cmp.
           bt_to_orl_lb cmp lb (node l (x,y) r) =
           if apto cmp lb x = LESS then
             bt_to_orl_lb_ub cmp lb l x ++ [(x,y)] ++ bt_to_orl_lb cmp x r
           else bt_to_orl_lb cmp lb r

   [bt_to_orl_lb_ac]  Theorem

      |- (!m lb cmp. bt_to_orl_lb_ac cmp lb nt m = m) /\
         !y x r m lb l cmp.
           bt_to_orl_lb_ac cmp lb (node l (x,y) r) m =
           if apto cmp lb x = LESS then
             bt_to_orl_lb_ub_ac cmp lb l x
               ((x,y)::bt_to_orl_lb_ac cmp x r m)
           else bt_to_orl_lb_ac cmp lb r m

   [bt_to_orl_lb_ac_ind]  Theorem

      |- !P.
           (!cmp lb m. P cmp lb nt m) /\
           (!cmp lb l x y r m.
              (apto cmp lb x <> LESS ==> P cmp lb r m) /\
              ((apto cmp lb x = LESS) ==> P cmp x r m) ==>
              P cmp lb (node l (x,y) r) m) ==>
           !v v1 v2 v3. P v v1 v2 v3

   [bt_to_orl_lb_ind]  Theorem

      |- !P.
           (!cmp lb. P cmp lb nt) /\
           (!cmp lb l x y r.
              (apto cmp lb x <> LESS ==> P cmp lb r) /\
              ((apto cmp lb x = LESS) ==> P cmp x r) ==>
              P cmp lb (node l (x,y) r)) ==>
           !v v1 v2. P v v1 v2

   [bt_to_orl_lb_ub]  Theorem

      |- (!ub lb cmp. bt_to_orl_lb_ub cmp lb nt ub = []) /\
         !y x ub r lb l cmp.
           bt_to_orl_lb_ub cmp lb (node l (x,y) r) ub =
           if apto cmp lb x = LESS then
             if apto cmp x ub = LESS then
               bt_to_orl_lb_ub cmp lb l x ++ [(x,y)] ++
               bt_to_orl_lb_ub cmp x r ub
             else bt_to_orl_lb_ub cmp lb l ub
           else bt_to_orl_lb_ub cmp lb r ub

   [bt_to_orl_lb_ub_ac]  Theorem

      |- (!ub m lb cmp. bt_to_orl_lb_ub_ac cmp lb nt ub m = m) /\
         !y x ub r m lb l cmp.
           bt_to_orl_lb_ub_ac cmp lb (node l (x,y) r) ub m =
           if apto cmp lb x = LESS then
             if apto cmp x ub = LESS then
               bt_to_orl_lb_ub_ac cmp lb l x
                 ((x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)
             else bt_to_orl_lb_ub_ac cmp lb l ub m
           else bt_to_orl_lb_ub_ac cmp lb r ub m

   [bt_to_orl_lb_ub_ac_ind]  Theorem

      |- !P.
           (!cmp lb ub m. P cmp lb nt ub m) /\
           (!cmp lb l x y r ub m.
              (apto cmp lb x <> LESS ==> P cmp lb r ub m) /\
              ((apto cmp lb x = LESS) /\ apto cmp x ub <> LESS ==>
               P cmp lb l ub m) /\
              ((apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
               P cmp lb l x ((x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)) /\
              ((apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
               P cmp x r ub m) ==>
              P cmp lb (node l (x,y) r) ub m) ==>
           !v v1 v2 v3 v4. P v v1 v2 v3 v4

   [bt_to_orl_lb_ub_ind]  Theorem

      |- !P.
           (!cmp lb ub. P cmp lb nt ub) /\
           (!cmp lb l x y r ub.
              (apto cmp lb x <> LESS ==> P cmp lb r ub) /\
              ((apto cmp lb x = LESS) /\ apto cmp x ub <> LESS ==>
               P cmp lb l ub) /\
              ((apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
               P cmp lb l x) /\
              ((apto cmp lb x = LESS) /\ (apto cmp x ub = LESS) ==>
               P cmp x r ub) ==>
              P cmp lb (node l (x,y) r) ub) ==>
           !v v1 v2 v3. P v v1 v2 v3

   [bt_to_orl_ub]  Theorem

      |- (!ub cmp. bt_to_orl_ub cmp nt ub = []) /\
         !y x ub r l cmp.
           bt_to_orl_ub cmp (node l (x,y) r) ub =
           if apto cmp x ub = LESS then
             bt_to_orl_ub cmp l x ++ [(x,y)] ++ bt_to_orl_lb_ub cmp x r ub
           else bt_to_orl_ub cmp l ub

   [bt_to_orl_ub_ac]  Theorem

      |- (!ub m cmp. bt_to_orl_ub_ac cmp nt ub m = m) /\
         !y x ub r m l cmp.
           bt_to_orl_ub_ac cmp (node l (x,y) r) ub m =
           if apto cmp x ub = LESS then
             bt_to_orl_ub_ac cmp l x
               ((x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)
           else bt_to_orl_ub_ac cmp l ub m

   [bt_to_orl_ub_ac_ind]  Theorem

      |- !P.
           (!cmp ub m. P cmp nt ub m) /\
           (!cmp l x y r ub m.
              (apto cmp x ub <> LESS ==> P cmp l ub m) /\
              ((apto cmp x ub = LESS) ==>
               P cmp l x ((x,y)::bt_to_orl_lb_ub_ac cmp x r ub m)) ==>
              P cmp (node l (x,y) r) ub m) ==>
           !v v1 v2 v3. P v v1 v2 v3

   [bt_to_orl_ub_ind]  Theorem

      |- !P.
           (!cmp ub. P cmp nt ub) /\
           (!cmp l x y r ub.
              (apto cmp x ub <> LESS ==> P cmp l ub) /\
              ((apto cmp x ub = LESS) ==> P cmp l x) ==>
              P cmp (node l (x,y) r) ub) ==>
           !v v1 v2. P v v1 v2

   [diff_merge]  Theorem

      |- (!cmp. diff_merge cmp [] [] = []) /\
         (!l cmp b a. diff_merge cmp ((a,b)::l) [] = (a,b)::l) /\
         (!y m cmp. diff_merge cmp [] (y::m) = []) /\
         !y m l cmp b a.
           diff_merge cmp ((a,b)::l) (y::m) =
           case apto cmp a y of
             LESS => (a,b)::diff_merge cmp l (y::m)
           | EQUAL => diff_merge cmp l m
           | GREATER => diff_merge cmp ((a,b)::l) m

   [diff_merge_ind]  Theorem

      |- !P.
           (!cmp. P cmp [] []) /\ (!cmp a b l. P cmp ((a,b)::l) []) /\
           (!cmp y m. P cmp [] (y::m)) /\
           (!cmp a b l y m.
              ((apto cmp a y = EQUAL) ==> P cmp l m) /\
              ((apto cmp a y = GREATER) ==> P cmp ((a,b)::l) m) /\
              ((apto cmp a y = LESS) ==> P cmp l (y::m)) ==>
              P cmp ((a,b)::l) (y::m)) ==>
           !v v1 v2. P v v1 v2

   [fmap_FDOM]  Theorem

      |- !l. FDOM (fmap l) = set (MAP FST l)

   [fmap_FDOM_rec]  Theorem

      |- (!x. x IN FDOM (fmap []) <=> F) /\
         !x w z l.
           x IN FDOM (fmap ((w,z)::l)) <=> (x = w) \/ x IN FDOM (fmap l)

   [fmap_ORWL_thm]  Theorem

      |- !cmp l. ORWL cmp (fmap l) (incr_sort cmp l)

   [incr_merge]  Theorem

      |- (!l cmp. incr_merge cmp l [] = [SOME l]) /\
         (!lol l cmp. incr_merge cmp l (NONE::lol) = SOME l::lol) /\
         !m lol l cmp.
           incr_merge cmp l (SOME m::lol) =
           NONE::incr_merge cmp (merge cmp l m) lol

   [incr_merge_ind]  Theorem

      |- !P.
           (!cmp l. P cmp l []) /\ (!cmp l lol. P cmp l (NONE::lol)) /\
           (!cmp l m lol.
              P cmp (merge cmp l m) lol ==> P cmp l (SOME m::lol)) ==>
           !v v1 v2. P v v1 v2

   [inter_merge]  Theorem

      |- (!cmp. inter_merge cmp [] [] = []) /\
         (!l cmp b a. inter_merge cmp ((a,b)::l) [] = []) /\
         (!y m cmp. inter_merge cmp [] (y::m) = []) /\
         !y m l cmp b a.
           inter_merge cmp ((a,b)::l) (y::m) =
           case apto cmp a y of
             LESS => inter_merge cmp l (y::m)
           | EQUAL => (a,b)::inter_merge cmp l m
           | GREATER => inter_merge cmp ((a,b)::l) m

   [inter_merge_ind]  Theorem

      |- !P.
           (!cmp. P cmp [] []) /\ (!cmp a b l. P cmp ((a,b)::l) []) /\
           (!cmp y m. P cmp [] (y::m)) /\
           (!cmp a b l y m.
              ((apto cmp a y = EQUAL) ==> P cmp l m) /\
              ((apto cmp a y = GREATER) ==> P cmp ((a,b)::l) m) /\
              ((apto cmp a y = LESS) ==> P cmp l (y::m)) ==>
              P cmp ((a,b)::l) (y::m)) ==>
           !v v1 v2. P v v1 v2

   [list_rplacv_cn]  Theorem

      |- (!y x cn. list_rplacv_cn (x,y) [] cn = []) /\
         !z y x w l cn.
           list_rplacv_cn (x,y) ((w,z)::l) cn =
           if x = w then cn ((x,y)::l)
           else list_rplacv_cn (x,y) l (\m. cn ((w,z)::m))

   [list_rplacv_cn_ind]  Theorem

      |- !P.
           (!x y cn. P (x,y) [] cn) /\
           (!x y w z l cn.
              (x <> w ==> P (x,y) l (\m. cn ((w,z)::m))) ==>
              P (x,y) ((w,z)::l) cn) ==>
           !v v1 v2 v3. P (v,v1) v2 v3

   [list_rplacv_thm]  Theorem

      |- !x y l.
           (let ans = list_rplacv_cn (x,y) l (\m. m)
            in
              if ans = [] then x NOTIN FDOM (fmap l)
              else x IN FDOM (fmap l) /\ (fmap l |+ (x,y) = fmap ans))

   [merge]  Theorem

      |- (!l cmp. merge cmp [] l = l) /\
         (!v5 v4 cmp. merge cmp (v4::v5) [] = v4::v5) /\
         !l2 l1 cmp b2 b1 a2 a1.
           merge cmp ((a1,b1)::l1) ((a2,b2)::l2) =
           case apto cmp a1 a2 of
             LESS => (a1,b1)::merge cmp l1 ((a2,b2)::l2)
           | EQUAL => (a1,b1)::merge cmp l1 l2
           | GREATER => (a2,b2)::merge cmp ((a1,b1)::l1) l2

   [merge_ind]  Theorem

      |- !P.
           (!cmp l. P cmp [] l) /\ (!cmp v4 v5. P cmp (v4::v5) []) /\
           (!cmp a1 b1 l1 a2 b2 l2.
              ((apto cmp a1 a2 = EQUAL) ==> P cmp l1 l2) /\
              ((apto cmp a1 a2 = GREATER) ==> P cmp ((a1,b1)::l1) l2) /\
              ((apto cmp a1 a2 = LESS) ==> P cmp l1 ((a2,b2)::l2)) ==>
              P cmp ((a1,b1)::l1) ((a2,b2)::l2)) ==>
           !v v1 v2. P v v1 v2

   [merge_out]  Theorem

      |- (!l cmp. merge_out cmp l [] = l) /\
         (!lol l cmp. merge_out cmp l (NONE::lol) = merge_out cmp l lol) /\
         !m lol l cmp.
           merge_out cmp l (SOME m::lol) =
           merge_out cmp (merge cmp l m) lol

   [merge_out_ind]  Theorem

      |- !P.
           (!cmp l. P cmp l []) /\
           (!cmp l lol. P cmp l lol ==> P cmp l (NONE::lol)) /\
           (!cmp l m lol.
              P cmp (merge cmp l m) lol ==> P cmp l (SOME m::lol)) ==>
           !v v1 v2. P v v1 v2

   [o_f_bt_map]  Theorem

      |- !cmp f t. f o_f FMAPAL cmp t = FMAPAL cmp (bt_map (AP_SND f) t)

   [o_f_fmap]  Theorem

      |- !f l. f o_f fmap l = fmap (MAP (AP_SND f) l)

   [optry_list]  Theorem

      |- (!f. optry_list f [] = NONE) /\
         (!l f. optry_list f (NONE::l) = optry_list f l) /\
         !z l f. optry_list f (SOME z::l) = optry (f z) (optry_list f l)

   [optry_list_ind]  Theorem

      |- !P.
           (!f. P f []) /\ (!f l. P f l ==> P f (NONE::l)) /\
           (!f z l. P f l ==> P f (SOME z::l)) ==>
           !v v1. P v v1


*)
end
