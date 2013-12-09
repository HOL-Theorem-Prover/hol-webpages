signature enumeralTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BL_ACCUM : thm
    val BL_CONS : thm
    val K2 : thm
    val LESS_ALL : thm
    val OL : thm
    val OL_bt : thm
    val OL_bt_lb : thm
    val OL_bt_lb_ub : thm
    val OL_bt_ub : thm
    val OL_sublists_curried : thm
    val OL_sublists_tupled_primitive : thm
    val OU : thm
    val OWL : thm
    val UO : thm
    val bl_TY_DEF : thm
    val bl_case_def : thm
    val bl_rev : thm
    val bl_size_def : thm
    val bl_to_bt : thm
    val bl_to_set : thm
    val bt_TY_DEF : thm
    val bt_rev : thm
    val bt_size_def : thm
    val bt_to_bl : thm
    val bt_to_list : thm
    val bt_to_list_ac : thm
    val bt_to_ol : thm
    val bt_to_ol_ac : thm
    val bt_to_ol_lb : thm
    val bt_to_ol_lb_ac : thm
    val bt_to_ol_lb_ub : thm
    val bt_to_ol_lb_ub_ac : thm
    val bt_to_ol_ub : thm
    val bt_to_ol_ub_ac : thm
    val bt_to_set : thm
    val bt_to_set_lb : thm
    val bt_to_set_lb_ub : thm
    val bt_to_set_ub : thm
    val incr_sbuild : thm
    val incr_smerge_curried : thm
    val incr_smerge_tupled_primitive : thm
    val incr_ssort : thm
    val list_to_bl : thm
    val list_to_bt : thm
    val lol_set_primitive : thm
    val sdiff_curried : thm
    val sdiff_tupled_primitive : thm
    val sinter_curried : thm
    val sinter_tupled_primitive : thm
    val smerge_curried : thm
    val smerge_out_curried : thm
    val smerge_out_tupled_primitive : thm
    val smerge_tupled_primitive : thm

  (*  Theorems  *)
    val EMPTY_OU : thm
    val ENUMERAL_set : thm
    val IN_bt_to_set : thm
    val IN_node : thm
    val LESS_ALL_OU : thm
    val LESS_ALL_OU_UO_LEM : thm
    val LESS_ALL_UO_LEM : thm
    val LESS_UO_LEM : thm
    val NOT_IN_nt : thm
    val OL_DIFF_IMP : thm
    val OL_ENUMERAL : thm
    val OL_INTER_IMP : thm
    val OL_UNION_IMP : thm
    val OL_bt_to_ol : thm
    val OL_bt_to_ol_lb : thm
    val OL_bt_to_ol_lb_ub : thm
    val OL_bt_to_ol_ub : thm
    val OL_sublists : thm
    val OL_sublists_ind : thm
    val OU_ASSOC : thm
    val OU_EMPTY : thm
    val OWL_DIFF_THM : thm
    val OWL_INTER_THM : thm
    val OWL_UNION_THM : thm
    val OWL_bt_to_ol : thm
    val better_bt_to_ol : thm
    val bl_11 : thm
    val bl_Axiom : thm
    val bl_case_cong : thm
    val bl_distinct : thm
    val bl_induction : thm
    val bl_nchotomy : thm
    val bt_11 : thm
    val bt_Axiom : thm
    val bt_case_cong : thm
    val bt_case_def : thm
    val bt_distinct : thm
    val bt_induction : thm
    val bt_nchotomy : thm
    val bt_to_list_thm : thm
    val bt_to_ol_ID_IMP : thm
    val datatype_bl : thm
    val datatype_bt : thm
    val incr_smerge : thm
    val incr_smerge_OL : thm
    val incr_smerge_ind : thm
    val lol_set : thm
    val lol_set_ind : thm
    val ol_set : thm
    val sdiff : thm
    val sdiff_ind : thm
    val set_OWL_thm : thm
    val sinter : thm
    val sinter_ind : thm
    val smerge : thm
    val smerge_OL : thm
    val smerge_ind : thm
    val smerge_nil : thm
    val smerge_out : thm
    val smerge_out_ind : thm

  val enumeral_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [toto] Parent theory of "enumeral"

   [BL_ACCUM]  Definition

      |- (!a ac. BL_ACCUM a ac nbl = onebl a ac nbl) /\
         (!a ac bl. BL_ACCUM a ac (zerbl bl) = onebl a ac bl) /\
         !a ac r rft bl.
           BL_ACCUM a ac (onebl r rft bl) =
           zerbl (BL_ACCUM a (node ac r rft) bl)

   [BL_CONS]  Definition

      |- !a bl. BL_CONS a bl = BL_ACCUM a nt bl

   [K2]  Definition

      |- !a. K2 a = 2

   [LESS_ALL]  Definition

      |- !cmp x s.
           LESS_ALL cmp x s <=> !y. y IN s ==> (apto cmp x y = LESS)

   [OL]  Definition

      |- (!cmp. OL cmp [] <=> T) /\
         !cmp a l.
           OL cmp (a::l) <=>
           OL cmp l /\ !p. MEM p l ==> (apto cmp a p = LESS)

   [OL_bt]  Definition

      |- (!cmp. OL_bt cmp nt <=> T) /\
         !cmp l x r.
           OL_bt cmp (node l x r) <=> OL_bt_ub cmp l x /\ OL_bt_lb cmp x r

   [OL_bt_lb]  Definition

      |- (!cmp lb. OL_bt_lb cmp lb nt <=> T) /\
         !cmp lb l x r.
           OL_bt_lb cmp lb (node l x r) <=>
           OL_bt_lb_ub cmp lb l x /\ OL_bt_lb cmp x r

   [OL_bt_lb_ub]  Definition

      |- (!cmp lb ub.
            OL_bt_lb_ub cmp lb nt ub <=> (apto cmp lb ub = LESS)) /\
         !cmp lb l x r ub.
           OL_bt_lb_ub cmp lb (node l x r) ub <=>
           OL_bt_lb_ub cmp lb l x /\ OL_bt_lb_ub cmp x r ub

   [OL_bt_ub]  Definition

      |- (!cmp ub. OL_bt_ub cmp nt ub <=> T) /\
         !cmp l x r ub.
           OL_bt_ub cmp (node l x r) ub <=>
           OL_bt_ub cmp l x /\ OL_bt_lb_ub cmp x r ub

   [OL_sublists_curried]  Definition

      |- !x x1. OL_sublists x x1 <=> OL_sublists_tupled (x,x1)

   [OL_sublists_tupled_primitive]  Definition

      |- OL_sublists_tupled =
         WFREC
           (@R.
              WF R /\ (!lol cmp. R (cmp,lol) (cmp,NONE::lol)) /\
              !m lol cmp. R (cmp,lol) (cmp,SOME m::lol))
           (\OL_sublists_tupled a.
              case a of
                (cmp,[]) => I T
              | (cmp,NONE::lol) => I (OL_sublists_tupled (cmp,lol))
              | (cmp,SOME m::lol) =>
                  I (OL cmp m /\ OL_sublists_tupled (cmp,lol)))

   [OU]  Definition

      |- !cmp t u.
           OU cmp t u =
           {x | x IN t /\ !z. z IN u ==> (apto cmp x z = LESS)} UNION u

   [OWL]  Definition

      |- !cmp s l. OWL cmp s l <=> (s = set l) /\ OL cmp l

   [UO]  Definition

      |- !cmp s t.
           UO cmp s t =
           s UNION {y | y IN t /\ !z. z IN s ==> (apto cmp z y = LESS)}

   [bl_TY_DEF]  Definition

      |- ?rep.
           TYPE_DEFINITION
             (\a0'.
                !'bl' .
                  (!a0'.
                     (a0' =
                      ind_type$CONSTR 0 (ARB,ARB) (\n. ind_type$BOTTOM)) \/
                     (?a.
                        (a0' =
                         (\a.
                            ind_type$CONSTR (SUC 0) (ARB,ARB)
                              (ind_type$FCONS a (\n. ind_type$BOTTOM)))
                           a) /\ 'bl' a) \/
                     (?a0 a1 a2.
                        (a0' =
                         (\a0 a1 a2.
                            ind_type$CONSTR (SUC (SUC 0)) (a0,a1)
                              (ind_type$FCONS a2 (\n. ind_type$BOTTOM))) a0
                           a1 a2) /\ 'bl' a2) ==>
                     'bl' a0') ==>
                  'bl' a0') rep

   [bl_case_def]  Definition

      |- (!v f f1. bl_CASE nbl v f f1 = v) /\
         (!a v f f1. bl_CASE (zerbl a) v f f1 = f a) /\
         !a0 a1 a2 v f f1. bl_CASE (onebl a0 a1 a2) v f f1 = f1 a0 a1 a2

   [bl_rev]  Definition

      |- (!ft. bl_rev ft nbl = ft) /\
         (!ft b. bl_rev ft (zerbl b) = bl_rev ft b) /\
         !ft a f b. bl_rev ft (onebl a f b) = bl_rev (node ft a f) b

   [bl_size_def]  Definition

      |- (!f. bl_size f nbl = 0) /\
         (!f a. bl_size f (zerbl a) = 1 + bl_size f a) /\
         !f a0 a1 a2.
           bl_size f (onebl a0 a1 a2) =
           1 + (f a0 + (bt_size f a1 + bl_size f a2))

   [bl_to_bt]  Definition

      |- bl_to_bt = bl_rev nt

   [bl_to_set]  Definition

      |- (!cmp. bl_to_set cmp nbl = {}) /\
         (!cmp b. bl_to_set cmp (zerbl b) = bl_to_set cmp b) /\
         !cmp x t b.
           bl_to_set cmp (onebl x t b) =
           OU cmp
             ({x} UNION {y | y IN ENUMERAL cmp t /\ (apto cmp x y = LESS)})
             (bl_to_set cmp b)

   [bt_TY_DEF]  Definition

      |- ?rep.
           TYPE_DEFINITION
             (\a0'.
                !'bt' .
                  (!a0'.
                     (a0' = ind_type$CONSTR 0 ARB (\n. ind_type$BOTTOM)) \/
                     (?a0 a1 a2.
                        (a0' =
                         (\a0 a1 a2.
                            ind_type$CONSTR (SUC 0) a1
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a2
                                    (\n. ind_type$BOTTOM)))) a0 a1 a2) /\
                        'bt' a0 /\ 'bt' a2) ==>
                     'bt' a0') ==>
                  'bt' a0') rep

   [bt_rev]  Definition

      |- (!bl. bt_rev nt bl = bl) /\
         !lft r rft bl.
           bt_rev (node lft r rft) bl = bt_rev lft (onebl r rft bl)

   [bt_size_def]  Definition

      |- (!f. bt_size f nt = 0) /\
         !f a0 a1 a2.
           bt_size f (node a0 a1 a2) =
           1 + (bt_size f a0 + (f a1 + bt_size f a2))

   [bt_to_bl]  Definition

      |- !t. bt_to_bl t = bt_rev t nbl

   [bt_to_list]  Definition

      |- (bt_to_list nt = []) /\
         !l x r.
           bt_to_list (node l x r) = bt_to_list l ++ [x] ++ bt_to_list r

   [bt_to_list_ac]  Definition

      |- (!m. bt_to_list_ac nt m = m) /\
         !l x r m.
           bt_to_list_ac (node l x r) m =
           bt_to_list_ac l (x::bt_to_list_ac r m)

   [bt_to_ol]  Definition

      |- (!cmp. bt_to_ol cmp nt = []) /\
         !cmp l x r.
           bt_to_ol cmp (node l x r) =
           bt_to_ol_ub cmp l x ++ [x] ++ bt_to_ol_lb cmp x r

   [bt_to_ol_ac]  Definition

      |- (!cmp m. bt_to_ol_ac cmp nt m = m) /\
         !cmp l x r m.
           bt_to_ol_ac cmp (node l x r) m =
           bt_to_ol_ub_ac cmp l x (x::bt_to_ol_lb_ac cmp x r m)

   [bt_to_ol_lb]  Definition

      |- (!cmp lb. bt_to_ol_lb cmp lb nt = []) /\
         !cmp lb l x r.
           bt_to_ol_lb cmp lb (node l x r) =
           if apto cmp lb x = LESS then
             bt_to_ol_lb_ub cmp lb l x ++ [x] ++ bt_to_ol_lb cmp x r
           else bt_to_ol_lb cmp lb r

   [bt_to_ol_lb_ac]  Definition

      |- (!cmp lb m. bt_to_ol_lb_ac cmp lb nt m = m) /\
         !cmp lb l x r m.
           bt_to_ol_lb_ac cmp lb (node l x r) m =
           if apto cmp lb x = LESS then
             bt_to_ol_lb_ub_ac cmp lb l x (x::bt_to_ol_lb_ac cmp x r m)
           else bt_to_ol_lb_ac cmp lb r m

   [bt_to_ol_lb_ub]  Definition

      |- (!cmp lb ub. bt_to_ol_lb_ub cmp lb nt ub = []) /\
         !cmp lb l x r ub.
           bt_to_ol_lb_ub cmp lb (node l x r) ub =
           if apto cmp lb x = LESS then
             if apto cmp x ub = LESS then
               bt_to_ol_lb_ub cmp lb l x ++ [x] ++
               bt_to_ol_lb_ub cmp x r ub
             else bt_to_ol_lb_ub cmp lb l ub
           else bt_to_ol_lb_ub cmp lb r ub

   [bt_to_ol_lb_ub_ac]  Definition

      |- (!cmp lb ub m. bt_to_ol_lb_ub_ac cmp lb nt ub m = m) /\
         !cmp lb l x r ub m.
           bt_to_ol_lb_ub_ac cmp lb (node l x r) ub m =
           if apto cmp lb x = LESS then
             if apto cmp x ub = LESS then
               bt_to_ol_lb_ub_ac cmp lb l x
                 (x::bt_to_ol_lb_ub_ac cmp x r ub m)
             else bt_to_ol_lb_ub_ac cmp lb l ub m
           else bt_to_ol_lb_ub_ac cmp lb r ub m

   [bt_to_ol_ub]  Definition

      |- (!cmp ub. bt_to_ol_ub cmp nt ub = []) /\
         !cmp l x r ub.
           bt_to_ol_ub cmp (node l x r) ub =
           if apto cmp x ub = LESS then
             bt_to_ol_ub cmp l x ++ [x] ++ bt_to_ol_lb_ub cmp x r ub
           else bt_to_ol_ub cmp l ub

   [bt_to_ol_ub_ac]  Definition

      |- (!cmp ub m. bt_to_ol_ub_ac cmp nt ub m = m) /\
         !cmp l x r ub m.
           bt_to_ol_ub_ac cmp (node l x r) ub m =
           if apto cmp x ub = LESS then
             bt_to_ol_ub_ac cmp l x (x::bt_to_ol_lb_ub_ac cmp x r ub m)
           else bt_to_ol_ub_ac cmp l ub m

   [bt_to_set]  Definition

      |- (!cmp. ENUMERAL cmp nt = {}) /\
         !cmp l x r.
           ENUMERAL cmp (node l x r) =
           {y | y IN ENUMERAL cmp l /\ (apto cmp y x = LESS)} UNION
           {x} UNION {z | z IN ENUMERAL cmp r /\ (apto cmp x z = LESS)}

   [bt_to_set_lb]  Definition

      |- !cmp lb t.
           bt_to_set_lb cmp lb t =
           {x | x IN ENUMERAL cmp t /\ (apto cmp lb x = LESS)}

   [bt_to_set_lb_ub]  Definition

      |- !cmp lb t ub.
           bt_to_set_lb_ub cmp lb t ub =
           {x |
            x IN ENUMERAL cmp t /\ (apto cmp lb x = LESS) /\
            (apto cmp x ub = LESS)}

   [bt_to_set_ub]  Definition

      |- !cmp t ub.
           bt_to_set_ub cmp t ub =
           {x | x IN ENUMERAL cmp t /\ (apto cmp x ub = LESS)}

   [incr_sbuild]  Definition

      |- (!cmp. incr_sbuild cmp [] = []) /\
         !cmp x l.
           incr_sbuild cmp (x::l) = incr_smerge cmp [x] (incr_sbuild cmp l)

   [incr_smerge_curried]  Definition

      |- !x x1 x2. incr_smerge x x1 x2 = incr_smerge_tupled (x,x1,x2)

   [incr_smerge_tupled_primitive]  Definition

      |- incr_smerge_tupled =
         WFREC
           (@R.
              WF R /\
              !lol m l cmp. R (cmp,smerge cmp l m,lol) (cmp,l,SOME m::lol))
           (\incr_smerge_tupled a.
              case a of
                (cmp,l,[]) => I [SOME l]
              | (cmp,l,NONE::lol) => I (SOME l::lol)
              | (cmp,l,SOME m::lol) =>
                  I (NONE::incr_smerge_tupled (cmp,smerge cmp l m,lol)))

   [incr_ssort]  Definition

      |- !cmp l. incr_ssort cmp l = smerge_out cmp [] (incr_sbuild cmp l)

   [list_to_bl]  Definition

      |- (list_to_bl [] = nbl) /\
         !a l. list_to_bl (a::l) = BL_CONS a (list_to_bl l)

   [list_to_bt]  Definition

      |- !l. list_to_bt l = bl_to_bt (list_to_bl l)

   [lol_set_primitive]  Definition

      |- lol_set =
         WFREC
           (@R.
              WF R /\ (!lol. R lol (NONE::lol)) /\
              !m lol. R lol (SOME m::lol))
           (\lol_set a.
              case a of
                [] => I {}
              | NONE::lol => I (lol_set lol)
              | SOME m::lol => I (set m UNION lol_set lol))

   [sdiff_curried]  Definition

      |- !x x1 x2. sdiff x x1 x2 = sdiff_tupled (x,x1,x2)

   [sdiff_tupled_primitive]  Definition

      |- sdiff_tupled =
         WFREC
           (@R.
              WF R /\
              (!m l y x cmp.
                 (apto cmp x y = EQUAL) ==> R (cmp,l,m) (cmp,x::l,y::m)) /\
              (!m l y x cmp.
                 (apto cmp x y = GREATER) ==>
                 R (cmp,x::l,m) (cmp,x::l,y::m)) /\
              !m l y x cmp.
                (apto cmp x y = LESS) ==> R (cmp,l,y::m) (cmp,x::l,y::m))
           (\sdiff_tupled a.
              case a of
                (cmp,[],v3) => I []
              | (cmp,x::l,[]) => I (x::l)
              | (cmp,x::l,y::m) =>
                  I
                    (case apto cmp x y of
                       LESS => x::sdiff_tupled (cmp,l,y::m)
                     | EQUAL => sdiff_tupled (cmp,l,m)
                     | GREATER => sdiff_tupled (cmp,x::l,m)))

   [sinter_curried]  Definition

      |- !x x1 x2. sinter x x1 x2 = sinter_tupled (x,x1,x2)

   [sinter_tupled_primitive]  Definition

      |- sinter_tupled =
         WFREC
           (@R.
              WF R /\
              (!m l y x cmp.
                 (apto cmp x y = EQUAL) ==> R (cmp,l,m) (cmp,x::l,y::m)) /\
              (!m l y x cmp.
                 (apto cmp x y = GREATER) ==>
                 R (cmp,x::l,m) (cmp,x::l,y::m)) /\
              !m l y x cmp.
                (apto cmp x y = LESS) ==> R (cmp,l,y::m) (cmp,x::l,y::m))
           (\sinter_tupled a.
              case a of
                (cmp,[],v3) => I []
              | (cmp,x::l,[]) => I []
              | (cmp,x::l,y::m) =>
                  I
                    (case apto cmp x y of
                       LESS => sinter_tupled (cmp,l,y::m)
                     | EQUAL => x::sinter_tupled (cmp,l,m)
                     | GREATER => sinter_tupled (cmp,x::l,m)))

   [smerge_curried]  Definition

      |- !x x1 x2. smerge x x1 x2 = smerge_tupled (x,x1,x2)

   [smerge_out_curried]  Definition

      |- !x x1 x2. smerge_out x x1 x2 = smerge_out_tupled (x,x1,x2)

   [smerge_out_tupled_primitive]  Definition

      |- smerge_out_tupled =
         WFREC
           (@R.
              WF R /\ (!lol l cmp. R (cmp,l,lol) (cmp,l,NONE::lol)) /\
              !lol m l cmp. R (cmp,smerge cmp l m,lol) (cmp,l,SOME m::lol))
           (\smerge_out_tupled a.
              case a of
                (cmp,l,[]) => I l
              | (cmp,l,NONE::lol) => I (smerge_out_tupled (cmp,l,lol))
              | (cmp,l,SOME m::lol) =>
                  I (smerge_out_tupled (cmp,smerge cmp l m,lol)))

   [smerge_tupled_primitive]  Definition

      |- smerge_tupled =
         WFREC
           (@R.
              WF R /\
              (!m l y x cmp.
                 (apto cmp x y = EQUAL) ==> R (cmp,l,m) (cmp,x::l,y::m)) /\
              (!m l y x cmp.
                 (apto cmp x y = GREATER) ==>
                 R (cmp,x::l,m) (cmp,x::l,y::m)) /\
              !m l y x cmp.
                (apto cmp x y = LESS) ==> R (cmp,l,y::m) (cmp,x::l,y::m))
           (\smerge_tupled a.
              case a of
                (cmp,[],[]) => I []
              | (cmp,[],y::m) => I (y::m)
              | (cmp,x::l,[]) => I (x::l)
              | (cmp,x::l,y'::m') =>
                  I
                    (case apto cmp x y' of
                       LESS => x::smerge_tupled (cmp,l,y'::m')
                     | EQUAL => x::smerge_tupled (cmp,l,m')
                     | GREATER => y'::smerge_tupled (cmp,x::l,m')))

   [EMPTY_OU]  Theorem

      |- !cmp sl. OU cmp {} sl = sl

   [ENUMERAL_set]  Theorem

      |- !cmp l. set l = ENUMERAL cmp (list_to_bt (incr_ssort cmp l))

   [IN_bt_to_set]  Theorem

      |- (!cmp y. y IN ENUMERAL cmp nt <=> F) /\
         !cmp l x r y.
           y IN ENUMERAL cmp (node l x r) <=>
           y IN ENUMERAL cmp l /\ (apto cmp y x = LESS) \/ (y = x) \/
           y IN ENUMERAL cmp r /\ (apto cmp x y = LESS)

   [IN_node]  Theorem

      |- !cmp x l y r.
           x IN ENUMERAL cmp (node l y r) <=>
           case apto cmp x y of
             LESS => x IN ENUMERAL cmp l
           | EQUAL => T
           | GREATER => x IN ENUMERAL cmp r

   [LESS_ALL_OU]  Theorem

      |- !cmp x u v.
           LESS_ALL cmp x (OU cmp u v) <=>
           LESS_ALL cmp x u /\ LESS_ALL cmp x v

   [LESS_ALL_OU_UO_LEM]  Theorem

      |- !cmp a s t.
           LESS_ALL cmp a s /\ LESS_ALL cmp a t ==>
           (OU cmp (UO cmp {a} s) t = a INSERT OU cmp s t)

   [LESS_ALL_UO_LEM]  Theorem

      |- !cmp a s. LESS_ALL cmp a s ==> (UO cmp {a} s = a INSERT s)

   [LESS_UO_LEM]  Theorem

      |- !cmp x y s.
           (!z. z IN UO cmp {x} s ==> (apto cmp y z = LESS)) <=>
           (apto cmp y x = LESS)

   [NOT_IN_nt]  Theorem

      |- !cmp y. y IN ENUMERAL cmp nt <=> F

   [OL_DIFF_IMP]  Theorem

      |- !cmp l.
           OL cmp l ==>
           !m.
             OL cmp m ==>
             OL cmp (sdiff cmp l m) /\
             (set (sdiff cmp l m) = set l DIFF set m)

   [OL_ENUMERAL]  Theorem

      |- !cmp l. OL cmp l ==> (set l = ENUMERAL cmp (list_to_bt l))

   [OL_INTER_IMP]  Theorem

      |- !cmp l.
           OL cmp l ==>
           !m.
             OL cmp m ==>
             OL cmp (sinter cmp l m) /\
             (set (sinter cmp l m) = set l INTER set m)

   [OL_UNION_IMP]  Theorem

      |- !cmp l.
           OL cmp l ==>
           !m.
             OL cmp m ==>
             OL cmp (smerge cmp l m) /\
             (set (smerge cmp l m) = set l UNION set m)

   [OL_bt_to_ol]  Theorem

      |- !cmp t. OL cmp (bt_to_ol cmp t)

   [OL_bt_to_ol_lb]  Theorem

      |- !cmp t lb. OL cmp (bt_to_ol_lb cmp lb t)

   [OL_bt_to_ol_lb_ub]  Theorem

      |- !cmp t lb ub. OL cmp (bt_to_ol_lb_ub cmp lb t ub)

   [OL_bt_to_ol_ub]  Theorem

      |- !cmp t ub. OL cmp (bt_to_ol_ub cmp t ub)

   [OL_sublists]  Theorem

      |- (!cmp. OL_sublists cmp [] <=> T) /\
         (!lol cmp. OL_sublists cmp (NONE::lol) <=> OL_sublists cmp lol) /\
         !m lol cmp.
           OL_sublists cmp (SOME m::lol) <=>
           OL cmp m /\ OL_sublists cmp lol

   [OL_sublists_ind]  Theorem

      |- !P.
           (!cmp. P cmp []) /\
           (!cmp lol. P cmp lol ==> P cmp (NONE::lol)) /\
           (!cmp m lol. P cmp lol ==> P cmp (SOME m::lol)) ==>
           !v v1. P v v1

   [OU_ASSOC]  Theorem

      |- !cmp a b c. OU cmp a (OU cmp b c) = OU cmp (OU cmp a b) c

   [OU_EMPTY]  Theorem

      |- !cmp t. OU cmp t {} = t

   [OWL_DIFF_THM]  Theorem

      |- !cmp s l t m.
           OWL cmp s l /\ OWL cmp t m ==>
           OWL cmp (s DIFF t) (sdiff cmp l m)

   [OWL_INTER_THM]  Theorem

      |- !cmp s l t m.
           OWL cmp s l /\ OWL cmp t m ==>
           OWL cmp (s INTER t) (sinter cmp l m)

   [OWL_UNION_THM]  Theorem

      |- !cmp s l t m.
           OWL cmp s l /\ OWL cmp t m ==>
           OWL cmp (s UNION t) (smerge cmp l m)

   [OWL_bt_to_ol]  Theorem

      |- !cmp t. OWL cmp (ENUMERAL cmp t) (bt_to_ol cmp t)

   [better_bt_to_ol]  Theorem

      |- !cmp t.
           bt_to_ol cmp t =
           if OL_bt cmp t then bt_to_list_ac t [] else bt_to_ol_ac cmp t []

   [bl_11]  Theorem

      |- (!a a'. (zerbl a = zerbl a') <=> (a = a')) /\
         !a0 a1 a2 a0' a1' a2'.
           (onebl a0 a1 a2 = onebl a0' a1' a2') <=>
           (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')

   [bl_Axiom]  Theorem

      |- !f0 f1 f2.
           ?fn.
             (fn nbl = f0) /\ (!a. fn (zerbl a) = f1 a (fn a)) /\
             !a0 a1 a2. fn (onebl a0 a1 a2) = f2 a0 a1 a2 (fn a2)

   [bl_case_cong]  Theorem

      |- !M M' v f f1.
           (M = M') /\ ((M' = nbl) ==> (v = v')) /\
           (!a. (M' = zerbl a) ==> (f a = f' a)) /\
           (!a0 a1 a2.
              (M' = onebl a0 a1 a2) ==> (f1 a0 a1 a2 = f1' a0 a1 a2)) ==>
           (bl_CASE M v f f1 = bl_CASE M' v' f' f1')

   [bl_distinct]  Theorem

      |- (!a. nbl <> zerbl a) /\ (!a2 a1 a0. nbl <> onebl a0 a1 a2) /\
         !a2 a1 a0 a. zerbl a <> onebl a0 a1 a2

   [bl_induction]  Theorem

      |- !P.
           P nbl /\ (!b. P b ==> P (zerbl b)) /\
           (!b. P b ==> !b0 a. P (onebl a b0 b)) ==>
           !b. P b

   [bl_nchotomy]  Theorem

      |- !bb.
           (bb = nbl) \/ (?b. bb = zerbl b) \/ ?a b0 b. bb = onebl a b0 b

   [bt_11]  Theorem

      |- !a0 a1 a2 a0' a1' a2'.
           (node a0 a1 a2 = node a0' a1' a2') <=>
           (a0 = a0') /\ (a1 = a1') /\ (a2 = a2')

   [bt_Axiom]  Theorem

      |- !f0 f1.
           ?fn.
             (fn nt = f0) /\
             !a0 a1 a2. fn (node a0 a1 a2) = f1 a1 a0 a2 (fn a0) (fn a2)

   [bt_case_cong]  Theorem

      |- !M M' v f.
           (M = M') /\ ((M' = nt) ==> (v = v')) /\
           (!a0 a1 a2.
              (M' = node a0 a1 a2) ==> (f a0 a1 a2 = f' a0 a1 a2)) ==>
           (bt_CASE M v f = bt_CASE M' v' f')

   [bt_case_def]  Theorem

      |- (!v f. bt_CASE nt v f = v) /\
         !a0 a1 a2 v f. bt_CASE (node a0 a1 a2) v f = f a0 a1 a2

   [bt_distinct]  Theorem

      |- !a2 a1 a0. nt <> node a0 a1 a2

   [bt_induction]  Theorem

      |- !P.
           P nt /\ (!b b0. P b /\ P b0 ==> !a. P (node b a b0)) ==> !b. P b

   [bt_nchotomy]  Theorem

      |- !bb. (bb = nt) \/ ?b a b0. bb = node b a b0

   [bt_to_list_thm]  Theorem

      |- !t. bt_to_list t = bt_to_list_ac t []

   [bt_to_ol_ID_IMP]  Theorem

      |- !cmp l. OL cmp l ==> (bt_to_ol cmp (list_to_bt l) = l)

   [datatype_bl]  Theorem

      |- DATATYPE (bl nbl zerbl onebl)

   [datatype_bt]  Theorem

      |- DATATYPE (bt nt node)

   [incr_smerge]  Theorem

      |- (!l cmp. incr_smerge cmp l [] = [SOME l]) /\
         (!lol l cmp. incr_smerge cmp l (NONE::lol) = SOME l::lol) /\
         !m lol l cmp.
           incr_smerge cmp l (SOME m::lol) =
           NONE::incr_smerge cmp (smerge cmp l m) lol

   [incr_smerge_OL]  Theorem

      |- !cmp lol l.
           OL_sublists cmp lol /\ OL cmp l ==>
           OL_sublists cmp (incr_smerge cmp l lol)

   [incr_smerge_ind]  Theorem

      |- !P.
           (!cmp l. P cmp l []) /\ (!cmp l lol. P cmp l (NONE::lol)) /\
           (!cmp l m lol.
              P cmp (smerge cmp l m) lol ==> P cmp l (SOME m::lol)) ==>
           !v v1 v2. P v v1 v2

   [lol_set]  Theorem

      |- (lol_set [] = {}) /\ (!lol. lol_set (NONE::lol) = lol_set lol) /\
         !m lol. lol_set (SOME m::lol) = set m UNION lol_set lol

   [lol_set_ind]  Theorem

      |- !P.
           P [] /\ (!lol. P lol ==> P (NONE::lol)) /\
           (!m lol. P lol ==> P (SOME m::lol)) ==>
           !v. P v

   [ol_set]  Theorem

      |- !cmp t. ENUMERAL cmp t = set (bt_to_ol cmp t)

   [sdiff]  Theorem

      |- (!cmp. sdiff cmp [] [] = []) /\
         (!x l cmp. sdiff cmp (x::l) [] = x::l) /\
         (!y m cmp. sdiff cmp [] (y::m) = []) /\
         !y x m l cmp.
           sdiff cmp (x::l) (y::m) =
           case apto cmp x y of
             LESS => x::sdiff cmp l (y::m)
           | EQUAL => sdiff cmp l m
           | GREATER => sdiff cmp (x::l) m

   [sdiff_ind]  Theorem

      |- !P.
           (!cmp. P cmp [] []) /\ (!cmp x l. P cmp (x::l) []) /\
           (!cmp y m. P cmp [] (y::m)) /\
           (!cmp x l y m.
              ((apto cmp x y = EQUAL) ==> P cmp l m) /\
              ((apto cmp x y = GREATER) ==> P cmp (x::l) m) /\
              ((apto cmp x y = LESS) ==> P cmp l (y::m)) ==>
              P cmp (x::l) (y::m)) ==>
           !v v1 v2. P v v1 v2

   [set_OWL_thm]  Theorem

      |- !cmp l. OWL cmp (set l) (incr_ssort cmp l)

   [sinter]  Theorem

      |- (!cmp. sinter cmp [] [] = []) /\
         (!x l cmp. sinter cmp (x::l) [] = []) /\
         (!y m cmp. sinter cmp [] (y::m) = []) /\
         !y x m l cmp.
           sinter cmp (x::l) (y::m) =
           case apto cmp x y of
             LESS => sinter cmp l (y::m)
           | EQUAL => x::sinter cmp l m
           | GREATER => sinter cmp (x::l) m

   [sinter_ind]  Theorem

      |- !P.
           (!cmp. P cmp [] []) /\ (!cmp x l. P cmp (x::l) []) /\
           (!cmp y m. P cmp [] (y::m)) /\
           (!cmp x l y m.
              ((apto cmp x y = EQUAL) ==> P cmp l m) /\
              ((apto cmp x y = GREATER) ==> P cmp (x::l) m) /\
              ((apto cmp x y = LESS) ==> P cmp l (y::m)) ==>
              P cmp (x::l) (y::m)) ==>
           !v v1 v2. P v v1 v2

   [smerge]  Theorem

      |- (!cmp. smerge cmp [] [] = []) /\
         (!x l cmp. smerge cmp (x::l) [] = x::l) /\
         (!y m cmp. smerge cmp [] (y::m) = y::m) /\
         !y x m l cmp.
           smerge cmp (x::l) (y::m) =
           case apto cmp x y of
             LESS => x::smerge cmp l (y::m)
           | EQUAL => x::smerge cmp l m
           | GREATER => y::smerge cmp (x::l) m

   [smerge_OL]  Theorem

      |- !cmp l m. OL cmp l /\ OL cmp m ==> OL cmp (smerge cmp l m)

   [smerge_ind]  Theorem

      |- !P.
           (!cmp. P cmp [] []) /\ (!cmp x l. P cmp (x::l) []) /\
           (!cmp y m. P cmp [] (y::m)) /\
           (!cmp x l y m.
              ((apto cmp x y = EQUAL) ==> P cmp l m) /\
              ((apto cmp x y = GREATER) ==> P cmp (x::l) m) /\
              ((apto cmp x y = LESS) ==> P cmp l (y::m)) ==>
              P cmp (x::l) (y::m)) ==>
           !v v1 v2. P v v1 v2

   [smerge_nil]  Theorem

      |- !cmp l. (smerge cmp l [] = l) /\ (smerge cmp [] l = l)

   [smerge_out]  Theorem

      |- (!l cmp. smerge_out cmp l [] = l) /\
         (!lol l cmp.
            smerge_out cmp l (NONE::lol) = smerge_out cmp l lol) /\
         !m lol l cmp.
           smerge_out cmp l (SOME m::lol) =
           smerge_out cmp (smerge cmp l m) lol

   [smerge_out_ind]  Theorem

      |- !P.
           (!cmp l. P cmp l []) /\
           (!cmp l lol. P cmp l lol ==> P cmp l (NONE::lol)) /\
           (!cmp l m lol.
              P cmp (smerge cmp l m) lol ==> P cmp l (SOME m::lol)) ==>
           !v v1 v2. P v v1 v2


*)
end
