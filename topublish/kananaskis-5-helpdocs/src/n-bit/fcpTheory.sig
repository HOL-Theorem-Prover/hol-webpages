signature fcpTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val EQUAL_def : thm
    val FCP : thm
    val FCP_CONS_def : thm
    val FCP_EVERY_def : thm
    val FCP_EXISTS_def : thm
    val FCP_HD_def : thm
    val FCP_MAP_def : thm
    val FCP_TL_def : thm
    val FCP_UPDATE_def : thm
    val HAS_SIZE_def : thm
    val IS_BIT0A_def : thm
    val IS_BIT0B_def : thm
    val IS_BIT1A_def : thm
    val IS_BIT1B_def : thm
    val IS_BIT1C_def : thm
    val L2V_def : thm
    val V2L_def : thm
    val abs_sub1_def : thm
    val bit0_TY_DEF : thm
    val bit0_case_def : thm
    val bit0_repfns : thm
    val bit0_size_def : thm
    val bit1_TY_DEF : thm
    val bit1_case_def : thm
    val bit1_repfns : thm
    val bit1_size_def : thm
    val cart_TY_DEF : thm
    val cart_tybij : thm
    val dimindex_def : thm
    val fcp_case_def : thm
    val fcp_index : thm
    val finite_image_TY_DEF : thm
    val finite_image_tybij : thm
    val finite_index_def : thm
    val rep_sub1_def : thm
    val sub1_TY_DEF : thm
    val sub1_bijections : thm
    val sub_equiv_def : thm
  
  (*  Theorems  *)
    val APPLY_FCP_UPDATE_ID : thm
    val CART_EQ : thm
    val DIMINDEX_GE_1 : thm
    val EL_V2L : thm
    val FCP_APPLY_UPDATE_THM : thm
    val FCP_BETA : thm
    val FCP_CONS : thm
    val FCP_ETA : thm
    val FCP_EVERY : thm
    val FCP_EXISTS : thm
    val FCP_HD : thm
    val FCP_MAP : thm
    val FCP_TL : thm
    val FCP_UPDATE_COMMUTES : thm
    val FCP_UPDATE_EQ : thm
    val FCP_UPDATE_IMP_ID : thm
    val INDEX_SUB1 : thm
    val LENGTH_V2L : thm
    val LISTS_EQ : thm
    val NULL_V2L : thm
    val READ_L2V : thm
    val READ_TL : thm
    val V2L_L2V : thm
    val V2L_RECURSIVE : thm
    val bit0_11 : thm
    val bit0_Axiom : thm
    val bit0_case_cong : thm
    val bit0_distinct : thm
    val bit0_induction : thm
    val bit0_nchotomy : thm
    val bit1_11 : thm
    val bit1_Axiom : thm
    val bit1_case_cong : thm
    val bit1_distinct : thm
    val bit1_induction : thm
    val bit1_nchotomy : thm
    val card_dimindex : thm
    val datatype_bit0 : thm
    val datatype_bit1 : thm
    val dimindex : thm
    val exists_v2l_thm : thm
    val fcp_Axiom : thm
    val fcp_ind : thm
    val fcp_subst_comp : thm
    val finite_bit0 : thm
    val finite_bit1 : thm
    val finite_one : thm
    val finite_sub1 : thm
    val finite_sum : thm
    val index_bit0 : thm
    val index_bit1 : thm
    val index_comp : thm
    val index_one : thm
    val index_sum : thm
    val sub1_ABS_REP_CLASS : thm
    val sub1_QUOTIENT : thm
  
  val fcp_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [quotient_list] Parent theory of "fcp"
   
   [quotient_option] Parent theory of "fcp"
   
   [quotient_pair] Parent theory of "fcp"
   
   [quotient_sum] Parent theory of "fcp"
   
   [EQUAL_def]  Definition
      
      |- EQUAL = {CHOICE UNIV; CHOICE (REST UNIV)}
   
   [FCP]  Definition
      
      |- $FCP = (\g. @f. !i. i < dimindex (:'b) ==> (f ' i = g i))
   
   [FCP_CONS_def]  Definition
      
      |- !h v. FCP_CONS h v = (0 :+ h) (FCP i. v ' (PRE i))
   
   [FCP_EVERY_def]  Definition
      
      |- !P v. FCP_EVERY P v <=> !i. dimindex (:'a) <= i \/ P (v ' i)
   
   [FCP_EXISTS_def]  Definition
      
      |- !P v. FCP_EXISTS P v <=> ?i. i < dimindex (:'a) /\ P (v ' i)
   
   [FCP_HD_def]  Definition
      
      |- !v. FCP_HD v = v ' 0
   
   [FCP_MAP_def]  Definition
      
      |- !f v. FCP_MAP f v = FCP i. f (v ' i)
   
   [FCP_TL_def]  Definition
      
      |- !v. FCP_TL v = FCP i. v ' (SUC i)
   
   [FCP_UPDATE_def]  Definition
      
      |- !a b. a :+ b = (\m. FCP c. if a = c then b else m ' c)
   
   [HAS_SIZE_def]  Definition
      
      |- !s n. (s HAS_SIZE n) <=> FINITE s /\ (CARD s = n)
   
   [IS_BIT0A_def]  Definition
      
      |- (!x. IS_BIT0A (BIT0A x) <=> T) /\ !x. IS_BIT0A (BIT0B x) <=> F
   
   [IS_BIT0B_def]  Definition
      
      |- (!x. IS_BIT0B (BIT0A x) <=> F) /\ !x. IS_BIT0B (BIT0B x) <=> T
   
   [IS_BIT1A_def]  Definition
      
      |- (!x. IS_BIT1A (BIT1A x) <=> T) /\
         (!x. IS_BIT1A (BIT1B x) <=> F) /\ (IS_BIT1A BIT1C <=> F)
   
   [IS_BIT1B_def]  Definition
      
      |- (!x. IS_BIT1B (BIT1A x) <=> F) /\
         (!x. IS_BIT1B (BIT1B x) <=> T) /\ (IS_BIT1B BIT1C <=> F)
   
   [IS_BIT1C_def]  Definition
      
      |- (!x. IS_BIT1C (BIT1A x) <=> F) /\
         (!x. IS_BIT1C (BIT1B x) <=> F) /\ (IS_BIT1C BIT1C <=> T)
   
   [L2V_def]  Definition
      
      |- !L. L2V L = FCP i. EL i L
   
   [V2L_def]  Definition
      
      |- !v.
           V2L v =
           @L.
             (LENGTH L = dimindex (:'b)) /\
             !i. i < dimindex (:'b) ==> (EL i L = v ' i)
   
   [abs_sub1_def]  Definition
      
      |- !r. abs_sub1 r = abs_sub1_CLASS (sub_equiv r)
   
   [bit0_TY_DEF]  Definition
      
      |- ?rep.
           TYPE_DEFINITION
             (\a0.
                !'bit0' .
                  (!a0.
                     (?a.
                        a0 =
                        (\a. ind_type$CONSTR 0 a (\n. ind_type$BOTTOM))
                          a) \/
                     (?a.
                        a0 =
                        (\a.
                           ind_type$CONSTR (SUC 0) a (\n. ind_type$BOTTOM))
                          a) ==>
                     'bit0' a0) ==>
                  'bit0' a0) rep
   
   [bit0_case_def]  Definition
      
      |- (!f f1 a. bit0_case f f1 (BIT0A a) = f a) /\
         !f f1 a. bit0_case f f1 (BIT0B a) = f1 a
   
   [bit0_repfns]  Definition
      
      |- (!a. mk_bit0 (dest_bit0 a) = a) /\
         !r.
           (\a0.
              !'bit0' .
                (!a0.
                   (?a.
                      a0 =
                      (\a. ind_type$CONSTR 0 a (\n. ind_type$BOTTOM)) a) \/
                   (?a.
                      a0 =
                      (\a. ind_type$CONSTR (SUC 0) a (\n. ind_type$BOTTOM))
                        a) ==>
                   'bit0' a0) ==>
                'bit0' a0) r <=> (dest_bit0 (mk_bit0 r) = r)
   
   [bit0_size_def]  Definition
      
      |- (!f a. bit0_size f (BIT0A a) = 1 + f a) /\
         !f a. bit0_size f (BIT0B a) = 1 + f a
   
   [bit1_TY_DEF]  Definition
      
      |- ?rep.
           TYPE_DEFINITION
             (\a0.
                !'bit1' .
                  (!a0.
                     (?a.
                        a0 =
                        (\a. ind_type$CONSTR 0 a (\n. ind_type$BOTTOM))
                          a) \/
                     (?a.
                        a0 =
                        (\a.
                           ind_type$CONSTR (SUC 0) a (\n. ind_type$BOTTOM))
                          a) \/
                     (a0 =
                      ind_type$CONSTR (SUC (SUC 0)) ARB
                        (\n. ind_type$BOTTOM)) ==>
                     'bit1' a0) ==>
                  'bit1' a0) rep
   
   [bit1_case_def]  Definition
      
      |- (!f f1 v a. bit1_case f f1 v (BIT1A a) = f a) /\
         (!f f1 v a. bit1_case f f1 v (BIT1B a) = f1 a) /\
         !f f1 v. bit1_case f f1 v BIT1C = v
   
   [bit1_repfns]  Definition
      
      |- (!a. mk_bit1 (dest_bit1 a) = a) /\
         !r.
           (\a0.
              !'bit1' .
                (!a0.
                   (?a.
                      a0 =
                      (\a. ind_type$CONSTR 0 a (\n. ind_type$BOTTOM)) a) \/
                   (?a.
                      a0 =
                      (\a. ind_type$CONSTR (SUC 0) a (\n. ind_type$BOTTOM))
                        a) \/
                   (a0 =
                    ind_type$CONSTR (SUC (SUC 0)) ARB
                      (\n. ind_type$BOTTOM)) ==>
                   'bit1' a0) ==>
                'bit1' a0) r <=> (dest_bit1 (mk_bit1 r) = r)
   
   [bit1_size_def]  Definition
      
      |- (!f a. bit1_size f (BIT1A a) = 1 + f a) /\
         (!f a. bit1_size f (BIT1B a) = 1 + f a) /\
         !f. bit1_size f BIT1C = 0
   
   [cart_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (\f. T) rep
   
   [cart_tybij]  Definition
      
      |- (!a. mk_cart (dest_cart a) = a) /\
         !r. (\f. T) r <=> (dest_cart (mk_cart r) = r)
   
   [dimindex_def]  Definition
      
      |- dimindex (:'a) = if FINITE UNIV then CARD UNIV else 1
   
   [fcp_case_def]  Definition
      
      |- !f' h. fcp_case f' (mk_cart h) = f' h
   
   [fcp_index]  Definition
      
      |- !x i. x ' i = dest_cart x (finite_index i)
   
   [finite_image_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (\x. (x = ARB) \/ FINITE UNIV) rep
   
   [finite_image_tybij]  Definition
      
      |- (!a. mk_finite_image (dest_finite_image a) = a) /\
         !r.
           (\x. (x = ARB) \/ FINITE UNIV) r <=>
           (dest_finite_image (mk_finite_image r) = r)
   
   [finite_index_def]  Definition
      
      |- finite_index = @f. !x. ?!n. n < dimindex (:'a) /\ (f n = x)
   
   [rep_sub1_def]  Definition
      
      |- !a. rep_sub1 a = $@ (rep_sub1_CLASS a)
   
   [sub1_TY_DEF]  Definition
      
      |- ?rep.
           TYPE_DEFINITION (\c. ?r. sub_equiv r r /\ (c = sub_equiv r)) rep
   
   [sub1_bijections]  Definition
      
      |- (!a. abs_sub1_CLASS (rep_sub1_CLASS a) = a) /\
         !r.
           (\c. ?r. sub_equiv r r /\ (c = sub_equiv r)) r <=>
           (rep_sub1_CLASS (abs_sub1_CLASS r) = r)
   
   [sub_equiv_def]  Definition
      
      |- !a b. sub_equiv a b <=> a IN EQUAL /\ b IN EQUAL \/ (a = b)
   
   [APPLY_FCP_UPDATE_ID]  Theorem
      
      |- !m a. (a :+ m ' a) m = m
   
   [CART_EQ]  Theorem
      
      |- !x y. (x = y) <=> !i. i < dimindex (:'b) ==> (x ' i = y ' i)
   
   [DIMINDEX_GE_1]  Theorem
      
      |- 1 <= dimindex (:'a)
   
   [EL_V2L]  Theorem
      
      |- i < dimindex (:'b) ==> (EL i (V2L v) = v ' i)
   
   [FCP_APPLY_UPDATE_THM]  Theorem
      
      |- !m a w b.
           (a :+ w) m ' b =
           if b < dimindex (:'b) then
             if a = b then w else m ' b
           else
             (a :+ w) m ' b
   
   [FCP_BETA]  Theorem
      
      |- !i. i < dimindex (:'b) ==> ($FCP g ' i = g i)
   
   [FCP_CONS]  Theorem
      
      |- FCP_CONS a v = L2V (a::V2L v)
   
   [FCP_ETA]  Theorem
      
      |- !g. (FCP i. g ' i) = g
   
   [FCP_EVERY]  Theorem
      
      |- FCP_EVERY P v <=> EVERY P (V2L v)
   
   [FCP_EXISTS]  Theorem
      
      |- FCP_EXISTS P v <=> EXISTS P (V2L v)
   
   [FCP_HD]  Theorem
      
      |- FCP_HD v = HD (V2L v)
   
   [FCP_MAP]  Theorem
      
      |- FCP_MAP f v = L2V (MAP f (V2L v))
   
   [FCP_TL]  Theorem
      
      |- 1 < dimindex (:'b) ==> (FCP_TL v = L2V (TL (V2L v)))
   
   [FCP_UPDATE_COMMUTES]  Theorem
      
      |- !m a b c d.
           a <> b ==> ((a :+ c) ((b :+ d) m) = (b :+ d) ((a :+ c) m))
   
   [FCP_UPDATE_EQ]  Theorem
      
      |- !m a b c. (a :+ c) ((a :+ b) m) = (a :+ c) m
   
   [FCP_UPDATE_IMP_ID]  Theorem
      
      |- !m a v. (m ' a = v) ==> ((a :+ v) m = m)
   
   [INDEX_SUB1]  Theorem
      
      |- dimindex (:'a sub1) =
         if 1 < dimindex (:'a) then PRE (dimindex (:'a)) else 1
   
   [LENGTH_V2L]  Theorem
      
      |- LENGTH (V2L v) = dimindex (:'b)
   
   [LISTS_EQ]  Theorem
      
      |- (x = y) <=>
         (LENGTH x = LENGTH y) /\ !i. i < LENGTH x ==> (EL i x = EL i y)
   
   [NULL_V2L]  Theorem
      
      |- ~NULL (V2L v)
   
   [READ_L2V]  Theorem
      
      |- i < dimindex (:'b) ==> (L2V a ' i = EL i a)
   
   [READ_TL]  Theorem
      
      |- i < dimindex (:'b) ==> (FCP_TL a ' i = a ' (SUC i))
   
   [V2L_L2V]  Theorem
      
      |- !x. (dimindex (:'b) = LENGTH x) ==> (V2L (L2V x) = x)
   
   [V2L_RECURSIVE]  Theorem
      
      |- V2L v =
         FCP_HD v::if dimindex (:'b) = 1 then [] else V2L (FCP_TL v)
   
   [bit0_11]  Theorem
      
      |- (!a a'. (BIT0A a = BIT0A a') <=> (a = a')) /\
         !a a'. (BIT0B a = BIT0B a') <=> (a = a')
   
   [bit0_Axiom]  Theorem
      
      |- !f0 f1. ?fn. (!a. fn (BIT0A a) = f0 a) /\ !a. fn (BIT0B a) = f1 a
   
   [bit0_case_cong]  Theorem
      
      |- !M M' f f1.
           (M = M') /\ (!a. (M' = BIT0A a) ==> (f a = f' a)) /\
           (!a. (M' = BIT0B a) ==> (f1 a = f1' a)) ==>
           (bit0_case f f1 M = bit0_case f' f1' M')
   
   [bit0_distinct]  Theorem
      
      |- !a' a. BIT0A a <> BIT0B a'
   
   [bit0_induction]  Theorem
      
      |- !P. (!a. P (BIT0A a)) /\ (!a. P (BIT0B a)) ==> !b. P b
   
   [bit0_nchotomy]  Theorem
      
      |- !bb. (?a. bb = BIT0A a) \/ ?a. bb = BIT0B a
   
   [bit1_11]  Theorem
      
      |- (!a a'. (BIT1A a = BIT1A a') <=> (a = a')) /\
         !a a'. (BIT1B a = BIT1B a') <=> (a = a')
   
   [bit1_Axiom]  Theorem
      
      |- !f0 f1 f2.
           ?fn.
             (!a. fn (BIT1A a) = f0 a) /\ (!a. fn (BIT1B a) = f1 a) /\
             (fn BIT1C = f2)
   
   [bit1_case_cong]  Theorem
      
      |- !M M' f f1 v.
           (M = M') /\ (!a. (M' = BIT1A a) ==> (f a = f' a)) /\
           (!a. (M' = BIT1B a) ==> (f1 a = f1' a)) /\
           ((M' = BIT1C) ==> (v = v')) ==>
           (bit1_case f f1 v M = bit1_case f' f1' v' M')
   
   [bit1_distinct]  Theorem
      
      |- (!a' a. BIT1A a <> BIT1B a') /\ (!a. BIT1A a <> BIT1C) /\
         !a. BIT1B a <> BIT1C
   
   [bit1_induction]  Theorem
      
      |- !P. (!a. P (BIT1A a)) /\ (!a. P (BIT1B a)) /\ P BIT1C ==> !b. P b
   
   [bit1_nchotomy]  Theorem
      
      |- !bb. (?a. bb = BIT1A a) \/ (?a. bb = BIT1B a) \/ (bb = BIT1C)
   
   [card_dimindex]  Theorem
      
      |- FINITE UNIV ==> (CARD UNIV = dimindex (:'a))
   
   [datatype_bit0]  Theorem
      
      |- DATATYPE (bit0 BIT0A BIT0B)
   
   [datatype_bit1]  Theorem
      
      |- DATATYPE (bit1 BIT1A BIT1B BIT1C)
   
   [dimindex]  Theorem
      
      |- dimindex (:'a) = if FINITE UNIV then CARD UNIV else 1
   
   [exists_v2l_thm]  Theorem
      
      |- ?x.
           (LENGTH x = dimindex (:'b)) /\
           !i. i < dimindex (:'b) ==> (EL i x = v ' i)
   
   [fcp_Axiom]  Theorem
      
      |- !f. ?g. !h. g (mk_cart h) = f h
   
   [fcp_ind]  Theorem
      
      |- !P. (!f. P (mk_cart f)) ==> !a. P a
   
   [fcp_subst_comp]  Theorem
      
      |- !a b f. (x :+ y) ($FCP f) = FCP c. if x = c then y else f c
   
   [finite_bit0]  Theorem
      
      |- FINITE UNIV <=> FINITE UNIV
   
   [finite_bit1]  Theorem
      
      |- FINITE UNIV <=> FINITE UNIV
   
   [finite_one]  Theorem
      
      |- FINITE UNIV
   
   [finite_sub1]  Theorem
      
      |- FINITE UNIV <=> FINITE UNIV
   
   [finite_sum]  Theorem
      
      |- FINITE UNIV <=> FINITE UNIV /\ FINITE UNIV
   
   [index_bit0]  Theorem
      
      |- dimindex (:'a bit0) =
         if FINITE UNIV then 2 * dimindex (:'a) else 1
   
   [index_bit1]  Theorem
      
      |- dimindex (:'a bit1) =
         if FINITE UNIV then 2 * dimindex (:'a) + 1 else 1
   
   [index_comp]  Theorem
      
      |- !f n.
           $FCP f ' n =
           if n < dimindex (:'b) then
             f n
           else
             FAIL $' FCP out of bounds ($FCP f) n
   
   [index_one]  Theorem
      
      |- dimindex (:unit) = 1
   
   [index_sum]  Theorem
      
      |- dimindex (:'a + 'b) =
         if FINITE UNIV /\ FINITE UNIV then
           dimindex (:'a) + dimindex (:'b)
         else
           1
   
   [sub1_ABS_REP_CLASS]  Theorem
      
      |- (!a. abs_sub1_CLASS (rep_sub1_CLASS a) = a) /\
         !c.
           (?r. sub_equiv r r /\ (c = sub_equiv r)) <=>
           (rep_sub1_CLASS (abs_sub1_CLASS c) = c)
   
   [sub1_QUOTIENT]  Theorem
      
      |- QUOTIENT sub_equiv abs_sub1 rep_sub1
   
   
*)
end
