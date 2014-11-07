signature EncodeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val biprefix_def : thm
    val collision_free_def : thm
    val encode_blist_def : thm
    val encode_bnum_def : thm
    val encode_bool_def : thm
    val encode_list_def : thm
    val encode_num_primitive_def : thm
    val encode_option_def : thm
    val encode_prod_def : thm
    val encode_sum_def : thm
    val encode_tree_curried_def : thm
    val encode_tree_tupled_primitive_def : thm
    val encode_unit_def : thm
    val lift_blist_def : thm
    val lift_option_def : thm
    val lift_prod_def : thm
    val lift_sum_def : thm
    val lift_tree_curried_def : thm
    val lift_tree_tupled_primitive_def : thm
    val tree_TY_DEF : thm
    val tree_case_def : thm
    val tree_size_def : thm
    val wf_encoder_def : thm
    val wf_pred_bnum_def : thm
    val wf_pred_def : thm

  (*  Theorems  *)
    val biprefix_append : thm
    val biprefix_appends : thm
    val biprefix_cons : thm
    val biprefix_refl : thm
    val biprefix_sym : thm
    val datatype_tree : thm
    val encode_blist_def_compute : thm
    val encode_bnum_def_compute : thm
    val encode_bnum_inj : thm
    val encode_bnum_length : thm
    val encode_list_cong : thm
    val encode_num_def : thm
    val encode_num_ind : thm
    val encode_prod_alt : thm
    val encode_tree_def : thm
    val lift_blist_suc : thm
    val lift_tree_def : thm
    val tree_11 : thm
    val tree_Axiom : thm
    val tree_case_cong : thm
    val tree_ind : thm
    val tree_induction : thm
    val tree_nchotomy : thm
    val wf_encode_blist : thm
    val wf_encode_bnum : thm
    val wf_encode_bnum_collision_free : thm
    val wf_encode_bool : thm
    val wf_encode_list : thm
    val wf_encode_num : thm
    val wf_encode_option : thm
    val wf_encode_prod : thm
    val wf_encode_sum : thm
    val wf_encode_tree : thm
    val wf_encode_unit : thm
    val wf_encoder_alt : thm
    val wf_encoder_eq : thm
    val wf_encoder_total : thm
    val wf_pred_bnum : thm
    val wf_pred_bnum_total : thm

  val Encode_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [rich_list] Parent theory of "Encode"

   [biprefix_def]  Definition

      |- ∀a b. biprefix a b ⇔ b ≼ a ∨ a ≼ b

   [collision_free_def]  Definition

      |- ∀m p.
           collision_free m p ⇔
           ∀x y. p x ∧ p y ∧ (x MOD 2 ** m = y MOD 2 ** m) ⇒ (x = y)

   [encode_blist_def]  Definition

      |- (∀e l. encode_blist 0 e l = []) ∧
         ∀m e l.
           encode_blist (SUC m) e l = e (HD l) ++ encode_blist m e (TL l)

   [encode_bnum_def]  Definition

      |- (∀n. encode_bnum 0 n = []) ∧
         ∀m n. encode_bnum (SUC m) n = ¬EVEN n::encode_bnum m (n DIV 2)

   [encode_bool_def]  Definition

      |- ∀x. encode_bool x = [x]

   [encode_list_def]  Definition

      |- (∀xb. encode_list xb [] = [F]) ∧
         ∀xb x xs. encode_list xb (x::xs) = T::(xb x ++ encode_list xb xs)

   [encode_num_primitive_def]  Definition

      |- encode_num =
         WFREC
           (@R.
              WF R ∧ (∀n. n ≠ 0 ∧ EVEN n ⇒ R ((n − 2) DIV 2) n) ∧
              ∀n. n ≠ 0 ∧ ¬EVEN n ⇒ R ((n − 1) DIV 2) n)
           (λencode_num n.
              I
                (if n = 0 then [T; T]
                 else if EVEN n then F::encode_num ((n − 2) DIV 2)
                 else T::F::encode_num ((n − 1) DIV 2)))

   [encode_option_def]  Definition

      |- (∀xb. encode_option xb NONE = [F]) ∧
         ∀xb x. encode_option xb (SOME x) = T::xb x

   [encode_prod_def]  Definition

      |- ∀xb yb x y. encode_prod xb yb (x,y) = xb x ++ yb y

   [encode_sum_def]  Definition

      |- (∀xb yb x. encode_sum xb yb (INL x) = T::xb x) ∧
         ∀xb yb y. encode_sum xb yb (INR y) = F::yb y

   [encode_tree_curried_def]  Definition

      |- ∀x x1. encode_tree x x1 = encode_tree_tupled (x,x1)

   [encode_tree_tupled_primitive_def]  Definition

      |- encode_tree_tupled =
         WFREC (@R. WF R ∧ ∀a e ts a'. MEM a' ts ⇒ R (e,a') (e,Node a ts))
           (λencode_tree_tupled a'.
              case a' of
                (e,Node a ts) =>
                  I (e a ++ encode_list (λa. encode_tree_tupled (e,a)) ts))

   [encode_unit_def]  Definition

      |- ∀v0. encode_unit v0 = []

   [lift_blist_def]  Definition

      |- ∀m p x. lift_blist m p x ⇔ EVERY p x ∧ (LENGTH x = m)

   [lift_option_def]  Definition

      |- ∀p x. lift_option p x ⇔ case x of NONE => T | SOME y => p y

   [lift_prod_def]  Definition

      |- ∀p1 p2 x. lift_prod p1 p2 x ⇔ p1 (FST x) ∧ p2 (SND x)

   [lift_sum_def]  Definition

      |- ∀p1 p2 x.
           lift_sum p1 p2 x ⇔ case x of INL x1 => p1 x1 | INR x2 => p2 x2

   [lift_tree_curried_def]  Definition

      |- ∀x x1. lift_tree x x1 ⇔ lift_tree_tupled (x,x1)

   [lift_tree_tupled_primitive_def]  Definition

      |- lift_tree_tupled =
         WFREC (@R. WF R ∧ ∀a p ts a'. MEM a' ts ⇒ R (p,a') (p,Node a ts))
           (λlift_tree_tupled a'.
              case a' of
                (p,Node a ts) =>
                  I (p a ∧ EVERY (λa. lift_tree_tupled (p,a)) ts))

   [tree_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'tree' 'list @ind_typeEncode0' .
                  (∀a0'.
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR 0 a0
                              (ind_type$FCONS a1 (λn. ind_type$BOTTOM))) a0
                           a1) ∧ 'list @ind_typeEncode0' a1) ⇒
                     'tree' a0') ∧
                  (∀a1'.
                     (a1' =
                      ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM)) ∨
                     (∃a0 a1.
                        (a1' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC (SUC 0)) ARB
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'tree' a0 ∧ 'list @ind_typeEncode0' a1) ⇒
                     'list @ind_typeEncode0' a1') ⇒
                  'tree' a0') rep

   [tree_case_def]  Definition

      |- ∀a0 a1 f. tree_CASE (Node a0 a1) f = f a0 a1

   [tree_size_def]  Definition

      |- (∀f a0 a1.
            tree_size f (Node a0 a1) = 1 + (f a0 + tree1_size f a1)) ∧
         (∀f. tree1_size f [] = 0) ∧
         ∀f a0 a1.
           tree1_size f (a0::a1) = 1 + (tree_size f a0 + tree1_size f a1)

   [wf_encoder_def]  Definition

      |- ∀p e. wf_encoder p e ⇔ ∀x y. p x ∧ p y ∧ e y ≼ e x ⇒ (x = y)

   [wf_pred_bnum_def]  Definition

      |- ∀m p. wf_pred_bnum m p ⇔ wf_pred p ∧ ∀x. p x ⇒ x < 2 ** m

   [wf_pred_def]  Definition

      |- ∀p. wf_pred p ⇔ ∃x. p x

   [biprefix_append]  Theorem

      |- ∀a b c d. biprefix (a ++ b) (c ++ d) ⇒ biprefix a c

   [biprefix_appends]  Theorem

      |- ∀a b c. biprefix (a ++ b) (a ++ c) ⇔ biprefix b c

   [biprefix_cons]  Theorem

      |- ∀a b c d. biprefix (a::b) (c::d) ⇔ (a = c) ∧ biprefix b d

   [biprefix_refl]  Theorem

      |- ∀x. biprefix x x

   [biprefix_sym]  Theorem

      |- ∀x y. biprefix x y ⇒ biprefix y x

   [datatype_tree]  Theorem

      |- DATATYPE (tree Node)

   [encode_blist_def_compute]  Theorem

      |- (∀e l. encode_blist 0 e l = []) ∧
         (∀m e l.
            encode_blist (NUMERAL (BIT1 m)) e l =
            e (HD l) ++ encode_blist (NUMERAL (BIT1 m) − 1) e (TL l)) ∧
         ∀m e l.
           encode_blist (NUMERAL (BIT2 m)) e l =
           e (HD l) ++ encode_blist (NUMERAL (BIT1 m)) e (TL l)

   [encode_bnum_def_compute]  Theorem

      |- (∀n. encode_bnum 0 n = []) ∧
         (∀m n.
            encode_bnum (NUMERAL (BIT1 m)) n =
            ¬EVEN n::encode_bnum (NUMERAL (BIT1 m) − 1) (n DIV 2)) ∧
         ∀m n.
           encode_bnum (NUMERAL (BIT2 m)) n =
           ¬EVEN n::encode_bnum (NUMERAL (BIT1 m)) (n DIV 2)

   [encode_bnum_inj]  Theorem

      |- ∀m x y.
           x < 2 ** m ∧ y < 2 ** m ∧ (encode_bnum m x = encode_bnum m y) ⇒
           (x = y)

   [encode_bnum_length]  Theorem

      |- ∀m n. LENGTH (encode_bnum m n) = m

   [encode_list_cong]  Theorem

      |- ∀l1 l2 f1 f2.
           (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (f1 x = f2 x)) ⇒
           (encode_list f1 l1 = encode_list f2 l2)

   [encode_num_def]  Theorem

      |- encode_num n =
         if n = 0 then [T; T]
         else if EVEN n then F::encode_num ((n − 2) DIV 2)
         else T::F::encode_num ((n − 1) DIV 2)

   [encode_num_ind]  Theorem

      |- ∀P.
           (∀n.
              (n ≠ 0 ∧ EVEN n ⇒ P ((n − 2) DIV 2)) ∧
              (n ≠ 0 ∧ ¬EVEN n ⇒ P ((n − 1) DIV 2)) ⇒
              P n) ⇒
           ∀v. P v

   [encode_prod_alt]  Theorem

      |- ∀xb yb p. encode_prod xb yb p = xb (FST p) ++ yb (SND p)

   [encode_tree_def]  Theorem

      |- encode_tree e (Node a ts) = e a ++ encode_list (encode_tree e) ts

   [lift_blist_suc]  Theorem

      |- ∀n p h t. lift_blist (SUC n) p (h::t) ⇔ p h ∧ lift_blist n p t

   [lift_tree_def]  Theorem

      |- lift_tree p (Node a ts) ⇔ p a ∧ EVERY (lift_tree p) ts

   [tree_11]  Theorem

      |- ∀a0 a1 a0' a1'.
           (Node a0 a1 = Node a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')

   [tree_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn0 fn1.
             (∀a0 a1. fn0 (Node a0 a1) = f0 a0 a1 (fn1 a1)) ∧
             (fn1 [] = f1) ∧
             ∀a0 a1. fn1 (a0::a1) = f2 a0 a1 (fn0 a0) (fn1 a1)

   [tree_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧ (∀a0 a1. (M' = Node a0 a1) ⇒ (f a0 a1 = f' a0 a1)) ⇒
           (tree_CASE M f = tree_CASE M' f')

   [tree_ind]  Theorem

      |- ∀p. (∀a ts. (∀t. MEM t ts ⇒ p t) ⇒ p (Node a ts)) ⇒ ∀t. p t

   [tree_induction]  Theorem

      |- ∀P0 P1.
           (∀l. P1 l ⇒ ∀a. P0 (Node a l)) ∧ P1 [] ∧
           (∀t l. P0 t ∧ P1 l ⇒ P1 (t::l)) ⇒
           (∀t. P0 t) ∧ ∀l. P1 l

   [tree_nchotomy]  Theorem

      |- ∀tt. ∃a l. tt = Node a l

   [wf_encode_blist]  Theorem

      |- ∀m p e.
           wf_encoder p e ⇒ wf_encoder (lift_blist m p) (encode_blist m e)

   [wf_encode_bnum]  Theorem

      |- ∀m p. wf_pred_bnum m p ⇒ wf_encoder p (encode_bnum m)

   [wf_encode_bnum_collision_free]  Theorem

      |- ∀m p. wf_encoder p (encode_bnum m) ⇔ collision_free m p

   [wf_encode_bool]  Theorem

      |- ∀p. wf_encoder p encode_bool

   [wf_encode_list]  Theorem

      |- ∀p e. wf_encoder p e ⇒ wf_encoder (EVERY p) (encode_list e)

   [wf_encode_num]  Theorem

      |- ∀p. wf_encoder p encode_num

   [wf_encode_option]  Theorem

      |- ∀p e.
           wf_encoder p e ⇒ wf_encoder (lift_option p) (encode_option e)

   [wf_encode_prod]  Theorem

      |- ∀p1 p2 e1 e2.
           wf_encoder p1 e1 ∧ wf_encoder p2 e2 ⇒
           wf_encoder (lift_prod p1 p2) (encode_prod e1 e2)

   [wf_encode_sum]  Theorem

      |- ∀p1 p2 e1 e2.
           wf_encoder p1 e1 ∧ wf_encoder p2 e2 ⇒
           wf_encoder (lift_sum p1 p2) (encode_sum e1 e2)

   [wf_encode_tree]  Theorem

      |- ∀p e. wf_encoder p e ⇒ wf_encoder (lift_tree p) (encode_tree e)

   [wf_encode_unit]  Theorem

      |- ∀p. wf_encoder p encode_unit

   [wf_encoder_alt]  Theorem

      |- wf_encoder p e ⇔ ∀x y. p x ∧ p y ∧ biprefix (e x) (e y) ⇒ (x = y)

   [wf_encoder_eq]  Theorem

      |- ∀p e f. wf_encoder p e ∧ (∀x. p x ⇒ (e x = f x)) ⇒ wf_encoder p f

   [wf_encoder_total]  Theorem

      |- ∀p e. wf_encoder (K T) e ⇒ wf_encoder p e

   [wf_pred_bnum]  Theorem

      |- ∀m p. wf_pred_bnum m p ⇒ collision_free m p

   [wf_pred_bnum_total]  Theorem

      |- ∀m. wf_pred_bnum m (λx. x < 2 ** m)


*)
end
