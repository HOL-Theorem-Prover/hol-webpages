signature lbtreeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val Lf_def : thm
    val Lfrep_def : thm
    val Nd_def : thm
    val Ndrep_def : thm
    val bf_flatten_def : thm
    val depth_def : thm
    val finite_def : thm
    val is_lbtree_def : thm
    val is_mmindex_def : thm
    val lbtree_TY_DEF : thm
    val lbtree_absrep : thm
    val lbtree_case_def : thm
    val map_def : thm
    val mem_def : thm
    val mindepth_def : thm
    val optmin_curried_def : thm
    val optmin_tupled_primitive_def : thm
    val path_follow_def : thm

  (*  Theorems  *)
    val EXISTS_FIRST : thm
    val Lf_NOT_Nd : thm
    val Nd_11 : thm
    val bf_flatten_append : thm
    val bf_flatten_eq_lnil : thm
    val depth_cases : thm
    val depth_ind : thm
    val depth_mem : thm
    val depth_rules : thm
    val depth_strongind : thm
    val exists_bf_flatten : thm
    val finite_cases : thm
    val finite_ind : thm
    val finite_map : thm
    val finite_rules : thm
    val finite_strongind : thm
    val finite_thm : thm
    val lbtree_bisimulation : thm
    val lbtree_case_thm : thm
    val lbtree_cases : thm
    val lbtree_strong_bisimulation : thm
    val lbtree_ue_Axiom : thm
    val map_eq_Lf : thm
    val map_eq_Nd : thm
    val mem_bf_flatten : thm
    val mem_cases : thm
    val mem_depth : thm
    val mem_ind : thm
    val mem_mindepth : thm
    val mem_rules : thm
    val mem_strongind : thm
    val mem_thm : thm
    val mindepth_depth : thm
    val mindepth_thm : thm
    val mmindex_EXISTS : thm
    val mmindex_unique : thm
    val optmin_def : thm
    val optmin_ind : thm

  val lbtree_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [llist] Parent theory of "lbtree"

   [Lf_def]  Definition

      |- Lf = lbtree_abs Lfrep

   [Lfrep_def]  Definition

      |- Lfrep = (λl. NONE)

   [Nd_def]  Definition

      |- ∀a t1 t2.
           Nd a t1 t2 =
           lbtree_abs (Ndrep a (lbtree_rep t1) (lbtree_rep t2))

   [Ndrep_def]  Definition

      |- ∀a t1 t2.
           Ndrep a t1 t2 =
           (λl. case l of [] => SOME a | T::xs => t1 xs | F::xs => t2 xs)

   [bf_flatten_def]  Definition

      |- (bf_flatten [] = [||]) ∧
         (∀ts. bf_flatten (Lf::ts) = bf_flatten ts) ∧
         ∀a t1 t2 ts.
           bf_flatten (Nd a t1 t2::ts) = a:::bf_flatten (ts ++ [t1; t2])

   [depth_def]  Definition

      |- lbtree$depth =
         (λa0 a1 a2.
            ∀depth'.
              (∀a0 a1 a2.
                 (∃t1 t2. (a1 = Nd a0 t1 t2) ∧ (a2 = 0)) ∨
                 (∃m a t1 t2.
                    (a1 = Nd a t1 t2) ∧ (a2 = SUC m) ∧ depth' a0 t1 m) ∨
                 (∃m a t1 t2.
                    (a1 = Nd a t1 t2) ∧ (a2 = SUC m) ∧ depth' a0 t2 m) ⇒
                 depth' a0 a1 a2) ⇒
              depth' a0 a1 a2)

   [finite_def]  Definition

      |- finite =
         (λa0.
            ∀finite'.
              (∀a0.
                 (a0 = Lf) ∨
                 (∃a t1 t2. (a0 = Nd a t1 t2) ∧ finite' t1 ∧ finite' t2) ⇒
                 finite' a0) ⇒
              finite' a0)

   [is_lbtree_def]  Definition

      |- ∀t.
           is_lbtree t ⇔
           ∃P.
             (∀t.
                P t ⇒
                (t = Lfrep) ∨
                ∃a t1 t2. P t1 ∧ P t2 ∧ (t = Ndrep a t1 t2)) ∧ P t

   [is_mmindex_def]  Definition

      |- ∀f l n d.
           lbtree$is_mmindex f l n d ⇔
           n < LENGTH l ∧ (f (EL n l) = SOME d) ∧
           ∀i.
             i < LENGTH l ⇒
             (f (EL i l) = NONE) ∨
             ∃d'. (f (EL i l) = SOME d') ∧ d ≤ d' ∧ (i < n ⇒ d < d')

   [lbtree_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION is_lbtree rep

   [lbtree_absrep]  Definition

      |- (∀a. lbtree_abs (lbtree_rep a) = a) ∧
         ∀r. is_lbtree r ⇔ (lbtree_rep (lbtree_abs r) = r)

   [lbtree_case_def]  Definition

      |- ∀e f t.
           lbtree_case e f t =
           if t = Lf then e
           else
             f (@a. ∃t1 t2. t = Nd a t1 t2) (@t1. ∃a t2. t = Nd a t1 t2)
               (@t2. ∃a t1. t = Nd a t1 t2)

   [map_def]  Definition

      |- ∀f.
           (map f Lf = Lf) ∧
           ∀a t1 t2. map f (Nd a t1 t2) = Nd (f a) (map f t1) (map f t2)

   [mem_def]  Definition

      |- mem =
         (λa0 a1.
            ∀mem'.
              (∀a0 a1.
                 (∃t1 t2. a1 = Nd a0 t1 t2) ∨
                 (∃b t1 t2. (a1 = Nd b t1 t2) ∧ mem' a0 t1) ∨
                 (∃b t1 t2. (a1 = Nd b t1 t2) ∧ mem' a0 t2) ⇒
                 mem' a0 a1) ⇒
              mem' a0 a1)

   [mindepth_def]  Definition

      |- ∀x t.
           lbtree$mindepth x t =
           if mem x t then SOME (LEAST n. lbtree$depth x t n) else NONE

   [optmin_curried_def]  Definition

      |- ∀x x1. lbtree$optmin x x1 = optmin_tupled (x,x1)

   [optmin_tupled_primitive_def]  Definition

      |- optmin_tupled =
         WFREC (@R. WF R)
           (λoptmin_tupled a.
              case a of
                (NONE,NONE) => I NONE
              | (NONE,SOME y) => I (SOME y)
              | (SOME x,NONE) => I (SOME x)
              | (SOME x,SOME y') => I (SOME (MIN x y')))

   [path_follow_def]  Definition

      |- (∀g x. path_follow g x [] = OPTION_MAP FST (g x)) ∧
         ∀g x h t.
           path_follow g x (h::t) =
           case g x of
             NONE => NONE
           | SOME (a,y,z) => path_follow g (if h then y else z) t

   [EXISTS_FIRST]  Theorem

      |- ∀l.
           EXISTS P l ⇒
           ∃l1 x l2. (l = l1 ++ x::l2) ∧ EVERY ($~ o P) l1 ∧ P x

   [Lf_NOT_Nd]  Theorem

      |- Lf ≠ Nd a t1 t2

   [Nd_11]  Theorem

      |- (Nd a1 t1 u1 = Nd a2 t2 u2) ⇔ (a1 = a2) ∧ (t1 = t2) ∧ (u1 = u2)

   [bf_flatten_append]  Theorem

      |- ∀l1. EVERY ($= Lf) l1 ⇒ (bf_flatten (l1 ++ l2) = bf_flatten l2)

   [bf_flatten_eq_lnil]  Theorem

      |- ∀l. (bf_flatten l = [||]) ⇔ EVERY ($= Lf) l

   [depth_cases]  Theorem

      |- ∀a0 a1 a2.
           lbtree$depth a0 a1 a2 ⇔
           (∃t1 t2. (a1 = Nd a0 t1 t2) ∧ (a2 = 0)) ∨
           (∃m a t1 t2.
              (a1 = Nd a t1 t2) ∧ (a2 = SUC m) ∧ lbtree$depth a0 t1 m) ∨
           ∃m a t1 t2.
             (a1 = Nd a t1 t2) ∧ (a2 = SUC m) ∧ lbtree$depth a0 t2 m

   [depth_ind]  Theorem

      |- ∀depth'.
           (∀x t1 t2. depth' x (Nd x t1 t2) 0) ∧
           (∀m x a t1 t2. depth' x t1 m ⇒ depth' x (Nd a t1 t2) (SUC m)) ∧
           (∀m x a t1 t2. depth' x t2 m ⇒ depth' x (Nd a t1 t2) (SUC m)) ⇒
           ∀a0 a1 a2. lbtree$depth a0 a1 a2 ⇒ depth' a0 a1 a2

   [depth_mem]  Theorem

      |- ∀x t n. lbtree$depth x t n ⇒ mem x t

   [depth_rules]  Theorem

      |- (∀x t1 t2. lbtree$depth x (Nd x t1 t2) 0) ∧
         (∀m x a t1 t2.
            lbtree$depth x t1 m ⇒ lbtree$depth x (Nd a t1 t2) (SUC m)) ∧
         ∀m x a t1 t2.
           lbtree$depth x t2 m ⇒ lbtree$depth x (Nd a t1 t2) (SUC m)

   [depth_strongind]  Theorem

      |- ∀depth'.
           (∀x t1 t2. depth' x (Nd x t1 t2) 0) ∧
           (∀m x a t1 t2.
              lbtree$depth x t1 m ∧ depth' x t1 m ⇒
              depth' x (Nd a t1 t2) (SUC m)) ∧
           (∀m x a t1 t2.
              lbtree$depth x t2 m ∧ depth' x t2 m ⇒
              depth' x (Nd a t1 t2) (SUC m)) ⇒
           ∀a0 a1 a2. lbtree$depth a0 a1 a2 ⇒ depth' a0 a1 a2

   [exists_bf_flatten]  Theorem

      |- exists ($= x) (bf_flatten tlist) ⇒ EXISTS (mem x) tlist

   [finite_cases]  Theorem

      |- ∀a0.
           finite a0 ⇔
           (a0 = Lf) ∨ ∃a t1 t2. (a0 = Nd a t1 t2) ∧ finite t1 ∧ finite t2

   [finite_ind]  Theorem

      |- ∀finite'.
           finite' Lf ∧
           (∀a t1 t2. finite' t1 ∧ finite' t2 ⇒ finite' (Nd a t1 t2)) ⇒
           ∀a0. finite a0 ⇒ finite' a0

   [finite_map]  Theorem

      |- finite (map f t) ⇔ finite t

   [finite_rules]  Theorem

      |- finite Lf ∧ ∀a t1 t2. finite t1 ∧ finite t2 ⇒ finite (Nd a t1 t2)

   [finite_strongind]  Theorem

      |- ∀finite'.
           finite' Lf ∧
           (∀a t1 t2.
              finite t1 ∧ finite' t1 ∧ finite t2 ∧ finite' t2 ⇒
              finite' (Nd a t1 t2)) ⇒
           ∀a0. finite a0 ⇒ finite' a0

   [finite_thm]  Theorem

      |- (finite Lf ⇔ T) ∧ (finite (Nd a t1 t2) ⇔ finite t1 ∧ finite t2)

   [lbtree_bisimulation]  Theorem

      |- ∀t u.
           (t = u) ⇔
           ∃R.
             R t u ∧
             ∀t u.
               R t u ⇒
               (t = Lf) ∧ (u = Lf) ∨
               ∃a t1 u1 t2 u2.
                 R t1 u1 ∧ R t2 u2 ∧ (t = Nd a t1 t2) ∧ (u = Nd a u1 u2)

   [lbtree_case_thm]  Theorem

      |- (lbtree_case e f Lf = e) ∧
         (lbtree_case e f (Nd a t1 t2) = f a t1 t2)

   [lbtree_cases]  Theorem

      |- ∀t. (t = Lf) ∨ ∃a t1 t2. t = Nd a t1 t2

   [lbtree_strong_bisimulation]  Theorem

      |- ∀t u.
           (t = u) ⇔
           ∃R.
             R t u ∧
             ∀t u.
               R t u ⇒
               (t = u) ∨
               ∃a t1 u1 t2 u2.
                 R t1 u1 ∧ R t2 u2 ∧ (t = Nd a t1 t2) ∧ (u = Nd a u1 u2)

   [lbtree_ue_Axiom]  Theorem

      |- ∀f.
           ∃!g.
             ∀x.
               g x =
               case f x of NONE => Lf | SOME (b,y,z) => Nd b (g y) (g z)

   [map_eq_Lf]  Theorem

      |- ((map f t = Lf) ⇔ (t = Lf)) ∧ ((Lf = map f t) ⇔ (t = Lf))

   [map_eq_Nd]  Theorem

      |- (map f t = Nd a t1 t2) ⇔
         ∃a' t1' t2'.
           (t = Nd a' t1' t2') ∧ (a = f a') ∧ (t1 = map f t1') ∧
           (t2 = map f t2')

   [mem_bf_flatten]  Theorem

      |- exists ($= x) (bf_flatten tlist) ⇔ EXISTS (mem x) tlist

   [mem_cases]  Theorem

      |- ∀a0 a1.
           mem a0 a1 ⇔
           (∃t1 t2. a1 = Nd a0 t1 t2) ∨
           (∃b t1 t2. (a1 = Nd b t1 t2) ∧ mem a0 t1) ∨
           ∃b t1 t2. (a1 = Nd b t1 t2) ∧ mem a0 t2

   [mem_depth]  Theorem

      |- ∀x t. mem x t ⇒ ∃n. lbtree$depth x t n

   [mem_ind]  Theorem

      |- ∀mem'.
           (∀a t1 t2. mem' a (Nd a t1 t2)) ∧
           (∀a b t1 t2. mem' a t1 ⇒ mem' a (Nd b t1 t2)) ∧
           (∀a b t1 t2. mem' a t2 ⇒ mem' a (Nd b t1 t2)) ⇒
           ∀a0 a1. mem a0 a1 ⇒ mem' a0 a1

   [mem_mindepth]  Theorem

      |- ∀x t. mem x t ⇒ ∃n. lbtree$mindepth x t = SOME n

   [mem_rules]  Theorem

      |- (∀a t1 t2. mem a (Nd a t1 t2)) ∧
         (∀a b t1 t2. mem a t1 ⇒ mem a (Nd b t1 t2)) ∧
         ∀a b t1 t2. mem a t2 ⇒ mem a (Nd b t1 t2)

   [mem_strongind]  Theorem

      |- ∀mem'.
           (∀a t1 t2. mem' a (Nd a t1 t2)) ∧
           (∀a b t1 t2. mem a t1 ∧ mem' a t1 ⇒ mem' a (Nd b t1 t2)) ∧
           (∀a b t1 t2. mem a t2 ∧ mem' a t2 ⇒ mem' a (Nd b t1 t2)) ⇒
           ∀a0 a1. mem a0 a1 ⇒ mem' a0 a1

   [mem_thm]  Theorem

      |- (mem a Lf ⇔ F) ∧
         (mem a (Nd b t1 t2) ⇔ (a = b) ∨ mem a t1 ∨ mem a t2)

   [mindepth_depth]  Theorem

      |- (lbtree$mindepth x t = SOME n) ⇒ lbtree$depth x t n

   [mindepth_thm]  Theorem

      |- (lbtree$mindepth x Lf = NONE) ∧
         (lbtree$mindepth x (Nd a t1 t2) =
          if x = a then SOME 0
          else
            OPTION_MAP SUC
              (lbtree$optmin (lbtree$mindepth x t1)
                 (lbtree$mindepth x t2)))

   [mmindex_EXISTS]  Theorem

      |- EXISTS (λe. ∃n. f e = SOME n) l ⇒ ∃i m. lbtree$is_mmindex f l i m

   [mmindex_unique]  Theorem

      |- lbtree$is_mmindex f l i m ⇒
         ∀j n. lbtree$is_mmindex f l j n ⇔ (j = i) ∧ (n = m)

   [optmin_def]  Theorem

      |- (lbtree$optmin NONE NONE = NONE) ∧
         (lbtree$optmin (SOME x) NONE = SOME x) ∧
         (lbtree$optmin NONE (SOME y) = SOME y) ∧
         (lbtree$optmin (SOME x) (SOME y) = SOME (MIN x y))

   [optmin_ind]  Theorem

      |- ∀P.
           P NONE NONE ∧ (∀x. P (SOME x) NONE) ∧ (∀y. P NONE (SOME y)) ∧
           (∀x y. P (SOME x) (SOME y)) ⇒
           ∀v v1. P v v1


*)
end
