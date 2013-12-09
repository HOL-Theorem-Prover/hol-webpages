signature alistTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ALOOKUP_curried_def : thm
    val ALOOKUP_tupled_primitive_def : thm
    val alist_to_fmap_def : thm
    val fmap_to_alist_def : thm

  (*  Theorems  *)
    val ALL_DISTINCT_fmap_to_alist_keys : thm
    val ALOOKUP_ALL_DISTINCT_MEM : thm
    val ALOOKUP_APPEND : thm
    val ALOOKUP_EQ_FLOOKUP : thm
    val ALOOKUP_FAILS : thm
    val ALOOKUP_LEAST_EL : thm
    val ALOOKUP_MAP : thm
    val ALOOKUP_MEM : thm
    val ALOOKUP_NONE : thm
    val ALOOKUP_SOME_FAPPLY_alist_to_fmap : thm
    val ALOOKUP_TABULATE : thm
    val ALOOKUP_def : thm
    val ALOOKUP_ind : thm
    val ALOOKUP_prefix : thm
    val FDOM_alist_to_fmap : thm
    val FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE : thm
    val FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME : thm
    val FUNION_alist_to_fmap : thm
    val FUPDATE_LIST_EQ_APPEND_REVERSE : thm
    val LENGTH_fmap_to_alist : thm
    val MEM_fmap_to_alist : thm
    val MEM_fmap_to_alist_FLOOKUP : thm
    val MEM_pair_fmap_to_alist_FLOOKUP : thm
    val PERM_fmap_to_alist : thm
    val alist_to_fmap_APPEND : thm
    val alist_to_fmap_FAPPLY_MEM : thm
    val alist_to_fmap_MAP : thm
    val alist_to_fmap_PERM : thm
    val alist_to_fmap_prefix : thm
    val alist_to_fmap_thm : thm
    val alist_to_fmap_to_alist : thm
    val alist_to_fmap_to_alist_PERM : thm
    val fmap_to_alist_FEMPTY : thm
    val fmap_to_alist_inj : thm
    val fmap_to_alist_preserves_FDOM : thm
    val fmap_to_alist_to_fmap : thm

  val alist_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "alist"

   [sorting] Parent theory of "alist"

   [ALOOKUP_curried_def]  Definition

      |- ∀x x1. ALOOKUP x x1 = ALOOKUP_tupled (x,x1)

   [ALOOKUP_tupled_primitive_def]  Definition

      |- ALOOKUP_tupled =
         WFREC (@R. WF R ∧ ∀y t q x. x ≠ q ⇒ R (t,q) ((x,y)::t,q))
           (λALOOKUP_tupled a.
              case a of
                ([],q) => I NONE
              | ((x,y)::t,q) =>
                  I (if x = q then SOME y else ALOOKUP_tupled (t,q)))

   [alist_to_fmap_def]  Definition

      |- ∀s. alist_to_fmap s = FOLDR (λ(k,v) f. f |+ (k,v)) FEMPTY s

   [fmap_to_alist_def]  Definition

      |- ∀s. fmap_to_alist s = MAP (λk. (k,s ' k)) (SET_TO_LIST (FDOM s))

   [ALL_DISTINCT_fmap_to_alist_keys]  Theorem

      |- ∀fm. ALL_DISTINCT (MAP FST (fmap_to_alist fm))

   [ALOOKUP_ALL_DISTINCT_MEM]  Theorem

      |- ALL_DISTINCT (MAP FST al) ∧ MEM (k,v) al ⇒ (ALOOKUP al k = SOME v)

   [ALOOKUP_APPEND]  Theorem

      |- ∀l1 l2 k.
           ALOOKUP (l1 ++ l2) k =
           case ALOOKUP l1 k of NONE => ALOOKUP l2 k | SOME v => SOME v

   [ALOOKUP_EQ_FLOOKUP]  Theorem

      |- (FLOOKUP (alist_to_fmap al) = ALOOKUP al) ∧
         (ALOOKUP (fmap_to_alist fm) = FLOOKUP fm)

   [ALOOKUP_FAILS]  Theorem

      |- (ALOOKUP l x = NONE) ⇔ ∀k v. MEM (k,v) l ⇒ k ≠ x

   [ALOOKUP_LEAST_EL]  Theorem

      |- ∀ls k.
           ALOOKUP ls k =
           if MEM k (MAP FST ls) then
             SOME (EL (LEAST n. EL n (MAP FST ls) = k) (MAP SND ls))
           else NONE

   [ALOOKUP_MAP]  Theorem

      |- ∀f al.
           ALOOKUP (MAP (λ(x,y). (x,f y)) al) = OPTION_MAP f o ALOOKUP al

   [ALOOKUP_MEM]  Theorem

      |- ∀al k v. (ALOOKUP al k = SOME v) ⇒ MEM (k,v) al

   [ALOOKUP_NONE]  Theorem

      |- ∀l x. (ALOOKUP l x = NONE) ⇔ x ∉ set (MAP FST l)

   [ALOOKUP_SOME_FAPPLY_alist_to_fmap]  Theorem

      |- ∀al k v. (ALOOKUP al k = SOME v) ⇒ (alist_to_fmap al ' k = v)

   [ALOOKUP_TABULATE]  Theorem

      |- ALL_DISTINCT l ∧ MEM x l ⇒
         (ALOOKUP (MAP (λk. (k,f k)) l) x = SOME (f x))

   [ALOOKUP_def]  Theorem

      |- (∀q. ALOOKUP [] q = NONE) ∧
         ∀y x t q.
           ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q

   [ALOOKUP_ind]  Theorem

      |- ∀P.
           (∀q. P [] q) ∧ (∀x y t q. (x ≠ q ⇒ P t q) ⇒ P ((x,y)::t) q) ⇒
           ∀v v1. P v v1

   [ALOOKUP_prefix]  Theorem

      |- ∀ls k ls2.
           ((ALOOKUP ls k = SOME v) ⇒ (ALOOKUP (ls ++ ls2) k = SOME v)) ∧
           ((ALOOKUP ls k = NONE) ⇒
            (ALOOKUP (ls ++ ls2) k = ALOOKUP ls2 k))

   [FDOM_alist_to_fmap]  Theorem

      |- ∀al. FDOM (alist_to_fmap al) = set (MAP FST al)

   [FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE]  Theorem

      |- (ALOOKUP ls k = NONE) ⇒
         (FLOOKUP (fm |++ REVERSE ls) k = FLOOKUP fm k)

   [FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME]  Theorem

      |- (ALOOKUP ls k = SOME v) ⇒ (FLOOKUP (fm |++ REVERSE ls) k = SOME v)

   [FUNION_alist_to_fmap]  Theorem

      |- ∀ls fm. alist_to_fmap ls ⊌ fm = fm |++ REVERSE ls

   [FUPDATE_LIST_EQ_APPEND_REVERSE]  Theorem

      |- ∀ls fm. fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm)

   [LENGTH_fmap_to_alist]  Theorem

      |- ∀fm. LENGTH (fmap_to_alist fm) = CARD (FDOM fm)

   [MEM_fmap_to_alist]  Theorem

      |- MEM (x,y) (fmap_to_alist fm) ⇔ x ∈ FDOM fm ∧ (fm ' x = y)

   [MEM_fmap_to_alist_FLOOKUP]  Theorem

      |- ∀p fm.
           MEM p (fmap_to_alist fm) ⇔ (FLOOKUP fm (FST p) = SOME (SND p))

   [MEM_pair_fmap_to_alist_FLOOKUP]  Theorem

      |- ∀x y fm. MEM (x,y) (fmap_to_alist fm) ⇔ (FLOOKUP fm x = SOME y)

   [PERM_fmap_to_alist]  Theorem

      |- PERM (fmap_to_alist fm1) (fmap_to_alist fm2) ⇔ (fm1 = fm2)

   [alist_to_fmap_APPEND]  Theorem

      |- ∀l1 l2.
           alist_to_fmap (l1 ++ l2) = alist_to_fmap l1 ⊌ alist_to_fmap l2

   [alist_to_fmap_FAPPLY_MEM]  Theorem

      |- ∀al z.
           z ∈ FDOM (alist_to_fmap al) ⇒ MEM (z,alist_to_fmap al ' z) al

   [alist_to_fmap_MAP]  Theorem

      |- ∀f1 f2 al.
           INJ f1 (set (MAP FST al)) 𝕌(:β) ⇒
           (alist_to_fmap (MAP (λ(x,y). (f1 x,f2 y)) al) =
            MAP_KEYS f1 (f2 o_f alist_to_fmap al))

   [alist_to_fmap_PERM]  Theorem

      |- ∀l1 l2.
           PERM l1 l2 ∧ ALL_DISTINCT (MAP FST l1) ⇒
           (alist_to_fmap l1 = alist_to_fmap l2)

   [alist_to_fmap_prefix]  Theorem

      |- ∀ls l1 l2.
           (alist_to_fmap l1 = alist_to_fmap l2) ⇒
           (alist_to_fmap (ls ++ l1) = alist_to_fmap (ls ++ l2))

   [alist_to_fmap_thm]  Theorem

      |- (alist_to_fmap [] = FEMPTY) ∧
         (alist_to_fmap ((k,v)::t) = alist_to_fmap t |+ (k,v))

   [alist_to_fmap_to_alist]  Theorem

      |- ∀al.
           fmap_to_alist (alist_to_fmap al) =
           MAP (λk. (k,THE (ALOOKUP al k)))
             (SET_TO_LIST (set (MAP FST al)))

   [alist_to_fmap_to_alist_PERM]  Theorem

      |- ∀al.
           ALL_DISTINCT (MAP FST al) ⇒
           PERM (fmap_to_alist (alist_to_fmap al)) al

   [fmap_to_alist_FEMPTY]  Theorem

      |- fmap_to_alist FEMPTY = []

   [fmap_to_alist_inj]  Theorem

      |- ∀f1 f2. (fmap_to_alist f1 = fmap_to_alist f2) ⇒ (f1 = f2)

   [fmap_to_alist_preserves_FDOM]  Theorem

      |- ∀fm1 fm2.
           (FDOM fm1 = FDOM fm2) ⇒
           (MAP FST (fmap_to_alist fm1) = MAP FST (fmap_to_alist fm2))

   [fmap_to_alist_to_fmap]  Theorem

      |- alist_to_fmap (fmap_to_alist fm) = fm


*)
end
