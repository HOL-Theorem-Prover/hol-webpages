signature alistTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ALOOKUP_curried_def : thm
    val ALOOKUP_tupled_primitive_def : thm
    val alist_range_def : thm
    val alist_to_fmap_def : thm
    val fmap_to_alist_def : thm

  (*  Theorems  *)
    val ALL_DISTINCT_fmap_to_alist_keys : thm
    val ALOOKUP_ALL_DISTINCT_EL : thm
    val ALOOKUP_ALL_DISTINCT_MEM : thm
    val ALOOKUP_ALL_DISTINCT_PERM_same : thm
    val ALOOKUP_APPEND : thm
    val ALOOKUP_APPEND_same : thm
    val ALOOKUP_EQ_FLOOKUP : thm
    val ALOOKUP_FAILS : thm
    val ALOOKUP_FILTER : thm
    val ALOOKUP_IN_FRANGE : thm
    val ALOOKUP_LEAST_EL : thm
    val ALOOKUP_MAP : thm
    val ALOOKUP_MEM : thm
    val ALOOKUP_NONE : thm
    val ALOOKUP_SOME_FAPPLY_alist_to_fmap : thm
    val ALOOKUP_TABULATE : thm
    val ALOOKUP_ZIP_MAP_SND : thm
    val ALOOKUP_def : thm
    val ALOOKUP_ind : thm
    val ALOOKUP_prefix : thm
    val FDOM_alist_to_fmap : thm
    val FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE : thm
    val FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME : thm
    val FRANGE_alist_to_fmap_SUBSET : thm
    val FUNION_alist_to_fmap : thm
    val FUPDATE_LIST_EQ_APPEND_REVERSE : thm
    val IN_FRANGE_alist_to_fmap_suff : thm
    val LENGTH_fmap_to_alist : thm
    val MAP_KEYS_I : thm
    val MAP_values_fmap_to_alist : thm
    val MEM_fmap_to_alist : thm
    val MEM_fmap_to_alist_FLOOKUP : thm
    val MEM_pair_fmap_to_alist_FLOOKUP : thm
    val PERM_fmap_to_alist : thm
    val alist_to_fmap_APPEND : thm
    val alist_to_fmap_FAPPLY_MEM : thm
    val alist_to_fmap_MAP : thm
    val alist_to_fmap_MAP_matchable : thm
    val alist_to_fmap_MAP_values : thm
    val alist_to_fmap_PERM : thm
    val alist_to_fmap_prefix : thm
    val alist_to_fmap_thm : thm
    val alist_to_fmap_to_alist : thm
    val alist_to_fmap_to_alist_PERM : thm
    val alookup_distinct_reverse : thm
    val alookup_filter : thm
    val alookup_stable_sorted : thm
    val flookup_fupdate_list : thm
    val fmap_to_alist_FEMPTY : thm
    val fmap_to_alist_inj : thm
    val fmap_to_alist_preserves_FDOM : thm
    val fmap_to_alist_to_fmap : thm
    val fupdate_list_funion : thm
    val mem_to_flookup : thm
    val set_MAP_FST_fmap_to_alist : thm

  val alist_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "alist"

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

   [alist_range_def]  Definition

      |- ∀m. alist_range m = {v | ∃k. ALOOKUP m k = SOME v}

   [alist_to_fmap_def]  Definition

      |- ∀s. alist_to_fmap s = FOLDR (λ(k,v) f. f |+ (k,v)) FEMPTY s

   [fmap_to_alist_def]  Definition

      |- ∀s. fmap_to_alist s = MAP (λk. (k,s ' k)) (SET_TO_LIST (FDOM s))

   [ALL_DISTINCT_fmap_to_alist_keys]  Theorem

      |- ∀fm. ALL_DISTINCT (MAP FST (fmap_to_alist fm))

   [ALOOKUP_ALL_DISTINCT_EL]  Theorem

      |- ∀ls n.
           n < LENGTH ls ∧ ALL_DISTINCT (MAP FST ls) ⇒
           (ALOOKUP ls (FST (EL n ls)) = SOME (SND (EL n ls)))

   [ALOOKUP_ALL_DISTINCT_MEM]  Theorem

      |- ALL_DISTINCT (MAP FST al) ∧ MEM (k,v) al ⇒ (ALOOKUP al k = SOME v)

   [ALOOKUP_ALL_DISTINCT_PERM_same]  Theorem

      |- ∀l1 l2.
           ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) (MAP FST l2) ∧
           (set l1 = set l2) ⇒
           (ALOOKUP l1 = ALOOKUP l2)

   [ALOOKUP_APPEND]  Theorem

      |- ∀l1 l2 k.
           ALOOKUP (l1 ++ l2) k =
           case ALOOKUP l1 k of NONE => ALOOKUP l2 k | SOME v => SOME v

   [ALOOKUP_APPEND_same]  Theorem

      |- ∀l1 l2 l.
           (ALOOKUP l1 = ALOOKUP l2) ⇒
           (ALOOKUP (l1 ++ l) = ALOOKUP (l2 ++ l))

   [ALOOKUP_EQ_FLOOKUP]  Theorem

      |- (FLOOKUP (alist_to_fmap al) = ALOOKUP al) ∧
         (ALOOKUP (fmap_to_alist fm) = FLOOKUP fm)

   [ALOOKUP_FAILS]  Theorem

      |- (ALOOKUP l x = NONE) ⇔ ∀k v. MEM (k,v) l ⇒ k ≠ x

   [ALOOKUP_FILTER]  Theorem

      |- ∀ls x.
           ALOOKUP (FILTER (λ(k,v). P k) ls) x =
           if P x then ALOOKUP ls x else NONE

   [ALOOKUP_IN_FRANGE]  Theorem

      |- ∀ls k v. (ALOOKUP ls k = SOME v) ⇒ v ∈ FRANGE (alist_to_fmap ls)

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

      |- ∀l x. (ALOOKUP l x = NONE) ⇔ ¬MEM x (MAP FST l)

   [ALOOKUP_SOME_FAPPLY_alist_to_fmap]  Theorem

      |- ∀al k v. (ALOOKUP al k = SOME v) ⇒ (alist_to_fmap al ' k = v)

   [ALOOKUP_TABULATE]  Theorem

      |- MEM x l ⇒ (ALOOKUP (MAP (λk. (k,f k)) l) x = SOME (f x))

   [ALOOKUP_ZIP_MAP_SND]  Theorem

      |- ∀l1 l2 k f.
           (LENGTH l1 = LENGTH l2) ⇒
           (ALOOKUP (ZIP (l1,MAP f l2)) =
            OPTION_MAP f o ALOOKUP (ZIP (l1,l2)))

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

   [FRANGE_alist_to_fmap_SUBSET]  Theorem

      |- FRANGE (alist_to_fmap ls) ⊆ IMAGE SND (set ls)

   [FUNION_alist_to_fmap]  Theorem

      |- ∀ls fm. alist_to_fmap ls ⊌ fm = fm |++ REVERSE ls

   [FUPDATE_LIST_EQ_APPEND_REVERSE]  Theorem

      |- ∀ls fm. fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm)

   [IN_FRANGE_alist_to_fmap_suff]  Theorem

      |- (∀v. MEM v (MAP SND ls) ⇒ P v) ⇒
         ∀v. v ∈ FRANGE (alist_to_fmap ls) ⇒ P v

   [LENGTH_fmap_to_alist]  Theorem

      |- ∀fm. LENGTH (fmap_to_alist fm) = CARD (FDOM fm)

   [MAP_KEYS_I]  Theorem

      |- ∀fm. MAP_KEYS I fm = fm

   [MAP_values_fmap_to_alist]  Theorem

      |- ∀f fm.
           MAP (λ(k,v). (k,f v)) (fmap_to_alist fm) =
           fmap_to_alist (f o_f fm)

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

   [alist_to_fmap_MAP_matchable]  Theorem

      |- ∀f1 f2 al mal v.
           INJ f1 (set (MAP FST al)) 𝕌(:β) ∧
           (mal = MAP (λ(x,y). (f1 x,f2 y)) al) ∧
           (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ⇒
           (alist_to_fmap mal = v)

   [alist_to_fmap_MAP_values]  Theorem

      |- ∀f al.
           alist_to_fmap (MAP (λ(k,v). (k,f v)) al) =
           f o_f alist_to_fmap al

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

   [alookup_distinct_reverse]  Theorem

      |- ∀l k.
           ALL_DISTINCT (MAP FST l) ⇒ (ALOOKUP (REVERSE l) k = ALOOKUP l k)

   [alookup_filter]  Theorem

      |- ∀f l x. ALOOKUP l x = ALOOKUP (FILTER (λ(x',y). x = x') l) x

   [alookup_stable_sorted]  Theorem

      |- ∀R sort x l.
           transitive R ∧ total R ∧ STABLE sort (inv_image R FST) ⇒
           (ALOOKUP (sort (inv_image R FST) l) x = ALOOKUP l x)

   [flookup_fupdate_list]  Theorem

      |- ∀l k m.
           FLOOKUP (m |++ l) k =
           case ALOOKUP (REVERSE l) k of
             NONE => FLOOKUP m k
           | SOME v => SOME v

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

   [fupdate_list_funion]  Theorem

      |- ∀m l. m |++ l = FEMPTY |++ l ⊌ m

   [mem_to_flookup]  Theorem

      |- ∀x y l.
           ALL_DISTINCT (MAP FST l) ∧ MEM (x,y) l ⇒
           (FLOOKUP (FEMPTY |++ l) x = SOME y)

   [set_MAP_FST_fmap_to_alist]  Theorem

      |- set (MAP FST (fmap_to_alist fm)) = FDOM fm


*)
end
