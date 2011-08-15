signature alistTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ALOOKUP_curried_def : thm
    val ALOOKUP_tupled_primitive_def : thm
    val alist_to_fmap_def : thm
    val fmap_to_alist_def : thm
  
  (*  Theorems  *)
    val ALOOKUP_EQ_FLOOKUP : thm
    val ALOOKUP_FAILS : thm
    val ALOOKUP_MEM : thm
    val ALOOKUP_TABULATE : thm
    val ALOOKUP_def : thm
    val ALOOKUP_ind : thm
    val ALOOKUP_prefix : thm
    val FDOM_alist_to_fmap : thm
    val FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE : thm
    val FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME : thm
    val FUPDATE_LIST_EQ_APPEND_REVERSE : thm
    val MEM_fmap_to_alist : thm
    val alist_to_fmap_prefix : thm
    val alist_to_fmap_thm : thm
    val fmap_to_alist_FEMPTY : thm
    val fmap_to_alist_to_fmap : thm
  
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
                 ([],q) -> I NONE
              || ((x,y)::t,q) ->
                   I (if x = q then SOME y else ALOOKUP_tupled (t,q)))
   
   [alist_to_fmap_def]  Definition
      
      |- ∀s. alist_to_fmap s = FOLDR (λ(k,v) f. f |+ (k,v)) FEMPTY s
   
   [fmap_to_alist_def]  Definition
      
      |- ∀s. fmap_to_alist s = MAP (λk. (k,s ' k)) (SET_TO_LIST (FDOM s))
   
   [ALOOKUP_EQ_FLOOKUP]  Theorem
      
      |- (FLOOKUP (alist_to_fmap al) = ALOOKUP al) ∧
         (ALOOKUP (fmap_to_alist fm) = FLOOKUP fm)
   
   [ALOOKUP_FAILS]  Theorem
      
      |- (ALOOKUP l x = NONE) ⇔ ∀k v. MEM (k,v) l ⇒ k ≠ x
   
   [ALOOKUP_MEM]  Theorem
      
      |- ∀al k v. (ALOOKUP al k = SOME v) ⇒ MEM (k,v) al
   
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
   
   [FUPDATE_LIST_EQ_APPEND_REVERSE]  Theorem
      
      |- ∀ls fm. fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm)
   
   [MEM_fmap_to_alist]  Theorem
      
      |- MEM (x,y) (fmap_to_alist fm) ⇔ x ∈ FDOM fm ∧ (fm ' x = y)
   
   [alist_to_fmap_prefix]  Theorem
      
      |- ∀ls l1 l2.
           (alist_to_fmap l1 = alist_to_fmap l2) ⇒
           (alist_to_fmap (ls ++ l1) = alist_to_fmap (ls ++ l2))
   
   [alist_to_fmap_thm]  Theorem
      
      |- (alist_to_fmap [] = FEMPTY) ∧
         (alist_to_fmap ((k,v)::t) = alist_to_fmap t |+ (k,v))
   
   [fmap_to_alist_FEMPTY]  Theorem
      
      |- fmap_to_alist FEMPTY = []
   
   [fmap_to_alist_to_fmap]  Theorem
      
      |- alist_to_fmap (fmap_to_alist fm) = fm
   
   
*)
end
