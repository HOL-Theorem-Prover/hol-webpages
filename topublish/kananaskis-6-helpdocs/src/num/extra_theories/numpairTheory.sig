signature numpairTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val invtri0_curried_def : thm
    val invtri0_tupled_primitive_def : thm
    val invtri_def : thm
    val napp_def : thm
    val ncons_def : thm
    val nfoldl_def : thm
    val nfst_def : thm
    val nlen_def : thm
    val nlistrec_curried_def : thm
    val nlistrec_tupled_primitive_def : thm
    val nmap_def : thm
    val npair_def : thm
    val nsnd_def : thm
    val tri_def : thm
  
  (*  Theorems  *)
    val SND_invtri0 : thm
    val invtri0_def : thm
    val invtri0_ind : thm
    val invtri0_thm : thm
    val invtri_le : thm
    val invtri_linverse : thm
    val invtri_linverse_r : thm
    val invtri_lower : thm
    val invtri_unique : thm
    val invtri_upper : thm
    val napp_thm : thm
    val ncons_11 : thm
    val ncons_not_nnil : thm
    val nfoldl_thm : thm
    val nfst_le : thm
    val nfst_npair : thm
    val nlen_thm : thm
    val nlist_cases : thm
    val nlist_ind : thm
    val nlistrec_thm : thm
    val nmap_thm : thm
    val npair : thm
    val npair_11 : thm
    val npair_cases : thm
    val nsnd_le : thm
    val nsnd_npair : thm
    val tri_11 : thm
    val tri_LE : thm
    val tri_LT : thm
    val tri_LT_I : thm
    val tri_eq_0 : thm
    val tri_formula : thm
    val tri_le : thm
    val twotri_formula : thm
  
  val numpair_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [basicSize] Parent theory of "numpair"
   
   [while] Parent theory of "numpair"
   
   [invtri0_curried_def]  Definition
      
      |- ∀x x1. invtri0 x x1 = invtri0_tupled (x,x1)
   
   [invtri0_tupled_primitive_def]  Definition
      
      |- invtri0_tupled =
         WFREC (@R. WF R ∧ ∀a n. ¬(n < a + 1) ⇒ R (n − (a + 1),a + 1) (n,a))
           (λinvtri0_tupled a'.
              case a' of
                 (n,a) ->
                   I
                     (if n < a + 1 then
                        (n,a)
                      else
                        invtri0_tupled (n − (a + 1),a + 1)))
   
   [invtri_def]  Definition
      
      |- ∀n. tri⁻¹ n = SND (invtri0 n 0)
   
   [napp_def]  Definition
      
      |- ∀l1 l2. napp l1 l2 = nlistrec l2 (λn t r. ncons n r) l1
   
   [ncons_def]  Definition
      
      |- ∀h t. ncons h t = h ⊗ t + 1
   
   [nfoldl_def]  Definition
      
      |- ∀f a l. nfoldl f a l = nlistrec (λa. a) (λn t r a. r (f n a)) l a
   
   [nfst_def]  Definition
      
      |- ∀n. nfst n = tri (tri⁻¹ n) + tri⁻¹ n − n
   
   [nlen_def]  Definition
      
      |- nlen = nlistrec 0 (λn t r. r + 1)
   
   [nlistrec_curried_def]  Definition
      
      |- ∀x x1 x2. nlistrec x x1 x2 = nlistrec_tupled (x,x1,x2)
   
   [nlistrec_tupled_primitive_def]  Definition
      
      |- nlistrec_tupled =
         WFREC (@R. WF R ∧ ∀f n l. l ≠ 0 ⇒ R (n,f,nsnd (l − 1)) (n,f,l))
           (λnlistrec_tupled a.
              case a of
                 (n,f,l) ->
                   I
                     (if l = 0 then
                        n
                      else
                        f (nfst (l − 1)) (nsnd (l − 1))
                          (nlistrec_tupled (n,f,nsnd (l − 1)))))
   
   [nmap_def]  Definition
      
      |- ∀f. nmap f = nlistrec 0 (λn t r. ncons (f n) r)
   
   [npair_def]  Definition
      
      |- ∀m n. m ⊗ n = tri (m + n) + n
   
   [nsnd_def]  Definition
      
      |- ∀n. nsnd n = n − tri (tri⁻¹ n)
   
   [tri_def]  Definition
      
      |- (tri 0 = 0) ∧ ∀n. tri (SUC n) = SUC n + tri n
   
   [SND_invtri0]  Theorem
      
      |- ∀n a. FST (invtri0 n a) < SUC (SND (invtri0 n a))
   
   [invtri0_def]  Theorem
      
      |- ∀n a.
           invtri0 n a = if n < a + 1 then (n,a) else invtri0 (n − (a + 1)) (a + 1)
   
   [invtri0_ind]  Theorem
      
      |- ∀P. (∀n a. (¬(n < a + 1) ⇒ P (n − (a + 1)) (a + 1)) ⇒ P n a) ⇒ ∀v v1. P v v1
   
   [invtri0_thm]  Theorem
      
      |- ∀n a. tri (SND (invtri0 n a)) + FST (invtri0 n a) = n + tri a
   
   [invtri_le]  Theorem
      
      |- tri⁻¹ n ≤ n
   
   [invtri_linverse]  Theorem
      
      |- tri⁻¹ (tri n) = n
   
   [invtri_linverse_r]  Theorem
      
      |- y ≤ x ⇒ (tri⁻¹ (tri x + y) = x)
   
   [invtri_lower]  Theorem
      
      |- tri (tri⁻¹ n) ≤ n
   
   [invtri_unique]  Theorem
      
      |- tri y ≤ n ∧ n < tri (y + 1) ⇒ (tri⁻¹ n = y)
   
   [invtri_upper]  Theorem
      
      |- n < tri (tri⁻¹ n + 1)
   
   [napp_thm]  Theorem
      
      |- (napp 0 nlist = nlist) ∧ (napp (ncons h t) nlist = ncons h (napp t nlist))
   
   [ncons_11]  Theorem
      
      |- (ncons x y = ncons h t) ⇔ (x = h) ∧ (y = t)
   
   [ncons_not_nnil]  Theorem
      
      |- ncons x y ≠ 0
   
   [nfoldl_thm]  Theorem
      
      |- (nfoldl f a 0 = a) ∧ (nfoldl f a (ncons h t) = nfoldl f (f h a) t)
   
   [nfst_le]  Theorem
      
      |- nfst n ≤ n
   
   [nfst_npair]  Theorem
      
      |- nfst (x ⊗ y) = x
   
   [nlen_thm]  Theorem
      
      |- (nlen 0 = 0) ∧ (nlen (ncons h t) = nlen t + 1)
   
   [nlist_cases]  Theorem
      
      |- ∀n. (n = 0) ∨ ∃h t. n = ncons h t
   
   [nlist_ind]  Theorem
      
      |- ∀P. P 0 ∧ (∀h t. P t ⇒ P (ncons h t)) ⇒ ∀n. P n
   
   [nlistrec_thm]  Theorem
      
      |- (nlistrec n f 0 = n) ∧ (nlistrec n f (ncons h t) = f h t (nlistrec n f t))
   
   [nmap_thm]  Theorem
      
      |- (nmap f 0 = 0) ∧ (nmap f (ncons h t) = ncons (f h) (nmap f t))
   
   [npair]  Theorem
      
      |- ∀n. nfst n ⊗ nsnd n = n
   
   [npair_11]  Theorem
      
      |- (x₁ ⊗ y₁ = x₂ ⊗ y₂) ⇔ (x₁ = x₂) ∧ (y₁ = y₂)
   
   [npair_cases]  Theorem
      
      |- ∀n. ∃x y. n = x ⊗ y
   
   [nsnd_le]  Theorem
      
      |- nsnd n ≤ n
   
   [nsnd_npair]  Theorem
      
      |- nsnd (x ⊗ y) = y
   
   [tri_11]  Theorem
      
      |- ∀m n. (tri m = tri n) ⇔ (m = n)
   
   [tri_LE]  Theorem
      
      |- ∀m n. tri m ≤ tri n ⇔ m ≤ n
   
   [tri_LT]  Theorem
      
      |- ∀n m. tri n < tri m ⇔ n < m
   
   [tri_LT_I]  Theorem
      
      |- ∀n m. n < m ⇒ tri n < tri m
   
   [tri_eq_0]  Theorem
      
      |- ((tri n = 0) ⇔ (n = 0)) ∧ ((0 = tri n) ⇔ (n = 0))
   
   [tri_formula]  Theorem
      
      |- tri n = n * (n + 1) DIV 2
   
   [tri_le]  Theorem
      
      |- n ≤ tri n
   
   [twotri_formula]  Theorem
      
      |- 2 * tri n = n * (n + 1)
   
   
*)
end
