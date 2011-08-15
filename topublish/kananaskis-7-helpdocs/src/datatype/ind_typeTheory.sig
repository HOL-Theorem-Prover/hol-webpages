signature ind_typeTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val BOTTOM : thm
    val CONSTR : thm
    val FCONS : thm
    val FNIL : thm
    val INJA : thm
    val INJF : thm
    val INJN : thm
    val INJP : thm
    val ISO : thm
    val NUMPAIR : thm
    val NUMPAIR_DEST : thm
    val NUMSUM : thm
    val NUMSUM_DEST : thm
    val ZBOT : thm
    val ZCONSTR : thm
    val ZRECSPACE_def : thm
    val recspace_TY_DEF : thm
    val recspace_repfns : thm
  
  (*  Theorems  *)
    val CONSTR_BOT : thm
    val CONSTR_IND : thm
    val CONSTR_INJ : thm
    val CONSTR_REC : thm
    val DEST_REC_INJ : thm
    val FCONS_DEST : thm
    val INJA_INJ : thm
    val INJF_INJ : thm
    val INJN_INJ : thm
    val INJP_INJ : thm
    val INJ_INVERSE2 : thm
    val ISO_FUN : thm
    val ISO_REFL : thm
    val ISO_USAGE : thm
    val MK_REC_INJ : thm
    val NUMPAIR_INJ : thm
    val NUMPAIR_INJ_LEMMA : thm
    val NUMSUM_INJ : thm
    val ZCONSTR_ZBOT : thm
    val ZRECSPACE_cases : thm
    val ZRECSPACE_ind : thm
    val ZRECSPACE_rules : thm
    val ZRECSPACE_strongind : thm
  
  val ind_type_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [numeral] Parent theory of "ind_type"
   
   [while] Parent theory of "ind_type"
   
   [BOTTOM]  Definition
      
      |- ind_type$BOTTOM = mk_rec ind_type$ZBOT
   
   [CONSTR]  Definition
      
      |- ∀c i r.
           ind_type$CONSTR c i r =
           mk_rec (ind_type$ZCONSTR c i (λn. dest_rec (r n)))
   
   [FCONS]  Definition
      
      |- (∀a f. ind_type$FCONS a f 0 = a) ∧
         ∀a f n. ind_type$FCONS a f (SUC n) = f n
   
   [FNIL]  Definition
      
      |- ∀n. ind_type$FNIL n = ARB
   
   [INJA]  Definition
      
      |- ∀a. ind_type$INJA a = (λn b. b = a)
   
   [INJF]  Definition
      
      |- ∀f. ind_type$INJF f = (λn. f (NUMFST n) (NUMSND n))
   
   [INJN]  Definition
      
      |- ∀m. ind_type$INJN m = (λn a. n = m)
   
   [INJP]  Definition
      
      |- ∀f1 f2.
           ind_type$INJP f1 f2 =
           (λn a.
              if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a)
   
   [ISO]  Definition
      
      |- ∀f g. ind_type$ISO f g ⇔ (∀x. f (g x) = x) ∧ ∀y. g (f y) = y
   
   [NUMPAIR]  Definition
      
      |- ∀x y. ind_type$NUMPAIR x y = 2 ** x * (2 * y + 1)
   
   [NUMPAIR_DEST]  Definition
      
      |- ∀x y.
           (NUMFST (ind_type$NUMPAIR x y) = x) ∧
           (NUMSND (ind_type$NUMPAIR x y) = y)
   
   [NUMSUM]  Definition
      
      |- ∀b x. ind_type$NUMSUM b x = if b then SUC (2 * x) else 2 * x
   
   [NUMSUM_DEST]  Definition
      
      |- ∀x y.
           (NUMLEFT (ind_type$NUMSUM x y) ⇔ x) ∧
           (NUMRIGHT (ind_type$NUMSUM x y) = y)
   
   [ZBOT]  Definition
      
      |- ind_type$ZBOT = ind_type$INJP (ind_type$INJN 0) (@z. T)
   
   [ZCONSTR]  Definition
      
      |- ∀c i r.
           ind_type$ZCONSTR c i r =
           ind_type$INJP (ind_type$INJN (SUC c))
             (ind_type$INJP (ind_type$INJA i) (ind_type$INJF r))
   
   [ZRECSPACE_def]  Definition
      
      |- ZRECSPACE =
         (λa0.
            ∀ZRECSPACE'.
              (∀a0.
                 (a0 = ind_type$ZBOT) ∨
                 (∃c i r.
                    (a0 = ind_type$ZCONSTR c i r) ∧ ∀n. ZRECSPACE' (r n)) ⇒
                 ZRECSPACE' a0) ⇒
              ZRECSPACE' a0)
   
   [recspace_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION ZRECSPACE rep
   
   [recspace_repfns]  Definition
      
      |- (∀a. mk_rec (dest_rec a) = a) ∧
         ∀r. ZRECSPACE r ⇔ (dest_rec (mk_rec r) = r)
   
   [CONSTR_BOT]  Theorem
      
      |- ∀c i r. ind_type$CONSTR c i r ≠ ind_type$BOTTOM
   
   [CONSTR_IND]  Theorem
      
      |- ∀P.
           P ind_type$BOTTOM ∧
           (∀c i r. (∀n. P (r n)) ⇒ P (ind_type$CONSTR c i r)) ⇒
           ∀x. P x
   
   [CONSTR_INJ]  Theorem
      
      |- ∀c1 i1 r1 c2 i2 r2.
           (ind_type$CONSTR c1 i1 r1 = ind_type$CONSTR c2 i2 r2) ⇔
           (c1 = c2) ∧ (i1 = i2) ∧ (r1 = r2)
   
   [CONSTR_REC]  Theorem
      
      |- ∀Fn.
           ∃f. ∀c i r. f (ind_type$CONSTR c i r) = Fn c i r (λn. f (r n))
   
   [DEST_REC_INJ]  Theorem
      
      |- ∀x y. (dest_rec x = dest_rec y) ⇔ (x = y)
   
   [FCONS_DEST]  Theorem
      
      |- ind_type$FCONS a f n = if n = 0 then a else f (n − 1)
   
   [INJA_INJ]  Theorem
      
      |- ∀a1 a2. (ind_type$INJA a1 = ind_type$INJA a2) ⇔ (a1 = a2)
   
   [INJF_INJ]  Theorem
      
      |- ∀f1 f2. (ind_type$INJF f1 = ind_type$INJF f2) ⇔ (f1 = f2)
   
   [INJN_INJ]  Theorem
      
      |- ∀n1 n2. (ind_type$INJN n1 = ind_type$INJN n2) ⇔ (n1 = n2)
   
   [INJP_INJ]  Theorem
      
      |- ∀f1 f1' f2 f2'.
           (ind_type$INJP f1 f2 = ind_type$INJP f1' f2') ⇔
           (f1 = f1') ∧ (f2 = f2')
   
   [INJ_INVERSE2]  Theorem
      
      |- ∀P.
           (∀x1 y1 x2 y2. (P x1 y1 = P x2 y2) ⇔ (x1 = x2) ∧ (y1 = y2)) ⇒
           ∃X Y. ∀x y. (X (P x y) = x) ∧ (Y (P x y) = y)
   
   [ISO_FUN]  Theorem
      
      |- ind_type$ISO f f' ∧ ind_type$ISO g g' ⇒
         ind_type$ISO (λh a'. g (h (f' a'))) (λh a. g' (h (f a)))
   
   [ISO_REFL]  Theorem
      
      |- ind_type$ISO (λx. x) (λx. x)
   
   [ISO_USAGE]  Theorem
      
      |- ind_type$ISO f g ⇒
         (∀P. (∀x. P x) ⇔ ∀x. P (g x)) ∧ (∀P. (∃x. P x) ⇔ ∃x. P (g x)) ∧
         ∀a b. (a = g b) ⇔ (f a = b)
   
   [MK_REC_INJ]  Theorem
      
      |- ∀x y. (mk_rec x = mk_rec y) ⇒ ZRECSPACE x ∧ ZRECSPACE y ⇒ (x = y)
   
   [NUMPAIR_INJ]  Theorem
      
      |- ∀x1 y1 x2 y2.
           (ind_type$NUMPAIR x1 y1 = ind_type$NUMPAIR x2 y2) ⇔
           (x1 = x2) ∧ (y1 = y2)
   
   [NUMPAIR_INJ_LEMMA]  Theorem
      
      |- ∀x1 y1 x2 y2.
           (ind_type$NUMPAIR x1 y1 = ind_type$NUMPAIR x2 y2) ⇒ (x1 = x2)
   
   [NUMSUM_INJ]  Theorem
      
      |- ∀b1 x1 b2 x2.
           (ind_type$NUMSUM b1 x1 = ind_type$NUMSUM b2 x2) ⇔
           (b1 ⇔ b2) ∧ (x1 = x2)
   
   [ZCONSTR_ZBOT]  Theorem
      
      |- ∀c i r. ind_type$ZCONSTR c i r ≠ ind_type$ZBOT
   
   [ZRECSPACE_cases]  Theorem
      
      |- ∀a0.
           ZRECSPACE a0 ⇔
           (a0 = ind_type$ZBOT) ∨
           ∃c i r. (a0 = ind_type$ZCONSTR c i r) ∧ ∀n. ZRECSPACE (r n)
   
   [ZRECSPACE_ind]  Theorem
      
      |- ∀ZRECSPACE'.
           ZRECSPACE' ind_type$ZBOT ∧
           (∀c i r.
              (∀n. ZRECSPACE' (r n)) ⇒
              ZRECSPACE' (ind_type$ZCONSTR c i r)) ⇒
           ∀a0. ZRECSPACE a0 ⇒ ZRECSPACE' a0
   
   [ZRECSPACE_rules]  Theorem
      
      |- ZRECSPACE ind_type$ZBOT ∧
         ∀c i r. (∀n. ZRECSPACE (r n)) ⇒ ZRECSPACE (ind_type$ZCONSTR c i r)
   
   [ZRECSPACE_strongind]  Theorem
      
      |- ∀ZRECSPACE'.
           ZRECSPACE' ind_type$ZBOT ∧
           (∀c i r.
              (∀n. ZRECSPACE (r n) ∧ ZRECSPACE' (r n)) ⇒
              ZRECSPACE' (ind_type$ZCONSTR c i r)) ⇒
           ∀a0. ZRECSPACE a0 ⇒ ZRECSPACE' a0
   
   
*)
end
