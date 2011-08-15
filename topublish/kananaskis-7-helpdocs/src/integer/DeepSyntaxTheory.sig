signature DeepSyntaxTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val Aset_def : thm
    val Bset_def : thm
    val alldivide_def : thm
    val deep_form_TY_DEF : thm
    val deep_form_case_def : thm
    val deep_form_repfns : thm
    val deep_form_size_def : thm
    val eval_form_def : thm
    val neginf_def : thm
    val posinf_def : thm
  
  (*  Theorems  *)
    val add_d_neginf : thm
    val add_d_posinf : thm
    val datatype_deep_form : thm
    val deep_form_11 : thm
    val deep_form_Axiom : thm
    val deep_form_case_cong : thm
    val deep_form_distinct : thm
    val deep_form_induction : thm
    val deep_form_nchotomy : thm
    val in_aset : thm
    val in_bset : thm
    val neginf_disj1_implies_exoriginal : thm
    val neginf_exoriginal_eq_rhs : thm
    val neginf_exoriginal_implies_rhs : thm
    val neginf_ok : thm
    val posinf_disj1_implies_exoriginal : thm
    val posinf_exoriginal_eq_rhs : thm
    val posinf_exoriginal_implies_rhs : thm
    val posinf_ok : thm
  
  val DeepSyntax_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [int_arith] Parent theory of "DeepSyntax"
   
   [Aset_def]  Definition
      
      |- (∀pos f1 f2. Aset pos (Conjn f1 f2) = Aset pos f1 ∪ Aset pos f2) ∧
         (∀pos f1 f2. Aset pos (Disjn f1 f2) = Aset pos f1 ∪ Aset pos f2) ∧
         (∀pos f. Aset pos (Negn f) = Aset (¬pos) f) ∧
         (∀pos b. Aset pos (UnrelatedBool b) = ∅) ∧
         (∀pos i. Aset pos (xLT i) = if pos then {i} else ∅) ∧
         (∀pos i. Aset pos (LTx i) = if pos then ∅ else {i + 1}) ∧
         (∀pos i. Aset pos (xEQ i) = if pos then {i + 1} else {i}) ∧
         ∀pos i1 i2. Aset pos (xDivided i1 i2) = ∅
   
   [Bset_def]  Definition
      
      |- (∀pos f1 f2. Bset pos (Conjn f1 f2) = Bset pos f1 ∪ Bset pos f2) ∧
         (∀pos f1 f2. Bset pos (Disjn f1 f2) = Bset pos f1 ∪ Bset pos f2) ∧
         (∀pos f. Bset pos (Negn f) = Bset (¬pos) f) ∧
         (∀pos b. Bset pos (UnrelatedBool b) = ∅) ∧
         (∀pos i. Bset pos (xLT i) = if pos then ∅ else {i + -1}) ∧
         (∀pos i. Bset pos (LTx i) = if pos then {i} else ∅) ∧
         (∀pos i. Bset pos (xEQ i) = if pos then {i + -1} else {i}) ∧
         ∀pos i1 i2. Bset pos (xDivided i1 i2) = ∅
   
   [alldivide_def]  Definition
      
      |- (∀f1 f2 d.
            alldivide (Conjn f1 f2) d ⇔ alldivide f1 d ∧ alldivide f2 d) ∧
         (∀f1 f2 d.
            alldivide (Disjn f1 f2) d ⇔ alldivide f1 d ∧ alldivide f2 d) ∧
         (∀f d. alldivide (Negn f) d ⇔ alldivide f d) ∧
         (∀b d. alldivide (UnrelatedBool b) d ⇔ T) ∧
         (∀i d. alldivide (xLT i) d ⇔ T) ∧
         (∀i d. alldivide (LTx i) d ⇔ T) ∧
         (∀i d. alldivide (xEQ i) d ⇔ T) ∧
         ∀i1 i2 d. alldivide (xDivided i1 i2) d ⇔ i1 int_divides d
   
   [deep_form_TY_DEF]  Definition
      
      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'deep_form' .
                  (∀a0'.
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR 0 (ARB,ARB,ARB)
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'deep_form' a0 ∧ 'deep_form' a1) ∨
                     (∃a0 a1.
                        (a0' =
                         (λa0 a1.
                            ind_type$CONSTR (SUC 0) (ARB,ARB,ARB)
                              (ind_type$FCONS a0
                                 (ind_type$FCONS a1
                                    (λn. ind_type$BOTTOM)))) a0 a1) ∧
                        'deep_form' a0 ∧ 'deep_form' a1) ∨
                     (∃a.
                        (a0' =
                         (λa.
                            ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB,ARB)
                              (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                           a) ∧ 'deep_form' a) ∨
                     (∃a.
                        a0' =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC 0))) (a,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0' =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC (SUC 0))))
                             (ARB,a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0' =
                        (λa.
                           ind_type$CONSTR (SUC (SUC (SUC (SUC (SUC 0)))))
                             (ARB,a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0' =
                        (λa.
                           ind_type$CONSTR
                             (SUC (SUC (SUC (SUC (SUC (SUC 0))))))
                             (ARB,a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                     (∃a0 a1.
                        a0' =
                        (λa0 a1.
                           ind_type$CONSTR
                             (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))
                             (ARB,a0,a1) (λn. ind_type$BOTTOM)) a0 a1) ⇒
                     'deep_form' a0') ⇒
                  'deep_form' a0') rep
   
   [deep_form_case_def]  Definition
      
      |- (∀f f1 f2 f3 f4 f5 f6 f7 a0 a1.
            deep_form_case f f1 f2 f3 f4 f5 f6 f7 (Conjn a0 a1) =
            f a0 a1) ∧
         (∀f f1 f2 f3 f4 f5 f6 f7 a0 a1.
            deep_form_case f f1 f2 f3 f4 f5 f6 f7 (Disjn a0 a1) =
            f1 a0 a1) ∧
         (∀f f1 f2 f3 f4 f5 f6 f7 a.
            deep_form_case f f1 f2 f3 f4 f5 f6 f7 (Negn a) = f2 a) ∧
         (∀f f1 f2 f3 f4 f5 f6 f7 a.
            deep_form_case f f1 f2 f3 f4 f5 f6 f7 (UnrelatedBool a) =
            f3 a) ∧
         (∀f f1 f2 f3 f4 f5 f6 f7 a.
            deep_form_case f f1 f2 f3 f4 f5 f6 f7 (xLT a) = f4 a) ∧
         (∀f f1 f2 f3 f4 f5 f6 f7 a.
            deep_form_case f f1 f2 f3 f4 f5 f6 f7 (LTx a) = f5 a) ∧
         (∀f f1 f2 f3 f4 f5 f6 f7 a.
            deep_form_case f f1 f2 f3 f4 f5 f6 f7 (xEQ a) = f6 a) ∧
         ∀f f1 f2 f3 f4 f5 f6 f7 a0 a1.
           deep_form_case f f1 f2 f3 f4 f5 f6 f7 (xDivided a0 a1) =
           f7 a0 a1
   
   [deep_form_repfns]  Definition
      
      |- (∀a. mk_deep_form (dest_deep_form a) = a) ∧
         ∀r.
           (λa0'.
              ∀'deep_form' .
                (∀a0'.
                   (∃a0 a1.
                      (a0' =
                       (λa0 a1.
                          ind_type$CONSTR 0 (ARB,ARB,ARB)
                            (ind_type$FCONS a0
                               (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                         a0 a1) ∧ 'deep_form' a0 ∧ 'deep_form' a1) ∨
                   (∃a0 a1.
                      (a0' =
                       (λa0 a1.
                          ind_type$CONSTR (SUC 0) (ARB,ARB,ARB)
                            (ind_type$FCONS a0
                               (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                         a0 a1) ∧ 'deep_form' a0 ∧ 'deep_form' a1) ∨
                   (∃a.
                      (a0' =
                       (λa.
                          ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB,ARB)
                            (ind_type$FCONS a (λn. ind_type$BOTTOM))) a) ∧
                      'deep_form' a) ∨
                   (∃a.
                      a0' =
                      (λa.
                         ind_type$CONSTR (SUC (SUC (SUC 0))) (a,ARB,ARB)
                           (λn. ind_type$BOTTOM)) a) ∨
                   (∃a.
                      a0' =
                      (λa.
                         ind_type$CONSTR (SUC (SUC (SUC (SUC 0))))
                           (ARB,a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                   (∃a.
                      a0' =
                      (λa.
                         ind_type$CONSTR (SUC (SUC (SUC (SUC (SUC 0)))))
                           (ARB,a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                   (∃a.
                      a0' =
                      (λa.
                         ind_type$CONSTR
                           (SUC (SUC (SUC (SUC (SUC (SUC 0))))))
                           (ARB,a,ARB) (λn. ind_type$BOTTOM)) a) ∨
                   (∃a0 a1.
                      a0' =
                      (λa0 a1.
                         ind_type$CONSTR
                           (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))
                           (ARB,a0,a1) (λn. ind_type$BOTTOM)) a0 a1) ⇒
                   'deep_form' a0') ⇒
                'deep_form' a0') r ⇔ (dest_deep_form (mk_deep_form r) = r)
   
   [deep_form_size_def]  Definition
      
      |- (∀a0 a1.
            deep_form_size (Conjn a0 a1) =
            1 + (deep_form_size a0 + deep_form_size a1)) ∧
         (∀a0 a1.
            deep_form_size (Disjn a0 a1) =
            1 + (deep_form_size a0 + deep_form_size a1)) ∧
         (∀a. deep_form_size (Negn a) = 1 + deep_form_size a) ∧
         (∀a. deep_form_size (UnrelatedBool a) = 1 + bool_size a) ∧
         (∀a. deep_form_size (xLT a) = 1) ∧
         (∀a. deep_form_size (LTx a) = 1) ∧
         (∀a. deep_form_size (xEQ a) = 1) ∧
         ∀a0 a1. deep_form_size (xDivided a0 a1) = 1
   
   [eval_form_def]  Definition
      
      |- (∀f1 f2 x.
            eval_form (Conjn f1 f2) x ⇔ eval_form f1 x ∧ eval_form f2 x) ∧
         (∀f1 f2 x.
            eval_form (Disjn f1 f2) x ⇔ eval_form f1 x ∨ eval_form f2 x) ∧
         (∀f x. eval_form (Negn f) x ⇔ ¬eval_form f x) ∧
         (∀b x. eval_form (UnrelatedBool b) x ⇔ b) ∧
         (∀i x. eval_form (xLT i) x ⇔ x < i) ∧
         (∀i x. eval_form (LTx i) x ⇔ i < x) ∧
         (∀i x. eval_form (xEQ i) x ⇔ (x = i)) ∧
         ∀i1 i2 x. eval_form (xDivided i1 i2) x ⇔ i1 int_divides x + i2
   
   [neginf_def]  Definition
      
      |- (∀f1 f2. neginf (Conjn f1 f2) = Conjn (neginf f1) (neginf f2)) ∧
         (∀f1 f2. neginf (Disjn f1 f2) = Disjn (neginf f1) (neginf f2)) ∧
         (∀f. neginf (Negn f) = Negn (neginf f)) ∧
         (∀b. neginf (UnrelatedBool b) = UnrelatedBool b) ∧
         (∀i. neginf (xLT i) = UnrelatedBool T) ∧
         (∀i. neginf (LTx i) = UnrelatedBool F) ∧
         (∀i. neginf (xEQ i) = UnrelatedBool F) ∧
         ∀i1 i2. neginf (xDivided i1 i2) = xDivided i1 i2
   
   [posinf_def]  Definition
      
      |- (∀f1 f2. posinf (Conjn f1 f2) = Conjn (posinf f1) (posinf f2)) ∧
         (∀f1 f2. posinf (Disjn f1 f2) = Disjn (posinf f1) (posinf f2)) ∧
         (∀f. posinf (Negn f) = Negn (posinf f)) ∧
         (∀b. posinf (UnrelatedBool b) = UnrelatedBool b) ∧
         (∀i. posinf (xLT i) = UnrelatedBool F) ∧
         (∀i. posinf (LTx i) = UnrelatedBool T) ∧
         (∀i. posinf (xEQ i) = UnrelatedBool F) ∧
         ∀i1 i2. posinf (xDivided i1 i2) = xDivided i1 i2
   
   [add_d_neginf]  Theorem
      
      |- ∀f x y d.
           alldivide f d ⇒
           (eval_form (neginf f) x ⇔ eval_form (neginf f) (x + y * d))
   
   [add_d_posinf]  Theorem
      
      |- ∀f x y d.
           alldivide f d ⇒
           (eval_form (posinf f) x ⇔ eval_form (posinf f) (x + y * d))
   
   [datatype_deep_form]  Theorem
      
      |- DATATYPE
           (deep_form Conjn Disjn Negn UnrelatedBool xLT LTx xEQ xDivided)
   
   [deep_form_11]  Theorem
      
      |- (∀a0 a1 a0' a1'.
            (Conjn a0 a1 = Conjn a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         (∀a0 a1 a0' a1'.
            (Disjn a0 a1 = Disjn a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')) ∧
         (∀a a'. (Negn a = Negn a') ⇔ (a = a')) ∧
         (∀a a'. (UnrelatedBool a = UnrelatedBool a') ⇔ (a ⇔ a')) ∧
         (∀a a'. (xLT a = xLT a') ⇔ (a = a')) ∧
         (∀a a'. (LTx a = LTx a') ⇔ (a = a')) ∧
         (∀a a'. (xEQ a = xEQ a') ⇔ (a = a')) ∧
         ∀a0 a1 a0' a1'.
           (xDivided a0 a1 = xDivided a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')
   
   [deep_form_Axiom]  Theorem
      
      |- ∀f0 f1 f2 f3 f4 f5 f6 f7.
           ∃fn.
             (∀a0 a1. fn (Conjn a0 a1) = f0 a0 a1 (fn a0) (fn a1)) ∧
             (∀a0 a1. fn (Disjn a0 a1) = f1 a0 a1 (fn a0) (fn a1)) ∧
             (∀a. fn (Negn a) = f2 a (fn a)) ∧
             (∀a. fn (UnrelatedBool a) = f3 a) ∧ (∀a. fn (xLT a) = f4 a) ∧
             (∀a. fn (LTx a) = f5 a) ∧ (∀a. fn (xEQ a) = f6 a) ∧
             ∀a0 a1. fn (xDivided a0 a1) = f7 a0 a1
   
   [deep_form_case_cong]  Theorem
      
      |- ∀M M' f f1 f2 f3 f4 f5 f6 f7.
           (M = M') ∧ (∀a0 a1. (M' = Conjn a0 a1) ⇒ (f a0 a1 = f' a0 a1)) ∧
           (∀a0 a1. (M' = Disjn a0 a1) ⇒ (f1 a0 a1 = f1' a0 a1)) ∧
           (∀a. (M' = Negn a) ⇒ (f2 a = f2' a)) ∧
           (∀a. (M' = UnrelatedBool a) ⇒ (f3 a = f3' a)) ∧
           (∀a. (M' = xLT a) ⇒ (f4 a = f4' a)) ∧
           (∀a. (M' = LTx a) ⇒ (f5 a = f5' a)) ∧
           (∀a. (M' = xEQ a) ⇒ (f6 a = f6' a)) ∧
           (∀a0 a1. (M' = xDivided a0 a1) ⇒ (f7 a0 a1 = f7' a0 a1)) ⇒
           (deep_form_case f f1 f2 f3 f4 f5 f6 f7 M =
            deep_form_case f' f1' f2' f3' f4' f5' f6' f7' M')
   
   [deep_form_distinct]  Theorem
      
      |- (∀a1' a1 a0' a0. Conjn a0 a1 ≠ Disjn a0' a1') ∧
         (∀a1 a0 a. Conjn a0 a1 ≠ Negn a) ∧
         (∀a1 a0 a. Conjn a0 a1 ≠ UnrelatedBool a) ∧
         (∀a1 a0 a. Conjn a0 a1 ≠ xLT a) ∧
         (∀a1 a0 a. Conjn a0 a1 ≠ LTx a) ∧
         (∀a1 a0 a. Conjn a0 a1 ≠ xEQ a) ∧
         (∀a1' a1 a0' a0. Conjn a0 a1 ≠ xDivided a0' a1') ∧
         (∀a1 a0 a. Disjn a0 a1 ≠ Negn a) ∧
         (∀a1 a0 a. Disjn a0 a1 ≠ UnrelatedBool a) ∧
         (∀a1 a0 a. Disjn a0 a1 ≠ xLT a) ∧
         (∀a1 a0 a. Disjn a0 a1 ≠ LTx a) ∧
         (∀a1 a0 a. Disjn a0 a1 ≠ xEQ a) ∧
         (∀a1' a1 a0' a0. Disjn a0 a1 ≠ xDivided a0' a1') ∧
         (∀a' a. Negn a ≠ UnrelatedBool a') ∧ (∀a' a. Negn a ≠ xLT a') ∧
         (∀a' a. Negn a ≠ LTx a') ∧ (∀a' a. Negn a ≠ xEQ a') ∧
         (∀a1 a0 a. Negn a ≠ xDivided a0 a1) ∧
         (∀a' a. UnrelatedBool a ≠ xLT a') ∧
         (∀a' a. UnrelatedBool a ≠ LTx a') ∧
         (∀a' a. UnrelatedBool a ≠ xEQ a') ∧
         (∀a1 a0 a. UnrelatedBool a ≠ xDivided a0 a1) ∧
         (∀a' a. xLT a ≠ LTx a') ∧ (∀a' a. xLT a ≠ xEQ a') ∧
         (∀a1 a0 a. xLT a ≠ xDivided a0 a1) ∧ (∀a' a. LTx a ≠ xEQ a') ∧
         (∀a1 a0 a. LTx a ≠ xDivided a0 a1) ∧
         ∀a1 a0 a. xEQ a ≠ xDivided a0 a1
   
   [deep_form_induction]  Theorem
      
      |- ∀P.
           (∀d d0. P d ∧ P d0 ⇒ P (Conjn d d0)) ∧
           (∀d d0. P d ∧ P d0 ⇒ P (Disjn d d0)) ∧ (∀d. P d ⇒ P (Negn d)) ∧
           (∀b. P (UnrelatedBool b)) ∧ (∀i. P (xLT i)) ∧ (∀i. P (LTx i)) ∧
           (∀i. P (xEQ i)) ∧ (∀i i0. P (xDivided i i0)) ⇒
           ∀d. P d
   
   [deep_form_nchotomy]  Theorem
      
      |- ∀dd.
           (∃d d0. dd = Conjn d d0) ∨ (∃d d0. dd = Disjn d d0) ∨
           (∃d. dd = Negn d) ∨ (∃b. dd = UnrelatedBool b) ∨
           (∃i. dd = xLT i) ∨ (∃i. dd = LTx i) ∨ (∃i. dd = xEQ i) ∨
           ∃i i0. dd = xDivided i i0
   
   [in_aset]  Theorem
      
      |- ((∃a. a ∈ Aset pos (Conjn f1 f2) ∧ P a) ⇔
          (∃a. a ∈ Aset pos f1 ∧ P a) ∨ ∃a. a ∈ Aset pos f2 ∧ P a) ∧
         ((∃a. a ∈ Aset pos (Disjn f1 f2) ∧ P a) ⇔
          (∃a. a ∈ Aset pos f1 ∧ P a) ∨ ∃a. a ∈ Aset pos f2 ∧ P a) ∧
         ((∃a. a ∈ Aset T (Negn f) ∧ P a) ⇔ ∃a. a ∈ Aset F f ∧ P a) ∧
         ((∃a. a ∈ Aset F (Negn f) ∧ P a) ⇔ ∃a. a ∈ Aset T f ∧ P a) ∧
         ((∃a. a ∈ Aset pos (UnrelatedBool a0) ∧ P a) ⇔ F) ∧
         ((∃a. a ∈ Aset T (xLT i) ∧ P a) ⇔ P i) ∧
         ((∃a. a ∈ Aset F (xLT i) ∧ P a) ⇔ F) ∧
         ((∃a. a ∈ Aset T (LTx i) ∧ P a) ⇔ F) ∧
         ((∃a. a ∈ Aset F (LTx i) ∧ P a) ⇔ P (i + 1)) ∧
         ((∃a. a ∈ Aset T (xEQ i) ∧ P a) ⇔ P (i + 1)) ∧
         ((∃a. a ∈ Aset F (xEQ i) ∧ P a) ⇔ P i) ∧
         ((∃a. a ∈ Aset pos (xDivided i1 i2) ∧ P a) ⇔ F)
   
   [in_bset]  Theorem
      
      |- ((∃b. b ∈ Bset pos (Conjn f1 f2) ∧ P b) ⇔
          (∃b. b ∈ Bset pos f1 ∧ P b) ∨ ∃b. b ∈ Bset pos f2 ∧ P b) ∧
         ((∃b. b ∈ Bset pos (Disjn f1 f2) ∧ P b) ⇔
          (∃b. b ∈ Bset pos f1 ∧ P b) ∨ ∃b. b ∈ Bset pos f2 ∧ P b) ∧
         ((∃b. b ∈ Bset T (Negn f) ∧ P b) ⇔ ∃b. b ∈ Bset F f ∧ P b) ∧
         ((∃b. b ∈ Bset F (Negn f) ∧ P b) ⇔ ∃b. b ∈ Bset T f ∧ P b) ∧
         ((∃b. b ∈ Bset pos (UnrelatedBool b0) ∧ P b) ⇔ F) ∧
         ((∃b. b ∈ Bset T (xLT i) ∧ P b) ⇔ F) ∧
         ((∃b. b ∈ Bset F (xLT i) ∧ P b) ⇔ P (i + -1)) ∧
         ((∃b. b ∈ Bset T (LTx i) ∧ P b) ⇔ P i) ∧
         ((∃b. b ∈ Bset F (LTx i) ∧ P b) ⇔ F) ∧
         ((∃b. b ∈ Bset T (xEQ i) ∧ P b) ⇔ P (i + -1)) ∧
         ((∃b. b ∈ Bset F (xEQ i) ∧ P b) ⇔ P i) ∧
         ((∃b. b ∈ Bset pos (xDivided i1 i2) ∧ P b) ⇔ F)
   
   [neginf_disj1_implies_exoriginal]  Theorem
      
      |- ∀f d i.
           alldivide f d ⇒
           0 < i ∧ i ≤ d ∧ eval_form (neginf f) i ⇒
           ∃x. eval_form f x
   
   [neginf_exoriginal_eq_rhs]  Theorem
      
      |- ∀f d.
           alldivide f d ∧ 0 < d ⇒
           ((∃x. eval_form f x) ⇔
            (∃i. K (0 < i ∧ i ≤ d) i ∧ eval_form (neginf f) i) ∨
            ∃b j.
              (b ∈ Bset T f ∧ K (0 < j ∧ j ≤ d) j) ∧ eval_form f (b + j))
   
   [neginf_exoriginal_implies_rhs]  Theorem
      
      |- ∀f d x.
           alldivide f d ∧ 0 < d ⇒
           eval_form f x ⇒
           (∃i. 0 < i ∧ i ≤ d ∧ eval_form (neginf f) i) ∨
           ∃j b. 0 < j ∧ j ≤ d ∧ b ∈ Bset T f ∧ eval_form f (b + j)
   
   [neginf_ok]  Theorem
      
      |- ∀f. ∃y. ∀x. x < y ⇒ (eval_form f x ⇔ eval_form (neginf f) x)
   
   [posinf_disj1_implies_exoriginal]  Theorem
      
      |- ∀f d i.
           alldivide f d ⇒
           0 < i ∧ i ≤ d ∧ eval_form (posinf f) i ⇒
           ∃x. eval_form f x
   
   [posinf_exoriginal_eq_rhs]  Theorem
      
      |- ∀f d.
           alldivide f d ∧ 0 < d ⇒
           ((∃x. eval_form f x) ⇔
            (∃i. K (0 < i ∧ i ≤ d) i ∧ eval_form (posinf f) i) ∨
            ∃b j.
              (b ∈ Aset T f ∧ K (0 < j ∧ j ≤ d) j) ∧
              eval_form f (b + -1 * j))
   
   [posinf_exoriginal_implies_rhs]  Theorem
      
      |- ∀f d x.
           alldivide f d ∧ 0 < d ⇒
           eval_form f x ⇒
           (∃i. 0 < i ∧ i ≤ d ∧ eval_form (posinf f) i) ∨
           ∃j b. 0 < j ∧ j ≤ d ∧ b ∈ Aset T f ∧ eval_form f (b + -j)
   
   [posinf_ok]  Theorem
      
      |- ∀f. ∃y. ∀x. y < x ⇒ (eval_form f x ⇔ eval_form (posinf f) x)
   
   
*)
end
