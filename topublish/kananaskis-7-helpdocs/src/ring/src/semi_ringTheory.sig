signature semi_ringTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val is_semi_ring_def : thm
    val semi_ring_SR0 : thm
    val semi_ring_SR0_fupd : thm
    val semi_ring_SR1 : thm
    val semi_ring_SR1_fupd : thm
    val semi_ring_SRM : thm
    val semi_ring_SRM_fupd : thm
    val semi_ring_SRP : thm
    val semi_ring_SRP_fupd : thm
    val semi_ring_TY_DEF : thm
    val semi_ring_case_def : thm
    val semi_ring_repfns : thm
    val semi_ring_size_def : thm
  
  (*  Theorems  *)
    val EXISTS_semi_ring : thm
    val FORALL_semi_ring : thm
    val datatype_semi_ring : thm
    val distr_left : thm
    val distr_right : thm
    val mult_assoc : thm
    val mult_one_left : thm
    val mult_one_right : thm
    val mult_permute : thm
    val mult_rotate : thm
    val mult_sym : thm
    val mult_zero_left : thm
    val mult_zero_right : thm
    val plus_assoc : thm
    val plus_permute : thm
    val plus_rotate : thm
    val plus_sym : thm
    val plus_zero_left : thm
    val plus_zero_right : thm
    val semi_ring_11 : thm
    val semi_ring_Axiom : thm
    val semi_ring_accessors : thm
    val semi_ring_accfupds : thm
    val semi_ring_case_cong : thm
    val semi_ring_component_equality : thm
    val semi_ring_fn_updates : thm
    val semi_ring_fupdcanon : thm
    val semi_ring_fupdcanon_comp : thm
    val semi_ring_fupdfupds : thm
    val semi_ring_fupdfupds_comp : thm
    val semi_ring_induction : thm
    val semi_ring_literal_11 : thm
    val semi_ring_literal_nchotomy : thm
    val semi_ring_nchotomy : thm
    val semi_ring_updates_eq_literal : thm
  
  val semi_ring_grammars : type_grammar.grammar * term_grammar.grammar
  
  val IMPORT : abstraction.inst_infos ->
    { is_semi_ring_def : thm,
      semi_ring_SRM_fupd : thm,
      semi_ring_SRP_fupd : thm,
      semi_ring_SR1_fupd : thm,
      semi_ring_SR0_fupd : thm,
      semi_ring_SRM : thm,
      semi_ring_SRP : thm,
      semi_ring_SR1 : thm,
      semi_ring_SR0 : thm,
      semi_ring_size_def : thm,
      semi_ring_case_def : thm,
      semi_ring_repfns : thm,
      semi_ring_TY_DEF : thm,
      mult_permute : thm,
      mult_rotate : thm,
      plus_permute : thm,
      plus_rotate : thm,
      distr_right : thm,
      mult_zero_right : thm,
      mult_one_right : thm,
      plus_zero_right : thm,
      distr_left : thm,
      mult_zero_left : thm,
      mult_one_left : thm,
      plus_zero_left : thm,
      mult_assoc : thm,
      mult_sym : thm,
      plus_assoc : thm,
      plus_sym : thm,
      semi_ring_induction : thm,
      semi_ring_Axiom : thm,
      semi_ring_nchotomy : thm,
      semi_ring_case_cong : thm,
      semi_ring_11 : thm,
      datatype_semi_ring : thm,
      semi_ring_literal_11 : thm,
      EXISTS_semi_ring : thm,
      FORALL_semi_ring : thm,
      semi_ring_literal_nchotomy : thm,
      semi_ring_updates_eq_literal : thm,
      semi_ring_component_equality : thm,
      semi_ring_fupdcanon_comp : thm,
      semi_ring_fupdcanon : thm,
      semi_ring_fupdfupds_comp : thm,
      semi_ring_fupdfupds : thm,
      semi_ring_accfupds : thm,
      semi_ring_fn_updates : thm,
      semi_ring_accessors : thm }
  
(*
   [list] Parent theory of "semi_ring"
   
   [is_semi_ring_def]  Definition
      
      |- ∀r.
           is_semi_ring r ⇔
           (∀n m. SRP r n m = SRP r m n) ∧
           (∀n m p. SRP r n (SRP r m p) = SRP r (SRP r n m) p) ∧
           (∀n m. SRM r n m = SRM r m n) ∧
           (∀n m p. SRM r n (SRM r m p) = SRM r (SRM r n m) p) ∧
           (∀n. SRP r (SR0 r) n = n) ∧ (∀n. SRM r (SR1 r) n = n) ∧
           (∀n. SRM r (SR0 r) n = SR0 r) ∧
           ∀n m p. SRM r (SRP r n m) p = SRP r (SRM r n p) (SRM r m p)
   
   [semi_ring_SR0]  Definition
      
      |- ∀a a0 f f0. SR0 (semi_ring a a0 f f0) = a
   
   [semi_ring_SR0_fupd]  Definition
      
      |- ∀f1 a a0 f f0.
           semi_ring a a0 f f0 with SR0 updated_by f1 =
           semi_ring (f1 a) a0 f f0
   
   [semi_ring_SR1]  Definition
      
      |- ∀a a0 f f0. SR1 (semi_ring a a0 f f0) = a0
   
   [semi_ring_SR1_fupd]  Definition
      
      |- ∀f1 a a0 f f0.
           semi_ring a a0 f f0 with SR1 updated_by f1 =
           semi_ring a (f1 a0) f f0
   
   [semi_ring_SRM]  Definition
      
      |- ∀a a0 f f0. SRM (semi_ring a a0 f f0) = f0
   
   [semi_ring_SRM_fupd]  Definition
      
      |- ∀f1 a a0 f f0.
           semi_ring a a0 f f0 with SRM updated_by f1 =
           semi_ring a a0 f (f1 f0)
   
   [semi_ring_SRP]  Definition
      
      |- ∀a a0 f f0. SRP (semi_ring a a0 f f0) = f
   
   [semi_ring_SRP_fupd]  Definition
      
      |- ∀f1 a a0 f f0.
           semi_ring a a0 f f0 with SRP updated_by f1 =
           semi_ring a a0 (f1 f) f0
   
   [semi_ring_TY_DEF]  Definition
      
      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'semi_ring' .
                  (∀a0'.
                     (∃a0 a1 a2 a3.
                        a0' =
                        (λa0 a1 a2 a3.
                           ind_type$CONSTR 0 (a0,a1,a2,a3)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3) ⇒
                     'semi_ring' a0') ⇒
                  'semi_ring' a0') rep
   
   [semi_ring_case_def]  Definition
      
      |- ∀f a0 a1 a2 a3.
           semi_ring_case f (semi_ring a0 a1 a2 a3) = f a0 a1 a2 a3
   
   [semi_ring_repfns]  Definition
      
      |- (∀a. mk_semi_ring (dest_semi_ring a) = a) ∧
         ∀r.
           (λa0'.
              ∀'semi_ring' .
                (∀a0'.
                   (∃a0 a1 a2 a3.
                      a0' =
                      (λa0 a1 a2 a3.
                         ind_type$CONSTR 0 (a0,a1,a2,a3)
                           (λn. ind_type$BOTTOM)) a0 a1 a2 a3) ⇒
                   'semi_ring' a0') ⇒
                'semi_ring' a0') r ⇔ (dest_semi_ring (mk_semi_ring r) = r)
   
   [semi_ring_size_def]  Definition
      
      |- ∀f a0 a1 a2 a3.
           semi_ring_size f (semi_ring a0 a1 a2 a3) = 1 + (f a0 + f a1)
   
   [EXISTS_semi_ring]  Theorem
      
      |- ∀P.
           (∃s. P s) ⇔
           ∃a0 a f0 f. P <|SR0 := a0; SR1 := a; SRP := f0; SRM := f|>
   
   [FORALL_semi_ring]  Theorem
      
      |- ∀P.
           (∀s. P s) ⇔
           ∀a0 a f0 f. P <|SR0 := a0; SR1 := a; SRP := f0; SRM := f|>
   
   [datatype_semi_ring]  Theorem
      
      |- DATATYPE (record semi_ring SR0 SR1 SRP SRM)
   
   [distr_left]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀n m p. SRM r (SRP r n m) p = SRP r (SRM r n p) (SRM r m p)
   
   [distr_right]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀m n p. SRM r m (SRP r n p) = SRP r (SRM r m n) (SRM r m p)
   
   [mult_assoc]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀n m p. SRM r n (SRM r m p) = SRM r (SRM r n m) p
   
   [mult_one_left]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n. SRM r (SR1 r) n = n
   
   [mult_one_right]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n. SRM r n (SR1 r) = n
   
   [mult_permute]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀m n p. SRM r (SRM r m n) p = SRM r (SRM r m p) n
   
   [mult_rotate]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀m n p. SRM r (SRM r m n) p = SRM r (SRM r n p) m
   
   [mult_sym]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n m. SRM r n m = SRM r m n
   
   [mult_zero_left]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n. SRM r (SR0 r) n = SR0 r
   
   [mult_zero_right]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n. SRM r n (SR0 r) = SR0 r
   
   [plus_assoc]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀n m p. SRP r n (SRP r m p) = SRP r (SRP r n m) p
   
   [plus_permute]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀m n p. SRP r (SRP r m n) p = SRP r (SRP r m p) n
   
   [plus_rotate]  Theorem
      
      |- ∀r.
           is_semi_ring r ⇒
           ∀m n p. SRP r (SRP r m n) p = SRP r (SRP r n p) m
   
   [plus_sym]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n m. SRP r n m = SRP r m n
   
   [plus_zero_left]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n. SRP r (SR0 r) n = n
   
   [plus_zero_right]  Theorem
      
      |- ∀r. is_semi_ring r ⇒ ∀n. SRP r n (SR0 r) = n
   
   [semi_ring_11]  Theorem
      
      |- ∀a0 a1 a2 a3 a0' a1' a2' a3'.
           (semi_ring a0 a1 a2 a3 = semi_ring a0' a1' a2' a3') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3')
   
   [semi_ring_Axiom]  Theorem
      
      |- ∀f. ∃fn. ∀a0 a1 a2 a3. fn (semi_ring a0 a1 a2 a3) = f a0 a1 a2 a3
   
   [semi_ring_accessors]  Theorem
      
      |- (∀a a0 f f0. SR0 (semi_ring a a0 f f0) = a) ∧
         (∀a a0 f f0. SR1 (semi_ring a a0 f f0) = a0) ∧
         (∀a a0 f f0. SRP (semi_ring a a0 f f0) = f) ∧
         ∀a a0 f f0. SRM (semi_ring a a0 f f0) = f0
   
   [semi_ring_accfupds]  Theorem
      
      |- (∀s f. SR0 (s with SR1 updated_by f) = SR0 s) ∧
         (∀s f. SR0 (s with SRP updated_by f) = SR0 s) ∧
         (∀s f. SR0 (s with SRM updated_by f) = SR0 s) ∧
         (∀s f. SR1 (s with SR0 updated_by f) = SR1 s) ∧
         (∀s f. SR1 (s with SRP updated_by f) = SR1 s) ∧
         (∀s f. SR1 (s with SRM updated_by f) = SR1 s) ∧
         (∀s f. SRP (s with SR0 updated_by f) = SRP s) ∧
         (∀s f. SRP (s with SR1 updated_by f) = SRP s) ∧
         (∀s f. SRP (s with SRM updated_by f) = SRP s) ∧
         (∀s f. SRM (s with SR0 updated_by f) = SRM s) ∧
         (∀s f. SRM (s with SR1 updated_by f) = SRM s) ∧
         (∀s f. SRM (s with SRP updated_by f) = SRM s) ∧
         (∀s f. SR0 (s with SR0 updated_by f) = f (SR0 s)) ∧
         (∀s f. SR1 (s with SR1 updated_by f) = f (SR1 s)) ∧
         (∀s f. SRP (s with SRP updated_by f) = f (SRP s)) ∧
         ∀s f. SRM (s with SRM updated_by f) = f (SRM s)
   
   [semi_ring_case_cong]  Theorem
      
      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3.
              (M' = semi_ring a0 a1 a2 a3) ⇒
              (f a0 a1 a2 a3 = f' a0 a1 a2 a3)) ⇒
           (semi_ring_case f M = semi_ring_case f' M')
   
   [semi_ring_component_equality]  Theorem
      
      |- ∀s1 s2.
           (s1 = s2) ⇔
           (SR0 s1 = SR0 s2) ∧ (SR1 s1 = SR1 s2) ∧ (SRP s1 = SRP s2) ∧
           (SRM s1 = SRM s2)
   
   [semi_ring_fn_updates]  Theorem
      
      |- (∀f1 a a0 f f0.
            semi_ring a a0 f f0 with SR0 updated_by f1 =
            semi_ring (f1 a) a0 f f0) ∧
         (∀f1 a a0 f f0.
            semi_ring a a0 f f0 with SR1 updated_by f1 =
            semi_ring a (f1 a0) f f0) ∧
         (∀f1 a a0 f f0.
            semi_ring a a0 f f0 with SRP updated_by f1 =
            semi_ring a a0 (f1 f) f0) ∧
         ∀f1 a a0 f f0.
           semi_ring a a0 f f0 with SRM updated_by f1 =
           semi_ring a a0 f (f1 f0)
   
   [semi_ring_fupdcanon]  Theorem
      
      |- (∀s g f.
            s with <|SR1 updated_by f; SR0 updated_by g|> =
            s with <|SR0 updated_by g; SR1 updated_by f|>) ∧
         (∀s g f.
            s with <|SRP updated_by f; SR0 updated_by g|> =
            s with <|SR0 updated_by g; SRP updated_by f|>) ∧
         (∀s g f.
            s with <|SRP updated_by f; SR1 updated_by g|> =
            s with <|SR1 updated_by g; SRP updated_by f|>) ∧
         (∀s g f.
            s with <|SRM updated_by f; SR0 updated_by g|> =
            s with <|SR0 updated_by g; SRM updated_by f|>) ∧
         (∀s g f.
            s with <|SRM updated_by f; SR1 updated_by g|> =
            s with <|SR1 updated_by g; SRM updated_by f|>) ∧
         ∀s g f.
           s with <|SRM updated_by f; SRP updated_by g|> =
           s with <|SRP updated_by g; SRM updated_by f|>
   
   [semi_ring_fupdcanon_comp]  Theorem
      
      |- ((∀g f.
              _ record fupdateSR1 f o  _ record fupdateSR0 g =
              _ record fupdateSR0 g o  _ record fupdateSR1 f) ∧
          ∀h g f.
             _ record fupdateSR1 f o  _ record fupdateSR0 g o h =
             _ record fupdateSR0 g o  _ record fupdateSR1 f o h) ∧
         ((∀g f.
              _ record fupdateSRP f o  _ record fupdateSR0 g =
              _ record fupdateSR0 g o  _ record fupdateSRP f) ∧
          ∀h g f.
             _ record fupdateSRP f o  _ record fupdateSR0 g o h =
             _ record fupdateSR0 g o  _ record fupdateSRP f o h) ∧
         ((∀g f.
              _ record fupdateSRP f o  _ record fupdateSR1 g =
              _ record fupdateSR1 g o  _ record fupdateSRP f) ∧
          ∀h g f.
             _ record fupdateSRP f o  _ record fupdateSR1 g o h =
             _ record fupdateSR1 g o  _ record fupdateSRP f o h) ∧
         ((∀g f.
              _ record fupdateSRM f o  _ record fupdateSR0 g =
              _ record fupdateSR0 g o  _ record fupdateSRM f) ∧
          ∀h g f.
             _ record fupdateSRM f o  _ record fupdateSR0 g o h =
             _ record fupdateSR0 g o  _ record fupdateSRM f o h) ∧
         ((∀g f.
              _ record fupdateSRM f o  _ record fupdateSR1 g =
              _ record fupdateSR1 g o  _ record fupdateSRM f) ∧
          ∀h g f.
             _ record fupdateSRM f o  _ record fupdateSR1 g o h =
             _ record fupdateSR1 g o  _ record fupdateSRM f o h) ∧
         (∀g f.
             _ record fupdateSRM f o  _ record fupdateSRP g =
             _ record fupdateSRP g o  _ record fupdateSRM f) ∧
         ∀h g f.
            _ record fupdateSRM f o  _ record fupdateSRP g o h =
            _ record fupdateSRP g o  _ record fupdateSRM f o h
   
   [semi_ring_fupdfupds]  Theorem
      
      |- (∀s g f.
            s with <|SR0 updated_by f; SR0 updated_by g|> =
            s with SR0 updated_by f o g) ∧
         (∀s g f.
            s with <|SR1 updated_by f; SR1 updated_by g|> =
            s with SR1 updated_by f o g) ∧
         (∀s g f.
            s with <|SRP updated_by f; SRP updated_by g|> =
            s with SRP updated_by f o g) ∧
         ∀s g f.
           s with <|SRM updated_by f; SRM updated_by g|> =
           s with SRM updated_by f o g
   
   [semi_ring_fupdfupds_comp]  Theorem
      
      |- ((∀g f.
              _ record fupdateSR0 f o  _ record fupdateSR0 g =
              _ record fupdateSR0 (f o g)) ∧
          ∀h g f.
             _ record fupdateSR0 f o  _ record fupdateSR0 g o h =
             _ record fupdateSR0 (f o g) o h) ∧
         ((∀g f.
              _ record fupdateSR1 f o  _ record fupdateSR1 g =
              _ record fupdateSR1 (f o g)) ∧
          ∀h g f.
             _ record fupdateSR1 f o  _ record fupdateSR1 g o h =
             _ record fupdateSR1 (f o g) o h) ∧
         ((∀g f.
              _ record fupdateSRP f o  _ record fupdateSRP g =
              _ record fupdateSRP (f o g)) ∧
          ∀h g f.
             _ record fupdateSRP f o  _ record fupdateSRP g o h =
             _ record fupdateSRP (f o g) o h) ∧
         (∀g f.
             _ record fupdateSRM f o  _ record fupdateSRM g =
             _ record fupdateSRM (f o g)) ∧
         ∀h g f.
            _ record fupdateSRM f o  _ record fupdateSRM g o h =
            _ record fupdateSRM (f o g) o h
   
   [semi_ring_induction]  Theorem
      
      |- ∀P. (∀a a0 f f0. P (semi_ring a a0 f f0)) ⇒ ∀s. P s
   
   [semi_ring_literal_11]  Theorem
      
      |- ∀a01 a1 f01 f1 a02 a2 f02 f2.
           (<|SR0 := a01; SR1 := a1; SRP := f01; SRM := f1|> =
            <|SR0 := a02; SR1 := a2; SRP := f02; SRM := f2|>) ⇔
           (a01 = a02) ∧ (a1 = a2) ∧ (f01 = f02) ∧ (f1 = f2)
   
   [semi_ring_literal_nchotomy]  Theorem
      
      |- ∀s. ∃a0 a f0 f. s = <|SR0 := a0; SR1 := a; SRP := f0; SRM := f|>
   
   [semi_ring_nchotomy]  Theorem
      
      |- ∀ss. ∃a a0 f f0. ss = semi_ring a a0 f f0
   
   [semi_ring_updates_eq_literal]  Theorem
      
      |- ∀s a0 a f0 f.
           s with <|SR0 := a0; SR1 := a; SRP := f0; SRM := f|> =
           <|SR0 := a0; SR1 := a; SRP := f0; SRM := f|>
   
   
*)
end
