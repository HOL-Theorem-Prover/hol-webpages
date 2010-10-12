signature ringTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val is_ring_def : thm
    val ring_R0 : thm
    val ring_R0_fupd : thm
    val ring_R1 : thm
    val ring_R1_fupd : thm
    val ring_RM : thm
    val ring_RM_fupd : thm
    val ring_RN : thm
    val ring_RN_fupd : thm
    val ring_RP : thm
    val ring_RP_fupd : thm
    val ring_TY_DEF : thm
    val ring_case_def : thm
    val ring_repfns : thm
    val ring_size_def : thm
    val semi_ring_of_def : thm
  
  (*  Theorems  *)
    val EXISTS_ring : thm
    val FORALL_ring : thm
    val datatype_ring : thm
    val distr_left : thm
    val mult_assoc : thm
    val mult_one_left : thm
    val mult_one_right : thm
    val mult_sym : thm
    val mult_zero_left : thm
    val mult_zero_right : thm
    val neg_mult : thm
    val opp_def : thm
    val plus_assoc : thm
    val plus_sym : thm
    val plus_zero_left : thm
    val plus_zero_right : thm
    val ring_11 : thm
    val ring_Axiom : thm
    val ring_accessors : thm
    val ring_accfupds : thm
    val ring_case_cong : thm
    val ring_component_equality : thm
    val ring_fn_updates : thm
    val ring_fupdcanon : thm
    val ring_fupdcanon_comp : thm
    val ring_fupdfupds : thm
    val ring_fupdfupds_comp : thm
    val ring_induction : thm
    val ring_is_semi_ring : thm
    val ring_literal_11 : thm
    val ring_literal_nchotomy : thm
    val ring_nchotomy : thm
    val ring_updates_eq_literal : thm
  
  val ring_grammars : type_grammar.grammar * term_grammar.grammar
  
  val IMPORT : abstraction.inst_infos ->
    { semi_ring_of_def : thm,
      is_ring_def : thm,
      ring_RN_fupd : thm,
      ring_RM_fupd : thm,
      ring_RP_fupd : thm,
      ring_R1_fupd : thm,
      ring_R0_fupd : thm,
      ring_RN : thm,
      ring_RM : thm,
      ring_RP : thm,
      ring_R1 : thm,
      ring_R0 : thm,
      ring_size_def : thm,
      ring_case_def : thm,
      ring_repfns : thm,
      ring_TY_DEF : thm,
      neg_mult : thm,
      mult_one_right : thm,
      ring_is_semi_ring : thm,
      mult_zero_right : thm,
      mult_zero_left : thm,
      plus_zero_right : thm,
      distr_left : thm,
      opp_def : thm,
      mult_one_left : thm,
      plus_zero_left : thm,
      mult_assoc : thm,
      mult_sym : thm,
      plus_assoc : thm,
      plus_sym : thm,
      ring_induction : thm,
      ring_Axiom : thm,
      ring_nchotomy : thm,
      ring_case_cong : thm,
      ring_11 : thm,
      datatype_ring : thm,
      ring_literal_11 : thm,
      EXISTS_ring : thm,
      FORALL_ring : thm,
      ring_literal_nchotomy : thm,
      ring_updates_eq_literal : thm,
      ring_component_equality : thm,
      ring_fupdcanon_comp : thm,
      ring_fupdcanon : thm,
      ring_fupdfupds_comp : thm,
      ring_fupdfupds : thm,
      ring_accfupds : thm,
      ring_fn_updates : thm,
      ring_accessors : thm }
  
(*
   [semi_ring] Parent theory of "ring"
   
   [is_ring_def]  Definition
      
      |- ∀r.
           is_ring r ⇔
           (∀n m. RP r n m = RP r m n) ∧
           (∀n m p. RP r n (RP r m p) = RP r (RP r n m) p) ∧
           (∀n m. RM r n m = RM r m n) ∧
           (∀n m p. RM r n (RM r m p) = RM r (RM r n m) p) ∧
           (∀n. RP r (R0 r) n = n) ∧ (∀n. RM r (R1 r) n = n) ∧
           (∀n. RP r n (RN r n) = R0 r) ∧
           ∀n m p. RM r (RP r n m) p = RP r (RM r n p) (RM r m p)
   
   [ring_R0]  Definition
      
      |- ∀a a0 f f0 f1. R0 (ring a a0 f f0 f1) = a
   
   [ring_R0_fupd]  Definition
      
      |- ∀f2 a a0 f f0 f1.
           ring a a0 f f0 f1 with R0 updated_by f2 = ring (f2 a) a0 f f0 f1
   
   [ring_R1]  Definition
      
      |- ∀a a0 f f0 f1. R1 (ring a a0 f f0 f1) = a0
   
   [ring_R1_fupd]  Definition
      
      |- ∀f2 a a0 f f0 f1.
           ring a a0 f f0 f1 with R1 updated_by f2 = ring a (f2 a0) f f0 f1
   
   [ring_RM]  Definition
      
      |- ∀a a0 f f0 f1. RM (ring a a0 f f0 f1) = f0
   
   [ring_RM_fupd]  Definition
      
      |- ∀f2 a a0 f f0 f1.
           ring a a0 f f0 f1 with RM updated_by f2 = ring a a0 f (f2 f0) f1
   
   [ring_RN]  Definition
      
      |- ∀a a0 f f0 f1. RN (ring a a0 f f0 f1) = f1
   
   [ring_RN_fupd]  Definition
      
      |- ∀f2 a a0 f f0 f1.
           ring a a0 f f0 f1 with RN updated_by f2 = ring a a0 f f0 (f2 f1)
   
   [ring_RP]  Definition
      
      |- ∀a a0 f f0 f1. RP (ring a a0 f f0 f1) = f
   
   [ring_RP_fupd]  Definition
      
      |- ∀f2 a a0 f f0 f1.
           ring a a0 f f0 f1 with RP updated_by f2 = ring a a0 (f2 f) f0 f1
   
   [ring_TY_DEF]  Definition
      
      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'ring' .
                  (∀a0'.
                     (∃a0 a1 a2 a3 a4.
                        a0' =
                        (λa0 a1 a2 a3 a4.
                           ind_type$CONSTR 0 (a0,a1,a2,a3,a4) (λn. ind_type$BOTTOM))
                          a0 a1 a2 a3 a4) ⇒
                     'ring' a0') ⇒
                  'ring' a0') rep
   
   [ring_case_def]  Definition
      
      |- ∀f a0 a1 a2 a3 a4. ring_case f (ring a0 a1 a2 a3 a4) = f a0 a1 a2 a3 a4
   
   [ring_repfns]  Definition
      
      |- (∀a. mk_ring (dest_ring a) = a) ∧
         ∀r.
           (λa0'.
              ∀'ring' .
                (∀a0'.
                   (∃a0 a1 a2 a3 a4.
                      a0' =
                      (λa0 a1 a2 a3 a4.
                         ind_type$CONSTR 0 (a0,a1,a2,a3,a4) (λn. ind_type$BOTTOM)) a0
                        a1 a2 a3 a4) ⇒
                   'ring' a0') ⇒
                'ring' a0') r ⇔ (dest_ring (mk_ring r) = r)
   
   [ring_size_def]  Definition
      
      |- ∀f a0 a1 a2 a3 a4. ring_size f (ring a0 a1 a2 a3 a4) = 1 + (f a0 + f a1)
   
   [semi_ring_of_def]  Definition
      
      |- ∀r. semi_ring_of r = semi_ring (R0 r) (R1 r) (RP r) (RM r)
   
   [EXISTS_ring]  Theorem
      
      |- ∀P.
           (∃r. P r) ⇔
           ∃a0 a f1 f0 f. P <|R0 := a0; R1 := a; RP := f1; RM := f0; RN := f|>
   
   [FORALL_ring]  Theorem
      
      |- ∀P.
           (∀r. P r) ⇔
           ∀a0 a f1 f0 f. P <|R0 := a0; R1 := a; RP := f1; RM := f0; RN := f|>
   
   [datatype_ring]  Theorem
      
      |- DATATYPE (record ring R0 R1 RP RM RN)
   
   [distr_left]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n m p. RM r (RP r n m) p = RP r (RM r n p) (RM r m p)
   
   [mult_assoc]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n m p. RM r n (RM r m p) = RM r (RM r n m) p
   
   [mult_one_left]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n. RM r (R1 r) n = n
   
   [mult_one_right]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n. RM r n (R1 r) = n
   
   [mult_sym]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n m. RM r n m = RM r m n
   
   [mult_zero_left]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n. RM r (R0 r) n = R0 r
   
   [mult_zero_right]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n. RM r n (R0 r) = R0 r
   
   [neg_mult]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀a b. RM r (RN r a) b = RN r (RM r a b)
   
   [opp_def]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n. RP r n (RN r n) = R0 r
   
   [plus_assoc]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n m p. RP r n (RP r m p) = RP r (RP r n m) p
   
   [plus_sym]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n m. RP r n m = RP r m n
   
   [plus_zero_left]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n. RP r (R0 r) n = n
   
   [plus_zero_right]  Theorem
      
      |- ∀r. is_ring r ⇒ ∀n. RP r n (R0 r) = n
   
   [ring_11]  Theorem
      
      |- ∀a0 a1 a2 a3 a4 a0' a1' a2' a3' a4'.
           (ring a0 a1 a2 a3 a4 = ring a0' a1' a2' a3' a4') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3') ∧ (a4 = a4')
   
   [ring_Axiom]  Theorem
      
      |- ∀f. ∃fn. ∀a0 a1 a2 a3 a4. fn (ring a0 a1 a2 a3 a4) = f a0 a1 a2 a3 a4
   
   [ring_accessors]  Theorem
      
      |- (∀a a0 f f0 f1. R0 (ring a a0 f f0 f1) = a) ∧
         (∀a a0 f f0 f1. R1 (ring a a0 f f0 f1) = a0) ∧
         (∀a a0 f f0 f1. RP (ring a a0 f f0 f1) = f) ∧
         (∀a a0 f f0 f1. RM (ring a a0 f f0 f1) = f0) ∧
         ∀a a0 f f0 f1. RN (ring a a0 f f0 f1) = f1
   
   [ring_accfupds]  Theorem
      
      |- (∀r f. R0 (r with R1 updated_by f) = R0 r) ∧
         (∀r f. R0 (r with RP updated_by f) = R0 r) ∧
         (∀r f. R0 (r with RM updated_by f) = R0 r) ∧
         (∀r f. R0 (r with RN updated_by f) = R0 r) ∧
         (∀r f. R1 (r with R0 updated_by f) = R1 r) ∧
         (∀r f. R1 (r with RP updated_by f) = R1 r) ∧
         (∀r f. R1 (r with RM updated_by f) = R1 r) ∧
         (∀r f. R1 (r with RN updated_by f) = R1 r) ∧
         (∀r f. RP (r with R0 updated_by f) = RP r) ∧
         (∀r f. RP (r with R1 updated_by f) = RP r) ∧
         (∀r f. RP (r with RM updated_by f) = RP r) ∧
         (∀r f. RP (r with RN updated_by f) = RP r) ∧
         (∀r f. RM (r with R0 updated_by f) = RM r) ∧
         (∀r f. RM (r with R1 updated_by f) = RM r) ∧
         (∀r f. RM (r with RP updated_by f) = RM r) ∧
         (∀r f. RM (r with RN updated_by f) = RM r) ∧
         (∀r f. RN (r with R0 updated_by f) = RN r) ∧
         (∀r f. RN (r with R1 updated_by f) = RN r) ∧
         (∀r f. RN (r with RP updated_by f) = RN r) ∧
         (∀r f. RN (r with RM updated_by f) = RN r) ∧
         (∀r f. R0 (r with R0 updated_by f) = f (R0 r)) ∧
         (∀r f. R1 (r with R1 updated_by f) = f (R1 r)) ∧
         (∀r f. RP (r with RP updated_by f) = f (RP r)) ∧
         (∀r f. RM (r with RM updated_by f) = f (RM r)) ∧
         ∀r f. RN (r with RN updated_by f) = f (RN r)
   
   [ring_case_cong]  Theorem
      
      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3 a4.
              (M' = ring a0 a1 a2 a3 a4) ⇒ (f a0 a1 a2 a3 a4 = f' a0 a1 a2 a3 a4)) ⇒
           (ring_case f M = ring_case f' M')
   
   [ring_component_equality]  Theorem
      
      |- ∀r1 r2.
           (r1 = r2) ⇔
           (R0 r1 = R0 r2) ∧ (R1 r1 = R1 r2) ∧ (RP r1 = RP r2) ∧ (RM r1 = RM r2) ∧
           (RN r1 = RN r2)
   
   [ring_fn_updates]  Theorem
      
      |- (∀f2 a a0 f f0 f1.
            ring a a0 f f0 f1 with R0 updated_by f2 = ring (f2 a) a0 f f0 f1) ∧
         (∀f2 a a0 f f0 f1.
            ring a a0 f f0 f1 with R1 updated_by f2 = ring a (f2 a0) f f0 f1) ∧
         (∀f2 a a0 f f0 f1.
            ring a a0 f f0 f1 with RP updated_by f2 = ring a a0 (f2 f) f0 f1) ∧
         (∀f2 a a0 f f0 f1.
            ring a a0 f f0 f1 with RM updated_by f2 = ring a a0 f (f2 f0) f1) ∧
         ∀f2 a a0 f f0 f1.
           ring a a0 f f0 f1 with RN updated_by f2 = ring a a0 f f0 (f2 f1)
   
   [ring_fupdcanon]  Theorem
      
      |- (∀r g f.
            r with <|R1 updated_by f; R0 updated_by g|> =
            r with <|R0 updated_by g; R1 updated_by f|>) ∧
         (∀r g f.
            r with <|RP updated_by f; R0 updated_by g|> =
            r with <|R0 updated_by g; RP updated_by f|>) ∧
         (∀r g f.
            r with <|RP updated_by f; R1 updated_by g|> =
            r with <|R1 updated_by g; RP updated_by f|>) ∧
         (∀r g f.
            r with <|RM updated_by f; R0 updated_by g|> =
            r with <|R0 updated_by g; RM updated_by f|>) ∧
         (∀r g f.
            r with <|RM updated_by f; R1 updated_by g|> =
            r with <|R1 updated_by g; RM updated_by f|>) ∧
         (∀r g f.
            r with <|RM updated_by f; RP updated_by g|> =
            r with <|RP updated_by g; RM updated_by f|>) ∧
         (∀r g f.
            r with <|RN updated_by f; R0 updated_by g|> =
            r with <|R0 updated_by g; RN updated_by f|>) ∧
         (∀r g f.
            r with <|RN updated_by f; R1 updated_by g|> =
            r with <|R1 updated_by g; RN updated_by f|>) ∧
         (∀r g f.
            r with <|RN updated_by f; RP updated_by g|> =
            r with <|RP updated_by g; RN updated_by f|>) ∧
         ∀r g f.
           r with <|RN updated_by f; RM updated_by g|> =
           r with <|RM updated_by g; RN updated_by f|>
   
   [ring_fupdcanon_comp]  Theorem
      
      |- ((∀g f.
              _ record fupdateR1 f o  _ record fupdateR0 g =
              _ record fupdateR0 g o  _ record fupdateR1 f) ∧
          ∀h g f.
             _ record fupdateR1 f o  _ record fupdateR0 g o h =
             _ record fupdateR0 g o  _ record fupdateR1 f o h) ∧
         ((∀g f.
              _ record fupdateRP f o  _ record fupdateR0 g =
              _ record fupdateR0 g o  _ record fupdateRP f) ∧
          ∀h g f.
             _ record fupdateRP f o  _ record fupdateR0 g o h =
             _ record fupdateR0 g o  _ record fupdateRP f o h) ∧
         ((∀g f.
              _ record fupdateRP f o  _ record fupdateR1 g =
              _ record fupdateR1 g o  _ record fupdateRP f) ∧
          ∀h g f.
             _ record fupdateRP f o  _ record fupdateR1 g o h =
             _ record fupdateR1 g o  _ record fupdateRP f o h) ∧
         ((∀g f.
              _ record fupdateRM f o  _ record fupdateR0 g =
              _ record fupdateR0 g o  _ record fupdateRM f) ∧
          ∀h g f.
             _ record fupdateRM f o  _ record fupdateR0 g o h =
             _ record fupdateR0 g o  _ record fupdateRM f o h) ∧
         ((∀g f.
              _ record fupdateRM f o  _ record fupdateR1 g =
              _ record fupdateR1 g o  _ record fupdateRM f) ∧
          ∀h g f.
             _ record fupdateRM f o  _ record fupdateR1 g o h =
             _ record fupdateR1 g o  _ record fupdateRM f o h) ∧
         ((∀g f.
              _ record fupdateRM f o  _ record fupdateRP g =
              _ record fupdateRP g o  _ record fupdateRM f) ∧
          ∀h g f.
             _ record fupdateRM f o  _ record fupdateRP g o h =
             _ record fupdateRP g o  _ record fupdateRM f o h) ∧
         ((∀g f.
              _ record fupdateRN f o  _ record fupdateR0 g =
              _ record fupdateR0 g o  _ record fupdateRN f) ∧
          ∀h g f.
             _ record fupdateRN f o  _ record fupdateR0 g o h =
             _ record fupdateR0 g o  _ record fupdateRN f o h) ∧
         ((∀g f.
              _ record fupdateRN f o  _ record fupdateR1 g =
              _ record fupdateR1 g o  _ record fupdateRN f) ∧
          ∀h g f.
             _ record fupdateRN f o  _ record fupdateR1 g o h =
             _ record fupdateR1 g o  _ record fupdateRN f o h) ∧
         ((∀g f.
              _ record fupdateRN f o  _ record fupdateRP g =
              _ record fupdateRP g o  _ record fupdateRN f) ∧
          ∀h g f.
             _ record fupdateRN f o  _ record fupdateRP g o h =
             _ record fupdateRP g o  _ record fupdateRN f o h) ∧
         (∀g f.
             _ record fupdateRN f o  _ record fupdateRM g =
             _ record fupdateRM g o  _ record fupdateRN f) ∧
         ∀h g f.
            _ record fupdateRN f o  _ record fupdateRM g o h =
            _ record fupdateRM g o  _ record fupdateRN f o h
   
   [ring_fupdfupds]  Theorem
      
      |- (∀r g f.
            r with <|R0 updated_by f; R0 updated_by g|> =
            r with R0 updated_by f o g) ∧
         (∀r g f.
            r with <|R1 updated_by f; R1 updated_by g|> =
            r with R1 updated_by f o g) ∧
         (∀r g f.
            r with <|RP updated_by f; RP updated_by g|> =
            r with RP updated_by f o g) ∧
         (∀r g f.
            r with <|RM updated_by f; RM updated_by g|> =
            r with RM updated_by f o g) ∧
         ∀r g f.
           r with <|RN updated_by f; RN updated_by g|> = r with RN updated_by f o g
   
   [ring_fupdfupds_comp]  Theorem
      
      |- ((∀g f.
              _ record fupdateR0 f o  _ record fupdateR0 g =
              _ record fupdateR0 (f o g)) ∧
          ∀h g f.
             _ record fupdateR0 f o  _ record fupdateR0 g o h =
             _ record fupdateR0 (f o g) o h) ∧
         ((∀g f.
              _ record fupdateR1 f o  _ record fupdateR1 g =
              _ record fupdateR1 (f o g)) ∧
          ∀h g f.
             _ record fupdateR1 f o  _ record fupdateR1 g o h =
             _ record fupdateR1 (f o g) o h) ∧
         ((∀g f.
              _ record fupdateRP f o  _ record fupdateRP g =
              _ record fupdateRP (f o g)) ∧
          ∀h g f.
             _ record fupdateRP f o  _ record fupdateRP g o h =
             _ record fupdateRP (f o g) o h) ∧
         ((∀g f.
              _ record fupdateRM f o  _ record fupdateRM g =
              _ record fupdateRM (f o g)) ∧
          ∀h g f.
             _ record fupdateRM f o  _ record fupdateRM g o h =
             _ record fupdateRM (f o g) o h) ∧
         (∀g f.
             _ record fupdateRN f o  _ record fupdateRN g =
             _ record fupdateRN (f o g)) ∧
         ∀h g f.
            _ record fupdateRN f o  _ record fupdateRN g o h =
            _ record fupdateRN (f o g) o h
   
   [ring_induction]  Theorem
      
      |- ∀P. (∀a a0 f f0 f1. P (ring a a0 f f0 f1)) ⇒ ∀r. P r
   
   [ring_is_semi_ring]  Theorem
      
      |- ∀r. is_ring r ⇒ is_semi_ring (semi_ring_of r)
   
   [ring_literal_11]  Theorem
      
      |- ∀a01 a1 f11 f01 f1 a02 a2 f12 f02 f2.
           (<|R0 := a01; R1 := a1; RP := f11; RM := f01; RN := f1|> =
            <|R0 := a02; R1 := a2; RP := f12; RM := f02; RN := f2|>) ⇔
           (a01 = a02) ∧ (a1 = a2) ∧ (f11 = f12) ∧ (f01 = f02) ∧ (f1 = f2)
   
   [ring_literal_nchotomy]  Theorem
      
      |- ∀r. ∃a0 a f1 f0 f. r = <|R0 := a0; R1 := a; RP := f1; RM := f0; RN := f|>
   
   [ring_nchotomy]  Theorem
      
      |- ∀rr. ∃a a0 f f0 f1. rr = ring a a0 f f0 f1
   
   [ring_updates_eq_literal]  Theorem
      
      |- ∀r a0 a f1 f0 f.
           r with <|R0 := a0; R1 := a; RP := f1; RM := f0; RN := f|> =
           <|R0 := a0; R1 := a; RP := f1; RM := f0; RN := f|>
   
   
*)
end
