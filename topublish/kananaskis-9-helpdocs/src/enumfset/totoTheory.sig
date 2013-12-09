signature totoTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ListOrd : thm
    val StrongLinearOrder_of_TO : thm
    val TO_inv : thm
    val TO_of_LinearOrder : thm
    val TotOrd : thm
    val WeakLinearOrder_of_TO : thm
    val charOrd : thm
    val charto : thm
    val cpn_BIJ : thm
    val cpn_CASE : thm
    val cpn_TY_DEF : thm
    val cpn_size_def : thm
    val imageOrd : thm
    val intOrd : thm
    val intto : thm
    val lexTO : thm
    val lextoto : thm
    val listorder_curried : thm
    val listorder_tupled_primitive : thm
    val listoto : thm
    val numOrd : thm
    val num_dtOrd_curried : thm
    val num_dtOrd_tupled_primitive : thm
    val num_dt_TY_DEF : thm
    val num_dt_case_def : thm
    val num_dt_size_def : thm
    val num_to_dt_primitive : thm
    val numto : thm
    val qk_numOrd_def : thm
    val qk_numto : thm
    val stringto : thm
    val to_bij : thm
    val toto_TY_DEF : thm
    val toto_inv : thm
    val toto_of_LinearOrder : thm

  (*  Theorems  *)
    val BIT1_gt_neg_thm : thm
    val BIT1_nz : thm
    val BIT2_gt_neg_thm : thm
    val BIT2_nz : thm
    val NOT_EQ_LESS_IMP : thm
    val TO_11 : thm
    val TO_apto_ID : thm
    val TO_apto_TO_ID : thm
    val TO_apto_TO_IMP : thm
    val TO_numOrd : thm
    val TO_onto : thm
    val TO_qk_numOrd : thm
    val TO_refl : thm
    val TotOrd_apto : thm
    val ZERO_eq_neg_ZERO_thm : thm
    val all_cpn_distinct : thm
    val ap_qk_numto_thm : thm
    val apcharto_thm : thm
    val apintto_thm : thm
    val aplextoto : thm
    val aplistoto : thm
    val apnumto_thm : thm
    val charOrd_eq_lem : thm
    val charOrd_gt_lem : thm
    val charOrd_lt_lem : thm
    val cpn2num_11 : thm
    val cpn2num_ONTO : thm
    val cpn2num_num2cpn : thm
    val cpn2num_thm : thm
    val cpn_Axiom : thm
    val cpn_EQ_cpn : thm
    val cpn_case_cong : thm
    val cpn_case_def : thm
    val cpn_distinct : thm
    val cpn_induction : thm
    val cpn_nchotomy : thm
    val datatype_cpn : thm
    val datatype_num_dt : thm
    val gt_neg_BIT1_thm : thm
    val gt_neg_BIT2_thm : thm
    val listorder : thm
    val listorder_ind : thm
    val neg_BIT1_lt_thm : thm
    val neg_BIT2_lt_thm : thm
    val neg_ZERO_eq_ZERO_thm : thm
    val neg_lt_BIT1_thm : thm
    val neg_lt_BIT2_thm : thm
    val neg_neg_thm : thm
    val num2cpn_11 : thm
    val num2cpn_ONTO : thm
    val num2cpn_cpn2num : thm
    val num2cpn_thm : thm
    val num_dtOrd : thm
    val num_dtOrd_ind : thm
    val num_dt_11 : thm
    val num_dt_Axiom : thm
    val num_dt_case_cong : thm
    val num_dt_distinct : thm
    val num_dt_induction : thm
    val num_dt_nchotomy : thm
    val numeralOrd : thm
    val onto_apto : thm
    val pos_pos_thm : thm
    val qk_numeralOrd : thm
    val totoEEtrans : thm
    val totoELtrans : thm
    val totoGGtrans : thm
    val totoGLtrans : thm
    val totoLEtrans : thm
    val totoLGtrans : thm
    val totoLLtrans : thm
    val toto_antisym : thm
    val toto_cpn_eqn : thm
    val toto_equal_eq : thm
    val toto_equal_imp : thm
    val toto_equal_imp_eq : thm
    val toto_equal_sym : thm
    val toto_glneq : thm
    val toto_not_less_refl : thm
    val toto_refl : thm
    val toto_swap_cases : thm
    val toto_trans_less : thm
    val toto_unequal_imp : thm

  val toto_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "toto"

   [int_arith] Parent theory of "toto"

   [string] Parent theory of "toto"

   [wot] Parent theory of "toto"

   [ListOrd]  Definition

      |- !c.
           ListOrd c =
           TO_of_LinearOrder (listorder (StrongLinearOrder_of_TO (apto c)))

   [StrongLinearOrder_of_TO]  Definition

      |- !c x y.
           StrongLinearOrder_of_TO c x y <=>
           case c x y of LESS => T | EQUAL => F | GREATER => F

   [TO_inv]  Definition

      |- !c x y. TO_inv c x y = c y x

   [TO_of_LinearOrder]  Definition

      |- !r x y.
           TO_of_LinearOrder r x y =
           if x = y then EQUAL else if r x y then LESS else GREATER

   [TotOrd]  Definition

      |- !c.
           TotOrd c <=>
           (!x y. (c x y = EQUAL) <=> (x = y)) /\
           (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
           !x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z = LESS)

   [WeakLinearOrder_of_TO]  Definition

      |- !c x y.
           WeakLinearOrder_of_TO c x y <=>
           case c x y of LESS => T | EQUAL => T | GREATER => F

   [charOrd]  Definition

      |- !a b. charOrd a b = numOrd (ORD a) (ORD b)

   [charto]  Definition

      |- charto = TO charOrd

   [cpn_BIJ]  Definition

      |- (!a. num2cpn (cpn2num a) = a) /\
         !r. (\n. n < 3) r <=> (cpn2num (num2cpn r) = r)

   [cpn_CASE]  Definition

      |- !x v0 v1 v2.
           (case x of LESS => v0 | EQUAL => v1 | GREATER => v2) =
           (\m. if m < 1 then v0 else if m = 1 then v1 else v2) (cpn2num x)

   [cpn_TY_DEF]  Definition

      |- ?rep. TYPE_DEFINITION (\n. n < 3) rep

   [cpn_size_def]  Definition

      |- !x. cpn_size x = 0

   [imageOrd]  Definition

      |- !f cp a b. imageOrd f cp a b = cp (f a) (f b)

   [intOrd]  Definition

      |- intOrd = TO_of_LinearOrder $<

   [intto]  Definition

      |- intto = TO intOrd

   [lexTO]  Definition

      |- !R V.
           R lexTO V =
           TO_of_LinearOrder
             (StrongLinearOrder_of_TO R LEX StrongLinearOrder_of_TO V)

   [lextoto]  Definition

      |- !c v. c lextoto v = TO (apto c lexTO apto v)

   [listorder_curried]  Definition

      |- !x x1 x2. listorder x x1 x2 <=> listorder_tupled (x,x1,x2)

   [listorder_tupled_primitive]  Definition

      |- listorder_tupled =
         WFREC (@R. WF R /\ !s r m l V. R (V,l,m) (V,r::l,s::m))
           (\listorder_tupled a.
              case a of
                (V,l,[]) => I F
              | (V,[],s::m) => I T
              | (V,r::l',s::m) =>
                  I (V r s \/ (r = s) /\ listorder_tupled (V,l',m)))

   [listoto]  Definition

      |- !c. listoto c = TO (ListOrd c)

   [numOrd]  Definition

      |- numOrd = TO_of_LinearOrder $<

   [num_dtOrd_curried]  Definition

      |- !x x1. num_dtOrd x x1 = num_dtOrd_tupled (x,x1)

   [num_dtOrd_tupled_primitive]  Definition

      |- num_dtOrd_tupled =
         WFREC
           (@R.
              WF R /\ (!y x. R (x,y) (bit1 x,bit1 y)) /\
              !y x. R (x,y) (bit2 x,bit2 y))
           (\num_dtOrd_tupled a.
              case a of
                (zer,zer) => I EQUAL
              | (zer,bit1 x) => I LESS
              | (zer,bit2 x') => I LESS
              | (bit1 x'',zer) => I GREATER
              | (bit1 x'',bit1 y'') => I (num_dtOrd_tupled (x'',y''))
              | (bit1 x'',bit2 y) => I LESS
              | (bit2 x''',zer) => I GREATER
              | (bit2 x''',bit1 y') => I GREATER
              | (bit2 x''',bit2 y''') => I (num_dtOrd_tupled (x''',y''')))

   [num_dt_TY_DEF]  Definition

      |- ?rep.
           TYPE_DEFINITION
             (\a0.
                !'num_dt' .
                  (!a0.
                     (a0 = ind_type$CONSTR 0 ARB (\n. ind_type$BOTTOM)) \/
                     (?a.
                        (a0 =
                         (\a.
                            ind_type$CONSTR (SUC 0) ARB
                              (ind_type$FCONS a (\n. ind_type$BOTTOM)))
                           a) /\ 'num_dt' a) \/
                     (?a.
                        (a0 =
                         (\a.
                            ind_type$CONSTR (SUC (SUC 0)) ARB
                              (ind_type$FCONS a (\n. ind_type$BOTTOM)))
                           a) /\ 'num_dt' a) ==>
                     'num_dt' a0) ==>
                  'num_dt' a0) rep

   [num_dt_case_def]  Definition

      |- (!v f f1. num_dt_CASE zer v f f1 = v) /\
         (!a v f f1. num_dt_CASE (bit1 a) v f f1 = f a) /\
         !a v f f1. num_dt_CASE (bit2 a) v f f1 = f1 a

   [num_dt_size_def]  Definition

      |- (num_dt_size zer = 0) /\
         (!a. num_dt_size (bit1 a) = 1 + num_dt_size a) /\
         !a. num_dt_size (bit2 a) = 1 + num_dt_size a

   [num_to_dt_primitive]  Definition

      |- num_to_dt =
         WFREC
           (@R.
              WF R /\ (!n. n <> 0 /\ ODD n ==> R (DIV2 (n - 1)) n) /\
              !n. n <> 0 /\ ~ODD n ==> R (DIV2 (n - 2)) n)
           (\num_to_dt n.
              I
                (if n = 0 then zer
                 else if ODD n then bit1 (num_to_dt (DIV2 (n - 1)))
                 else bit2 (num_to_dt (DIV2 (n - 2)))))

   [numto]  Definition

      |- numto = TO numOrd

   [qk_numOrd_def]  Definition

      |- !m n. qk_numOrd m n = num_dtOrd (num_to_dt m) (num_to_dt n)

   [qk_numto]  Definition

      |- qk_numto = TO qk_numOrd

   [stringto]  Definition

      |- stringto = listoto charto

   [to_bij]  Definition

      |- (!a. TO (apto a) = a) /\ !r. TotOrd r <=> (apto (TO r) = r)

   [toto_TY_DEF]  Definition

      |- ?rep. TYPE_DEFINITION TotOrd rep

   [toto_inv]  Definition

      |- !c. toto_inv c = TO (TO_inv (apto c))

   [toto_of_LinearOrder]  Definition

      |- !r. toto_of_LinearOrder r = TO (TO_of_LinearOrder r)

   [BIT1_gt_neg_thm]  Theorem

      |- !m n. intOrd (&BIT1 m) (-&n) = GREATER

   [BIT1_nz]  Theorem

      |- !n. BIT1 n <> 0

   [BIT2_gt_neg_thm]  Theorem

      |- !m n. intOrd (&BIT2 m) (-&n) = GREATER

   [BIT2_nz]  Theorem

      |- !n. BIT2 n <> 0

   [NOT_EQ_LESS_IMP]  Theorem

      |- !cmp x y.
           apto cmp x y <> LESS ==> (x = y) \/ (apto cmp y x = LESS)

   [TO_11]  Theorem

      |- !r r'. TotOrd r ==> TotOrd r' ==> ((TO r = TO r') <=> (r = r'))

   [TO_apto_ID]  Theorem

      |- !a. TO (apto a) = a

   [TO_apto_TO_ID]  Theorem

      |- !r. TotOrd r <=> (apto (TO r) = r)

   [TO_apto_TO_IMP]  Theorem

      |- !r. TotOrd r ==> (apto (TO r) = r)

   [TO_numOrd]  Theorem

      |- TotOrd numOrd

   [TO_onto]  Theorem

      |- !a. ?r. (a = TO r) /\ TotOrd r

   [TO_qk_numOrd]  Theorem

      |- TotOrd qk_numOrd

   [TO_refl]  Theorem

      |- !c. TotOrd c ==> !x. c x x = EQUAL

   [TotOrd_apto]  Theorem

      |- !c. TotOrd (apto c)

   [ZERO_eq_neg_ZERO_thm]  Theorem

      |- intOrd (&ZERO) (-&ZERO) = EQUAL

   [all_cpn_distinct]  Theorem

      |- (LESS <> EQUAL /\ LESS <> GREATER /\ EQUAL <> GREATER) /\
         EQUAL <> LESS /\ GREATER <> LESS /\ GREATER <> EQUAL

   [ap_qk_numto_thm]  Theorem

      |- apto qk_numto = qk_numOrd

   [apcharto_thm]  Theorem

      |- apto charto = charOrd

   [apintto_thm]  Theorem

      |- apto intto = intOrd

   [aplextoto]  Theorem

      |- !c v x1 x2 y1 y2.
           apto (c lextoto v) (x1,x2) (y1,y2) =
           case apto c x1 y1 of
             LESS => LESS
           | EQUAL => apto v x2 y2
           | GREATER => GREATER

   [aplistoto]  Theorem

      |- !c.
           (apto (listoto c) [] [] = EQUAL) /\
           (!b y. apto (listoto c) [] (b::y) = LESS) /\
           (!a x. apto (listoto c) (a::x) [] = GREATER) /\
           !a x b y.
             apto (listoto c) (a::x) (b::y) =
             case apto c a b of
               LESS => LESS
             | EQUAL => apto (listoto c) x y
             | GREATER => GREATER

   [apnumto_thm]  Theorem

      |- apto numto = numOrd

   [charOrd_eq_lem]  Theorem

      |- !a b. (numOrd a b = EQUAL) ==> (charOrd (CHR a) (CHR b) = EQUAL)

   [charOrd_gt_lem]  Theorem

      |- !a b.
           (numOrd a b = GREATER) ==>
           (a < 256 <=> T) ==>
           (charOrd (CHR a) (CHR b) = GREATER)

   [charOrd_lt_lem]  Theorem

      |- !a b.
           (numOrd a b = LESS) ==>
           (b < 256 <=> T) ==>
           (charOrd (CHR a) (CHR b) = LESS)

   [cpn2num_11]  Theorem

      |- !a a'. (cpn2num a = cpn2num a') <=> (a = a')

   [cpn2num_ONTO]  Theorem

      |- !r. r < 3 <=> ?a. r = cpn2num a

   [cpn2num_num2cpn]  Theorem

      |- !r. r < 3 <=> (cpn2num (num2cpn r) = r)

   [cpn2num_thm]  Theorem

      |- (cpn2num LESS = 0) /\ (cpn2num EQUAL = 1) /\ (cpn2num GREATER = 2)

   [cpn_Axiom]  Theorem

      |- !x0 x1 x2. ?f. (f LESS = x0) /\ (f EQUAL = x1) /\ (f GREATER = x2)

   [cpn_EQ_cpn]  Theorem

      |- !a a'. (a = a') <=> (cpn2num a = cpn2num a')

   [cpn_case_cong]  Theorem

      |- !M M' v0 v1 v2.
           (M = M') /\ ((M' = LESS) ==> (v0 = v0')) /\
           ((M' = EQUAL) ==> (v1 = v1')) /\
           ((M' = GREATER) ==> (v2 = v2')) ==>
           ((case M of LESS => v0 | EQUAL => v1 | GREATER => v2) =
            case M' of LESS => v0' | EQUAL => v1' | GREATER => v2')

   [cpn_case_def]  Theorem

      |- (!v0 v1 v2.
            (case LESS of LESS => v0 | EQUAL => v1 | GREATER => v2) =
            v0) /\
         (!v0 v1 v2.
            (case EQUAL of LESS => v0 | EQUAL => v1 | GREATER => v2) =
            v1) /\
         !v0 v1 v2.
           (case GREATER of LESS => v0 | EQUAL => v1 | GREATER => v2) = v2

   [cpn_distinct]  Theorem

      |- LESS <> EQUAL /\ LESS <> GREATER /\ EQUAL <> GREATER

   [cpn_induction]  Theorem

      |- !P. P EQUAL /\ P GREATER /\ P LESS ==> !a. P a

   [cpn_nchotomy]  Theorem

      |- !a. (a = LESS) \/ (a = EQUAL) \/ (a = GREATER)

   [datatype_cpn]  Theorem

      |- DATATYPE (cpn LESS EQUAL GREATER)

   [datatype_num_dt]  Theorem

      |- DATATYPE (num_dt zer bit1 bit2)

   [gt_neg_BIT1_thm]  Theorem

      |- !m n. intOrd (&m) (-&BIT1 n) = GREATER

   [gt_neg_BIT2_thm]  Theorem

      |- !m n. intOrd (&m) (-&BIT2 n) = GREATER

   [listorder]  Theorem

      |- (!l V. listorder V l [] <=> F) /\
         (!s m V. listorder V [] (s::m) <=> T) /\
         !s r m l V.
           listorder V (r::l) (s::m) <=>
           V r s \/ (r = s) /\ listorder V l m

   [listorder_ind]  Theorem

      |- !P.
           (!V l. P V l []) /\ (!V s m. P V [] (s::m)) /\
           (!V r l s m. P V l m ==> P V (r::l) (s::m)) ==>
           !v v1 v2. P v v1 v2

   [neg_BIT1_lt_thm]  Theorem

      |- !m n. intOrd (-&BIT1 m) (&n) = LESS

   [neg_BIT2_lt_thm]  Theorem

      |- !m n. intOrd (-&BIT2 m) (&n) = LESS

   [neg_ZERO_eq_ZERO_thm]  Theorem

      |- intOrd (-&ZERO) (&ZERO) = EQUAL

   [neg_lt_BIT1_thm]  Theorem

      |- !m n. intOrd (-&m) (&BIT1 n) = LESS

   [neg_lt_BIT2_thm]  Theorem

      |- !m n. intOrd (-&m) (&BIT2 n) = LESS

   [neg_neg_thm]  Theorem

      |- !m n. intOrd (-&m) (-&n) = numOrd n m

   [num2cpn_11]  Theorem

      |- !r r'.
           r < 3 ==> r' < 3 ==> ((num2cpn r = num2cpn r') <=> (r = r'))

   [num2cpn_ONTO]  Theorem

      |- !a. ?r. (a = num2cpn r) /\ r < 3

   [num2cpn_cpn2num]  Theorem

      |- !a. num2cpn (cpn2num a) = a

   [num2cpn_thm]  Theorem

      |- (num2cpn 0 = LESS) /\ (num2cpn 1 = EQUAL) /\ (num2cpn 2 = GREATER)

   [num_dtOrd]  Theorem

      |- (num_dtOrd zer zer = EQUAL) /\
         (!x. num_dtOrd zer (bit1 x) = LESS) /\
         (!x. num_dtOrd zer (bit2 x) = LESS) /\
         (!x. num_dtOrd (bit1 x) zer = GREATER) /\
         (!x. num_dtOrd (bit2 x) zer = GREATER) /\
         (!y x. num_dtOrd (bit1 x) (bit2 y) = LESS) /\
         (!y x. num_dtOrd (bit2 x) (bit1 y) = GREATER) /\
         (!y x. num_dtOrd (bit1 x) (bit1 y) = num_dtOrd x y) /\
         !y x. num_dtOrd (bit2 x) (bit2 y) = num_dtOrd x y

   [num_dtOrd_ind]  Theorem

      |- !P.
           P zer zer /\ (!x. P zer (bit1 x)) /\ (!x. P zer (bit2 x)) /\
           (!x. P (bit1 x) zer) /\ (!x. P (bit2 x) zer) /\
           (!x y. P (bit1 x) (bit2 y)) /\ (!x y. P (bit2 x) (bit1 y)) /\
           (!x y. P x y ==> P (bit1 x) (bit1 y)) /\
           (!x y. P x y ==> P (bit2 x) (bit2 y)) ==>
           !v v1. P v v1

   [num_dt_11]  Theorem

      |- (!a a'. (bit1 a = bit1 a') <=> (a = a')) /\
         !a a'. (bit2 a = bit2 a') <=> (a = a')

   [num_dt_Axiom]  Theorem

      |- !f0 f1 f2.
           ?fn.
             (fn zer = f0) /\ (!a. fn (bit1 a) = f1 a (fn a)) /\
             !a. fn (bit2 a) = f2 a (fn a)

   [num_dt_case_cong]  Theorem

      |- !M M' v f f1.
           (M = M') /\ ((M' = zer) ==> (v = v')) /\
           (!a. (M' = bit1 a) ==> (f a = f' a)) /\
           (!a. (M' = bit2 a) ==> (f1 a = f1' a)) ==>
           (num_dt_CASE M v f f1 = num_dt_CASE M' v' f' f1')

   [num_dt_distinct]  Theorem

      |- (!a. zer <> bit1 a) /\ (!a. zer <> bit2 a) /\
         !a' a. bit1 a <> bit2 a'

   [num_dt_induction]  Theorem

      |- !P.
           P zer /\ (!n. P n ==> P (bit1 n)) /\
           (!n. P n ==> P (bit2 n)) ==>
           !n. P n

   [num_dt_nchotomy]  Theorem

      |- !nn. (nn = zer) \/ (?n. nn = bit1 n) \/ ?n. nn = bit2 n

   [numeralOrd]  Theorem

      |- !x y.
           (numOrd ZERO ZERO = EQUAL) /\ (numOrd ZERO (BIT1 y) = LESS) /\
           (numOrd ZERO (BIT2 y) = LESS) /\
           (numOrd (BIT1 x) ZERO = GREATER) /\
           (numOrd (BIT2 x) ZERO = GREATER) /\
           (numOrd (BIT1 x) (BIT1 y) = numOrd x y) /\
           (numOrd (BIT2 x) (BIT2 y) = numOrd x y) /\
           (numOrd (BIT1 x) (BIT2 y) =
            case numOrd x y of
              LESS => LESS
            | EQUAL => LESS
            | GREATER => GREATER) /\
           (numOrd (BIT2 x) (BIT1 y) =
            case numOrd x y of
              LESS => LESS
            | EQUAL => GREATER
            | GREATER => GREATER)

   [onto_apto]  Theorem

      |- !r. TotOrd r <=> ?a. r = apto a

   [pos_pos_thm]  Theorem

      |- !m n. intOrd (&m) (&n) = numOrd m n

   [qk_numeralOrd]  Theorem

      |- !x y.
           (qk_numOrd ZERO ZERO = EQUAL) /\
           (qk_numOrd ZERO (BIT1 y) = LESS) /\
           (qk_numOrd ZERO (BIT2 y) = LESS) /\
           (qk_numOrd (BIT1 x) ZERO = GREATER) /\
           (qk_numOrd (BIT2 x) ZERO = GREATER) /\
           (qk_numOrd (BIT1 x) (BIT1 y) = qk_numOrd x y) /\
           (qk_numOrd (BIT2 x) (BIT2 y) = qk_numOrd x y) /\
           (qk_numOrd (BIT1 x) (BIT2 y) = LESS) /\
           (qk_numOrd (BIT2 x) (BIT1 y) = GREATER)

   [totoEEtrans]  Theorem

      |- !c x y z.
           ((apto c x y = EQUAL) /\ (apto c y z = EQUAL) ==>
            (apto c x z = EQUAL)) /\
           ((apto c x y = EQUAL) /\ (apto c z y = EQUAL) ==>
            (apto c x z = EQUAL))

   [totoELtrans]  Theorem

      |- !c x y z.
           (apto c x y = EQUAL) /\ (apto c y z = LESS) ==>
           (apto c x z = LESS)

   [totoGGtrans]  Theorem

      |- !c x y z.
           (apto c y x = GREATER) /\ (apto c z y = GREATER) ==>
           (apto c x z = LESS)

   [totoGLtrans]  Theorem

      |- !c x y z.
           (apto c y x = GREATER) /\ (apto c y z = LESS) ==>
           (apto c x z = LESS)

   [totoLEtrans]  Theorem

      |- !c x y z.
           (apto c x y = LESS) /\ (apto c y z = EQUAL) ==>
           (apto c x z = LESS)

   [totoLGtrans]  Theorem

      |- !c x y z.
           (apto c x y = LESS) /\ (apto c z y = GREATER) ==>
           (apto c x z = LESS)

   [totoLLtrans]  Theorem

      |- !c x y z.
           (apto c x y = LESS) /\ (apto c y z = LESS) ==>
           (apto c x z = LESS)

   [toto_antisym]  Theorem

      |- !c x y. (apto c x y = GREATER) <=> (apto c y x = LESS)

   [toto_cpn_eqn]  Theorem

      |- (!c x y. (apto c x y = EQUAL) ==> (x = y)) /\
         (!c x y. (apto c x y = LESS) ==> x <> y) /\
         !c x y. (apto c x y = GREATER) ==> x <> y

   [toto_equal_eq]  Theorem

      |- !c x y. (apto c x y = EQUAL) <=> (x = y)

   [toto_equal_imp]  Theorem

      |- !cmp phi.
           LinearOrder phi /\ (cmp = toto_of_LinearOrder phi) ==>
           !x y. ((x = y) <=> T) ==> (apto cmp x y = EQUAL)

   [toto_equal_imp_eq]  Theorem

      |- !c x y. (apto c x y = EQUAL) ==> (x = y)

   [toto_equal_sym]  Theorem

      |- !c x y. (apto c x y = EQUAL) <=> (apto c y x = EQUAL)

   [toto_glneq]  Theorem

      |- (!c x y. (apto c x y = LESS) ==> x <> y) /\
         !c x y. (apto c x y = GREATER) ==> x <> y

   [toto_not_less_refl]  Theorem

      |- !cmp h. (apto cmp h h = LESS) <=> F

   [toto_refl]  Theorem

      |- !c x. apto c x x = EQUAL

   [toto_swap_cases]  Theorem

      |- !c x y.
           apto c y x =
           case apto c x y of
             LESS => GREATER
           | EQUAL => EQUAL
           | GREATER => LESS

   [toto_trans_less]  Theorem

      |- (!c x y z.
            (apto c x y = LESS) /\ (apto c y z = LESS) ==>
            (apto c x z = LESS)) /\
         (!c x y z.
            (apto c x y = LESS) /\ (apto c z y = GREATER) ==>
            (apto c x z = LESS)) /\
         (!c x y z.
            (apto c y x = GREATER) /\ (apto c z y = GREATER) ==>
            (apto c x z = LESS)) /\
         (!c x y z.
            (apto c y x = GREATER) /\ (apto c y z = LESS) ==>
            (apto c x z = LESS)) /\
         (!c x y z.
            (apto c x y = LESS) /\ (apto c y z = EQUAL) ==>
            (apto c x z = LESS)) /\
         !c x y z.
           (apto c x y = EQUAL) /\ (apto c y z = LESS) ==>
           (apto c x z = LESS)

   [toto_unequal_imp]  Theorem

      |- !cmp phi.
           LinearOrder phi /\ (cmp = toto_of_LinearOrder phi) ==>
           !x y.
             ((x = y) <=> F) ==>
             if phi x y then apto cmp x y = LESS
             else apto cmp x y = GREATER


*)
end
